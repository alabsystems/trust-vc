// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::extern_spec_registry::{ExternSpecEntry, ResolutionScope};
use crate::vc::ObligationKind;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn test_register_extern_spec() {
    register_extern_spec("Option::unwrap", &["self.is_some()".to_string()], &[]);

    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        let contracts = contracts.borrow();
        assert_eq!(contracts.len(), 1);
        assert_eq!(contracts[0].target, "Option::unwrap");
        assert!(contracts[0].param_names.is_empty());
        assert_eq!(contracts[0].requires, vec!["self.is_some()"]);
    });
}

#[test]
fn test_apply_extern_specs() {
    EXTERN_SPEC_CONTRACTS.with(|c| c.borrow_mut().clear());
    register_extern_spec(
        "Vec::pop",
        &["self.len() > 0".to_string()],
        &["result.is_some()".to_string()],
    );

    let mut ctx = VerificationContext::new();
    apply_extern_specs_to_context(&mut ctx).unwrap();

    // Should have 2 obligations: 1 requires (assert) + 1 ensures (assume)
    assert_eq!(ctx.obligations.len(), 2);

    // Requires → Assert (caller must prove preconditions)
    let req = ctx
        .obligations
        .iter()
        .find(|o| o.name.contains("requires"))
        .unwrap();
    assert_eq!(
        req.kind,
        ObligationKind::Assert,
        "requires should be Assert at call site"
    );

    // Ensures → Assume (caller assumes postconditions)
    let ens = ctx
        .obligations
        .iter()
        .find(|o| o.name.contains("ensures"))
        .unwrap();
    assert_eq!(
        ens.kind,
        ObligationKind::Assume,
        "ensures should be Assume at call site"
    );
}

#[test]
fn test_register_extern_spec_from_source_loads_contracts() {
    clear_extern_contracts();

    register_extern_spec_from_source(
        "register_from_source.rs",
        r#"
                trust_vc::extern_spec! {
                    impl i32 {
                        #[requires(false)]
                        #[ensures(true)]
                        fn abs(self) -> i32;
                    }
                }
            "#,
        "i32::abs",
    )
    .expect("source-backed registration should succeed");

    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        let contracts = contracts.borrow();
        assert_eq!(contracts.len(), 1);
        assert_eq!(contracts[0].target, "i32::abs");
        assert!(contracts[0].param_names.is_empty());
        assert_eq!(contracts[0].requires, vec!["false"]);
        assert_eq!(contracts[0].ensures, vec!["true"]);
    });
}

#[test]
fn test_spec_registration_and_application() {
    // Test the full flow from registration to application
    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        contracts.borrow_mut().clear();
    });

    // Register multiple specs
    register_extern_spec(
        "HashMap::get",
        &["self.contains_key(key)".to_string()],
        &["result.is_some()".to_string()],
    );

    register_extern_spec(
        "Vec::index",
        &["index < self.len()".to_string()],
        &["result == self[index]".to_string()],
    );

    // Apply all specs to context
    let mut ctx = VerificationContext::new();
    apply_extern_specs_to_context(&mut ctx).unwrap();

    // Should have obligations for both requires and ensures from both functions
    // 2 functions × (1 requires + 1 ensures) = 4 obligations
    assert!(ctx.obligations.len() >= 4);

    // Verify specific obligations exist
    let obligation_names: Vec<String> = ctx.obligations.iter().map(|o| o.name.clone()).collect();

    assert!(obligation_names
        .iter()
        .any(|n| n.contains("HashMap::get_requires")));
    assert!(obligation_names
        .iter()
        .any(|n| n.contains("HashMap::get_ensures")));
    assert!(obligation_names
        .iter()
        .any(|n| n.contains("Vec::index_requires")));
    assert!(obligation_names
        .iter()
        .any(|n| n.contains("Vec::index_ensures")));
}

#[test]
fn test_register_extern_spec_from_source_errors_on_lexical_mismatch() {
    clear_extern_contracts();

    let error = register_extern_spec_from_source(
        "register_mismatch.rs",
        r#"
                trust_vc::extern_spec! {
                    impl std::vec::Vec::<T> {
                        fn pop(&mut self) -> Option<T>;
                    }
                }
            "#,
        "Vec::<i32>::pop",
    )
    .expect_err("lexical mismatch should fail closed");
    let error = error.to_string();

    assert!(
        error.contains("file-local only"),
        "error should explain file-local-only lookup, got: {error}"
    );
    assert!(
        error.contains("external_spec!"),
        "error should mention the preferred alias spelling, got: {error}"
    );
}

#[test]
fn test_cross_crate_target_produces_specific_diagnostic() {
    clear_extern_contracts();

    let error = register_extern_spec_from_source(
        "cross_crate.rs",
        "", // empty source — no extern_spec blocks
        "std::vec::Vec::pop",
    )
    .expect_err("cross-crate target without local spec should fail");
    let error = error.to_string();

    assert!(
        error.contains("cross-crate"),
        "error should mention cross-crate resolution: {error}"
    );
    assert!(
        error.contains("#2392"),
        "error should reference tracking issue: {error}"
    );
    assert!(
        error.contains("external_spec!"),
        "error should mention the preferred alias spelling, got: {error}"
    );
}

fn unique_test_dir(name: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    PathBuf::from("target")
        .join("extern_spec_verify_tests")
        .join(format!("{name}_{nonce}"))
}

struct ManifestCatalogFixture {
    cleanup_root: PathBuf,
    manifest_dir: PathBuf,
}

impl ManifestCatalogFixture {
    fn new(name: &str) -> Self {
        let cleanup_root = unique_test_dir(name);
        let manifest_dir = cleanup_root.join("crate");
        fs::create_dir_all(&manifest_dir).expect("should create manifest dir");
        fs::write(
            manifest_dir.join("Cargo.toml"),
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("should write fixture manifest");
        Self {
            cleanup_root,
            manifest_dir,
        }
    }

    fn manifest_dir(&self) -> &Path {
        &self.manifest_dir
    }

    fn write(&self, relative_path: &str, source: &str) {
        let path = self.manifest_dir.join(relative_path);
        fs::create_dir_all(path.parent().expect("fixture file should have a parent"))
            .expect("should create fixture directories");
        fs::write(path, source).expect("should write fixture source");
    }
}

impl Drop for ManifestCatalogFixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.cleanup_root).ok();
    }
}

fn write_abs_spec(fixture: &ManifestCatalogFixture, relative_path: &str, requires: bool) {
    let requires_text = if requires { "true" } else { "false" };
    fixture.write(
        relative_path,
        &format!(
            r#"
                trust_vc::extern_spec! {{
                    impl i32 {{
                        #[requires({requires_text})]
                        fn abs(self) -> i32;
                    }}
                }}
            "#
        ),
    );
}

#[test]
fn test_register_extern_spec_from_call_site_reads_manifest_relative_source() {
    clear_extern_contracts();

    let test_dir = unique_test_dir("manifest_relative");
    let manifest_dir = test_dir.join("crate");
    let test_file = manifest_dir.join("tests").join("call_site.rs");
    fs::create_dir_all(test_file.parent().expect("test file should have a parent"))
        .expect("should create manifest-relative test directory");
    fs::write(
        &test_file,
        r#"
                trust_vc::extern_spec! {
                    impl i32 {
                        #[requires(false)]
                        fn abs(self) -> i32;
                    }
                }
            "#,
    )
    .expect("should write manifest-relative source");

    register_extern_spec_from_call_site(
        "tests/call_site.rs",
        manifest_dir.to_str().expect("manifest dir should be utf-8"),
        "i32::abs",
    )
    .expect("manifest-relative call site should resolve");

    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        let contracts = contracts.borrow();
        assert_eq!(contracts.len(), 1);
        assert_eq!(contracts[0].target, "i32::abs");
        assert!(contracts[0].param_names.is_empty());
        assert_eq!(contracts[0].requires, vec!["false"]);
    });

    fs::remove_dir_all(&test_dir).ok();
}

#[test]
fn test_lookup_extern_spec_in_manifest_prefers_exact_caller_file_match() {
    let fixture = ManifestCatalogFixture::new("exact_caller_file");
    write_abs_spec(&fixture, "tests/call_site.rs", false);
    write_abs_spec(&fixture, "src/specs.rs", true);

    let contract = crate::extern_spec_catalog::lookup_extern_spec_in_manifest(
        fixture.manifest_dir(),
        "i32::abs",
        Some("tests/call_site.rs"),
    )
    .expect("lookup should succeed")
    .expect("caller file should disambiguate exact match");

    assert!(
        contract
            .source_file
            .ends_with(Path::new("tests/call_site.rs")),
        "exact caller-file suffix should win, got: {}",
        contract.source_file.display()
    );
    assert_eq!(contract.entry.requires, vec!["false"]);
}

#[test]
fn test_lookup_extern_spec_in_manifest_prefers_caller_stem_subtree_match() {
    let fixture = ManifestCatalogFixture::new("caller_stem_subtree");
    fixture.write(
        "tests/extern_spec_cross_file_verify.rs",
        "// call-site file only\n",
    );
    write_abs_spec(
        &fixture,
        "tests/extern_spec_cross_file_verify/helpers.rs",
        false,
    );
    write_abs_spec(&fixture, "src/specs.rs", true);

    let contract = crate::extern_spec_catalog::lookup_extern_spec_in_manifest(
        fixture.manifest_dir(),
        "i32::abs",
        Some("tests/extern_spec_cross_file_verify.rs"),
    )
    .expect("lookup should succeed")
    .expect("caller stem subtree should disambiguate broad match");

    assert!(
        contract
            .source_file
            .ends_with(Path::new("tests/extern_spec_cross_file_verify/helpers.rs")),
        "caller-stem subtree should win, got: {}",
        contract.source_file.display()
    );
    assert_eq!(contract.entry.requires, vec!["false"]);
}

#[test]
fn test_lookup_extern_spec_in_manifest_errors_without_caller_file() {
    let fixture = ManifestCatalogFixture::new("no_caller_file");
    write_abs_spec(&fixture, "tests/spec_a.rs", false);
    write_abs_spec(&fixture, "src/spec_b.rs", true);

    let error = crate::extern_spec_catalog::lookup_extern_spec_in_manifest(
        fixture.manifest_dir(),
        "i32::abs",
        None,
    )
    .expect_err("missing caller file should leave exact-match ambiguity unresolved")
    .to_string();

    assert!(error.contains("ambiguous extern_spec lookup for `i32::abs`"));
    assert!(error.contains("tests/spec_a.rs"));
    assert!(error.contains("src/spec_b.rs"));
}

#[test]
fn test_lookup_extern_spec_in_manifest_errors_when_caller_file_has_no_match() {
    let fixture = ManifestCatalogFixture::new("caller_no_match");
    fixture.write("tests/call_site.rs", "// unrelated caller file\n");
    write_abs_spec(&fixture, "tests/spec_a.rs", false);
    write_abs_spec(&fixture, "src/spec_b.rs", true);

    let error = crate::extern_spec_catalog::lookup_extern_spec_in_manifest(
        fixture.manifest_dir(),
        "i32::abs",
        Some("tests/call_site.rs"),
    )
    .expect_err("non-matching caller path should preserve ambiguity")
    .to_string();

    assert!(error.contains("ambiguous extern_spec lookup for `i32::abs`"));
    assert!(error.contains("tests/spec_a.rs"));
    assert!(error.contains("src/spec_b.rs"));
}

#[test]
fn test_lookup_extern_spec_in_manifest_errors_for_multiple_exact_suffix_matches() {
    let fixture = ManifestCatalogFixture::new("multiple_exact_suffixes");
    write_abs_spec(&fixture, "tests/call_site.rs", false);
    write_abs_spec(&fixture, "src/nested/tests/call_site.rs", true);

    let error = crate::extern_spec_catalog::lookup_extern_spec_in_manifest(
        fixture.manifest_dir(),
        "i32::abs",
        Some("tests/call_site.rs"),
    )
    .expect_err("multiple exact suffix matches should remain ambiguous")
    .to_string();

    assert!(error.contains("ambiguous extern_spec lookup for `i32::abs`"));
    assert!(error.contains("tests/call_site.rs"));
    assert!(error.contains("src/nested/tests/call_site.rs"));
}

#[test]
fn test_register_extern_spec_from_call_site_reads_workspace_relative_source() {
    clear_extern_contracts();

    let test_dir = unique_test_dir("workspace_relative");
    let workspace_root = test_dir.join("workspace");
    let manifest_dir = workspace_root.join("nested").join("path").join("member");
    let test_file = manifest_dir.join("tests").join("call_site.rs");
    fs::create_dir_all(test_file.parent().expect("test file should have a parent"))
        .expect("should create workspace-relative test directory");
    fs::write(
        &test_file,
        r#"
                trust_vc::extern_spec! {
                    impl i32 {
                        #[requires(true)]
                        #[ensures(true)]
                        fn signum(self) -> i32;
                    }
                }
            "#,
    )
    .expect("should write workspace-relative source");

    register_extern_spec_from_call_site(
        "nested/path/member/tests/call_site.rs",
        manifest_dir.to_str().expect("manifest dir should be utf-8"),
        "i32::signum",
    )
    .expect("workspace-relative call site should resolve from an ancestor");

    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        let contracts = contracts.borrow();
        assert_eq!(contracts.len(), 1);
        assert_eq!(contracts[0].target, "i32::signum");
        assert!(contracts[0].param_names.is_empty());
        assert_eq!(contracts[0].requires, vec!["true"]);
        assert_eq!(contracts[0].ensures, vec!["true"]);
    });

    fs::remove_dir_all(&test_dir).ok();
}

#[test]
fn test_register_extern_spec_from_manifest_scope_reports_supported_boundary() {
    clear_extern_contracts();

    let test_dir = unique_test_dir("manifest_scope_miss");
    let manifest_dir = test_dir.join("crate");
    let test_file = manifest_dir.join("tests").join("call_site.rs");
    fs::create_dir_all(test_file.parent().expect("test file should have a parent"))
        .expect("should create manifest-scope miss directory");
    fs::write(&test_file, "// no extern_spec declarations here\n")
        .expect("should write call-site source");

    let error = register_extern_spec_from_manifest_scope(
        "tests/call_site.rs",
        manifest_dir.to_str().expect("manifest dir should be utf-8"),
        "core::primitive::i32::abs",
    )
    .expect_err("cross-package target should fail closed");
    let error = error.to_string();

    assert!(
        error.contains("current package rooted at"),
        "error should mention the searched current package, got: {error}"
    );
    assert!(
        error.contains("dependency crates are not searched"),
        "error should mention the unsupported dependency-crate boundary, got: {error}"
    );

    fs::remove_dir_all(&test_dir).ok();
}

#[test]
fn test_apply_extern_specs_polarity() {
    // Regression test: apply_extern_specs_to_context must use correct polarity.
    // requires -> Assert (caller must prove preconditions)
    // ensures -> Assume (caller trusts postconditions)
    // Previously both were inverted (requires=Assume, ensures=Assert).
    EXTERN_SPEC_CONTRACTS.with(|contracts| {
        contracts.borrow_mut().clear();
    });

    register_extern_spec(
        "test_fn",
        &["x > 0".to_string()],
        &["result > 0".to_string()],
    );

    let mut ctx = VerificationContext::new();
    apply_extern_specs_to_context(&mut ctx).unwrap();

    assert_eq!(ctx.obligations.len(), 2);

    let req = ctx
        .obligations
        .iter()
        .find(|o| o.name.contains("requires"))
        .expect("Should have requires obligation");
    assert_eq!(
        req.kind,
        ObligationKind::Assert,
        "requires must be Assert (caller proves precondition)"
    );

    let ens = ctx
        .obligations
        .iter()
        .find(|o| o.name.contains("ensures"))
        .expect("Should have ensures obligation");
    assert_eq!(
        ens.kind,
        ObligationKind::Assume,
        "ensures must be Assume (caller trusts postcondition)"
    );
}

#[test]
fn test_apply_extern_specs_substitutes_call_bindings() {
    clear_extern_contracts();
    register_extern_spec_entry(
        ExternSpecEntry {
            target_path: "u32::rotate_left".to_string(),
            param_names: vec!["shift".to_string()],
            requires: vec!["shift == 0".to_string()],
            ensures: vec!["result == self".to_string()],
            resolution_scope: ResolutionScope::FileLocal,
        },
        Some(ExternSpecCallBindings {
            receiver_expr: Some("input".to_string()),
            arg_exprs: vec!["zero_amount".to_string()],
            result_expr: Some("rotated".to_string()),
        }),
    );

    let mut ctx = VerificationContext::new();
    apply_extern_specs_to_context(&mut ctx).expect("bound extern specs should apply");

    let requires = ctx
        .obligations
        .iter()
        .find(|obligation| obligation.name.contains("requires"))
        .expect("requires obligation should exist");
    assert!(requires.condition.contains("zero_amount"));
    assert!(!requires.condition.contains("shift == 0"));

    let ensures = ctx
        .obligations
        .iter()
        .find(|obligation| obligation.name.contains("ensures"))
        .expect("ensures obligation should exist");
    assert!(ensures.condition.contains("rotated"));
    assert!(ensures.condition.contains("input"));
    assert!(!ensures.condition.contains("result == self"));
}

#[test]
fn test_clear_extern_contracts_skips_on_borrow_conflict() {
    // clear_extern_contracts gracefully skips when borrowed (#1955).
    // Cleanup functions must not panic — panicking aborts ALL subsequent
    // clears in clear_all_thread_locals.
    test_helpers::with_extern_spec_contracts_borrowed(|| {
        clear_extern_contracts(); // should complete without panicking
    });
}
