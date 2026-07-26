// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;
use trust_vc_core::{clear_extern_contracts, register_extern_spec_from_manifest_scope};

struct ManifestFixture {
    cleanup_root: PathBuf,
    manifest_dir: PathBuf,
}

impl ManifestFixture {
    fn new(name: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let cleanup_root = PathBuf::from("target")
            .join("extern_spec_manifest_scope_tests")
            .join(format!("{name}_{nonce}"));
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

impl Drop for ManifestFixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.cleanup_root).ok();
    }
}

#[test]
fn test_register_extern_spec_from_manifest_scope_still_resolves_same_file() {
    common::with_clean_verification(|| {
        clear_extern_contracts();

        let fixture = ManifestFixture::new("same_file");
        fixture.write(
            "tests/call_site.rs",
            r#"
                trust_vc::external_spec! {
                    impl i32 {
                        #[requires(false)]
                        fn abs(self) -> i32;
                    }
                }
            "#,
        );

        register_extern_spec_from_manifest_scope(
            "tests/call_site.rs",
            fixture
                .manifest_dir()
                .to_str()
                .expect("manifest dir should be utf-8"),
            "i32::abs",
        )
        .expect("same-file registration should succeed");

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "same-file requires(false) should reach verification, got: {result:?}"
        );
    });
}

#[test]
fn test_register_extern_spec_from_manifest_scope_finds_cross_file_contract() {
    common::with_clean_verification(|| {
        clear_extern_contracts();

        let fixture = ManifestFixture::new("cross_file");
        fixture.write("tests/call_site.rs", "// call-site file only\n");
        fixture.write(
            "src/specs.rs",
            r#"
                trust_vc::external_spec! {
                    impl u32 {
                        #[requires(false)]
                        fn count_ones(self) -> u32;
                    }
                }
            "#,
        );

        register_extern_spec_from_manifest_scope(
            "tests/call_site.rs",
            fixture
                .manifest_dir()
                .to_str()
                .expect("manifest dir should be utf-8"),
            "u32::count_ones",
        )
        .expect("same-package cross-file registration should succeed");

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "cross-file requires(false) should reach verification, got: {result:?}"
        );
    });
}

#[test]
fn test_register_extern_spec_from_manifest_scope_preserves_ambiguity_hint() {
    clear_extern_contracts();

    let fixture = ManifestFixture::new("ambiguity");
    fixture.write("tests/call_site.rs", "// call-site file only\n");
    fixture.write(
        "src/spec_vec_u8.rs",
        r#"
            trust_vc::extern_spec! {
                impl Vec::<u8> {
                    #[requires(false)]
                    fn pop(&mut self) -> Option<u8>;
                }
            }
        "#,
    );
    fixture.write(
        "tests/spec_vec_u16.rs",
        r#"
            trust_vc::extern_spec! {
                impl Vec::<u16> {
                    #[requires(true)]
                    fn pop(&mut self) -> Option<u16>;
                }
            }
        "#,
    );

    let error = register_extern_spec_from_manifest_scope(
        "tests/call_site.rs",
        fixture
            .manifest_dir()
            .to_str()
            .expect("manifest dir should be utf-8"),
        "Vec::pop",
    )
    .expect_err("ambiguous shorthand lookup should fail closed")
    .to_string();

    assert!(
        error.contains("Vec::pop"),
        "error should identify the ambiguous target, got: {error}"
    );
    assert!(
        error.contains("2 entries match"),
        "error should report the number of conflicting matches, got: {error}"
    );
    assert!(
        error.contains("use explicit generic arguments to disambiguate"),
        "error should preserve the ambiguity hint, got: {error}"
    );
}

#[test]
fn test_register_extern_spec_from_manifest_scope_reports_supported_boundary() {
    clear_extern_contracts();

    let fixture = ManifestFixture::new("supported_boundary");
    fixture.write("tests/call_site.rs", "// call-site file only\n");

    let error = register_extern_spec_from_manifest_scope(
        "tests/call_site.rs",
        fixture
            .manifest_dir()
            .to_str()
            .expect("manifest dir should be utf-8"),
        "std::vec::Vec::pop",
    )
    .expect_err("dependency-crate target should fail closed")
    .to_string();

    assert!(
        error.contains("current package rooted at"),
        "error should mention the searched current package, got: {error}"
    );
    assert!(
        error.contains("dependency crates are not searched"),
        "error should mention the unsupported dependency-crate boundary, got: {error}"
    );
}

#[test]
fn test_register_extern_spec_from_manifest_scope_imports_bit_method_contract_text() {
    common::with_clean_verification(|| {
        clear_extern_contracts();

        let fixture = ManifestFixture::new("bit_method_contract");
        fixture.write("tests/call_site.rs", "// call-site file only\n");
        fixture.write(
            "src/bit_specs.rs",
            r#"
                trust_vc::extern_spec! {
                    impl u32 {
                        #[ensures(result <= 32)]
                        fn leading_zeros(self) -> u32;
                    }
                }
            "#,
        );

        register_extern_spec_from_manifest_scope(
            "tests/call_site.rs",
            fixture
                .manifest_dir()
                .to_str()
                .expect("manifest dir should be utf-8"),
            "u32::leading_zeros",
        )
        .expect("bit-method cross-file registration should succeed");

        let pipeline = VerificationPipeline::collect_from_macros();
        let obligations = pipeline.context().obligations();

        let ensures = obligations
            .iter()
            .find(|o| o.name().contains("leading_zeros") && o.name().contains("ensures"))
            .expect("should import an ensures obligation for u32::leading_zeros");

        assert_eq!(
            ensures.kind(),
            ObligationKind::Assume,
            "ensures should arrive as Assume at the call site"
        );
        assert!(
            ensures.condition().contains("result <= 32"),
            "ensures condition should contain the bit-method contract text, got: {}",
            ensures.condition()
        );
    });
}
