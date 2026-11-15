// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the maps.rs replacement evidence and local support
//! witnesses that stay outside the upstream-mapped corpus case set.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
    process::Command,
};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn maps_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/maps.rs")
}

fn maps_local_witnesses_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/maps_local_witnesses.rs")
}

fn maps_fails_subtype_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/maps_fails_subtype")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const EXPECTED_CASES: &[(&str, &str, &str, &str, usize)] = &[
    (
        "test1",
        "test1",
        "evals/verus/ported/maps.rs",
        "verified",
        8,
    ),
    (
        "test1_fails1",
        "test1_fails1",
        "evals/verus/ported/maps.rs",
        "counterexample",
        3,
    ),
    (
        "test1_fails2",
        "test1_fails2",
        "evals/verus/ported/maps.rs",
        "counterexample",
        3,
    ),
    (
        "test1_fails_subtype",
        "test1_fails_subtype",
        "evals/verus/ported/maps_fails_subtype",
        "error",
        0,
    ),
    (
        "test1_fails_eq",
        "test1_fails_eq",
        "evals/verus/ported/maps.rs",
        "counterexample",
        2,
    ),
    (
        "map_contains",
        "map_contains",
        "evals/verus/ported/maps.rs",
        "verified",
        3,
    ),
    (
        "map_insert_implies_contains",
        "map_insert_implies_contains",
        "evals/verus/ported/maps.rs",
        "verified",
        3,
    ),
    (
        "map_overwrite",
        "map_overwrite",
        "evals/verus/ported/maps.rs",
        "verified",
        9,
    ),
    (
        "set_choose_regression_408",
        "set_choose_regression_408",
        "evals/verus/ported/maps.rs",
        "verified",
        2,
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    trust_vc_path: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("maps port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal");
    };
    value.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal");
    };
    value
        .base10_parse()
        .expect("min obligations should be a usize literal")
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array.elems.iter().map(literal_string).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "MAPS_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple error-pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "error-pattern entries should have case and fragments"
        );

        let case_id = literal_string(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "MAPS_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple expected-case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            5,
            "expected-case entries should have case, upstream case, TrustVc path, verdict, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate maps metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            trust_vc_path: literal_string(&tuple.elems[2]),
            expected_verdict: literal_string(&tuple.elems[3]),
            min_obligations: literal_usize(&tuple.elems[4]),
            expected_error_patterns,
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, trust_vc_path, expected_verdict, min_obligations)| {
                CaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    trust_vc_path: (*trust_vc_path).to_string(),
                    expected_verdict: (*expected_verdict).to_string(),
                    min_obligations: *min_obligations,
                    expected_error_patterns: if *case_id == "test1_fails_subtype" {
                        vec!["mismatched types".to_string()]
                    } else {
                        Vec::new()
                    },
                }
            },
        )
        .collect()
}

fn manifest_expected_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/maps.rs")
        })
        .expect("Verus manifest should contain maps.rs row");

    row["expected_cases"]
        .as_array()
        .expect("maps.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry["upstream_case_id"]
                .as_str()
                .expect("upstream_case_id should be a string")
                .to_string(),
            trust_vc_path: entry["trust_vc_path"]
                .as_str()
                .expect("trust_vc_path should be a string")
                .to_string(),
            expected_verdict: entry["expected_verdict"]
                .as_str()
                .expect("expected_verdict should be a string")
                .to_string(),
            min_obligations: entry["min_obligations"]
                .as_u64()
                .expect("min_obligations should be an integer")
                as usize,
            expected_error_patterns: entry
                .get("expected_error_patterns")
                .and_then(serde_json::Value::as_array)
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns values should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

#[test]
fn maps_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(maps_port_path()).expect("maps port should be readable");
    let file = syn::parse_file(&source).expect("maps port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn maps_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(maps_port_path()).expect("maps port should be readable");
    let file = syn::parse_file(&source).expect("maps port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("test1", "test1"),
    (
        "map_plain_eq_auto_ext_equal_model_verifies",
        "test1_fails_eq plain auto-extensional half",
    ),
    (
        "map_strict_eq_same_finite_mk_map_function_model_verifies",
        "test1 strict equal finite Set::mk_map function model",
    ),
    ("map_contains", "map_contains"),
    ("map_insert_implies_contains", "map_insert_implies_contains"),
    ("map_index_syntax", "map index syntax local scaffold"),
    (
        "map_insert_overwrite_updates_index",
        "Map::insert overwrite updates indexed reads",
    ),
    ("map_overwrite", "map_overwrite"),
    (
        "map_remove_preserves_unremoved_keys",
        "Map::remove preserves unremoved keys",
    ),
    (
        "set_mk_map_dom_tracks_source_set",
        "Set::mk_map(...).dom() tracks source set",
    ),
    ("set_choose_regression_408", "set_choose_regression_408"),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    ("test1_fails1", "test1_fails1"),
    ("test1_fails2", "test1_fails2"),
    (
        "test1_fails_eq",
        "test1_fails_eq strict === with auto-ext disabled",
    ),
    (
        "map_strict_eq_commuted_finite_mk_map_function_fails",
        "strict equal finite Set::mk_map rejects commuted function body",
    ),
    (
        "map_insert_overwrite_fails_keeps_old_value",
        "Map::insert overwrite counterexample for retaining the old indexed value",
    ),
    (
        "map_remove_fails_drops_unremoved_key",
        "Map::remove counterexample for dropping an unremoved key",
    ),
    (
        "set_mk_map_dom_fails_contains_absent_source_key",
        "Set::mk_map(...).dom() counterexample for absent source key",
    ),
];

/// Liar twins of verified rows that had none of their own shape in the port file
/// (measured 2026-09-15 at ay 0.26.0, TRUST_VC_DISABLE_VC_CACHE=1). They stay out of
/// `EXPECTED_CASES`, the port table and the manifest: their upstream cases are
/// `=> Ok(())`, so a mapped `counterexample` row would be a verdict mismatch.
///
/// They also live in a SEPARATE FILE, `evals/verus/ported/maps_local_witnesses.rs`,
/// which no manifest entry declares. Each carries a `#[trust_vc::ensures(..)]`
/// contract, and the corpus gate scans every contract-carrying function of a
/// DECLARED `trust_vc_path` as a case of that entry — so inside `maps.rs` an
/// undeclared twin failed the whole path with `unexpected observed case`. Nothing
/// about the twins changed in the move; only the file they sit in did.
///
/// NOT every verified row gets one: `set_choose_regression_408`'s negation came back
/// `unknown ((incomplete quantifier-unhandled))`, so that pin stays without a twin
/// (recorded as a hole in `evals/verus/ported/maps.rs`).
const LOCAL_WITNESS_COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "map_contains_absent_key_fails",
        "map_contains liar twin: contains_key of an absent key",
    ),
    (
        "map_contains_absent_value_fails",
        "map_contains liar twin: contains_value of an absent value",
    ),
    (
        "map_insert_does_not_imply_contains_fails",
        "map_insert_implies_contains liar twin: the inserted key claimed absent",
    ),
    (
        "map_index_syntax_wrong_value_fails",
        "map index syntax liar twin: the inserted value read back wrong",
    ),
];

#[test]
fn maps_rs_verified_subset_verifies_from_file() {
    let path = maps_port_path();
    let path = path.to_str().expect("maps port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn maps_rs_counterexample_subset_is_rejected_from_file() {
    let path = maps_port_path();
    let path = path.to_str().expect("maps port path should be UTF-8");

    for (case, upstream_case) in COUNTEREXAMPLE_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn maps_rs_local_witness_counterexamples_are_rejected_from_file() {
    let path = maps_local_witnesses_path();
    let path = path
        .to_str()
        .expect("maps local witnesses path should be UTF-8");

    for (case, upstream_case) in LOCAL_WITNESS_COUNTEREXAMPLE_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

/// Per-unit Trust verification scope for a fixture typecheck.
///
/// `rust-toolchain.toml` pins `channel = "trust"`, whose compiler verifies
/// every unit it compiles and is strict by default. Unscoped, `cargo check` of
/// this fixture stops in third-party units (the `quote`, `proc-macro2` and
/// `serde_core` build scripts, the `unicode-ident` library) before the fixture
/// crate is reached, so the assertion below would read their errors. The scope
/// is the one the evidence gate gives a corpus fixture
/// (`trust_per_unit_scope_args` in cargo-trust-vc): the default profile, which
/// here is the fixture crate alone, stays verified at `advisory`; every package
/// it only links (`"*"`, which never matches the fixture itself) is compiled
/// with the pipeline off.
const FIXTURE_VERIFICATION_SCOPE: &[&str] = &[
    "-Zprofile-rustflags",
    "--config",
    "profile.dev.rustflags=[\"-Ztrust-policy=advisory\"]",
    "--config",
    "profile.dev.package.\"*\".rustflags=[\"-Ztrust-verify=off\"]",
];

/// The Trust toolchain's `cargo`, which accepts the per-unit scope above.
///
/// A test run under Targo hands the child `$CARGO` = Targo, and Targo cannot
/// run this probe: both of its lanes are whole-build (`trust` verifies every
/// unit fail-closed, `--unverified` appends `-Ztrust-verify=off` to every unit,
/// the fixture included). The Trust toolchain ships its upstream-Cargo
/// compatibility frontend `cargo` beside Targo (same toolchain, same trustc),
/// so that one is used. Owner directive 2026-09-28: no PATH `cargo` fallback
/// and no pass-through of a `$CARGO` that is not Targo; either would let a
/// stock toolchain run the probe.
fn scoped_cargo_program() -> PathBuf {
    let cargo = format!("cargo{}", std::env::consts::EXE_SUFFIX);
    let program = std::env::var_os("CARGO").map(PathBuf::from).expect(
        "$CARGO is unset: run this test under the Trust toolchain (`targo --unverified test`)",
    );
    let is_targo = program
        .file_stem()
        .and_then(|stem| stem.to_str())
        .is_some_and(|stem| stem == "targo" || stem.starts_with("targo-"));
    assert!(
        is_targo,
        "$CARGO `{}` is not the Trust toolchain's targo; run this test with `targo --unverified test`",
        program.display()
    );
    let sibling = program.with_file_name(&cargo);
    assert!(
        sibling.is_file(),
        "the Trust toolchain ships `{cargo}` beside targo, but `{}` is missing",
        sibling.display()
    );
    sibling
}

/// A `cargo check` child under the per-unit scope. An environment `RUSTFLAGS`
/// or `CARGO_ENCODED_RUSTFLAGS` would replace profile rustflags for every unit,
/// so the child does not inherit either.
fn cargo_check_command() -> Command {
    let mut command = Command::new(scoped_cargo_program());
    command
        .args(FIXTURE_VERIFICATION_SCOPE)
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .arg("check");
    command
}

#[test]
fn maps_rs_subtype_fixture_fails_closed_with_expected_diagnostic() {
    let output = cargo_check_command()
        .arg("--verbose")
        .current_dir(maps_fails_subtype_path())
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .expect("maps_fails_subtype cargo check should run");

    assert!(
        !output.status.success(),
        "maps_fails_subtype should fail cargo check"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("mismatched types"),
        "maps_fails_subtype diagnostic should contain mismatched types, got: {stderr}"
    );
    // The scope is per unit: the fixture crate itself was compiled with its
    // verification on, not switched off with the packages it links.
    let fixture_unit = stderr
        .lines()
        .find(|line| {
            line.contains("Running `")
                && line.contains("--crate-name trust_vc_verus_maps_fails_subtype ")
        })
        .unwrap_or_else(|| panic!("the fixture crate's compiler invocation is missing: {stderr}"));
    assert!(
        fixture_unit.contains("-Ztrust-policy=advisory")
            && !fixture_unit.contains("-Ztrust-verify=off"),
        "the fixture crate must be compiled with verification on: {fixture_unit}"
    );
}
