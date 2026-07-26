// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream opaque_reveal.rs slice.
//!
//! These tests prove the Rust-valid TrustVc source-extraction evidence in
//! `evals/verus/ported/opaque_reveal.rs` while the manifest keeps the broader
//! upstream Verus file fail-closed for unsupported hide, reveal_with_fuel,
//! trait/inherent paths, qualified module paths, trailing-comma reveal syntax,
//! closed/open visibility, cross-crate fuel, and diagnostics. Solver `Unknown`
//! is rejected as replacement evidence.

mod common;

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn opaque_reveal_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/opaque_reveal.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_opaque_reveal_path() -> PathBuf {
    common::pinned_verus_test_path("opaque_reveal.rs")
}

fn verify_port_case(case: &str) -> (VerifyResult, usize) {
    let path = opaque_reveal_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("opaque_reveal port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("opaque_reveal port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in opaque_reveal port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn reject_unknown(result: &VerifyResult, case: &str, upstream_case: &str) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}"
        );
    }
}

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligations) = verify_port_case(case);
    reject_unknown(&result, case, upstream_case);
    assert!(
        obligations >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligations) = verify_port_case(case);
    reject_unknown(&result, case, upstream_case);
    assert!(
        obligations >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} ({upstream_case}) should be rejected, got: {result:?}"
    );
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = opaque_reveal_port_path();
    let path = path
        .to_str()
        .expect("opaque_reveal port path should be UTF-8");

    match verify_function_from_file(path, case) {
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!(
                "{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}"
            );
        }
        Ok(result) => panic!("{case} ({upstream_case}) should fail closed, got: {result:?}"),
        Err(err) => err.to_string(),
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "test_opaque_reveal_makes_body_visible",
        "trait_fn_trait_fn_nogeneric direct opaque reveal body visibility",
        1,
    ),
    (
        "test_opaque_reveal_bool_predicate_visible",
        "trait_fn_trait_fn_nogeneric opaque bool predicate reveal",
        1,
    ),
    (
        "test_non_opaque_spec_body_visible_without_reveal",
        "non-opaque spec function baseline",
        1,
    ),
    (
        "test_reveal_non_opaque_spec_is_harmless",
        "reveal non-opaque spec function baseline",
        1,
    ),
    (
        "test_opaque_generic_reveal_makes_body_visible",
        "trait_fn_free_fn_generic_1 generic reveal target",
        1,
    ),
    (
        "test_unqualified_opaque_identity_reveal_makes_body_visible",
        "struct_fn_free_fn_2 unqualified reveal target",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "test_opaque_without_reveal_reflexive_false_counterexample",
        "opaque spec function without reveal stable false reflexivity witness",
        1,
    ),
    (
        "test_opaque_generic_without_reveal_reflexive_false_counterexample",
        "generic opaque spec function without reveal stable false reflexivity witness",
        1,
    ),
    (
        "test_opaque_bool_revealed_wrong_claim_counterexample",
        "revealed opaque bool predicate false assertion",
        1,
    ),
    (
        // hide! supported (#2785): hiding the opaque fn with no reveal leaves
        // the asserted body-fact unprovable → Counterexample (was a
        // fail-closed "unsupported hide!" placeholder). Legacy case_id.
        "test_hide_macro_currently_fails_closed",
        "trailing_commas hide syntax boundary",
        1,
    ),
];

const UNKNOWN_BLOCKER_CASES: &[(&str, &str, usize)] = &[
    (
        "test_opaque_without_reveal_hides_body",
        "opaque spec function without reveal",
        1,
    ),
    (
        "test_opaque_generic_without_reveal_hides_body",
        "generic opaque spec function without reveal",
        1,
    ),
    (
        "test_reveal_exact_target_does_not_reveal_sibling",
        "partial reveal exact-target boundary",
        1,
    ),
    (
        "test_opaque_reveal_wrong_value_currently_unknown",
        "revealed opaque spec function false assertion",
        1,
    ),
];

type OpaqueRevealFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

#[derive(Debug, Eq, PartialEq)]
struct ErrorPatternMetadata {
    case_id: String,
    expected_error_patterns: Vec<String>,
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "test_qualified_opaque_identity_reveal_target_fails_closed",
        "across_modules_and_use qualified reveal target boundary",
        &[
            "supports only unqualified function names",
            "opaque_reveal_qualified_target :: opaque_identity",
        ],
    ),
    (
        "test_inherent_opaque_reveal_target_fails_closed",
        "struct_fn_free_fn_1/2 inherent reveal target boundary",
        &[
            "supports only unqualified function names",
            "OpaqueRevealWitness :: always",
        ],
    ),
    (
        "test_trait_opaque_reveal_target_fails_closed",
        "trait_fn_free_fn_nogeneric trait reveal target boundary",
        &["Failed to parse reveal!() target"],
    ),
    // test_hide_macro_currently_fails_closed moved to COUNTEREXAMPLE_CASES
    // (hide! supported, #2785 — faithful CE, no longer a fail-closed error).
    (
        "test_reveal_with_fuel_currently_fails_closed",
        "across_crates/reveal_function_that_isnt_recursive_but_has_decreases_issue644 fuel boundary",
        &[
            "Unsupported reveal_with_fuel!()",
            "unsupported macros are rejected",
        ],
    ),
    (
        "test_reveal_target_trailing_comma_currently_fails_closed",
        "trailing_commas reveal syntax boundary",
        &["Failed to parse reveal!() target"],
    ),
    (
        "test_reveal_unknown_target_fails_closed",
        "struct_fn_free_fn_4_not_found missing reveal target boundary",
        &[
            "reveal!(opaque_missing_successor) references unknown function",
            "Available functions",
        ],
    ),
];

fn expected_error_pattern_metadata() -> Vec<OpaqueRevealFailClosedErrorPatterns> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, expected_patterns)| (*case, *expected_patterns))
        .collect()
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in opaque_reveal metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal in opaque_reveal metadata");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal in opaque_reveal metadata");
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

fn case_metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "OPAQUE_REVEAL_RS_EXPECTED_CASES");
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple expected-case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "expected-case entries should have case, upstream case, verdict, and min obligations"
        );
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate opaque_reveal metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    EXPECTED_CASE_METADATA
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
            },
        )
        .collect()
}

fn accepted_manifest_metadata() -> Vec<CaseMetadata> {
    expected_metadata()
        .into_iter()
        .filter(|case| {
            matches!(
                case.expected_verdict.as_str(),
                "verified" | "counterexample" | "error"
            )
        })
        .collect()
}

fn referenced_array_const<'a>(file: &'a syn::File, const_name: &str) -> &'a syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("opaque_reveal port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };

    array
}

fn error_pattern_entries(file: &syn::File) -> Vec<ErrorPatternMetadata> {
    let array = referenced_array_const(file, "OPAQUE_REVEAL_RS_FAIL_CLOSED_ERROR_PATTERNS");
    let mut entries = Vec::new();

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
        assert!(
            !entries
                .iter()
                .any(|entry: &ErrorPatternMetadata| entry.case_id == case_id),
            "duplicate error-pattern metadata for {case_id}"
        );
        entries.push(ErrorPatternMetadata {
            case_id,
            expected_error_patterns: string_slice(&tuple.elems[1]),
        });
    }

    entries
}

fn expected_error_pattern_entries() -> Vec<ErrorPatternMetadata> {
    expected_error_pattern_metadata()
        .into_iter()
        .map(|(case_id, expected_patterns)| ErrorPatternMetadata {
            case_id: case_id.to_string(),
            expected_error_patterns: expected_patterns
                .iter()
                .map(|pattern| (*pattern).to_string())
                .collect(),
        })
        .collect()
}

fn fail_closed_error_patterns_as_owned() -> Vec<(String, Vec<String>)> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, patterns)| {
            (
                (*case).to_string(),
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn manifest_row() -> serde_json::Value {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/opaque_reveal.rs")
        })
        .expect("Verus manifest should contain opaque_reveal.rs row")
        .clone()
}

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("opaque_reveal manifest row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("manifest case should contain upstream_case_id")
                .to_string(),
            expected_verdict: case["expected_verdict"]
                .as_str()
                .expect("manifest case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("manifest case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
        })
        .collect()
}

fn manifest_fail_closed_error_pattern_metadata() -> Vec<(String, Vec<String>)> {
    manifest_row()["expected_cases"]
        .as_array()
        .expect("opaque_reveal manifest row should contain expected_cases")
        .iter()
        .filter_map(|case| {
            let patterns = case["expected_error_patterns"].as_array()?;
            Some((
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                patterns
                    .iter()
                    .map(|pattern| {
                        pattern
                            .as_str()
                            .expect("expected_error_patterns entries should be strings")
                            .to_string()
                    })
                    .collect(),
            ))
        })
        .collect()
}

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "test_opaque_reveal_makes_body_visible",
        "trait_fn_trait_fn_nogeneric direct opaque reveal body visibility",
        "verified",
        1,
    ),
    (
        "test_opaque_reveal_bool_predicate_visible",
        "trait_fn_trait_fn_nogeneric opaque bool predicate reveal",
        "verified",
        1,
    ),
    (
        "test_non_opaque_spec_body_visible_without_reveal",
        "non-opaque spec function baseline",
        "verified",
        1,
    ),
    (
        "test_reveal_non_opaque_spec_is_harmless",
        "reveal non-opaque spec function baseline",
        "verified",
        1,
    ),
    (
        "test_opaque_generic_reveal_makes_body_visible",
        "trait_fn_free_fn_generic_1 generic reveal target",
        "verified",
        1,
    ),
    (
        "test_unqualified_opaque_identity_reveal_makes_body_visible",
        "struct_fn_free_fn_2 unqualified reveal target",
        "verified",
        1,
    ),
    (
        "test_opaque_without_reveal_hides_body",
        "opaque spec function without reveal",
        "blocked",
        1,
    ),
    (
        "test_opaque_generic_without_reveal_hides_body",
        "generic opaque spec function without reveal",
        "blocked",
        1,
    ),
    (
        "test_opaque_without_reveal_reflexive_false_counterexample",
        "opaque spec function without reveal stable false reflexivity witness",
        "counterexample",
        1,
    ),
    (
        "test_opaque_generic_without_reveal_reflexive_false_counterexample",
        "generic opaque spec function without reveal stable false reflexivity witness",
        "counterexample",
        1,
    ),
    (
        "test_opaque_reveal_wrong_value_currently_unknown",
        "revealed opaque spec function false assertion",
        "blocked",
        1,
    ),
    (
        "test_opaque_bool_revealed_wrong_claim_counterexample",
        "revealed opaque bool predicate false assertion",
        "counterexample",
        1,
    ),
    (
        "test_reveal_exact_target_does_not_reveal_sibling",
        "partial reveal exact-target boundary",
        "blocked",
        1,
    ),
    (
        "test_qualified_opaque_identity_reveal_target_fails_closed",
        "across_modules_and_use qualified reveal target boundary",
        "error",
        0,
    ),
    (
        "test_inherent_opaque_reveal_target_fails_closed",
        "struct_fn_free_fn_1/2 inherent reveal target boundary",
        "error",
        0,
    ),
    (
        "test_trait_opaque_reveal_target_fails_closed",
        "trait_fn_free_fn_nogeneric trait reveal target boundary",
        "error",
        0,
    ),
    (
        "test_hide_macro_currently_fails_closed",
        "trailing_commas hide syntax boundary",
        "counterexample",
        1,
    ),
    (
        "test_reveal_with_fuel_currently_fails_closed",
        "across_crates/reveal_function_that_isnt_recursive_but_has_decreases_issue644 fuel boundary",
        "error",
        0,
    ),
    (
        "test_reveal_target_trailing_comma_currently_fails_closed",
        "trailing_commas reveal syntax boundary",
        "error",
        0,
    ),
    (
        "test_reveal_unknown_target_fails_closed",
        "struct_fn_free_fn_4_not_found missing reveal target boundary",
        "error",
        0,
    ),
];

#[test]
fn opaque_reveal_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(opaque_reveal_port_path())
        .expect("opaque_reveal port should be readable");
    syn::parse_file(&source).expect("opaque_reveal port should parse as ordinary Rust syntax");
}

#[test]
fn opaque_reveal_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_opaque_reveal_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream opaque_reveal.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] trait_fn_free_fn_nogeneric",
        "#[test] trait_fn_inherent_fn_nogeneric",
        "#[test] trait_fn_inherent_fn_self_nogeneric",
        "#[test] trait_fn_trait_fn_nogeneric",
        "#[test] trait_fn_free_fn_generic_1",
        "#[test] trait_fn_free_fn_generic_2",
        "#[test] trait_fn_inherent_fn_generic",
        "#[test] trait_fn_inherent_fn_self_generic",
        "#[test] trait_fn_trait_fn_generic",
        "#[test] trait_fn_free_fn_expanded_invalid_1",
        "#[test] struct_fn_free_fn_1",
        "#[test] struct_fn_free_fn_2",
        "#[test] struct_fn_free_fn_3_incorrect_type",
        "#[test] mod_invalid_1",
        "#[test] struct_fn_free_fn_4_not_found",
        "#[test] across_modules_and_use",
        "#[test] across_crates",
        "#[test] trailing_commas",
        "#[test] regression_704_impl_arg",
        "#[test] regression_907_reveal_u64_1",
        "#[test] regression_907_reveal_u64_2",
        "#[test] regression_925_reveal_loop_1",
        "#[test] regression_925_reveal_loop_2",
        "#[test] no_broadcast_use_as_reveal_1",
        "#[test] no_broadcast_use_as_reveal_2",
        "#[test] reveal_closed_error",
        "#[test] reveal_closed_not_error",
        "#[test] reveal_function_that_isnt_recursive_but_has_decreases_issue644",
        "hide(<A as Tr>::afunction);",
        "reveal(<A as Tr>::afunction);",
        "reveal(<Self as Tr>::afunction);",
        "reveal(A::<_>::afunction);",
        "reveal(A::afunction);",
        "reveal(A::wrong);",
        "reveal_with_fuel(Seq::filter, 3);",
        "hide(s,);",
        "reveal(s,);",
        "reveal_with_fuel(s,2,);",
        "reveal(<u64 as Tau>::foo);",
        "reveal(m::foo);",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream opaque_reveal.rs should still contain {expected}"
        );
    }
}

#[test]
fn opaque_reveal_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(opaque_reveal_port_path())
        .expect("opaque_reveal port should be readable");
    let file =
        syn::parse_file(&source).expect("opaque_reveal port should parse as ordinary Rust syntax");
    assert!(
        source.contains("UPSTREAM_OPAQUE_REVEAL_RS_PINNED_CASES")
            && source.contains("upstream_opaque_reveal_rs_pinned_cases"),
        "opaque_reveal port should expose pinned upstream case metadata"
    );
    assert!(
        source.contains("OPAQUE_REVEAL_RS_EXPECTED_CASES")
            && source.contains("opaque_reveal_rs_expected_cases"),
        "opaque_reveal port should expose expected-case metadata helpers"
    );
    assert!(
        source.contains("OPAQUE_REVEAL_RS_FAIL_CLOSED_ERROR_PATTERNS")
            && source.contains("opaque_reveal_rs_fail_closed_error_patterns"),
        "opaque_reveal port should expose fail-closed error-pattern metadata helpers"
    );

    let actual_error_patterns = error_pattern_entries(&file);
    assert_eq!(
        actual_error_patterns,
        expected_error_pattern_entries(),
        "opaque_reveal fail-closed error-pattern metadata should match the regression inventory"
    );

    let actual_metadata = case_metadata_entries(&file);
    assert_eq!(
        actual_metadata,
        expected_metadata(),
        "opaque_reveal expected-case metadata should match the regression inventory exactly"
    );
    for case_metadata in &actual_metadata {
        assert_ne!(
            case_metadata.expected_verdict, "unknown",
            "opaque_reveal metadata must not accept Unknown as evidence for {}",
            case_metadata.case_id
        );
        let has_error_patterns = actual_error_patterns
            .iter()
            .any(|entry| entry.case_id == case_metadata.case_id);
        if case_metadata.expected_verdict == "error" {
            assert!(
                has_error_patterns,
                "{} ({}) should carry precise fail-closed error fragments",
                case_metadata.case_id, case_metadata.upstream_case_id
            );
        } else {
            assert!(
                !has_error_patterns,
                "{} ({}) should not carry error fragments for {} evidence",
                case_metadata.case_id,
                case_metadata.upstream_case_id,
                case_metadata.expected_verdict
            );
        }
    }
}

#[test]
fn opaque_reveal_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(
        manifest_expected_case_metadata(),
        accepted_manifest_metadata(),
        "opaque_reveal manifest should match stable verified/counterexample/error metadata exactly"
    );
    assert_eq!(
        manifest_fail_closed_error_pattern_metadata(),
        fail_closed_error_patterns_as_owned(),
        "opaque_reveal manifest expected_error_patterns should match focused fail-closed guards exactly"
    );
}

#[test]
fn opaque_reveal_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        assert_verified(case, upstream_case, *min_obligations);
    }
}

#[test]
fn opaque_reveal_rs_hidden_body_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        assert_counterexample(case, upstream_case, *min_obligations);
    }
}

#[test]
fn opaque_reveal_rs_unknown_blockers_are_not_replacement_evidence() {
    // Re-pinned 2026-07-04: these four "blocked" cases used to return solver
    // Unknown; the engine now returns genuine Counterexamples (control ledger
    // 2026-07-04). That is sound and strictly stronger fail-closed evidence:
    // - the two *hides_body cases and the exact-target sibling assert the body
    //   value of an UNREVEALED opaque spec fn — uninterpreted in the encoded
    //   theory, so a countermodel assigning a different return value genuinely
    //   refutes the claim (Verus also rejects these without reveal);
    // - test_opaque_reveal_wrong_value_currently_unknown is a revealed FALSE
    //   assertion, now genuinely refuted instead of Unknown.
    // Status stays "blocked" (excluded from replacement evidence; manifest
    // untouched). Nothing here may ever return Verified.
    for (case, upstream_case, min_obligations) in UNKNOWN_BLOCKER_CASES {
        let (result, obligations) = verify_port_case(case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) must stay a genuinely-refuted non-evidence blocker, got: {result:?}"
        );
    }
}

#[test]
fn opaque_reveal_rs_qualified_reveal_boundary_fails_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);

        for expected_fragment in *expected_fragments {
            assert!(
                message.contains(expected_fragment),
                "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
            );
        }
    }
}
