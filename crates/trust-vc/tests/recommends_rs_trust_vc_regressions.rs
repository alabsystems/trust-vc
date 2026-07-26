// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Recommends.rs-specific guards for the current unsupported-gap scout.
//!
//! These tests intentionally keep the row fail-closed: local expected cases may
//! verify, produce a counterexample, or fail closed with an extraction error,
//! but solver Unknown is not accepted as evidence.

mod common;

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

const UPSTREAM_ACTIVE_CASES: &[&str] = &[
    "ensures_forall_recommends_failure",
    "ensures_type_substitutes_issue1566",
];

const EXPECTED_CASE_METADATA: &[(&str, &str, &str, usize)] = &[
    (
        "ensures_forall_recommends_positive_witness",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "requires_recommended_source_spec_positive",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "assert_recommended_source_spec_positive",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "assume_recommended_source_spec_positive",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "ensures_forall_recommends_failure",
        "ensures_forall_recommends_failure",
        "counterexample",
        1,
    ),
    (
        "ensures_forall_recommends_quantified_exact_failure",
        "ensures_forall_recommends_failure",
        "counterexample",
        1,
    ),
    (
        "requires_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "assert_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "assume_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "body_call_unscoped_recommends_argument_advisory",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "ensures_type_substitutes_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "ensures_type_substitutes_exists_recommends_false_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "ensures_type_substitutes_issue1566",
        "ensures_type_substitutes_issue1566",
        "counterexample",
        1,
    ),
    (
        "ensures_forall_recommends_quantified_failure",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "recommends_false_never_assumed_tripwire",
        "ensures_type_substitutes_issue1566",
        "counterexample",
        1,
    ),
];

fn recommends_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/recommends.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_recommends_path() -> PathBuf {
    common::pinned_verus_test_path("recommends.rs")
}

fn read_recommends_source() -> String {
    let path = recommends_port_path();
    std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("recommends.rs should read from {:?}: {err}", path))
}

fn parse_recommends_source() -> syn::File {
    syn::parse_file(&read_recommends_source())
        .unwrap_or_else(|err| panic!("recommends.rs should parse: {err}"))
}

fn find_recommends_function<'a>(parsed: &'a syn::File, case: &str) -> &'a syn::ItemFn {
    parsed
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in recommends.rs"))
}

fn extract_recommends_case(case: &str) -> trust_vc_core::vc::VerificationContext {
    let parsed = parse_recommends_source();
    let func = find_recommends_function(&parsed, case);

    extract_verification_conditions_with_file_context(&parsed, func)
        .unwrap_or_else(|err| panic!("{case} should extract from recommends.rs: {err}"))
}

fn literal_string(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit),
            ..
        }) => lit.value(),
        _ => panic!("expected string literal in metadata"),
    }
}

fn literal_usize(expr: &syn::Expr) -> usize {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => lit
            .base10_parse::<usize>()
            .unwrap_or_else(|err| panic!("expected usize literal in metadata: {err}")),
        _ => panic!("expected usize literal in metadata"),
    }
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

fn const_array<'a>(source: &'a syn::File, const_name: &str) -> &'a syn::ExprArray {
    let const_item = source
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("recommends.rs should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array
}

fn parse_string_array_metadata(source: &syn::File, const_name: &str) -> Vec<String> {
    const_array(source, const_name)
        .elems
        .iter()
        .map(literal_string)
        .collect()
}

fn parse_expected_case_metadata(source: &syn::File) -> Vec<(String, String, String, usize)> {
    const_array(source, "RECOMMENDS_RS_EXPECTED_CASES")
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "metadata entries should have case, upstream case, status, and min obligations"
            );
            (
                literal_string(&tuple.elems[0]),
                literal_string(&tuple.elems[1]),
                literal_string(&tuple.elems[2]),
                literal_usize(&tuple.elems[3]),
            )
        })
        .collect()
}

fn parse_error_pattern_metadata(source: &syn::File) -> BTreeMap<String, Vec<String>> {
    const_array(source, "RECOMMENDS_RS_ERROR_PATTERNS")
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple error-pattern metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                2,
                "error-pattern entries should have case and fragments"
            );
            (
                literal_string(&tuple.elems[0]),
                string_slice(&tuple.elems[1]),
            )
        })
        .collect()
}

fn parse_expected_case_metadata_with_patterns(
    source: &syn::File,
) -> Vec<(String, String, String, usize, Vec<String>)> {
    let mut error_patterns = parse_error_pattern_metadata(source);
    let entries = parse_expected_case_metadata(source)
        .into_iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| {
                let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
                (
                    case_id,
                    upstream_case_id,
                    expected_verdict,
                    min_obligations,
                    expected_error_patterns,
                )
            },
        )
        .collect::<Vec<_>>();

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn manifest_expected_metadata() -> Vec<(String, String, String, usize, Vec<String>)> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/recommends.rs")
        })
        .expect("Verus manifest should contain recommends.rs row");

    row["expected_cases"]
        .as_array()
        .expect("recommends.rs row should contain expected_cases")
        .iter()
        .map(|entry| {
            let expected_error_patterns = entry
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
                .unwrap_or_default();
            (
                entry["case_id"]
                    .as_str()
                    .expect("case_id should be a string")
                    .to_string(),
                entry["upstream_case_id"]
                    .as_str()
                    .expect("upstream_case_id should be a string")
                    .to_string(),
                entry["expected_verdict"]
                    .as_str()
                    .expect("expected_verdict should be a string")
                    .to_string(),
                entry["min_obligations"]
                    .as_u64()
                    .expect("min_obligations should be an integer") as usize,
                expected_error_patterns,
            )
        })
        .collect()
}

fn assert_recommends_verified(case: &str) {
    let path = recommends_port_path();
    let path = path.to_str().expect("recommends.rs path should be UTF-8");

    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from recommends.rs: {err}"));
    match result {
        VerifyResult::Verified => {}
        VerifyResult::Unknown { reason, .. } => {
            panic!("{case} returned solver Unknown, which is not stable evidence: {reason}");
        }
        other => panic!("{case} should verify, got: {other:?}"),
    }
}

fn assert_recommends_counterexample(case: &str, expected_obligation: &str) {
    let path = recommends_port_path();
    let path = path.to_str().expect("recommends.rs path should be UTF-8");

    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from recommends.rs: {err}"));

    match result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => {
            if !expected_obligation.is_empty() {
                assert_eq!(
                    obligation_name, expected_obligation,
                    "{case} should fail on the propagated callee recommends obligation"
                );
            }
        }
        VerifyResult::Unknown { reason, .. } => {
            panic!("{case} returned solver Unknown, which is not stable evidence: {reason}");
        }
        other => {
            panic!("{case} should be rejected by propagated recommends, got: {other:?}")
        }
    }
}

fn fail_closed_message(case: &str) -> String {
    let path = recommends_port_path();
    let path = path.to_str().expect("recommends.rs path should be UTF-8");

    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => panic!("{case} should fail closed with Error, got: {other:?}"),
    }
}

#[test]
fn recommends_rs_port_file_is_rust_syntax() {
    parse_recommends_source();
}

#[test]
fn recommends_rs_expected_case_metadata_is_schema_valid_and_exact() {
    let source = parse_recommends_source();

    assert_eq!(
        parse_string_array_metadata(&source, "UPSTREAM_RECOMMENDS_RS_ACTIVE_CASES"),
        UPSTREAM_ACTIVE_CASES
            .iter()
            .map(|case| (*case).to_string())
            .collect::<Vec<_>>()
    );

    let actual = parse_expected_case_metadata(&source);
    let expected = EXPECTED_CASE_METADATA
        .iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            (
                (*case).to_string(),
                (*upstream_case).to_string(),
                (*status).to_string(),
                *min_obligations,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual, expected,
        "recommends.rs metadata should exactly match the regression inventory"
    );

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA {
        assert!(
            matches!(*status, "verified" | "counterexample" | "error"),
            "{case} must use a schema-valid status, got {status}"
        );
        assert!(
            UPSTREAM_ACTIVE_CASES.contains(upstream_case),
            "{case} should map to a pinned upstream recommends.rs harness case"
        );
        if *status != "error" {
            assert!(
                *min_obligations >= 1,
                "{case} non-error evidence should require positive obligations"
            );
        }
    }
}

#[test]
fn recommends_rs_expected_case_metadata_matches_manifest() {
    let source = parse_recommends_source();
    assert_eq!(
        parse_expected_case_metadata_with_patterns(&source),
        manifest_expected_metadata()
    );
}

#[test]
fn recommends_rs_expected_cases_do_not_use_unknown_evidence() {
    for (case, _upstream_case, status, min_obligations) in EXPECTED_CASE_METADATA {
        match *status {
            "verified" => assert_recommends_verified(case),
            "counterexample" => assert_recommends_counterexample(case, ""),
            "error" => {
                let message = fail_closed_message(case);
                assert!(
                    message.contains("source spec recommends")
                        && message.contains("Unsupported source-spec recommends call argument"),
                    "{case} should fail closed on unsupported source-spec recommends semantics, got: {message}"
                );
            }
            other => panic!("{case} has unsupported expected status {other}"),
        }

        if *status != "error" {
            let vc = extract_recommends_case(case);
            assert!(
                vc.obligations().len() >= *min_obligations,
                "{case} should collect at least {min_obligations} obligation(s), got {}",
                vc.obligations().len()
            );
        } else {
            assert!(
                *min_obligations == 0,
                "{case} error evidence should use min_obligations 0"
            );
        }
    }
}

#[test]
fn recommends_rs_pinned_upstream_shapes_are_present() {
    let path = pinned_upstream_recommends_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream recommends.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    for expected_shape in [
        "#[test] ensures_forall_recommends_failure",
        "spec fn foo(i: int) -> bool",
        "recommends 0 <= i < 5",
        "i + 3 == 20",
        "ensures forall |i: int| 0 <= i < 20 ==> foo(i)",
        "#[test] ensures_type_substitutes_issue1566",
        "spec fn bar(w: W) -> bool",
        "recommends false",
        "exists |w| bar(w)",
        "assert_one_fails",
    ] {
        assert!(
            source.contains(expected_shape),
            "pinned upstream recommends.rs should contain {expected_shape}"
        );
    }
}

#[test]
fn recommends_rs_port_preserves_upstream_source_shapes() {
    let source = read_recommends_source();

    for expected_shape in [
        "fn foo(i: int) -> bool",
        "#[trust_vc::recommends(0 <= i && i < 5)]",
        "i + 3 == 20",
        "#[trust_vc::ensures(forall(|i: int| !(0 <= i && i < 20) || foo(i)))]",
        "fn bar_recommends_false(_witness: int) -> bool",
        "fn bounded_true_u64(i: u64) -> bool",
        "#[trust_vc::recommends(false)]",
        "exists(|witness: int| bar_recommends_false(witness))",
        "body_call_unscoped_recommends_argument_advisory",
        "fn recommends_false_never_assumed_tripwire()",
    ] {
        assert!(
            source.contains(expected_shape),
            "ported recommends.rs should contain {expected_shape}"
        );
    }
}

/// The false-BODY counterexamples are INDEPENDENT of recommends and MUST
/// survive advisory recommends: the counterexample comes from the false
/// postcondition, not from any (now-dropped) recommends obligation.
#[test]
fn false_body_counterexamples_survive_advisory_recommends() {
    for case in [
        "ensures_forall_recommends_failure",
        "ensures_forall_recommends_quantified_exact_failure",
        "ensures_type_substitutes_issue1566",
    ] {
        assert_recommends_counterexample(case, "postcondition");
    }
}

#[test]
fn recommends_adjacent_positive_contract_and_body_shapes_verify() {
    for case in [
        "ensures_forall_recommends_positive_witness",
        "requires_recommended_source_spec_positive",
        "assert_recommended_source_spec_positive",
        "assume_recommended_source_spec_positive",
    ] {
        assert_recommends_verified(case);
    }
}

/// Advisory recommends: `bar_recommends_false` has `recommends(false)` but a
/// true BODY, and `bounded_true_u64` has an unresolvable body-call recommends
/// argument. Because a callee's recommends is verdict-neutral (dropped, never
/// propagated), all of these now VERIFY. Their earlier counterexample/error
/// verdicts were solely artifacts of the former hard recommends obligation.
#[test]
fn advisory_source_spec_recommends_cases_verify() {
    for case in [
        "requires_false_recommends_advisory",
        "assert_false_recommends_advisory",
        "assume_false_recommends_advisory",
        "ensures_type_substitutes_false_recommends_advisory",
        "ensures_type_substitutes_exists_recommends_false_advisory",
        "body_call_unscoped_recommends_argument_advisory",
        "ensures_forall_recommends_quantified_failure",
    ] {
        assert_recommends_verified(case);
    }
}

/// Advisory recommends emits NO caller-side proof obligation. A former hard
/// `__call_recommends_*` assert would have appeared here; its absence proves the
/// recommends is verdict-neutral (dropped, not downgraded to an assumption).
#[test]
fn advisory_source_spec_recommends_emits_no_call_obligation() {
    for case in [
        "requires_false_recommends_advisory",
        "assert_false_recommends_advisory",
        "assume_false_recommends_advisory",
        "ensures_type_substitutes_false_recommends_advisory",
        "ensures_type_substitutes_exists_recommends_false_advisory",
        "body_call_unscoped_recommends_argument_advisory",
        "ensures_forall_recommends_quantified_failure",
        "ensures_forall_recommends_quantified_exact_failure",
    ] {
        let vc = extract_recommends_case(case);
        assert!(
            vc.obligations()
                .iter()
                .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
            "{case} must not emit a caller-side recommends obligation, got: {:?}",
            vc.obligations()
                .iter()
                .map(|obligation| obligation.name().to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// SOUNDNESS TRIPWIRE. Recommends is advisory and MUST NEVER be assumed by a
/// caller. `bar_recommends_false` has `recommends(false)`; this caller assumes
/// only the callee BODY (`true`) via its `requires`, so the `ensures(false)`
/// postcondition is unprovable. If the callee's `recommends(false)` ever leaked
/// into the caller's assumptions (e.g. a naive downgrade to a `Recommends`-kind
/// obligation, which is ASSUMED at BodyLevel), the caller could prove anything
/// and this would flip to Verified — an unsoundness. It MUST stay a
/// counterexample and MUST NOT verify.
#[test]
fn recommends_false_is_never_assumed_soundness_tripwire() {
    let case = "recommends_false_never_assumed_tripwire";
    let path = recommends_port_path();
    let path = path.to_str().expect("recommends.rs path should be UTF-8");

    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from recommends.rs: {err}"));
    assert!(
        !matches!(result, VerifyResult::Verified),
        "SOUNDNESS: {case} must NOT verify — a callee recommends(false) must never \
         be assumed by the caller, got: {result:?}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} should be a counterexample (false postcondition, recommends not assumed), got: {result:?}"
    );

    // The false postcondition, not any recommends obligation, is the sole cause.
    let vc = extract_recommends_case(case);
    assert!(
        vc.obligations()
            .iter()
            .all(|obligation| !obligation.name().starts_with("__call_recommends_")),
        "{case} must not emit a recommends obligation (advisory), got: {:?}",
        vc.obligations()
            .iter()
            .map(|obligation| obligation.name().to_string())
            .collect::<Vec<_>>()
    );
}
