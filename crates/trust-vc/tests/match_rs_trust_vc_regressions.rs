// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream match.rs subset.
//!
//! These tests intentionally do not claim full Verus match.rs parity. They pin
//! upstream case shapes, prove only the listed executable scout slices, require
//! stable counterexamples for false witnesses, and keep unsupported match
//! surfaces fail-closed while the manifest remains `unsupported-gap`.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn match_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/match.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_match_path() -> PathBuf {
    common::pinned_verus_test_path("match.rs")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source = std::fs::read_to_string(match_port_path()).expect("match port should be readable");
    let ast = syn::parse_file(&source).expect("match port should parse as ordinary Rust syntax");
    (source, ast)
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = match_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("match port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("match port should parse: {err}"));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in match port"));

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} ({upstream_case}) should produce a counterexample, got: {result:?}"
    );
}

fn assert_fail_closed(case: &str, upstream_case: &str, expected_fragments: &[&str]) {
    let path = match_port_path();
    let path = path.to_str().expect("match port path should be UTF-8");
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        // NotProved (model-less incompleteness) is a DEFINITE fail-closed verdict
        // (the Unknown-as-failure resolution) — stable fail-closed evidence, unlike
        // raw solver Unknown below.
        Ok(VerifyResult::NotProved { reason, .. }) => reason,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    };

    assert!(
        expected_fragments
            .iter()
            .all(|fragment| message.contains(fragment)),
        "{case} ({upstream_case}) error should contain all of {expected_fragments:?}, got: {message}"
    );
}

fn string_lit(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal in match metadata");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal in match metadata");
    };
    value.value()
}

fn usize_lit(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected usize literal in match metadata");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected usize literal in match metadata");
    };
    value
        .base10_parse()
        .expect("match metadata min obligation should parse")
}

fn parse_match_expected_cases(file: &syn::File) -> Vec<(String, String, String, usize)> {
    let expected_const = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == "MATCH_RS_EXPECTED_CASES" => Some(item),
            _ => None,
        })
        .expect("match port should define MATCH_RS_EXPECTED_CASES");

    let syn::Expr::Reference(reference) = expected_const.expr.as_ref() else {
        panic!("MATCH_RS_EXPECTED_CASES should be a referenced array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("MATCH_RS_EXPECTED_CASES should reference an array literal");
    };

    array
        .elems
        .iter()
        .map(|entry| {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("MATCH_RS_EXPECTED_CASES entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "MATCH_RS_EXPECTED_CASES entries should have four fields"
            );
            (
                string_lit(&tuple.elems[0]),
                string_lit(&tuple.elems[1]),
                string_lit(&tuple.elems[2]),
                usize_lit(&tuple.elems[3]),
            )
        })
        .collect()
}

fn expected_case_metadata() -> Vec<(String, String, String, usize)> {
    let mut expected = Vec::new();
    expected.extend(
        VERIFIED_CASES
            .iter()
            .map(|(case, upstream_case, min_obligations)| {
                (
                    (*case).to_string(),
                    (*upstream_case).to_string(),
                    "verified".to_string(),
                    *min_obligations,
                )
            }),
    );
    expected.extend(
        COUNTEREXAMPLE_CASES
            .iter()
            .map(|(case, upstream_case, min_obligations)| {
                (
                    (*case).to_string(),
                    (*upstream_case).to_string(),
                    "counterexample".to_string(),
                    *min_obligations,
                )
            }),
    );
    expected.extend(
        FAIL_CLOSED_CASES
            .iter()
            .map(|(case, upstream_case, _expected_fragments)| {
                (
                    (*case).to_string(),
                    (*upstream_case).to_string(),
                    "error".to_string(),
                    0,
                )
            }),
    );
    expected
}

fn fail_closed_pattern_metadata() -> BTreeMap<String, Vec<String>> {
    FAIL_CLOSED_CASES
        .iter()
        .map(|(case, _, expected_fragments)| {
            (
                (*case).to_string(),
                expected_fragments
                    .iter()
                    .map(|fragment| (*fragment).to_string())
                    .collect(),
            )
        })
        .collect()
}

fn attach_error_patterns(
    cases: Vec<(String, String, String, usize)>,
) -> Vec<(String, String, String, usize, Vec<String>)> {
    let patterns = fail_closed_pattern_metadata();
    cases
        .into_iter()
        .map(|(case, upstream_case, status, min_obligations)| {
            let expected_patterns = patterns.get(&case).cloned().unwrap_or_default();
            (
                case,
                upstream_case,
                status,
                min_obligations,
                expected_patterns,
            )
        })
        .collect()
}

fn manifest_expected_case_metadata() -> Vec<(String, String, String, usize, Vec<String>)> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/match.rs")
        })
        .expect("Verus manifest should contain match.rs row");

    row["expected_cases"]
        .as_array()
        .expect("match manifest row should contain expected_cases")
        .iter()
        .map(|case| {
            (
                case["case_id"]
                    .as_str()
                    .expect("manifest case should contain case_id")
                    .to_string(),
                case["upstream_case_id"]
                    .as_str()
                    .expect("manifest case should contain upstream_case_id")
                    .to_string(),
                case["expected_verdict"]
                    .as_str()
                    .expect("manifest case should contain expected_verdict")
                    .to_string(),
                case["min_obligations"]
                    .as_u64()
                    .expect("manifest case should contain min_obligations")
                    .try_into()
                    .expect("min_obligations should fit usize"),
                case["expected_error_patterns"]
                    .as_array()
                    .map(|patterns| {
                        patterns
                            .iter()
                            .map(|pattern| {
                                pattern
                                    .as_str()
                                    .expect("expected_error_patterns entries should be strings")
                                    .to_string()
                            })
                            .collect()
                    })
                    .unwrap_or_default(),
            )
        })
        .collect()
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "match_if_let_expression_verified",
        "test_if_let1 executable if-let expression",
        1,
    ),
    (
        "match_payload_binding_value_verified",
        "test1 Maybe::Some payload binding",
        1,
    ),
    (
        "match_none_arm_selection_verified",
        "test1 Maybe::None arm selection witness",
        1,
    ),
    (
        "match_literal_bool_selection_verified",
        "const_and_literals m_bool_lit true branch",
        1,
    ),
    (
        "match_literal_fallback_value_verified",
        "const_and_literals integer fallback branch",
        1,
    ),
    (
        "match_single_arm_enum_verified",
        "match_single_arm_issue_444 c subset",
        1,
    ),
    (
        "match_struct_rest_payload_verified",
        "test3_struct_dots struct rest projection",
        1,
    ),
    (
        "match_or_pattern_payload_verified",
        "test_or_patterns Foo::Bar/Foo::Qux payload merge subset",
        1,
    ),
    (
        "match_tuple_struct_payload_binding_value_verified",
        "tuple-struct payload binding local",
        1,
    ),
    (
        "match_named_struct_exact_payload_verified",
        "test3_struct exact struct field projection",
        1,
    ),
    (
        "match_literal_integer_specific_arm_verified",
        "const_and_literals test3 integer literal arm selection",
        1,
    ),
    (
        "match_or_pattern_empty_variant_verified",
        "or_pattern_1_disjunct_issue1588 empty fallback witness",
        1,
    ),
    (
        "match_enum_tuple_variant_pair_payload_verified",
        "test3/test3b Pair::Pair payload match-expression subset",
        1,
    ),
    (
        "match_enum_struct_variant_payload_verified",
        "test3_enum_struct Pair::Pair record payload match-expression subset",
        1,
    ),
    (
        "match_leading_or_pattern_single_variant_verified",
        "or_pattern_1_disjunct_issue1588 leading single-disjunct arm",
        1,
    ),
    (
        "match_range_pattern_expression_verified",
        "pattern_ranges executable range pattern",
        1,
    ),
    (
        "match_spec_range_expression_verified",
        "pattern_ranges spec match expression",
        1,
    ),
    // Match guards now supported: a proof-mode guarded match with constant arm bodies
    // and a trailing wildcard verifies (the guard selects the correct arm).
    (
        "match_proof_guard_statement_verified",
        "proof-mode guarded match statement",
        1,
    ),
    (
        "match_plain_tuple_local_pattern_verified",
        "test4 tuple local pattern boundary",
        2,
    ),
    (
        "match_tuple_struct_local_destructure_verified",
        "test3_tuple_struct local destructuring boundary",
        3,
    ),
    (
        "match_enum_tuple_variant_local_destructure_verified",
        "test3/test3b Pair::Pair local destructuring boundary",
        3,
    ),
    (
        "match_tuple_struct_rest_local_destructure_verified",
        "dot_dot_patterns tuple constructor rest destructuring boundary",
        6,
    ),
    (
        "match_struct_rest_local_destructure_verified",
        "test3_struct_dots local struct rest destructuring boundary",
        2,
    ),
    (
        "match_struct_exact_local_destructure_verified",
        "test3_struct local exact struct destructuring boundary",
        3,
    ),
    (
        "match_generic_enum_expression_verified",
        "test1 Maybe<A> generic enum match boundary",
        1,
    ),
    // Phase E match sub-lane: a plain-tuple pattern in match-EXPRESSION position
    // `match (a, b) { (left, right) => left && !right }` lowers through the
    // single-variant "Tuple" datatype (left/right project to selectors
    // Tuple_0/Tuple_1) and verifies via the value path. (An arithmetic body needs
    // the exec obligation to bind the projection in body_extract — out of scope;
    // see the engine gate `match_plain_tuple_expression_soundness`.)
    (
        "match_plain_tuple_pattern_expression_verified",
        "plain tuple match-expression pattern boundary",
        1,
    ),
    // Phase E match sub-lane: a TRAILING `..` rest in a tuple / tuple-struct
    // pattern in match-EXPRESSION position lowers through the Constructor
    // `has_rest` machinery (mirroring the sound struct-rest path) — the leading
    // binding projects to its exact field selector (`Tuple_0` / `MatchQuad_0`)
    // and the trailing fields are ignored. Certified genuine by the engine gate
    // `match_rest_pattern_expression_soundness` (false-payload + ignored-field
    // both Counterexample; a middle/back rest stays fail-closed).
    (
        "match_tuple_rest_expression_verified",
        "dot_dot_patterns plain tuple trailing rest match-expression",
        1,
    ),
    (
        "match_tuple_struct_rest_expression_verified",
        "dot_dot_patterns tuple constructor trailing rest match-expression",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "match_literal_arm_wrong_value_counterexample",
        "const_and_literals test3 reachable false literal arm",
        1,
    ),
    (
        "match_literal_bool_wrong_branch_counterexample",
        "const_and_literals m_bool_lit false witness",
        1,
    ),
    (
        "match_single_arm_enum_wrong_value_counterexample",
        "match_single_arm_issue_444 c_fail subset",
        1,
    ),
    (
        "match_struct_rest_false_arm_counterexample",
        "test3_struct_dots_fail struct rest false witness",
        1,
    ),
    (
        "match_or_pattern_false_arm_counterexample",
        "test_or_patterns false or-pattern arm witness",
        1,
    ),
    (
        "match_or_pattern_with_guard_counterexample",
        "pattern_has_both_or_pat_and_if_guard_issue1208 Rust-semantics false arm",
        1,
    ),
    (
        "match_enum_payload_false_branch_counterexample",
        "test1 Maybe::Some payload false branch",
        1,
    ),
    (
        "match_tuple_struct_payload_false_branch_counterexample",
        "test3_tuple_struct tuple-struct payload false branch",
        1,
    ),
    (
        "match_named_struct_exact_false_branch_counterexample",
        "test3_struct exact struct false branch",
        1,
    ),
    (
        "match_literal_fallback_false_branch_counterexample",
        "const_and_literals integer fallback false branch",
        1,
    ),
    (
        "match_or_pattern_empty_variant_wrong_branch_counterexample",
        "or_pattern_1_disjunct_issue1588 empty arm false witness",
        1,
    ),
    (
        "match_leading_or_pattern_single_variant_counterexample",
        "or_pattern_1_disjunct_issue1588 leading single-disjunct false arm",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "match_enum_tuple_variant_statement_payload_error",
        "test3_fails3 Pair::Pair statement-arm payload boundary",
        &["unresolved variable `right`"],
    ),
    (
        // Guards now lower; this case stays fail-closed on a SEPARATE, pre-existing
        // limitation: an arm-body arithmetic expression over a pattern binding leaves
        // the binding unresolved in the overflow-check obligation (orthogonal to
        // guards — the unguarded counterpart fails identically).
        "match_guard_order_expression_error",
        "test1 guarded Maybe::Some match expression",
        &["unresolved variable"],
    ),
    (
        // An arm combining an or-pattern with a guard is rejected fail-closed
        // (faithfulness — Verus rejects it too).
        "match_or_pattern_with_guard_expression_error",
        "pattern_has_both_or_pat_and_if_guard_issue1208 guard boundary",
        &["or-pattern (|) and a match-guard"],
    ),
    (
        // The adjacent `@`-guard fix routes a tuple-struct `@`-subpattern to the
        // fail-closed constructor sub-pattern diagnostic (previously the dropped
        // `@` left `payload` unresolved — a different, weaker fail-closed path).
        "match_at_pattern_expression_error",
        "at_patterns nested binding boundary",
        &["unsupported constructor sub-pattern"],
    ),
    (
        "match_unreached_call_expression_error",
        "test2_unreached unreachable call boundary",
        &["Unsupported unreachable!()"],
    ),
    (
        "match_unreached_dead_branch_expression_error",
        "test2_unreached dead unreached arm boundary",
        &["Unsupported unreachable!()"],
    ),
    (
        "match_boxed_recursive_list_expression_error",
        "test2 List<A> boxed recursive match boundary",
        // ay 4df6ab25 (lazy-DT-AUFLIA) now ENCODES the boxed recursive datatype
        // (the old structural "constructor pattern 'Nil'/MatchBoxList" rejection is
        // gone — progress); the residual gap is the recursive quantifier, so the
        // case now fails closed as NotProved(quantifier-unhandled). Both are sound.
        &["quantifier"],
    ),
];

#[test]
fn match_rs_port_file_is_rust_syntax() {
    let (source, _ast) = port_source_and_ast();
    assert!(
        source.contains("pub const MATCH_RS_EXPECTED_CASES")
            && source.contains("match_rs_expected_cases"),
        "match port should expose expected-case metadata helpers"
    );
}

#[test]
fn match_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_match_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream match.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test1",
        "Maybe::Some(n) if n < 10",
        "#[test] test2_unreached",
        "vstd::pervasive::unreached()",
        "#[test] test2",
        "enum List<A>",
        "Cons(A, Box<List<A>>)",
        "spec fn len<A>(list: &List<A>) -> nat",
        "match iter",
        "#[test] test3_tuple_struct",
        "let Pair(mut y, z) = Pair(true, false);",
        "#[test] test3",
        "enum Pair<A, B>",
        "Pair(A, B)",
        "#[test] test3_struct",
        "struct Pair<A, B> { a: A, b: B }",
        "#[test] test3_struct_dots",
        "let Pair { b: z, .. } = Pair { a: true, b: false };",
        "#[test] test4",
        "let (mut y, z) = (true, false);",
        "#[test] test_if_let1",
        "if let E::X(u) = e",
        "#[test] test_or_patterns",
        "Foo::Bar(x) | Foo::Qux(x) => x as int + 1",
        "spec fn match_spec(foo: Foo) -> int",
        "proof fn test_match_statements(foo: Foo)",
        "#[test] match_single_arm_issue_444",
        "let (d, e) = match self",
        "spec fn d(self) -> (int, int)",
        "#[test] match_arm_returns_poly_issue_523",
        "fn unreached<A>() -> A",
        "#[test] dot_dot_patterns",
        "let Foo::Bar(x, .., y) = tup;",
        "#[test] at_patterns",
        "Some(y @ Some(z))",
        "#[test] const_and_literals",
        "match x {\n                7 => 0,",
        "#[test] pattern_ranges",
        "3u64..=5u64 => true",
        "#[test] pattern_has_both_or_pat_and_if_guard_issue1208",
        "(true, a) | (a, false) if a",
        "#[test] non_exhaustive_spec_ranges",
        "#[test] non_exhaustive_spec_ranges_nested",
        "#[test] non_exhaustive_in_closure",
        "#[test] refut_let",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream match.rs should still contain {expected}"
        );
    }
}

#[test]
fn match_rs_expected_case_metadata_is_exact() {
    let (_source, ast) = port_source_and_ast();
    let actual = parse_match_expected_cases(&ast);
    let expected = expected_case_metadata();
    assert_eq!(
        actual, expected,
        "match port expected-case metadata should exactly match the regression inventory"
    );

    let function_names = ast
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(function) => Some(function.sig.ident.to_string()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut seen_cases = BTreeSet::new();
    for (case, _upstream_case, status, min_obligations) in actual {
        assert!(
            seen_cases.insert(case.clone()),
            "match metadata should not duplicate case {case}"
        );
        assert!(
            function_names.contains(&case),
            "match metadata case {case} should have a matching function"
        );
        assert!(
            matches!(status.as_str(), "verified" | "counterexample" | "error"),
            "match metadata for {case} should use only verified/counterexample/error, got {status}"
        );
        assert_ne!(
            status.to_ascii_lowercase(),
            "unknown",
            "match metadata must not accept Unknown as evidence for {case}"
        );
        if status == "error" {
            assert_eq!(
                min_obligations, 0,
                "error metadata for {case} should record zero expected obligations"
            );
        } else {
            assert!(
                min_obligations >= 1,
                "non-error metadata for {case} should require at least one obligation"
            );
        }
    }

    let metadata_error_cases = expected_case_metadata()
        .into_iter()
        .filter_map(|(case, upstream_case, status, _)| {
            (status == "error").then_some((case, upstream_case))
        })
        .collect::<Vec<_>>();
    let fail_closed_cases = FAIL_CLOSED_CASES
        .iter()
        .map(|(case, upstream_case, _)| ((*case).to_string(), (*upstream_case).to_string()))
        .collect::<Vec<_>>();
    assert_eq!(
        metadata_error_cases, fail_closed_cases,
        "error metadata should match the fail-closed inventory exactly"
    );
}

#[test]
fn match_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();

    assert_eq!(
        manifest_expected_case_metadata(),
        attach_error_patterns(parse_match_expected_cases(&ast)),
        "match manifest expected_cases should match port metadata and fail-closed patterns exactly"
    );
}

#[test]
fn match_rs_fail_closed_fragments_are_specific() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        assert!(
            !expected_fragments.is_empty()
                && expected_fragments
                    .iter()
                    .all(|fragment| fragment.len() >= 8),
            "{case} ({upstream_case}) should pin non-empty, specific diagnostic fragments"
        );
    }
}

#[test]
fn match_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        assert_verified(case, upstream_case, *min_obligations);
    }
}

#[test]
fn match_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        assert_counterexample(case, upstream_case, *min_obligations);
    }
}

#[test]
fn match_rs_unsupported_boundaries_fail_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        assert_fail_closed(case, upstream_case, expected_fragments);
    }
}
