// trust-vc-oracle — Template applicability and coverage tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// For each of the 32 templates, verify it matches at least one realistic
// signature, does NOT match inappropriate signatures, and that instantiation
// produces valid spec syntax. Also tests template refinement with mock
// counterexample data.

use std::time::Duration;
use trust_vc_oracle::{
    all_templates, applicable_templates, CounterexampleField, FailureLocalization,
    FunctionSignature, ProofFeedback,
};

// ---------------------------------------------------------------------------
// Signature factories for realistic function shapes
// ---------------------------------------------------------------------------

fn sig_u32_unary() -> FunctionSignature {
    FunctionSignature::new(
        "inc",
        vec![("x".to_string(), "u32".to_string())],
        Some("u32".to_string()),
        "fn inc(x: u32) -> u32 { x + 1 }",
    )
}

fn sig_i32_unary() -> FunctionSignature {
    FunctionSignature::new(
        "negate",
        vec![("x".to_string(), "i32".to_string())],
        Some("i32".to_string()),
        "fn negate(x: i32) -> i32 { -x }",
    )
}

fn sig_i32_binary() -> FunctionSignature {
    FunctionSignature::new(
        "add",
        vec![
            ("a".to_string(), "i32".to_string()),
            ("b".to_string(), "i32".to_string()),
        ],
        Some("i32".to_string()),
        "fn add(a: i32, b: i32) -> i32 { a + b }",
    )
}

fn sig_u64_binary() -> FunctionSignature {
    FunctionSignature::new(
        "mul",
        vec![
            ("a".to_string(), "u64".to_string()),
            ("b".to_string(), "u64".to_string()),
        ],
        Some("u64".to_string()),
        "fn mul(a: u64, b: u64) -> u64 { a * b }",
    )
}

fn sig_vec_sort() -> FunctionSignature {
    FunctionSignature::new(
        "sort",
        vec![("v".to_string(), "Vec<i32>".to_string())],
        Some("Vec<i32>".to_string()),
        "fn sort(v: Vec<i32>) -> Vec<i32> { todo!() }",
    )
}

fn sig_seq_reverse() -> FunctionSignature {
    FunctionSignature::new(
        "reverse",
        vec![("s".to_string(), "Seq<u64>".to_string())],
        Some("Seq<u64>".to_string()),
        "fn reverse(s: Seq<u64>) -> Seq<u64> { todo!() }",
    )
}

fn sig_vec_to_numeric() -> FunctionSignature {
    FunctionSignature::new(
        "sum",
        vec![("v".to_string(), "Vec<i32>".to_string())],
        Some("i32".to_string()),
        "fn sum(v: Vec<i32>) -> i32 { v.iter().sum() }",
    )
}

fn sig_result_fn() -> FunctionSignature {
    FunctionSignature::new(
        "safe_div",
        vec![
            ("a".to_string(), "i32".to_string()),
            ("b".to_string(), "i32".to_string()),
        ],
        Some("Result<i32, String>".to_string()),
        "fn safe_div(a: i32, b: i32) -> Result<i32, String> { todo!() }",
    )
}

fn sig_void() -> FunctionSignature {
    FunctionSignature::new(
        "log",
        vec![("msg".to_string(), "String".to_string())],
        None,
        "fn log(msg: String) {}",
    )
}

fn sig_bool_return() -> FunctionSignature {
    FunctionSignature::new(
        "is_positive",
        vec![("x".to_string(), "i32".to_string())],
        Some("bool".to_string()),
        "fn is_positive(x: i32) -> bool { x > 0 }",
    )
}

fn sig_bool_relation() -> FunctionSignature {
    FunctionSignature::new(
        "leq",
        vec![
            ("a".to_string(), "i32".to_string()),
            ("b".to_string(), "i32".to_string()),
        ],
        Some("bool".to_string()),
        "fn leq(a: i32, b: i32) -> bool { a <= b }",
    )
}

fn sig_option_fn() -> FunctionSignature {
    FunctionSignature::new(
        "get",
        vec![
            ("v".to_string(), "Vec<i32>".to_string()),
            ("idx".to_string(), "usize".to_string()),
        ],
        Some("Option<i32>".to_string()),
        "fn get(v: Vec<i32>, idx: usize) -> Option<i32> { v.get(idx).copied() }",
    )
}

fn sig_division() -> FunctionSignature {
    FunctionSignature::new(
        "div",
        vec![
            ("a".to_string(), "i32".to_string()),
            ("b".to_string(), "i32".to_string()),
        ],
        Some("i32".to_string()),
        "fn div(a: i32, b: i32) -> i32 { a / b }",
    )
}

fn sig_different_types() -> FunctionSignature {
    FunctionSignature::new(
        "convert",
        vec![
            ("x".to_string(), "i32".to_string()),
            ("y".to_string(), "u64".to_string()),
        ],
        Some("i32".to_string()),
        "fn convert(x: i32, y: u64) -> i32 { x }",
    )
}

fn make_failed_feedback(cx_name: &str, cx_type: &str, cx_value: &str) -> ProofFeedback {
    ProofFeedback::Failed {
        counterexamples: vec![CounterexampleField {
            name: cx_name.to_string(),
            ty: cx_type.to_string(),
            value: cx_value.to_string(),
        }],
        localization: FailureLocalization {
            full_assertion: None,
            sub_results: vec![],
        },
        obligation_name: "ensures".to_string(),
        solver_mode: "default".to_string(),
        elapsed: Duration::from_millis(5),
    }
}

fn make_failed_with_two(
    name1: &str,
    ty1: &str,
    val1: &str,
    name2: &str,
    ty2: &str,
    val2: &str,
) -> ProofFeedback {
    ProofFeedback::Failed {
        counterexamples: vec![
            CounterexampleField {
                name: name1.to_string(),
                ty: ty1.to_string(),
                value: val1.to_string(),
            },
            CounterexampleField {
                name: name2.to_string(),
                ty: ty2.to_string(),
                value: val2.to_string(),
            },
        ],
        localization: FailureLocalization {
            full_assertion: None,
            sub_results: vec![],
        },
        obligation_name: "ensures".to_string(),
        solver_mode: "default".to_string(),
        elapsed: Duration::from_millis(5),
    }
}

// ===========================================================================
// A. Template positive applicability: each template matches at least one sig
// ===========================================================================

#[test]
fn test_range_template_matches_numeric_return() {
    let templates = applicable_templates(&sig_u32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(names.contains(&"range"), "range should match u32 return");
}

#[test]
fn test_non_negative_template_matches_numeric_return() {
    let templates = applicable_templates(&sig_i32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"non_negative"),
        "non_negative should match i32 return"
    );
}

#[test]
fn test_monotonic_template_matches_two_same_numeric() {
    let templates = applicable_templates(&sig_i32_binary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"monotonic"),
        "monotonic should match two same-typed numeric params"
    );
}

#[test]
fn test_idempotent_template_matches_same_in_out_type() {
    let templates = applicable_templates(&sig_u32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"idempotent"),
        "idempotent should match single param with matching return type"
    );
}

#[test]
fn test_length_preserving_template_matches_collection_to_collection() {
    let templates = applicable_templates(&sig_vec_sort());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"length_preserving"),
        "length_preserving should match Vec->Vec"
    );
}

#[test]
fn test_sorted_template_matches_collection_return() {
    let templates = applicable_templates(&sig_vec_sort());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(names.contains(&"sorted"), "sorted should match Vec return");
}

#[test]
fn test_permutation_template_matches_collection_to_collection() {
    let templates = applicable_templates(&sig_seq_reverse());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"permutation"),
        "permutation should match Seq->Seq"
    );
}

#[test]
fn test_injective_template_matches_single_numeric_to_numeric() {
    let templates = applicable_templates(&sig_u32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"injective"),
        "injective should match single numeric param with numeric return"
    );
}

#[test]
fn test_bounded_by_input_template_matches_numeric_params() {
    let templates = applicable_templates(&sig_i32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"bounded_by_input"),
        "bounded_by_input should match numeric params with numeric return"
    );
}

#[test]
fn test_identity_template_matches_same_in_out_type() {
    let templates = applicable_templates(&sig_i32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"identity"),
        "identity should match single param with matching return type"
    );
}

#[test]
fn test_preserves_property_template_matches_same_in_out() {
    let templates = applicable_templates(&sig_u32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"preserves_property"),
        "preserves_property should match single param with matching return type"
    );
}

#[test]
fn test_commutativity_template_matches_two_same_type() {
    let templates = applicable_templates(&sig_i32_binary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"commutativity"),
        "commutativity should match two same-typed params"
    );
}

#[test]
fn test_associativity_template_matches_closed_binary_op() {
    let templates = applicable_templates(&sig_i32_binary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"associativity"),
        "associativity should match closed binary op"
    );
}

#[test]
fn test_distributivity_template_matches_numeric_binary() {
    let templates = applicable_templates(&sig_u64_binary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"distributivity"),
        "distributivity should match two same-typed numeric params"
    );
}

#[test]
fn test_invariant_template_matches_collection_to_collection() {
    let templates = applicable_templates(&sig_vec_sort());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"invariant"),
        "invariant should match collection->collection"
    );
}

#[test]
fn test_error_free_template_matches_result_return() {
    let templates = applicable_templates(&sig_result_fn());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        names.contains(&"error_free"),
        "error_free should match Result return"
    );
}

// ===========================================================================
// B. Template negative applicability: templates DON'T match inappropriate sigs
// ===========================================================================

#[test]
fn test_no_template_matches_void_function() {
    let templates = applicable_templates(&sig_void());
    assert!(
        templates.is_empty(),
        "void function should have no applicable templates, got: {:?}",
        templates.iter().map(|t| t.name()).collect::<Vec<_>>()
    );
}

#[test]
fn test_numeric_templates_dont_match_bool_return() {
    let templates = applicable_templates(&sig_bool_return());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();

    assert!(
        !names.contains(&"range"),
        "range should not match bool return"
    );
    assert!(
        !names.contains(&"non_negative"),
        "non_negative should not match bool return"
    );
    assert!(
        !names.contains(&"monotonic"),
        "monotonic should not match bool return with single param"
    );
}

#[test]
fn test_collection_templates_dont_match_numeric() {
    let templates = applicable_templates(&sig_i32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();

    assert!(
        !names.contains(&"sorted"),
        "sorted should not match numeric return"
    );
    assert!(
        !names.contains(&"permutation"),
        "permutation should not match numeric return"
    );
    assert!(
        !names.contains(&"length_preserving"),
        "length_preserving should not match numeric return"
    );
    assert!(
        !names.contains(&"invariant"),
        "invariant should not match numeric return"
    );
}

#[test]
fn test_error_free_doesnt_match_non_result() {
    let templates = applicable_templates(&sig_u32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        !names.contains(&"error_free"),
        "error_free should not match non-Result return"
    );
}

#[test]
fn test_monotonic_doesnt_match_different_types() {
    let templates = applicable_templates(&sig_different_types());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        !names.contains(&"monotonic"),
        "monotonic should not match different param types"
    );
}

#[test]
fn test_commutativity_doesnt_match_single_param() {
    let templates = applicable_templates(&sig_u32_unary());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        !names.contains(&"commutativity"),
        "commutativity should not match single-param fn"
    );
}

#[test]
fn test_associativity_doesnt_match_when_return_type_differs() {
    // a: i32, b: i32 but return Result<...> — not a closed binary op
    let templates = applicable_templates(&sig_result_fn());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        !names.contains(&"associativity"),
        "associativity should not match when return type differs from param types"
    );
}

#[test]
fn test_identity_doesnt_match_when_return_differs() {
    let templates = applicable_templates(&sig_vec_to_numeric());
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    assert!(
        !names.contains(&"identity"),
        "identity should not match when return type differs from param type"
    );
}

// ===========================================================================
// C. Template instantiation produces valid spec syntax
// ===========================================================================

#[test]
fn test_range_instantiation_syntax() {
    let all = all_templates();
    let range = all.iter().find(|t| t.name() == "range").unwrap();
    let proposals = range.instantiate(&sig_u32_unary());

    assert!(!proposals.is_empty(), "range should produce proposals");
    for p in &proposals {
        for ens in &p.ensures {
            assert!(
                ens.contains("result"),
                "range ensures should reference 'result', got: {}",
                ens
            );
        }
    }
}

#[test]
fn test_non_negative_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "non_negative").unwrap();
    let proposals = tmpl.instantiate(&sig_i32_unary());

    assert!(!proposals.is_empty());
    let has_result_nonneg = proposals
        .iter()
        .any(|p| p.ensures.iter().any(|e| e.contains("result >= 0")));
    assert!(
        has_result_nonneg,
        "non_negative should produce 'result >= 0'"
    );
}

#[test]
fn test_sorted_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "sorted").unwrap();
    let proposals = tmpl.instantiate(&sig_vec_sort());

    assert_eq!(proposals.len(), 1);
    let spec = &proposals[0].ensures[0];
    assert!(
        spec.contains("forall"),
        "sorted should use forall quantifier"
    );
    assert!(spec.contains("result@"), "sorted should reference result@");
    assert!(spec.contains("<="), "sorted should use <= for ordering");
}

#[test]
fn test_permutation_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "permutation").unwrap();
    let proposals = tmpl.instantiate(&sig_vec_sort());

    assert_eq!(proposals.len(), 1);
    let spec = &proposals[0].ensures[0];
    assert!(
        spec.contains("to_multiset"),
        "permutation should reference to_multiset"
    );
    assert!(
        spec.contains("v@"),
        "permutation should reference input param"
    );
    assert!(
        spec.contains("result@"),
        "permutation should reference result@"
    );
}

#[test]
fn test_commutativity_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "commutativity").unwrap();
    let proposals = tmpl.instantiate(&sig_i32_binary());

    assert_eq!(proposals.len(), 1);
    let spec = &proposals[0].ensures[0];
    assert!(
        spec.contains("add(b, a)"),
        "commutativity should propose f(b, a), got: {}",
        spec
    );
    assert!(
        spec.contains("result =="),
        "commutativity should assert result ==, got: {}",
        spec
    );
}

#[test]
fn test_error_free_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "error_free").unwrap();
    let proposals = tmpl.instantiate(&sig_result_fn());

    assert_eq!(proposals.len(), 1);
    let spec = &proposals[0].ensures[0];
    assert_eq!(
        spec, "result.is_ok()",
        "error_free should produce 'result.is_ok()'"
    );
    assert!(
        proposals[0].requires.is_empty(),
        "error_free initial proposal should have no preconditions"
    );
}

#[test]
fn test_identity_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "identity").unwrap();
    let proposals = tmpl.instantiate(&sig_u32_unary());

    assert_eq!(proposals.len(), 1);
    assert_eq!(proposals[0].ensures, vec!["result == x"]);
    assert!(proposals[0].requires.is_empty());
}

#[test]
fn test_bounded_by_input_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "bounded_by_input").unwrap();
    let proposals = tmpl.instantiate(&sig_u32_unary());

    // Should propose both upper and lower bounds
    assert!(
        proposals.len() >= 2,
        "should propose at least upper and lower bounds"
    );
    let all_ensures: Vec<&str> = proposals
        .iter()
        .flat_map(|p| p.ensures.iter().map(|e| e.as_str()))
        .collect();
    assert!(
        all_ensures.contains(&"result <= x"),
        "should propose upper bound"
    );
    assert!(
        all_ensures.contains(&"result >= x"),
        "should propose lower bound"
    );
}

#[test]
fn test_length_preserving_instantiation_syntax() {
    let all = all_templates();
    let tmpl = all
        .iter()
        .find(|t| t.name() == "length_preserving")
        .unwrap();
    let proposals = tmpl.instantiate(&sig_vec_sort());

    assert_eq!(proposals.len(), 1);
    let spec = &proposals[0].ensures[0];
    assert!(
        spec.contains("result@.len()") && spec.contains("v@.len()"),
        "should reference both result and input lengths, got: {}",
        spec
    );
}

// ===========================================================================
// D. Template refinement with mock counterexample data
// ===========================================================================

#[test]
fn test_non_negative_refinement_adds_preconditions() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "non_negative").unwrap();
    let feedback = make_failed_feedback("result", "i32", "-5");

    let refined = tmpl.refine(&sig_i32_unary(), &feedback);
    assert!(!refined.is_empty(), "refine should produce proposals");

    let has_precond = refined.iter().any(|p| !p.requires.is_empty());
    assert!(
        has_precond,
        "non_negative refine should add preconditions when result is negative"
    );

    // Precondition should constrain the input to non-negative
    let preconds: Vec<&str> = refined
        .iter()
        .flat_map(|p| p.requires.iter().map(|r| r.as_str()))
        .collect();
    assert!(
        preconds.iter().any(|p| p.contains(">= 0")),
        "precondition should require >= 0, got: {:?}",
        preconds
    );
}

#[test]
fn test_range_refinement_with_negative_counterexample() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "range").unwrap();

    let feedback = make_failed_feedback("result", "i32", "-10");
    let refined = tmpl.refine(&sig_i32_unary(), &feedback);

    assert!(!refined.is_empty(), "refine should produce proposals");
    // When result is negative, range should widen the lower bound
    let ensures: Vec<&str> = refined
        .iter()
        .flat_map(|p| p.ensures.iter().map(|e| e.as_str()))
        .collect();
    assert!(
        ensures.iter().any(|e| e.contains("-10")),
        "range refine should use counterexample value in bound, got: {:?}",
        ensures
    );
}

#[test]
fn test_bounded_by_input_refinement_switches_direction() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "bounded_by_input").unwrap();

    // Counterexample: result (5) > input (3), so upper bound failed
    let feedback = make_failed_with_two("x", "u32", "3", "result", "u32", "5");
    let refined = tmpl.refine(&sig_u32_unary(), &feedback);

    assert!(!refined.is_empty());
    let ensures: Vec<&str> = refined
        .iter()
        .flat_map(|p| p.ensures.iter().map(|e| e.as_str()))
        .collect();
    assert!(
        ensures.iter().any(|e| e.contains("result >= x")),
        "when result > input, should switch to lower bound, got: {:?}",
        ensures
    );
}

#[test]
fn test_identity_refinement_weakens_to_bounds() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "identity").unwrap();

    let feedback = make_failed_feedback("result", "u32", "5");
    let refined = tmpl.refine(&sig_u32_unary(), &feedback);

    assert!(
        !refined.is_empty(),
        "identity refine should produce weaker proposals"
    );
    let ensures: Vec<&str> = refined
        .iter()
        .flat_map(|p| p.ensures.iter().map(|e| e.as_str()))
        .collect();
    // Should weaken to either >= or <= bound
    assert!(
        ensures
            .iter()
            .any(|e| e.contains("result >=") || e.contains("result <=")),
        "identity refine should weaken to bounds, got: {:?}",
        ensures
    );
}

#[test]
fn test_error_free_refinement_adds_numeric_preconditions() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "error_free").unwrap();

    let feedback = make_failed_feedback("result", "Result", "Err(division by zero)");
    let refined = tmpl.refine(&sig_result_fn(), &feedback);

    assert!(!refined.is_empty());
    let has_precond = refined.iter().any(|p| !p.requires.is_empty());
    assert!(
        has_precond,
        "error_free refine should add numeric preconditions"
    );

    // Should constrain numeric params to >= 0
    let preconds: Vec<&str> = refined
        .iter()
        .flat_map(|p| p.requires.iter().map(|r| r.as_str()))
        .collect();
    assert!(
        preconds.iter().any(|p| p.contains(">= 0")),
        "should constrain numeric params, got: {:?}",
        preconds
    );
}

#[test]
fn test_sorted_refinement_weakens_to_adjacent() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "sorted").unwrap();

    let feedback = make_failed_feedback("result", "Vec<i32>", "[3, 1, 2]");
    let refined = tmpl.refine(&sig_vec_sort(), &feedback);

    assert!(!refined.is_empty());
    let spec = &refined[0].ensures[0];
    assert!(
        spec.contains("i + 1"),
        "sorted refine should weaken to adjacent comparison, got: {}",
        spec
    );
}

#[test]
fn test_permutation_refinement_weakens_to_length() {
    let all = all_templates();
    let tmpl = all.iter().find(|t| t.name() == "permutation").unwrap();

    let feedback = make_failed_feedback("result", "Vec<i32>", "[1, 2, 3]");
    let refined = tmpl.refine(&sig_vec_sort(), &feedback);

    assert!(!refined.is_empty());
    let spec = &refined[0].ensures[0];
    assert!(
        spec.contains("len()"),
        "permutation refine should weaken to length equality, got: {}",
        spec
    );
}

// ===========================================================================
// E. Structural properties of the template registry
// ===========================================================================

#[test]
fn test_all_template_names_are_unique() {
    let templates = all_templates();
    let names: Vec<&str> = templates.iter().map(|t| t.name()).collect();
    let mut deduped = names.clone();
    deduped.sort();
    deduped.dedup();
    assert_eq!(names.len(), deduped.len(), "template names must be unique");
}

#[test]
fn test_all_templates_have_nonempty_description() {
    for t in all_templates() {
        assert!(
            !t.description().is_empty(),
            "template '{}' has empty description",
            t.name()
        );
    }
}

#[test]
fn test_every_template_instantiates_nonempty_for_its_matching_sig() {
    // For each template, find a sig it matches and verify instantiation is non-empty
    let template_sig_pairs: Vec<(&str, FunctionSignature)> = vec![
        ("range", sig_u32_unary()),
        ("non_negative", sig_i32_unary()),
        ("monotonic", sig_i32_binary()),
        ("idempotent", sig_u32_unary()),
        ("length_preserving", sig_vec_sort()),
        ("sorted", sig_vec_sort()),
        ("permutation", sig_vec_sort()),
        ("injective", sig_u32_unary()),
        ("bounded_by_input", sig_u32_unary()),
        ("identity", sig_u32_unary()),
        ("preserves_property", sig_u32_unary()),
        ("commutativity", sig_i32_binary()),
        ("associativity", sig_i32_binary()),
        ("distributivity", sig_i32_binary()),
        ("invariant", sig_vec_sort()),
        ("error_free", sig_result_fn()),
        // New CGSR templates (17-32)
        ("transitivity", sig_bool_relation()),
        ("reflexivity", sig_bool_relation()),
        ("symmetry", sig_bool_relation()),
        ("antisymmetry", sig_bool_relation()),
        ("totality", sig_bool_relation()),
        ("surjective", sig_u32_unary()),
        ("nullability_guard", sig_option_fn()),
        ("involution", sig_u32_unary()),
        ("fixed_point", sig_u32_unary()),
        ("zero_element", sig_i32_binary()),
        ("identity_element", sig_i32_binary()),
        ("cancellation", sig_i32_binary()),
        ("containment_preserving", sig_vec_sort()),
        ("subset_bound", sig_vec_sort()),
        ("division_safety", sig_division()),
        ("boundedness", sig_i32_binary()),
    ];

    let all = all_templates();
    for (name, sig) in &template_sig_pairs {
        let tmpl = all
            .iter()
            .find(|t| t.name() == *name)
            .unwrap_or_else(|| panic!("template '{}' not found", name));

        assert!(
            tmpl.applicable_to(sig),
            "template '{}' should be applicable to its matching sig",
            name
        );

        let proposals = tmpl.instantiate(sig);
        assert!(
            !proposals.is_empty(),
            "template '{}' should produce at least one proposal for its matching sig",
            name
        );

        // Every proposal should have at least one ensures clause
        for (i, p) in proposals.iter().enumerate() {
            assert!(
                !p.ensures.is_empty(),
                "template '{}' proposal {} has empty ensures",
                name,
                i
            );
        }
    }
}

#[test]
fn test_every_template_refine_returns_proposals_on_failure() {
    let template_sig_pairs: Vec<(&str, FunctionSignature)> = vec![
        ("range", sig_u32_unary()),
        ("non_negative", sig_i32_unary()),
        ("monotonic", sig_i32_binary()),
        ("idempotent", sig_u32_unary()),
        ("length_preserving", sig_vec_sort()),
        ("sorted", sig_vec_sort()),
        ("permutation", sig_vec_sort()),
        ("injective", sig_u32_unary()),
        ("bounded_by_input", sig_u32_unary()),
        ("identity", sig_u32_unary()),
        ("preserves_property", sig_u32_unary()),
        ("commutativity", sig_i32_binary()),
        ("associativity", sig_i32_binary()),
        ("distributivity", sig_i32_binary()),
        ("invariant", sig_vec_sort()),
        ("error_free", sig_result_fn()),
        // New CGSR templates (17-32)
        ("transitivity", sig_bool_relation()),
        ("reflexivity", sig_bool_relation()),
        ("symmetry", sig_bool_relation()),
        ("antisymmetry", sig_bool_relation()),
        ("totality", sig_bool_relation()),
        ("surjective", sig_u32_unary()),
        ("nullability_guard", sig_option_fn()),
        ("involution", sig_u32_unary()),
        ("fixed_point", sig_u32_unary()),
        ("zero_element", sig_i32_binary()),
        ("identity_element", sig_i32_binary()),
        ("cancellation", sig_i32_binary()),
        ("containment_preserving", sig_vec_sort()),
        ("subset_bound", sig_vec_sort()),
        ("division_safety", sig_division()),
        ("boundedness", sig_i32_binary()),
    ];

    let feedback = make_failed_feedback("result", "i32", "-1");
    let all = all_templates();

    for (name, sig) in &template_sig_pairs {
        let tmpl = all
            .iter()
            .find(|t| t.name() == *name)
            .unwrap_or_else(|| panic!("template '{}' not found", name));

        let refined = tmpl.refine(sig, &feedback);
        assert!(
            !refined.is_empty(),
            "template '{}' refine should produce at least one proposal on failure",
            name
        );
    }
}
