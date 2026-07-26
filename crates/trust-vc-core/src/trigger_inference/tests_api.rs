// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::tests_support::*;
use super::*;
use crate::ir_expr::TrustVcExpr;

// --- Single function call trigger ---

#[test]
fn test_infer_single_fncall_trigger() {
    // forall(|x| f(x) > 0) → trigger [f(x)]
    let body = compare_gt(fn_call("f", vec![var("x")]), int_lit(0));
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert_eq!(result.len(), 1, "should infer one trigger group");
    assert_eq!(result[0].len(), 1, "group should have one trigger");
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "f"),
        "trigger should be f(x)"
    );
}

// --- Index trigger ---

#[test]
fn test_infer_index_trigger() {
    // forall(|i| s[i] > 0) → trigger [s[i]]
    let body = compare_gt(index_expr(var("s"), var("i")), int_lit(0));
    let bvars = vec![("i".to_string(), u32_ty())];
    let result = infer_triggers(&bvars, &body);
    assert_eq!(result.len(), 1);
    assert!(
        matches!(&result[0][0], TrustVcExpr::Index { .. }),
        "trigger should be s[i]"
    );
}

// --- Multi-trigger for two bound vars ---

#[test]
fn test_infer_multi_trigger() {
    // forall(|x, y| f(x) && g(y)) → trigger group [f(x), g(y)]
    let body = logic_and(
        fn_call_bool("f", vec![var("x")]),
        fn_call_bool("g", vec![var("y")]),
    );
    let result = infer_triggers(&bound_vars(&["x", "y"]), &body);
    assert!(!result.is_empty(), "should find at least one trigger group");
    // The group should cover both x and y
    let group = &result[0];
    assert_eq!(group.len(), 2, "pair trigger group should have two members");
}

// --- No trigger for pure arithmetic ---

#[test]
fn test_no_trigger_for_pure_arith() {
    // forall(|x| x + 1 > 0) → no eligible candidates
    let body = compare_gt(arith_add(var("x"), int_lit(1)), int_lit(0));
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "pure arithmetic body should yield no triggers"
    );
}

// --- Comparison is not a trigger candidate ---

#[test]
fn test_excludes_comparison_triggers() {
    // forall(|x| x == f(x)) → trigger [f(x)], not [x == f(x)]
    let body = compare_eq(var("x"), fn_call("f", vec![var("x")]));
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert_eq!(result.len(), 1);
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "f"),
        "trigger should be f(x), not the comparison"
    );
}

// --- Coverage check: single trigger must mention all bound vars ---

#[test]
fn test_covers_all_bound_vars() {
    // forall(|x, y| f(x) > 0) — f(x) only covers x, not y
    // g(x, y) covers both
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(fn_call("g", vec![var("x"), var("y")]), int_lit(0)),
    );
    let result = infer_triggers(&bound_vars(&["x", "y"]), &body);
    assert_eq!(result.len(), 1);
    // Conservative mode should pick g(x, y) as the single trigger
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "g"),
        "should prefer g(x, y) which covers all bound vars"
    );
}

// --- Conservative picks best (smallest) ---

#[test]
fn test_conservative_picks_best() {
    // Two candidates: f(x) and g(x, x + 1) — f(x) is smaller
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(
            fn_call("g", vec![var("x"), arith_add(var("x"), int_lit(1))]),
            int_lit(0),
        ),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].len(), 1);
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "f"),
        "conservative should pick f(x) over g(x, x+1) because it's smaller"
    );
}

// --- Aggressive returns all valid single triggers ---

#[test]
fn test_aggressive_returns_all() {
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(fn_call("g", vec![var("x")]), int_lit(0)),
    );
    let result = infer_triggers_aggressive(&bound_vars(&["x"]), &body);
    assert_eq!(
        result.len(),
        2,
        "aggressive should return both f(x) and g(x)"
    );
}

// --- Empty bound vars returns empty ---

#[test]
fn test_empty_bound_vars() {
    let body = fn_call("f", vec![var("x")]);
    let result = infer_triggers(&[], &body);
    assert!(result.is_empty());
}

// --- Nested function call: both outer and inner are candidates ---

#[test]
fn test_nested_fncall_both_candidates() {
    // forall(|x| h(f(x)) > 0) — both h(f(x)) and f(x) are candidates
    // Conservative picks f(x) as it's smaller
    let body = compare_gt(fn_call("h", vec![fn_call("f", vec![var("x")])]), int_lit(0));
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].len(), 1);
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "f"),
        "should prefer inner f(x) over outer h(f(x))"
    );
}

// --- FnCall with no bound var references yields no trigger ---

#[test]
fn test_fncall_no_bound_var_not_candidate() {
    // forall(|x| f(y) > x) — f(y) doesn't reference x
    let body = compare_gt(
        fn_call(
            "f",
            vec![TrustVcExpr::Var {
                name: "y".to_string(),
                ty: u32_ty(),
            }],
        ),
        var("x"),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(result.is_empty(), "f(y) doesn't reference bound var x");
}

// --- Mode-aware API tests (#2461 Slice 3) ---

#[test]
fn test_with_mode_conservative_picks_one() {
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(fn_call("g", vec![var("x")]), int_lit(0)),
    );
    let result = infer_triggers_with_mode(
        &bound_vars(&["x"]),
        &body,
        TriggerInferenceMode::Conservative,
    );
    assert_eq!(result.len(), 1, "conservative mode should return one group");
    assert_eq!(result[0].len(), 1, "group should have one trigger");
}

#[test]
fn test_with_mode_aggressive_returns_all() {
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(fn_call("g", vec![var("x")]), int_lit(0)),
    );
    let result =
        infer_triggers_with_mode(&bound_vars(&["x"]), &body, TriggerInferenceMode::Aggressive);
    assert_eq!(
        result.len(),
        2,
        "aggressive mode should return both f(x) and g(x)"
    );
}

#[test]
fn test_from_names_with_mode_conservative() {
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(fn_call("g", vec![var("x")]), int_lit(0)),
    );
    let result =
        infer_triggers_from_names_with_mode(&["x"], &body, TriggerInferenceMode::Conservative);
    assert_eq!(result.len(), 1, "conservative names-only should return one");
}

#[test]
fn test_from_names_with_mode_aggressive() {
    let body = logic_and(
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        compare_gt(fn_call("g", vec![var("x")]), int_lit(0)),
    );
    let result =
        infer_triggers_from_names_with_mode(&["x"], &body, TriggerInferenceMode::Aggressive);
    assert_eq!(result.len(), 2, "aggressive names-only should return both");
}

#[test]
fn test_default_mode_is_conservative() {
    assert_eq!(
        TriggerInferenceMode::default(),
        TriggerInferenceMode::Conservative,
        "default mode should be conservative"
    );
}
