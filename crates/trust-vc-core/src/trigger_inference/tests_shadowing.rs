// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::tests_support::*;
use super::*;
use crate::ir_expr::TrustVcExpr;

#[test]
fn test_let_shadowing_excludes_body_candidate() {
    // forall |x| let x = 5 in f(x) > 0
    // f(x) inside the let body refers to let-bound x, not quantifier x.
    // No eligible trigger should be found.
    let body = let_expr(
        "x",
        int_lit(5),
        compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "f(x) inside let x = 5 should not be a trigger for quantifier-bound x, got: {result:?}"
    );
}

#[test]
fn test_let_shadowing_preserves_value_candidate() {
    // forall |x| let y = f(x) in g(y) > 0
    // f(x) in the let value DOES reference quantifier-bound x. g(y) does not.
    let body = let_expr(
        "y",
        fn_call("f", vec![var("x")]),
        compare_gt(fn_call("g", vec![var("y")]), int_lit(0)),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert_eq!(result.len(), 1, "should find f(x) in let value");
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "f"),
        "trigger should be f(x) from the let value, got: {:?}",
        result[0][0]
    );
}

#[test]
fn test_let_partial_shadow_two_bound_vars() {
    // forall |x, y| let x = 5 in f(x, y) > 0
    // x is shadowed by let, but y still refers to quantifier-bound y.
    // f(x, y) references y but not quantifier-bound x.
    // f(x, y) covers only y, not x — cannot be a single trigger for both.
    let body = let_expr(
        "x",
        int_lit(5),
        compare_gt(fn_call("f", vec![var("x"), var("y")]), int_lit(0)),
    );
    let result = infer_triggers(&bound_vars(&["x", "y"]), &body);
    // f(x, y) covers y but not x (x is shadowed). No single trigger covers both.
    // No pairs possible either. Result should be empty.
    assert!(
        result.is_empty(),
        "f(x, y) inside let x = 5 should only cover y, not both; got: {result:?}"
    );
}

#[test]
fn test_choose_shadowing_excludes_candidate() {
    // forall |x| choose(|x| is_prime(x)) > 0
    // is_prime(x) inside choose refers to choose-bound x, not quantifier x.
    let body = compare_gt(
        choose_expr("x", fn_call_bool("is_prime", vec![var("x")])),
        int_lit(0),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "is_prime(x) inside choose should not trigger on quantifier-bound x, got: {result:?}"
    );
}

#[test]
fn test_spec_closure_shadowing_excludes_candidate() {
    // forall |x| spec_closure(|x| f(x)) ...
    // f(x) inside closure refers to closure param x, not quantifier x.
    let body = compare_gt(
        spec_closure(&["x"], fn_call("f", vec![var("x")])),
        int_lit(0),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "f(x) inside closure should not trigger on quantifier-bound x, got: {result:?}"
    );
}

#[test]
fn test_nested_quantifier_shadowing_in_references_check() {
    // forall |x| h(forall |x| g(x)) > 0
    // The inner forall rebinds x. h(...) contains a nested quantifier
    // but h itself doesn't take the outer x as a direct argument.
    // expr_references_any_bound should not count inner x as outer x.
    let inner_quant = quantifier_expr(&["x"], compare_gt(fn_call("g", vec![var("x")]), int_lit(0)));
    let body = compare_gt(fn_call("h", vec![inner_quant]), int_lit(0));
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "h(forall |x| g(x)) should not reference outer x; got: {result:?}"
    );
}

#[test]
fn test_no_shadow_no_regression() {
    // forall |x| let y = f(x) in y > 0
    // No shadowing — f(x) should still be collected as trigger.
    let body = let_expr(
        "y",
        fn_call("f", vec![var("x")]),
        compare_gt(var("y"), int_lit(0)),
    );
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert_eq!(result.len(), 1);
    assert!(
        matches!(&result[0][0], TrustVcExpr::FnCall { name, .. } if name == "f"),
        "f(x) should still be inferred when no shadowing"
    );
}

#[test]
fn test_match_arm_constructor_shadowing_excludes_candidate() {
    // forall |x| match foo { Some(x) => f(x) > 0, None => true }
    // f(x) inside the Some(x) arm refers to the pattern-bound x, not
    // the quantifier-bound x. No trigger should be inferred.
    use crate::ir::MatchArm;
    use crate::ir_expr::MatchPattern;

    let body = TrustVcExpr::Match {
        scrutinee: Box::new(var("foo")),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Constructor {
                    variant_name: "Some".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
                body: compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Ident("_".into()),
                body: TrustVcExpr::BoolLit(true),
                guard: None,
            },
        ],
        ty: bool_ty(),
    };
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "f(x) inside match Some(x) arm should not trigger on quantifier-bound x, got: {result:?}"
    );
}

#[test]
fn test_match_arm_ident_shadowing_excludes_candidate() {
    // forall |x| match foo { x => f(x) > 0 }
    // The Ident(x) pattern rebinds x. f(x) in the body refers to the
    // pattern-bound x, not the quantifier-bound x.
    use crate::ir::MatchArm;
    use crate::ir_expr::MatchPattern;

    let body = TrustVcExpr::Match {
        scrutinee: Box::new(var("foo")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Ident("x".into()),
            body: compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
            guard: None,
        }],
        ty: bool_ty(),
    };
    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "f(x) inside match x => arm should not trigger on quantifier-bound x, got: {result:?}"
    );
}
