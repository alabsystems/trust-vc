// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::encoder::ir_encoder::normalize::{normalize_int_expr, substitute_vars};

// ========================================================================
// normalize.rs additive cancellation boundary conditions (P1 iter 939)
// ========================================================================

fn math_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::MathInt,
    }
}

fn math_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::MathInt,
    }
}

fn math_add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: crate::ir_expr::ArithOp::Add,
        left: Box::new(left),
        right: Box::new(right),
        ty: TrustVcType::MathInt,
    }
}

fn math_mul(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: crate::ir_expr::ArithOp::Mul,
        left: Box::new(left),
        right: Box::new(right),
        ty: TrustVcType::MathInt,
    }
}

fn math_eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir_expr::CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Boundary: additive cancellation when one side fully cancels.
///
/// `(a + b) == a` — after normalizing and cancelling `a`, the right side
/// is empty, so `try_cancel_common_addends` returns None (missed simplification
/// to `b == 0`). The Compare is returned with both sides normalized but
/// NOT simplified. This is correct (not unsound) because ay still has the
/// original equality. Part of P1 iter 939 algorithm_audit.
#[test]
fn test_cancellation_one_side_empty_returns_unsimplified() {
    let a = math_var("a");
    let b = math_var("b");

    // (a + b) == a — should NOT simplify via cancellation (right side empty)
    let expr = math_eq(math_add(a.clone(), b.clone()), a.clone());
    let result = normalize_int_expr(&expr);

    // After normalization, both sides are normalized individually but no
    // cross-side cancellation occurs. The result is Compare(Eq, (a+b), a).
    match &result {
        TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Eq,
            left,
            right,
        } => {
            // Left is (a+b) normalized — should be (a+b) (already canonical).
            // Right is just a.
            let expected_left = math_add(a.clone(), b.clone());
            let expected_right = a;
            assert_eq!(
                **left, expected_left,
                "Left side should be (a+b) after normalization"
            );
            assert_eq!(**right, expected_right, "Right side should be a");
        }
        _ => panic!("Expected Compare after normalization, got: {:?}", result),
    }
}

/// Boundary: additive cancellation with duplicate terms cancels one-for-one.
///
/// (a + a + b) == (a + c) — cancels one `a`, yielding (a + b) == c.
/// Part of P1 iter 939 algorithm_audit.
#[test]
fn test_cancellation_duplicate_terms_one_for_one() {
    let a = math_var("a");
    let b = math_var("b");
    let c = math_var("c");

    // (a + a + b) == (a + c) → after cancelling one a: (a + b) == c
    let expr = math_eq(
        math_add(math_add(a.clone(), a.clone()), b.clone()),
        math_add(a.clone(), c.clone()),
    );
    let result = normalize_int_expr(&expr);

    // After normalization + cancellation:
    // Left flattens to [a, a, b], right to [a, c]. One a cancels.
    // Remaining left [a, b], remaining right [c].
    // Rebuilt: (a + b) == c
    let expected = math_eq(math_add(a, b), c);
    assert_eq!(
        result, expected,
        "Duplicate terms should cancel one-for-one: (a+a+b)==(a+c) → (a+b)==c"
    );
}

/// Boundary: substitute_vars does NOT recurse into FnCall arguments.
///
/// This is a known limitation: the wildcard arm in substitute_vars_inner
/// returns expr.clone() for FnCall, Let, Match, etc. Variables inside
/// these nodes are not substituted. ay congruence closure compensates.
/// Part of P1 iter 939 algorithm_audit.
#[test]
fn test_substitute_does_not_recurse_into_fncall() {
    let mut bindings = std::collections::HashMap::new();
    bindings.insert("y".to_string(), math_lit(5));

    // f(y) — variable inside FnCall
    let expr = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![math_var("y")],
        return_ty: TrustVcType::MathInt,
    };
    let result = substitute_vars(&expr, &bindings);

    // Substitution doesn't recurse into FnCall → y is NOT replaced.
    assert_eq!(
        result, expr,
        "substitute_vars does not recurse into FnCall (known limitation, ay compensates)"
    );
}

/// Boundary: substitute_vars does NOT recurse into Let value or body.
/// Part of P1 iter 939 algorithm_audit.
#[test]
fn test_substitute_does_not_recurse_into_let() {
    let mut bindings = std::collections::HashMap::new();
    bindings.insert("y".to_string(), math_lit(5));

    // let z = y in z + y
    let expr = TrustVcExpr::Let {
        name: "z".to_string(),
        ty: TrustVcType::MathInt,
        value: Box::new(math_var("y")),
        body: Box::new(math_add(math_var("z"), math_var("y"))),
    };
    let result = substitute_vars(&expr, &bindings);

    assert_eq!(
        result, expr,
        "substitute_vars does not recurse into Let (known limitation, ay compensates)"
    );
}

/// Boundary: normalize_int_expr does NOT recurse into FnCall arguments.
///
/// Mul(b, a) inside a FnCall argument is not normalized to Mul(a, b).
/// Part of P1 iter 939 algorithm_audit.
#[test]
fn test_normalize_does_not_recurse_into_fncall() {
    let a = math_var("a");
    let b = math_var("b");

    // f(b * a) — non-canonical order inside FnCall arg
    let expr = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![math_mul(b.clone(), a.clone())],
        return_ty: TrustVcType::MathInt,
    };
    let result = normalize_int_expr(&expr);

    // Normalization doesn't recurse into FnCall → b*a stays as b*a, not a*b.
    assert_eq!(
        result, expr,
        "normalize_int_expr does not recurse into FnCall (known limitation)"
    );
}

/// Boundary: cancellation with no common terms returns identity.
#[test]
fn test_cancellation_no_common_terms_no_simplification() {
    let a = math_var("a");
    let b = math_var("b");
    let c = math_var("c");

    // a == (b + c) — no common addends
    let expr = math_eq(a.clone(), math_add(b.clone(), c.clone()));
    let result = normalize_int_expr(&expr);

    // No cancellation possible, both sides returned normalized.
    let expected = math_eq(a, math_add(b, c));
    assert_eq!(result, expected, "No common addends → no simplification");
}
