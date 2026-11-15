// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Equality substitution, scope boundary, and binding accumulation tests.
//! Extracted from monolithic normalize.rs as part of #2476.

use std::collections::HashMap;

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, TrustVcExpr};

use super::arith::normalize_int_expr;
use super::substitution::{
    accumulate_equality_binding, extract_equality_binding, insert_and_back_propagate,
    substitute_and_normalize, substitute_vars,
};

fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::MathInt,
    }
}

fn mul(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Mul,
        left: Box::new(left),
        right: Box::new(right),
        ty: TrustVcType::MathInt,
    }
}

fn add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(left),
        right: Box::new(right),
        ty: TrustVcType::MathInt,
    }
}

fn int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::MathInt,
    }
}

fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Extract equality binding: `y == d * q2` → ("y", d * q2)
#[test]
fn test_extract_equality_var_lhs() {
    let y = var("y");
    let d = var("d");
    let q2 = var("q2");
    let rhs = mul(d, q2);
    let assumption = eq(y, rhs.clone());

    let binding = extract_equality_binding(&assumption);
    assert_eq!(binding, Some(("y".to_string(), rhs)));
}

/// Extract equality binding: `d * q2 == y` → ("y", d * q2)
#[test]
fn test_extract_equality_var_rhs() {
    let y = var("y");
    let d = var("d");
    let q2 = var("q2");
    let lhs = mul(d, q2);
    let assumption = eq(lhs.clone(), y);

    let binding = extract_equality_binding(&assumption);
    assert_eq!(binding, Some(("y".to_string(), lhs)));
}

/// No extraction for var == var (ambiguous direction).
#[test]
fn test_extract_equality_var_var_skipped() {
    let a = var("a");
    let b = var("b");
    let assumption = eq(a, b);
    assert_eq!(extract_equality_binding(&assumption), None);
}

/// No extraction for a float variable: `x == 0.0` holds for `x = -0.0`.
#[test]
fn test_extract_equality_float_var_skipped() {
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Float { width: 64 },
    };
    let zero = TrustVcExpr::Cast {
        expr: Box::new(int_lit(0)),
        from_ty: TrustVcType::MathInt,
        to_ty: TrustVcType::Float { width: 64 },
    };
    assert_eq!(extract_equality_binding(&eq(x.clone(), zero.clone())), None);
    assert_eq!(extract_equality_binding(&eq(zero, x)), None);
}

/// No extraction for non-equality comparisons.
#[test]
fn test_extract_equality_non_eq_skipped() {
    let y = var("y");
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(y),
        right: Box::new(int_lit(10)),
    };
    assert_eq!(extract_equality_binding(&expr), None);
}

/// Core GCD substitution test: given `y == d * q2`, substituting into
/// `q * y == d * (q * q2)` should make both sides identical after normalization.
#[test]
fn test_substitute_and_normalize_gcd_step1() {
    let d = var("d");
    let q = var("q");
    let q2 = var("q2");
    let y = var("y");

    // Assumption: y == d * q2
    let mut bindings = HashMap::new();
    bindings.insert("y".to_string(), mul(d.clone(), q2.clone()));

    // Assertion: q * y == d * (q * q2)
    let assertion = eq(
        mul(q.clone(), y),
        mul(d.clone(), mul(q.clone(), q2.clone())),
    );

    let result = substitute_and_normalize(&assertion, &bindings);

    // After substitution: q * (d * q2) == d * (q * q2)
    // After normalization: ((d * q) * q2) == ((d * q) * q2)
    if let TrustVcExpr::Compare { left, right, .. } = &result {
        assert_eq!(
            left, right,
            "q*y == d*(q*q2) with y==d*q2 should normalize to identical sides"
        );
    } else {
        panic!("Expected Compare after substitute_and_normalize");
    }
}

/// Substitution with empty bindings is just normalization.
#[test]
fn test_substitute_and_normalize_empty_bindings() {
    let d = var("d");
    let q = var("q");
    let q2 = var("q2");

    let expr = mul(q.clone(), mul(d.clone(), q2.clone()));
    let expected = normalize_int_expr(&expr);
    let result = substitute_and_normalize(&expr, &HashMap::new());
    assert_eq!(result, expected);
}

/// Substitution doesn't touch unbound variables.
#[test]
fn test_substitute_preserves_unbound_vars() {
    let x = var("x");
    let y = var("y");
    let two = int_lit(2);

    let mut bindings = HashMap::new();
    bindings.insert("y".to_string(), two.clone());

    // x + y → x + 2, then normalize to 2 + x (literal first)
    let expr = add(x.clone(), y);
    let result = substitute_and_normalize(&expr, &bindings);
    let expected = add(two, x);
    assert_eq!(result, expected);
}

// =================================================================
// Substitution scope boundary tests (algorithm audit)
// =================================================================

/// Substitution does NOT recurse into FnCall arguments.
///
/// This is a known limitation: `substitute_vars_inner` returns
/// `expr.clone()` for the wildcard arm (FnCall, Let, Match, etc.).
/// Variables inside FnCall args are not substituted. ay congruence
/// closure compensates (the equality assumption is separately asserted).
/// Part of #2428 audit.
#[test]
fn test_substitute_does_not_recurse_into_fncall() {
    let mut bindings = HashMap::new();
    bindings.insert("y".to_string(), int_lit(5));

    // f(y) — variable inside FnCall
    let expr = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![var("y")],
        return_ty: TrustVcType::MathInt,
    };
    let result = substitute_vars(&expr, &bindings);

    // Substitution doesn't recurse into FnCall → y is NOT replaced.
    assert_eq!(
        result, expr,
        "substitute_vars does not recurse into FnCall (known limitation)"
    );
}

/// Substitution does NOT recurse into Let value or body.
/// Part of #2428 audit.
#[test]
fn test_substitute_does_not_recurse_into_let() {
    let mut bindings = HashMap::new();
    bindings.insert("y".to_string(), int_lit(5));

    // let z = y in z + y
    let expr = TrustVcExpr::Let {
        name: "z".to_string(),
        ty: TrustVcType::MathInt,
        value: Box::new(var("y")),
        body: Box::new(add(var("z"), var("y"))),
    };
    let result = substitute_vars(&expr, &bindings);

    // Neither value nor body is substituted.
    assert_eq!(
        result, expr,
        "substitute_vars does not recurse into Let (known limitation)"
    );
}

/// Normalization does NOT recurse into FnCall arguments.
/// Part of #2428 audit.
#[test]
fn test_normalize_does_not_recurse_into_fncall() {
    let b = var("b");
    let a = var("a");

    // f(b * a) — Mul inside FnCall arg with non-canonical order
    let expr = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![mul(b.clone(), a.clone())],
        return_ty: TrustVcType::MathInt,
    };
    let result = normalize_int_expr(&expr);

    // Normalization doesn't recurse into FnCall → b*a stays as b*a, not a*b.
    assert_eq!(
        result, expr,
        "normalize_int_expr does not recurse into FnCall (known limitation)"
    );
}

// =================================================================
// Shared binding accumulation tests (Part of #2454)
// =================================================================

/// Basic accumulate: `a == 2` produces binding {a → 2}.
#[test]
fn test_accumulate_equality_basic() {
    let mut bindings = HashMap::new();
    let assumption = eq(var("a"), int_lit(2));
    accumulate_equality_binding(&assumption, &mut bindings);
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings.get("a"), Some(&int_lit(2)));
}

/// Chained accumulation: `a == 2`, then `b == a + 1`.
/// RHS is resolved against existing bindings: b → 2 + 1.
#[test]
fn test_accumulate_chained_resolves_rhs() {
    let mut bindings = HashMap::new();
    accumulate_equality_binding(&eq(var("a"), int_lit(2)), &mut bindings);
    accumulate_equality_binding(&eq(var("b"), add(var("a"), int_lit(1))), &mut bindings);
    assert_eq!(bindings.len(), 2);
    // b should resolve to 2 + 1 (a substituted)
    assert_eq!(bindings.get("b"), Some(&add(int_lit(2), int_lit(1))));
}

/// Back-propagation: `b == a + 1`, then `a == 2`.
/// After a→2 is inserted, b's binding updates from `a + 1` to `2 + 1`.
#[test]
fn test_accumulate_back_propagation() {
    let mut bindings = HashMap::new();
    accumulate_equality_binding(&eq(var("b"), add(var("a"), int_lit(1))), &mut bindings);
    assert_eq!(bindings.get("b"), Some(&add(var("a"), int_lit(1))));

    accumulate_equality_binding(&eq(var("a"), int_lit(2)), &mut bindings);
    // b should now be back-propagated: 2 + 1
    assert_eq!(
        bindings.get("b"),
        Some(&add(int_lit(2), int_lit(1))),
        "Back-propagation should update b from a+1 to 2+1"
    );
}

/// Duplicate variable: `a == 2`, then `a == 3` — second is skipped.
#[test]
fn test_accumulate_duplicate_skipped() {
    let mut bindings = HashMap::new();
    accumulate_equality_binding(&eq(var("a"), int_lit(2)), &mut bindings);
    accumulate_equality_binding(&eq(var("a"), int_lit(3)), &mut bindings);
    assert_eq!(bindings.len(), 1);
    assert_eq!(
        bindings.get("a"),
        Some(&int_lit(2)),
        "Duplicate binding should be skipped; first wins"
    );
}

/// Non-equality assumptions are silently ignored.
#[test]
fn test_accumulate_non_equality_ignored() {
    let mut bindings = HashMap::new();
    let range = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(var("x")),
        right: Box::new(int_lit(10)),
    };
    accumulate_equality_binding(&range, &mut bindings);
    assert!(
        bindings.is_empty(),
        "Non-equality should produce no binding"
    );
}

/// insert_and_back_propagate returns true on new insert, false on duplicate.
#[test]
fn test_insert_and_back_propagate_return_value() {
    let mut bindings = HashMap::new();
    assert!(insert_and_back_propagate(
        &mut bindings,
        "x".to_string(),
        int_lit(5)
    ));
    assert!(!insert_and_back_propagate(
        &mut bindings,
        "x".to_string(),
        int_lit(10)
    ));
}
