// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Additive cancellation boundary condition tests (algorithm audit).
//! Extracted from monolithic normalize.rs as part of #2476.

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, TrustVcExpr};

use super::arith::{normalize_int_expr, try_cancel_common_addends};

fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
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

// =================================================================
// Additive cancellation boundary condition tests (algorithm audit)
// =================================================================

/// Boundary: both sides fully cancel → returns None (not simplified to true).
///
/// `a + b == b + a` normalizes both sides identically, so cancellation
/// removes all terms. The function returns None because both sides are
/// empty. This is a missed simplification (could return BoolLit(true)),
/// but is NOT unsound — the equality is still provable via ay structural
/// identity on the already-normalized sides. Part of #2428 audit.
#[test]
fn test_cancel_both_sides_fully_cancel_returns_none() {
    let a = var("a");
    let b = var("b");
    let ty = TrustVcType::MathInt;

    // a + b and b + a normalize to the same form, so cancellation removes all.
    let lhs = normalize_int_expr(&add(a.clone(), b.clone()));
    let rhs = normalize_int_expr(&add(b.clone(), a.clone()));

    let result = try_cancel_common_addends(&lhs, &rhs, &ty);
    assert_eq!(
        result, None,
        "Full cancellation returns None (missed simplification, not a bug)"
    );
}

/// Boundary: one side fully cancels → returns None.
///
/// `a + b == a` — after cancelling `a`, left=[b], right=[].
/// Returns None because right is empty. Could simplify to `b == 0`.
/// Part of #2428 audit.
#[test]
fn test_cancel_one_side_fully_cancels_returns_none() {
    let a = var("a");
    let b = var("b");
    let ty = TrustVcType::MathInt;

    let lhs = add(a.clone(), b.clone());
    let rhs = a.clone();

    let result = try_cancel_common_addends(&lhs, &rhs, &ty);
    assert_eq!(
        result, None,
        "One-side-empty cancellation returns None (missed simplification)"
    );
}

/// Boundary: duplicate terms cancel correctly one-for-one.
///
/// `a + a + b == a + c` → after cancelling one `a`: `a + b == c`.
/// Part of #2428 audit.
#[test]
fn test_cancel_duplicate_terms_one_for_one() {
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let ty = TrustVcType::MathInt;

    // a + a + b == a + c → one `a` cancels → a + b == c
    let lhs = add(add(a.clone(), a.clone()), b.clone());
    let rhs = add(a.clone(), c.clone());

    let result = try_cancel_common_addends(&lhs, &rhs, &ty);
    assert!(result.is_some(), "Partial cancellation should succeed");

    let simplified = result.unwrap();
    // After cancellation: left=[a, b], right=[c]
    // Rebuilt: (a + b) == c
    let expected = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(add(a, b)),
        right: Box::new(c),
    };
    assert_eq!(
        simplified, expected,
        "Duplicate cancels one-for-one: a+a+b==a+c → a+b==c"
    );
}

/// Boundary: no common terms → returns None.
#[test]
fn test_cancel_no_common_terms_returns_none() {
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let ty = TrustVcType::MathInt;

    let result = try_cancel_common_addends(&a, &add(b, c), &ty);
    assert_eq!(result, None, "No common addends → None");
}
