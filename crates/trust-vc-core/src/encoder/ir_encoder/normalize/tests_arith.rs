// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Arithmetic normalization and distribution tests.
//! Extracted from monolithic normalize.rs as part of #2476.

use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, TrustVcExpr};

use super::arith::normalize_int_expr;

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

fn real_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Real,
    }
}

fn real_add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(left),
        right: Box::new(right),
        ty: TrustVcType::Real,
    }
}

fn sub(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Sub,
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

/// Core GCD test: `q * (d * q2)` and `d * (q * q2)` must normalize
/// to the same canonical form.
#[test]
fn test_mul_commutativity_associativity_canonical() {
    let d = var("d");
    let q = var("q");
    let q2 = var("q2");

    // q * (d * q2)
    let lhs = mul(q.clone(), mul(d.clone(), q2.clone()));
    // d * (q * q2)
    let rhs = mul(d.clone(), mul(q.clone(), q2.clone()));

    let lhs_norm = normalize_int_expr(&lhs);
    let rhs_norm = normalize_int_expr(&rhs);

    assert_eq!(
        lhs_norm, rhs_norm,
        "q * (d * q2) and d * (q * q2) must normalize to the same form"
    );
}

/// Verify the canonical form is left-associative alphabetical: ((d * q) * q2).
#[test]
fn test_mul_canonical_form() {
    let d = var("d");
    let q = var("q");
    let q2 = var("q2");

    let expr = mul(q.clone(), mul(d.clone(), q2.clone()));
    let normalized = normalize_int_expr(&expr);

    // Expected: ((d * q) * q2) — alphabetical, left-associative
    let expected = mul(mul(d, q), q2);
    assert_eq!(normalized, expected);
}

/// Addition also normalizes: `c + a + b` → `((a + b) + c)`.
#[test]
fn test_add_canonical_form() {
    let a = var("a");
    let b = var("b");
    let c = var("c");

    // (c + a) + b
    let expr = add(add(c.clone(), a.clone()), b.clone());
    let normalized = normalize_int_expr(&expr);

    // Expected: ((a + b) + c) — alphabetical
    let expected = add(add(a, b), c);
    assert_eq!(normalized, expected);
}

#[test]
fn test_real_add_commutativity_is_canonical() {
    let x = real_var("x");
    let y = real_var("y");

    let lhs = normalize_int_expr(&real_add(x.clone(), y.clone()));
    let rhs = normalize_int_expr(&real_add(y, x));

    assert_eq!(lhs, rhs, "exact Real addition must have one canonical form");
}

#[test]
fn test_float_addition_preserves_source_order() {
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Float { width: 64 },
    };
    let y = TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Float { width: 64 },
    };
    let expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(y),
        right: Box::new(x),
        ty: TrustVcType::Float { width: 64 },
    };

    assert_eq!(
        normalize_int_expr(&expr),
        expr,
        "IEEE addition must not be reordered"
    );
}

/// Subtraction and division are NOT commutative/associative — left unchanged.
#[test]
fn test_sub_div_not_normalized() {
    let a = var("a");
    let b = var("b");

    let sub = TrustVcExpr::Arith {
        op: ArithOp::Sub,
        left: Box::new(b.clone()),
        right: Box::new(a.clone()),
        ty: TrustVcType::MathInt,
    };
    let normalized = normalize_int_expr(&sub);

    // Sub is not commutative, so b - a stays as b - a
    assert_eq!(normalized, sub);
}

/// Literals sort before variables: `x * 2` → `2 * x`.
#[test]
fn test_literal_sorts_first() {
    let x = var("x");
    let two = int_lit(2);

    let expr = mul(x.clone(), two.clone());
    let normalized = normalize_int_expr(&expr);

    let expected = mul(two, x);
    assert_eq!(normalized, expected);
}

/// Nested normalization through comparisons.
#[test]
fn test_normalize_through_compare() {
    use crate::ir_expr::CompareOp;

    let d = var("d");
    let q = var("q");
    let q2 = var("q2");

    // q * (d * q2) == d * (q * q2)
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(mul(q.clone(), mul(d.clone(), q2.clone()))),
        right: Box::new(mul(d.clone(), mul(q.clone(), q2.clone()))),
    };

    let normalized = normalize_int_expr(&expr);

    // After normalization, both sides should be identical
    if let TrustVcExpr::Compare { left, right, .. } = &normalized {
        assert_eq!(
            left, right,
            "Both sides of equality should normalize to same form"
        );
    } else {
        panic!("Expected Compare after normalization");
    }
}

// =================================================================
// Distribution tests (Part of #2400)
// =================================================================

/// Distribution: `d * (a + b)` → `d*a + d*b` after normalization.
#[test]
fn test_distribute_mul_over_add() {
    let a = var("a");
    let b = var("b");
    let d = var("d");

    // d * (a + b)
    let expr = mul(d.clone(), add(a.clone(), b.clone()));
    let result = normalize_int_expr(&expr);

    // Expected: (a*d) + (b*d) — each product sorted, then sum sorted
    // a*d sorts before b*d (Variable("a") < Variable("b"))
    let expected = add(mul(a, d.clone()), mul(b, d));
    assert_eq!(result, expected, "d*(a+b) should distribute to (a*d)+(b*d)");
}

/// Distribution: `d * (a - b)` → `d*a - d*b` after normalization.
#[test]
fn test_distribute_mul_over_sub() {
    let a = var("a");
    let b = var("b");
    let d = var("d");

    let expr = mul(d.clone(), sub(a.clone(), b.clone()));
    let result = normalize_int_expr(&expr);

    let expected = sub(mul(a, d.clone()), mul(b, d));
    assert_eq!(result, expected, "d*(a-b) should distribute to (a*d)-(b*d)");
}

/// Symbolic distributivity shape: `(x - y) * z` and `x*z - y*z`
/// normalize to the same tree.
#[test]
fn test_distribute_mul_over_sub_matches_expanded_form() {
    let x = var("x");
    let y = var("y");
    let z = var("z");

    let factored = mul(sub(x.clone(), y.clone()), z.clone());
    let expanded = sub(mul(x, z.clone()), mul(y, z));

    assert_eq!(normalize_int_expr(&factored), normalize_int_expr(&expanded));
}

/// Distribution with multiple factors: `d * e * (a + b)` →
/// `(d*e)*a + (d*e)*b` after normalization.
#[test]
fn test_distribute_mul_multi_factor_over_add() {
    let a = var("a");
    let b = var("b");
    let d = var("d");
    let e = var("e");

    // d * e * (a + b) = d * (e * (a + b))
    let expr = mul(d.clone(), mul(e.clone(), add(a.clone(), b.clone())));
    let result = normalize_int_expr(&expr);

    // After flattening: [d, e, (a+b)]. One Add found → distribute.
    // factor = (d*e), sum_terms = [a, b]
    // distributed: normalize(d*e * a), normalize(d*e * b)
    // Each: flatten [d, e, a] → sort → ((a*d)*e), and [d, e, b] → ((b*d)*e)
    // Final sum sorted: ((a*d)*e) + ((b*d)*e)
    let ade = mul(mul(a, d.clone()), e.clone());
    let bde = mul(mul(b, d), e);
    let expected = add(ade, bde);
    assert_eq!(
        result, expected,
        "d*e*(a+b) should distribute to ((a*d)*e)+((b*d)*e)"
    );
}

/// No distribution when two Add operands in product (avoids blowup).
#[test]
fn test_no_distribute_two_sums() {
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let d = var("d");

    // (a + b) * (c + d) — two Add operands → no distribution
    let expr = mul(add(a.clone(), b.clone()), add(c.clone(), d.clone()));
    let result = normalize_int_expr(&expr);

    // Should flatten to sorted operands but NOT distribute
    // Flattened Mul operands: [(a+b), (c+d)] — both are Compound sort keys
    // Compound("...") ordering depends on Debug repr, but no distribution occurs
    assert!(
        !matches!(
            result,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                ..
            }
        ),
        "(a+b)*(c+d) should NOT distribute (two sums); got Add at top level"
    );
}

/// GCD chain: back-propagation + distribution resolve chained equalities.
/// Given y→d*q2, x→q*y+r (resolved to q*(d*q2)+r), q1→q*q2+q3,
/// substituting into `x == d*q1` yields:
///   q*(d*q2)+r == d*(q*q2+q3)
/// After distribution + normalization:
///   (d*q)*q2 + r == (d*q)*q2 + d*q3
#[test]
fn test_gcd_chain_distribution_normalizes_both_sides() {
    let d = var("d");
    let q = var("q");
    let q2 = var("q2");
    let q3 = var("q3");
    let r = var("r");

    // LHS of the substituted fourth assumption: q*(d*q2) + r
    let lhs = add(mul(q.clone(), mul(d.clone(), q2.clone())), r.clone());
    // RHS: d*(q*q2 + q3)
    let rhs = mul(d.clone(), add(mul(q.clone(), q2.clone()), q3.clone()));

    let lhs_norm = normalize_int_expr(&lhs);
    let rhs_norm = normalize_int_expr(&rhs);

    // LHS: q*(d*q2)+r → flatten mul [d,q,q2] → (d*q)*q2, then add [((d*q)*q2), r]
    // RHS: d*(q*q2+q3) → distribute: d*(q*q2) + d*q3 → ((d*q)*q2) + (d*q3)
    // These are NOT equal (r vs d*q3), but structure should be Add at top level
    assert!(
        matches!(
            lhs_norm,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                ..
            }
        ),
        "LHS should normalize to sum form"
    );
    assert!(
        matches!(
            rhs_norm,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                ..
            }
        ),
        "RHS should normalize to sum form"
    );
}
