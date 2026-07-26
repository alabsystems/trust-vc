//! Tests for the nonlinear-real certificate search.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, LogicOp, TrustVcExpr};

// ---------------------------------------------------------------------------
// TrustVcExpr builders (real-typed)
// ---------------------------------------------------------------------------

fn rvar(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Real,
    }
}

fn rlit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Real,
    }
}

fn arith(op: ArithOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(l),
        right: Box::new(r),
        ty: TrustVcType::Real,
    }
}

fn add(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    arith(ArithOp::Add, l, r)
}

fn mul(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    arith(ArithOp::Mul, l, r)
}

fn cmp(op: CompareOp, l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}

fn and(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(l),
        right: Box::new(r),
    }
}

fn implies(p: TrustVcExpr, c: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Implies {
        premise: Box::new(p),
        conclusion: Box::new(c),
    }
}

/// Build the `real_nonlinear1` goal:
/// `a >= 0 && b >= 0 && a*a + b*b == (a*b + 1)*q ==> q >= 0`.
fn real_nonlinear_goal() -> TrustVcExpr {
    let a = || rvar("a");
    let b = || rvar("b");
    let q = || rvar("q");

    let h1 = cmp(CompareOp::Ge, a(), rlit(0));
    let h2 = cmp(CompareOp::Ge, b(), rlit(0));
    // a*a + b*b == (a*b + 1)*q
    let lhs = add(mul(a(), a()), mul(b(), b()));
    let rhs = mul(add(mul(a(), b()), rlit(1)), q());
    let h3 = cmp(CompareOp::Eq, lhs, rhs);

    let premise = and(and(h1, h2), h3);
    implies(premise, cmp(CompareOp::Ge, q(), rlit(0)))
}

// ---------------------------------------------------------------------------
// should-verify direction
// ---------------------------------------------------------------------------

#[test]
fn proves_real_nonlinear1_division_shape() {
    let expr = real_nonlinear_goal();
    assert_eq!(
        try_prove_nonlinear_real(&expr),
        NonlinearRealOutcome::Proven,
        "real_nonlinear1 division-shape lemma must be discharged by certificate search"
    );
}

#[test]
fn proves_sum_of_squares_nonneg() {
    // (no premise) ==> a*a + b*b >= 0
    let a = rvar("a");
    let b = rvar("b");
    let goal = cmp(
        CompareOp::Ge,
        add(mul(a.clone(), a.clone()), mul(b.clone(), b.clone())),
        rlit(0),
    );
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::Proven,
        "a^2 + b^2 >= 0 is a sum of squares"
    );
}

#[test]
fn proves_single_square_nonneg() {
    // x*x >= 0
    let x = rvar("x");
    let goal = cmp(CompareOp::Ge, mul(x.clone(), x.clone()), rlit(0));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::Proven
    );
}

#[test]
fn proves_completed_square_psd_form() {
    // x*x + 2*x*y + y*y >= 0   (i.e. (x+y)^2 >= 0)
    let x = rvar("x");
    let y = rvar("y");
    let xx = mul(x.clone(), x.clone());
    let yy = mul(y.clone(), y.clone());
    let two_xy = mul(rlit(2), mul(x.clone(), y.clone()));
    let quad = add(add(xx, two_xy), yy);
    let goal = cmp(CompareOp::Ge, quad, rlit(0));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::Proven,
        "(x+y)^2 >= 0 is PSD"
    );
}

#[test]
fn proves_product_of_nonneg_hypotheses() {
    // a >= 0 && b >= 0 ==> a*b >= 0
    let a = rvar("a");
    let b = rvar("b");
    let premise = and(
        cmp(CompareOp::Ge, a.clone(), rlit(0)),
        cmp(CompareOp::Ge, b.clone(), rlit(0)),
    );
    let goal = implies(premise, cmp(CompareOp::Ge, mul(a, b), rlit(0)));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::Proven,
        "product of two nonneg reals is nonneg"
    );
}

#[test]
fn outcome_wrapper_returns_verified_when_proven() {
    let expr = real_nonlinear_goal();
    assert!(matches!(
        try_prove_nonlinear_real_outcome(&expr),
        Some(AssertionOutcome::Verified)
    ));
}

#[test]
fn proves_implication_in_disjunctive_normal_form() {
    // `P ==> Q` normalized to `!(P) || Q` (the encoder's lowered form).
    let a = || rvar("a");
    let b = || rvar("b");
    let q = || rvar("q");
    let h1 = cmp(CompareOp::Ge, a(), rlit(0));
    let h2 = cmp(CompareOp::Ge, b(), rlit(0));
    let lhs = add(mul(a(), a()), mul(b(), b()));
    let rhs = mul(add(mul(a(), b()), rlit(1)), q());
    let h3 = cmp(CompareOp::Eq, lhs, rhs);
    let premise = and(and(h1, h2), h3);
    let not_premise = TrustVcExpr::Not(Box::new(premise));
    let dnf = TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(not_premise),
        right: Box::new(cmp(CompareOp::Ge, q(), rlit(0))),
    };
    assert_eq!(
        try_prove_nonlinear_real(&dnf),
        NonlinearRealOutcome::Proven,
        "implication in `!P || Q` form must be recognized and proven"
    );
}

#[test]
fn does_not_treat_plain_disjunction_as_implication() {
    // `a >= 0 || b >= 0` is NOT an implication (no negated disjunct) and is
    // not universally true, so it must fail closed.
    let a = rvar("a");
    let b = rvar("b");
    let goal = TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(cmp(CompareOp::Ge, a, rlit(0))),
        right: Box::new(cmp(CompareOp::Ge, b, rlit(0))),
    };
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished,
        "a plain `||` with no negated disjunct is not an implication"
    );
}

// ---------------------------------------------------------------------------
// should-fail direction (must NOT spuriously prove — fail-closed)
// ---------------------------------------------------------------------------

#[test]
fn does_not_prove_indefinite_quadratic() {
    // x*x - y*y >= 0  is FALSE in general (e.g. x=0, y=1). Must not prove.
    let x = rvar("x");
    let y = rvar("y");
    let quad = arith(
        ArithOp::Sub,
        mul(x.clone(), x.clone()),
        mul(y.clone(), y.clone()),
    );
    let goal = cmp(CompareOp::Ge, quad, rlit(0));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished,
        "x^2 - y^2 >= 0 is not universally true; must fail closed"
    );
}

#[test]
fn does_not_prove_division_shape_without_sign_hypotheses() {
    // Drop the a>=0, b>=0 hypotheses. Then a*b+1 is NOT provably positive
    // (a*b can be very negative), so q*(a*b+1)=a^2+b^2 does NOT force q>=0.
    // This mirrors real_nonlinear2 failing without the nonlinear_arith hint.
    let a = || rvar("a");
    let b = || rvar("b");
    let q = || rvar("q");
    let lhs = add(mul(a(), a()), mul(b(), b()));
    let rhs = mul(add(mul(a(), b()), rlit(1)), q());
    let premise = cmp(CompareOp::Eq, lhs, rhs);
    let goal = implies(premise, cmp(CompareOp::Ge, q(), rlit(0)));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished,
        "without a,b >= 0 the divisor sign is unknown; must fail closed"
    );
}

#[test]
fn does_not_prove_strict_goal_from_nonneg_numerator() {
    // a >= 0 && b >= 0 && a*a + b*b == (a*b+1)*q ==> q > 0 is FALSE
    // (take a=b=0 => q=0, not > 0). Strict goal must not be proven by the
    // non-strict numerator certificate.
    let a = || rvar("a");
    let b = || rvar("b");
    let q = || rvar("q");
    let h1 = cmp(CompareOp::Ge, a(), rlit(0));
    let h2 = cmp(CompareOp::Ge, b(), rlit(0));
    let lhs = add(mul(a(), a()), mul(b(), b()));
    let rhs = mul(add(mul(a(), b()), rlit(1)), q());
    let h3 = cmp(CompareOp::Eq, lhs, rhs);
    let premise = and(and(h1, h2), h3);
    let goal = implies(premise, cmp(CompareOp::Gt, q(), rlit(0)));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished,
        "strict q > 0 is false at a=b=0; must fail closed"
    );
}

#[test]
fn does_not_prove_division_with_indefinite_numerator() {
    // a >= 0 && b >= 0 && (a*b + 1)*q == a - b ==> q >= 0 is FALSE
    // (a=0, b=1 => q = -1). The divisor a*b+1 > 0 is provable, but the
    // numerator `a - b` is NOT provably non-negative, so the division rule
    // must NOT fire. Fail-closed.
    let a = || rvar("a");
    let b = || rvar("b");
    let q = || rvar("q");
    let h1 = cmp(CompareOp::Ge, a(), rlit(0));
    let h2 = cmp(CompareOp::Ge, b(), rlit(0));
    let lhs = mul(add(mul(a(), b()), rlit(1)), q());
    let rhs = arith(ArithOp::Sub, a(), b());
    let h3 = cmp(CompareOp::Eq, lhs, rhs);
    let premise = and(and(h1, h2), h3);
    let goal = implies(premise, cmp(CompareOp::Ge, q(), rlit(0)));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished,
        "indefinite numerator a - b must not be certified non-negative"
    );
}

#[test]
fn does_not_prove_non_real_typed_expr() {
    // Integer-typed variables are outside the real fragment: fall through.
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::MathInt,
    };
    let goal = cmp(
        CompareOp::Ge,
        TrustVcExpr::Arith {
            op: ArithOp::Mul,
            left: Box::new(x.clone()),
            right: Box::new(x.clone()),
            ty: TrustVcType::MathInt,
        },
        TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::MathInt,
        },
    );
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished,
        "non-real typed expressions are out of fragment"
    );
}

#[test]
fn does_not_prove_unrelated_false_goal() {
    // a >= 0 ==> a <= 0   is FALSE (a can be positive). Must fail closed.
    let a = rvar("a");
    let premise = cmp(CompareOp::Ge, a.clone(), rlit(0));
    let goal = implies(premise, cmp(CompareOp::Le, a, rlit(0)));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::NotEstablished
    );
}

#[test]
fn handles_division_by_constant_in_polynomial() {
    // a >= 0 ==> a / 2 >= 0   (exact rational scaling). Provable.
    let a = rvar("a");
    let premise = cmp(CompareOp::Ge, a.clone(), rlit(0));
    let half_a = arith(ArithOp::Div, a, rlit(2));
    let goal = implies(premise, cmp(CompareOp::Ge, half_a, rlit(0)));
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::Proven,
        "a >= 0 ==> a/2 >= 0 (cone membership with rational multiplier)"
    );
}

#[test]
fn search_terminates_on_high_arity() {
    // Many hypotheses: the search must still terminate (bounded). We don't
    // require a particular verdict — just that the call returns.
    let mut premise = cmp(CompareOp::Ge, rvar("v0"), rlit(0));
    for i in 1..10 {
        premise = and(premise, cmp(CompareOp::Ge, rvar(&format!("v{i}")), rlit(0)));
    }
    let goal = implies(premise, cmp(CompareOp::Ge, rvar("v0"), rlit(0)));
    // v0 >= 0 ==> v0 >= 0 is trivially true and within the cone.
    assert_eq!(
        try_prove_nonlinear_real(&goal),
        NonlinearRealOutcome::Proven
    );
}

// ---------------------------------------------------------------------------
// Default-prover boundary detector (`unhinted_nonlinear_real_construct`):
// the Verus `smt.arith.nl=false` analog. Positive cases must be detected so
// the hint-free path refuses them; linear shapes must pass through.
// ---------------------------------------------------------------------------

fn ivar(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Int { width: 32 },
    }
}

fn imul(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Mul,
        left: Box::new(l),
        right: Box::new(r),
        ty: TrustVcType::Int { width: 32 },
    }
}

/// The exact upstream `real_nonlinear2` goal shape must be detected: it
/// contains `a*a`, `b*b`, `a*b`, and `(a*b + 1)*q` — all products of
/// non-constant real terms.
#[test]
fn boundary_detects_real_nonlinear2_goal_shape() {
    let premise = and(
        and(
            cmp(CompareOp::Ge, rvar("a"), rlit(0)),
            cmp(CompareOp::Ge, rvar("b"), rlit(0)),
        ),
        cmp(
            CompareOp::Eq,
            add(mul(rvar("a"), rvar("a")), mul(rvar("b"), rvar("b"))),
            mul(add(mul(rvar("a"), rvar("b")), rlit(1)), rvar("q")),
        ),
    );
    let goal = implies(premise, cmp(CompareOp::Ge, rvar("q"), rlit(0)));
    assert_eq!(
        unhinted_nonlinear_real_construct(&goal),
        Some("a product of two non-constant real-typed terms")
    );
}

/// A constant-scaled real term (`2 * x`) is linear and must NOT be detected.
#[test]
fn boundary_allows_constant_scaled_real_terms() {
    let goal = cmp(CompareOp::Ge, mul(rlit(2), rvar("x")), rlit(0));
    assert_eq!(unhinted_nonlinear_real_construct(&goal), None);
    // Symmetric operand order.
    let goal = cmp(CompareOp::Ge, mul(rvar("x"), rlit(2)), rlit(0));
    assert_eq!(unhinted_nonlinear_real_construct(&goal), None);
    // Folded constant factor: `(2 + 3) * x`.
    let goal = cmp(
        CompareOp::Ge,
        mul(add(rlit(2), rlit(3)), rvar("x")),
        rlit(0),
    );
    assert_eq!(unhinted_nonlinear_real_construct(&goal), None);
}

/// Division by a CONSTANT real divisor (upstream `real_basics`: `x / 2.0`,
/// `x / 3.0`) is linear and must NOT be detected; division by a non-constant
/// divisor is nonlinear and must be refused.
#[test]
fn boundary_division_constant_vs_symbolic_divisor() {
    let by_const = cmp(
        CompareOp::Gt,
        arith(ArithOp::Div, rvar("x"), rlit(3)),
        rlit(0),
    );
    assert_eq!(unhinted_nonlinear_real_construct(&by_const), None);

    let by_var = cmp(
        CompareOp::Gt,
        arith(ArithOp::Div, rvar("x"), rvar("y")),
        rlit(0),
    );
    assert_eq!(
        unhinted_nonlinear_real_construct(&by_var),
        Some("a division by a non-constant real-typed divisor")
    );
}

/// INT products are outside this boundary (the int side has its own
/// Verus-parity story; no ported corpus divergence exists there today).
#[test]
fn boundary_ignores_integer_products() {
    let goal = cmp(CompareOp::Ge, imul(ivar("x"), ivar("x")), ivar("y"));
    assert_eq!(unhinted_nonlinear_real_construct(&goal), None);
}

/// Products buried under logic/negation/ITE still get found (whole-tree walk).
#[test]
fn boundary_walks_nested_expressions() {
    let nested = TrustVcExpr::Not(Box::new(and(
        cmp(CompareOp::Ge, rvar("a"), rlit(0)),
        cmp(CompareOp::Eq, mul(rvar("a"), rvar("q")), rlit(1)),
    )));
    assert_eq!(
        unhinted_nonlinear_real_construct(&nested),
        Some("a product of two non-constant real-typed terms")
    );
}
