//! End-to-end quantifier division overflow tests (#1988, #1852) and
//! per-expression wrapping width tests (#2036).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from int_mode_div_rem_overflow.rs (#2145).

use super::*;

// ========================================================================
// End-to-end quantifier division overflow tests (#1988)
// ========================================================================

/// DISCRIMINATING: Division inside a quantifier body should verify when safe.
///
/// forall(|x: i32| !(x > 0 && x < 100) || x / 2 > 0)
/// All values in (0, 100) have x / 2 >= 0, and since x > 0, x / 2 >= 1 > 0
/// for x >= 2. For x == 1, 1 / 2 == 0 which is NOT > 0.
/// Use x >= 2 to make it valid.
#[test]
fn test_int_mode_div_safe_in_quantifier_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 1"));
    // Safe division: x >= 2 and x < 100 ensures x / 2 >= 1 > 0
    ctx.push_obligation(ProofObligation::assert(
        "safe_div",
        "forall(|x: i32| !(x >= 2 && x < 100) || x / 2 > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Safe division in quantifier verifies (no overflow possible).
    expect_verified(
        &result,
        "Safe division in quantifier should not error (#1988)",
    );
}

/// Overflow predicates inside forall bodies are suppressed (#2557) because
/// they reference bound variables that leak to the outer assertion scope.
///
/// forall(|x: i32, y: i32| !(y != 0) || x / y == x / y)
/// This is tautological. Without the overflow predicate scope leak fix,
/// the signed MIN/-1 overflow guard would constrain x,y globally, causing
/// false counterexamples. With the fix, the tautology correctly verifies.
///
/// Future work: Verus-style body precondition encoding for quantifier-body
/// overflow checks (e.g., forall |x,y| !overflow(x/y) ==> ...).
#[test]
fn test_int_mode_signed_div_min_neg1_in_quantifier_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("z_val", "z == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "div_in_forall",
        "forall(|x: i32, y: i32| !(y != 0) || x / y == x / y)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Modular wrapping inside quantifier bodies creates NIA terms. The solver
    // may find a genuine BV-semantics counterexample or return Unknown(incomplete).
    // Both are sound non-Verified results. Part of #2557, #2668.
    expect_fail_closed(
        &result,
        "#2668: overflow in quantifier body correctly detected or solver inconclusive",
    );
}

// ========================================================================
// Int-mode div-by-zero in quantifiers (#1852)
// ========================================================================

/// Division by unconstrained variable in quantifier body (#2557, #2701).
///
/// forall(|x: u32, y: u32| x / y <= x)
/// True for y >= 1 (unsigned integer division of x by y >= 1 yields <= x).
/// But y is unconstrained and could be 0. In SMT-LIB semantics, (div x 0) is
/// an unspecified total function value — the solver may find a model where
/// (div x 0) > x, producing a counterexample, or return Unknown(incomplete).
/// Either is a sound non-Verified result.
///
/// Replaces the previous tautological formula `x / y == x / y` (#2701) which
/// had identical TermIds on both sides, causing eq(t,t) → true at term
/// construction level.
#[test]
fn test_int_mode_div_by_zero_unconstrained_in_quantifier_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("z_val", "z == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "div_zero_forall",
        "forall(|x: u32, y: u32| x / y <= x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Div-by-zero IS possible (y unconstrained). The property x / y <= x
    // is unprovable when y = 0 because (div x 0) is unspecified in SMT.
    // Solver correctly detects it or returns Unknown(incomplete).
    expect_fail_closed(
        &result,
        "#2701: div-by-zero in quantifier body — x / y <= x unprovable with y unconstrained",
    );
}

/// Remainder by unconstrained variable in quantifier body (#2557, #2701).
///
/// forall(|x: u32, y: u32| x % y <= x)
/// True for y >= 1 (unsigned remainder of x by y >= 1 is in [0, y-1], hence
/// <= x). But y is unconstrained and could be 0. In SMT-LIB semantics,
/// (mod x 0) is an unspecified total function value — the solver may find a
/// model where (mod x 0) > x, producing a counterexample, or return
/// Unknown(incomplete). Either is a sound non-Verified result.
///
/// Replaces the previous tautological formula `x % y == x % y` (#2701) which
/// had identical TermIds on both sides.
#[test]
fn test_int_mode_rem_by_zero_unconstrained_in_quantifier_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("z_val", "z == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "rem_zero_forall",
        "forall(|x: u32, y: u32| x % y <= x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Rem-by-zero IS possible (y unconstrained). The property x % y <= x
    // is unprovable when y = 0 because (mod x 0) is unspecified in SMT.
    // Solver correctly detects it or returns Unknown(incomplete).
    expect_fail_closed(
        &result,
        "#2701: rem-by-zero in quantifier body — x % y <= x unprovable with y unconstrained",
    );
}

/// DISCRIMINATING: Division by nonzero-constrained variable inside a
/// quantifier with overflow checks SHOULD verify.
///
/// forall(|x: u32, y: u32| !(y > 0) || x / y == x / y)
/// The guard `y > 0` excludes zero. The "division by zero" overflow check
/// (y != 0) is guarded by the implication: ¬(y > 0) ∨ (y != 0), which is
/// trivially true. Body is tautological, so the assertion verifies.
///
/// This test discriminates against an overly-conservative implementation
/// that rejects ALL variable divisors in int-mode even when constrained.
/// Uses u32 to avoid signed MIN/-1 complications.
#[test]
fn test_int_mode_div_nonzero_constrained_in_quantifier_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("z_val", "z == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "safe_div_forall",
        "forall(|x: u32, y: u32| !(y > 0) || x / y == x / y)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Division by nonzero-constrained y in quantifier should verify (#1852)",
    );
}

// ========================================================================
// Per-expression wrapping width tests (#2036)
// ========================================================================

/// Regression test for #2036: encode_int_arith uses per-expression type for
/// wrapping instead of a broader quantifier scope context.
///
/// `TrustVcExpr::Arith { ty: Uint { width: 32 }, .. }` should wrap at 2^32
/// even when an outer quantifier scope has u8 width/sign information.
#[test]
fn test_encode_int_arith_uses_per_expression_type_for_wrapping() {
    use crate::ir::{ArithOp, TrustVcType};
    use crate::ir_expr::TrustVcExpr;

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let mut parser = make_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Simulate a quantifier scope where bound vars are u8.
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[("i".to_string(), TrustVcType::Uint { width: 8 })]);

    // Declare a u32 variable in local scope
    let j_term = parser.solver.declare_const("j", ay_dpll::api::Sort::Int);
    parser.local_vars.insert("j".to_string(), j_term);
    parser
        .local_var_types
        .insert("j".to_string(), TrustVcType::Uint { width: 32 });

    // Encode: j + 200 with result type u32
    let j_expr = TrustVcExpr::Var {
        name: "j".to_string(),
        ty: TrustVcType::Uint { width: 32 },
    };
    let lit_200 = TrustVcExpr::IntLit {
        value: 200,
        ty: TrustVcType::Uint { width: 32 },
    };
    let arith_expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(j_expr),
        right: Box::new(lit_200),
        ty: TrustVcType::Uint { width: 32 },
    };

    // Encode the arithmetic — should use u32 wrapping (2^32), NOT u8 (2^8)
    let result_term = parser
        .encode_trust_vc_expr(&arith_expr)
        .expect("encode_arith should succeed");

    // If wrapping uses u32 (correct): 200 + 200 = 400 (no wrap)
    // If wrapping uses u8 (wrong):    200 + 200 = 400 mod 256 = 144
    let j_val = parser.solver.int_const(200);
    let eq_j = parser.solver.try_eq(j_term, j_val).unwrap();
    parser.solver.try_assert_term(eq_j).unwrap();

    // Assert result == 400 (correct u32 wrapping)
    let expected = parser.solver.int_const(400);
    let eq_400 = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq_400).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "j + 200 with j=200 should equal 400 under u32 wrapping (not 144 under u8 wrapping) (#2036)"
    );
}

/// Regression: overflow check uses per-expression width (#2036).
///
/// With an outer u8 quantifier scope but expression type u32, the overflow
/// check for `j + 200` at j=200 should NOT fire (400 < 2^32), but would
/// fire incorrectly under u8 wrapping (400 > 255).
#[test]
fn test_encode_int_arith_overflow_check_uses_per_expression_type() {
    use crate::ir::{ArithOp, TrustVcType};
    use crate::ir_expr::TrustVcExpr;

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Simulate a quantifier scope where bound vars are u8.
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[("i".to_string(), TrustVcType::Uint { width: 8 })]);

    // Declare a u32 variable in local scope
    let j_term = parser.solver.declare_const("j", ay_dpll::api::Sort::Int);
    parser.local_vars.insert("j".to_string(), j_term);
    parser
        .local_var_types
        .insert("j".to_string(), TrustVcType::Uint { width: 32 });

    // Encode: j + 200 with result type u32
    let j_expr = TrustVcExpr::Var {
        name: "j".to_string(),
        ty: TrustVcType::Uint { width: 32 },
    };
    let lit_200 = TrustVcExpr::IntLit {
        value: 200,
        ty: TrustVcType::Uint { width: 32 },
    };
    let arith_expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(j_expr),
        right: Box::new(lit_200),
        ty: TrustVcType::Uint { width: 32 },
    };

    // Clear overflow checks and encode
    parser.overflow_checks.clear();
    let _result_term = parser
        .encode_trust_vc_expr(&arith_expr)
        .expect("encode_arith should succeed");

    // Set j = 200 (so j + 200 = 400, which fits in u32 but not u8)
    let j_val = parser.solver.int_const(200);
    let eq_j = parser.solver.try_eq(j_term, j_val).unwrap();
    parser.solver.try_assert_term(eq_j).unwrap();

    // Assert all overflow checks pass
    for (name, check) in &parser.overflow_checks {
        parser.solver.try_assert_term(*check).unwrap();
        assert_eq!(
            parser.solver.try_check_sat().unwrap(),
            SolveResult::Sat,
            "overflow check '{}' should pass at j=200 under u32 wrapping (#2036)",
            name
        );
    }
}
