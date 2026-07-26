//! Tests for real number arithmetic encoding (#2517).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{ArithOp, CompareOp, TrustVcExpr, TrustVcType};
use ay_dpll::api::{Logic, Solver, Sort, Term, TermKind};

/// Real addition: x + y == y + x (commutativity).
#[test]
fn test_real_addition_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assert("add_comm", "x + y == y + x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Real addition should be commutative");
}

/// Real subtraction: x - x == 0.
#[test]
fn test_real_subtraction_self_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assert("sub_self", "x - x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Real x - x should equal 0");
}

/// Real multiplication: x * 1 == x.
#[test]
fn test_real_multiplication_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assert("mul_id", "x * 1 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Real x * 1 should equal x");
}

/// Real division: exact (not truncating). x/2 != 0 when x == 1.
#[test]
fn test_real_division_exact() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assume("x_is_one", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("div_exact", "x / 2 != 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Real 1/2 should not equal 0 (exact division)");
}

/// Division by zero literal is rejected.
#[test]
fn test_real_division_by_zero_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assert("div_zero", "x / 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "division by zero should not verify");
}

/// Real comparison: x > 0 implies x + 1 > 1 (linear, decidable).
#[test]
fn test_real_comparison_linear() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("add_gt", "x + 1 > 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "For x > 0, x + 1 > 1 should hold in reals");
}

/// Upstream real_basics regression: x >= 0 is too weak to prove x / 3 > 0.
#[test]
fn test_real_nonnegative_division_strict_positive_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0"));
    ctx.push_obligation(ProofObligation::assert("div_strict_pos", "x / 3 > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "x = 0 should refute x / 3 > 0");
}

/// Real modulo is rejected.
#[test]
fn test_real_rem_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assert("rem_real", "x % y == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "real modulo should not verify");
}

/// Real negation: -x + x == 0.
#[test]
fn test_real_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
    ctx.push_obligation(ProofObligation::assert("neg_self", "-x + x == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-x + x should equal 0 for reals");
}

/// Decimal source literals lower to exact Real rationals, not binary floats.
#[test]
fn test_source_decimal_real_literal_exact() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("decimal_exact", "1.5 == 3.0 / 2.0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decimal real literals should be exact rationals");
}

/// Upstream real.rs `test_chained`: nat casts participate in real chained comparisons.
#[test]
fn test_source_real_chained_nat_cast_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Nat);
    ctx.push_obligation(ProofObligation::assert(
        "chained_nat_real",
        "0 <= 0 < (n as real) + 1 < (n as real) + 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nat-to-real casts should verify inside chained real comparisons",
    );
}

/// Real → int casts use SMT floor semantics.
#[test]
fn test_source_real_floor_casts_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.declare_var_typed("y", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_lower", "x >= 2"));
    ctx.push_obligation(ProofObligation::assume("x_upper", "x < 3"));
    ctx.push_obligation(ProofObligation::assume("y_lower", "y >= -3"));
    ctx.push_obligation(ProofObligation::assume("y_upper", "y < -2"));
    ctx.push_obligation(ProofObligation::assert("positive_floor", "(x as int) == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "negative_floor",
        "(y as int) == -3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real to int casts should floor");
}

/// Verus-style real floor method lowers to the same floor semantics as `as int`.
#[test]
fn test_source_real_floor_method_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_lower", "x >= 1.5"));
    ctx.push_obligation(ProofObligation::assume("x_upper", "x < 2.0"));
    ctx.push_obligation(ProofObligation::assert("floor_method", "x.floor() == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real floor method should floor to int");
}

/// DISCRIMINATING: real → int casts must floor negative rationals.
#[test]
fn test_source_real_floor_cast_wrong_negative_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("y_lower", "y >= -3"));
    ctx.push_obligation(ProofObligation::assume("y_upper", "y < -2"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_negative_floor",
        "(y as int) == -2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "negative real floor should be -3, not -2");
}

/// Upstream real.rs `archimedean_nat`: `floor(x) as nat` is a witness above x.
/// Latest ay proves this mixed Int/Real floor witness directly.
#[test]
fn test_source_real_archimedean_nat_floor_witness_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "archimedean_floor_nat_witness",
        "x < (((x.floor() as nat) + 1) as real)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "archimedean_nat floor witness");
}

/// DISCRIMINATING: casting a negative floor to nat must fail closed.
#[test]
fn test_source_real_archimedean_nat_negative_floor_cast_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_below_zero", "x < 0.0"));
    ctx.push_obligation(ProofObligation::assume("x_above_minus_one", "x >= -0.5"));
    ctx.push_obligation(ProofObligation::assert(
        "negative_floor_to_nat",
        "((x.floor() as nat) + 1) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "negative real floor is not a valid nat cast");
}

/// LOAD-BEARING: the archimedean witness depends on the `x >= 0` hypothesis;
/// without it the nat cast of a possibly-negative floor is unconstrained, so
/// the witness must NOT verify. This proves the verifying form above is not
/// vacuous — the floor bracket alone is insufficient without nonnegativity.
#[test]
fn test_source_real_archimedean_nat_witness_requires_nonnegative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    // NB: no `x >= 0.0` assumption.
    ctx.push_obligation(ProofObligation::assert(
        "archimedean_floor_nat_witness_unconstrained",
        "x < (((x.floor() as nat) + 1) as real)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "archimedean witness must not verify without the x >= 0 hypothesis",
    );
}

/// SOUNDNESS GUARD: the floor lower bracket `floor(x) <= x` is a real fact and
/// must verify (for nonnegative x the as-nat round-trip preserves the value).
#[test]
fn test_source_real_floor_lower_bracket_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "floor_lower_bracket",
        "((x.floor() as nat) as real) <= x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "floor(x) <= x lower bracket");
}

/// SOUNDNESS GUARD (FALSE floor fact): claiming `x < floor(x)` inverts the
/// floor bracket and must fail closed — never verify. This is the explicit
/// "a FALSE floor fact still fails closed" guard for the floor encoding.
#[test]
fn test_source_real_false_floor_fact_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "false_floor_strict_lower",
        "x < ((x.floor() as nat) as real)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x < floor(x) is false (floor bracket); must fail closed",
    );
}

/// SOUNDNESS GUARD (FALSE upper-bracket fact): claiming `floor(x) + 1 <= x`
/// contradicts the strict floor upper bracket `x < floor(x) + 1` and must fail
/// closed. Guards the upper half of the floor bracket the witness relies on.
#[test]
fn test_source_real_false_floor_upper_bracket_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "false_floor_upper",
        "(((x.floor() as nat) + 1) as real) <= x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "floor(x) + 1 <= x is false (floor bracket); must fail closed",
    );
}

/// ADVERSARIAL (no false Verified): the floor lower bracket is `floor(x) <= x`,
/// NOT `floor(x) <= x - 1`. The stronger claim is false (it fails when x is an
/// integer, where floor(x) == x) and must never verify.
#[test]
fn test_source_real_floor_lower_bracket_minus_one_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "floor_lower_minus_one",
        "((x.floor() as nat) as real) <= x - 1.0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "floor(x) <= x - 1 is false (e.g. x integer); must not verify",
    );
}

/// ADVERSARIAL (no false Verified): the floor upper bracket is the STRICT
/// `x < floor(x) + 1`. Dropping the `+ 1` to claim `x < floor(x)` inverts the
/// lower bracket and must never verify.
#[test]
fn test_source_real_floor_strict_without_plus_one_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_nonnegative", "x >= 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "floor_strict_no_plus_one",
        "x < ((x.floor() as nat) as real)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x < floor(x) (missing + 1) is false; must not verify",
    );
}

/// ADVERSARIAL (negative floor handled correctly): the floor brackets restated
/// on the nat-cast result are guarded by `x >= 0`. With `x < 0` the as-nat cast
/// is an unconstrained fail-closed value, so the lower-bracket shape that
/// verifies for nonnegative x must NOT verify here.
#[test]
fn test_source_real_floor_lower_bracket_negative_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Real);
    ctx.push_obligation(ProofObligation::assume("x_negative", "x < 0.0"));
    ctx.push_obligation(ProofObligation::assert(
        "floor_lower_negative",
        "((x.floor() as nat) as real) <= x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "negative-x floor lower bracket relies on an unconstrained nat cast; must not verify",
    );
}

fn float_var(name: &str, width: u32) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Float { width },
    }
}

fn int_var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

fn encode_finite_int_to_real_bv(
    from_ty: TrustVcType,
    width: u32,
    signed: bool,
) -> (Solver, Term, Term) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(width));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), from_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.use_int_arithmetic = false;
    parser.term_widths.insert(x, (width, signed));

    let expr = TrustVcExpr::Cast {
        expr: Box::new(int_var("x", from_ty.clone())),
        from_ty,
        to_ty: TrustVcType::Real,
    };
    let cast = parser
        .encode_trust_vc_expr(&expr)
        .expect("finite integer as real should encode");
    assert_eq!(parser.solver.term_sort(cast), Sort::Real);
    drop(parser);

    (solver, x, cast)
}

fn assert_bv_as_real_encodes(from_ty: TrustVcType, width: u32, signed: bool, label: &str) {
    let (solver, _x, cast) = encode_finite_int_to_real_bv(from_ty, width, signed);

    assert_eq!(solver.term_sort(cast), Sort::Real, "{label}");
    assert_eq!(
        solver.term_kind(cast),
        TermKind::App {
            name: "to_real".to_string(),
            num_args: 1,
        },
        "{label}"
    );
}

/// BV-mode u8 -> real casts preserve the unsigned value through Int-to-Real.
#[test]
fn test_ir_u8_cast_to_real_preserves_unsigned_value() {
    assert_bv_as_real_encodes(
        TrustVcType::Uint { width: 8 },
        8,
        false,
        "u8 as real should encode as Int-to-Real",
    );
}

/// BV-mode i8 -> real casts sign-interpret the BV before Int-to-Real.
#[test]
fn test_ir_i8_cast_to_real_preserves_signed_value() {
    assert_bv_as_real_encodes(
        TrustVcType::Int { width: 8 },
        8,
        true,
        "i8 as real should encode as signed Int-to-Real",
    );
}

/// IR float arithmetic must lower to native `fp.*` terms, not Int/Real/BV ops.
#[test]
fn test_ir_float_arith_emits_fp_ops() {
    let width = 32;
    let float_ty = TrustVcType::Float { width };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    let y = solver.declare_const("y", Sort::FloatingPoint(8, 24));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), float_ty.clone());
    var_types.insert("y".to_string(), float_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    for (op, expected_name, expected_args) in [
        (ArithOp::Add, "fp.add", 3usize),
        (ArithOp::Sub, "fp.sub", 3),
        (ArithOp::Mul, "fp.mul", 3),
        (ArithOp::Div, "fp.div", 3),
        (ArithOp::Rem, "fp.rem", 2),
    ] {
        let expr = TrustVcExpr::Arith {
            op,
            left: Box::new(float_var("x", width)),
            right: Box::new(float_var("y", width)),
            ty: float_ty.clone(),
        };
        let term = parser
            .encode_trust_vc_expr(&expr)
            .expect("float arithmetic should encode");
        assert_eq!(parser.solver.term_sort(term), Sort::FloatingPoint(8, 24));
        assert_eq!(
            parser.solver.term_kind(term),
            TermKind::App {
                name: expected_name.to_string(),
                num_args: expected_args,
            }
        );
    }
}

/// Float comparisons and unary negation must use native FP operators.
#[test]
fn test_ir_float_compare_and_neg_emit_fp_ops() {
    let width = 64;
    let float_ty = TrustVcType::Float { width };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));
    let y = solver.declare_const("y", Sort::FloatingPoint(11, 53));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), float_ty.clone());
    var_types.insert("y".to_string(), float_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    for (op, expected_name) in [
        (CompareOp::Eq, "fp.eq"),
        (CompareOp::Lt, "fp.lt"),
        (CompareOp::Le, "fp.leq"),
        (CompareOp::Gt, "fp.gt"),
        (CompareOp::Ge, "fp.geq"),
    ] {
        let expr = TrustVcExpr::Compare {
            op,
            left: Box::new(float_var("x", width)),
            right: Box::new(float_var("y", width)),
        };
        let term = parser
            .encode_trust_vc_expr(&expr)
            .expect("float comparison should encode");
        assert_eq!(parser.solver.term_sort(term), Sort::Bool);
        assert_eq!(
            parser.solver.term_kind(term),
            TermKind::App {
                name: expected_name.to_string(),
                num_args: 2,
            }
        );
    }

    let neg = parser
        .encode_trust_vc_expr(&TrustVcExpr::Neg(Box::new(float_var("x", width))))
        .expect("float negation should encode");
    assert_eq!(parser.solver.term_sort(neg), Sort::FloatingPoint(11, 53));
    assert_eq!(
        parser.solver.term_kind(neg),
        TermKind::App {
            name: "fp.neg".to_string(),
            num_args: 1,
        }
    );
}

/// TrustVcType::Real parses from "real" and round-trips.
#[test]
fn test_real_type_parsing() {
    let ty = crate::ir::TrustVcType::from_str("real").unwrap();
    assert_eq!(ty, crate::ir::TrustVcType::Real);
    assert_eq!(ty.to_type_string(), "real");
    assert!(!ty.contains_float());
    assert!(ty.bit_width().is_none());
    assert!(!ty.is_unsigned());
}

/// TrustVcType::Float parses from "f32"/"f64" and round-trips.
#[test]
fn test_float_type_parsing() {
    let f32_ty = crate::ir::TrustVcType::from_str("f32").unwrap();
    assert!(matches!(
        f32_ty,
        crate::ir::TrustVcType::Float { width: 32 }
    ));
    assert_eq!(f32_ty.to_type_string(), "f32");
    assert!(f32_ty.contains_float());

    let f64_ty = crate::ir::TrustVcType::from_str("f64").unwrap();
    assert!(matches!(
        f64_ty,
        crate::ir::TrustVcType::Float { width: 64 }
    ));
    assert_eq!(f64_ty.to_type_string(), "f64");
    assert!(f64_ty.contains_float());
}

// === Float cast encoding tests (Part of #2680 Slice 1) ===

/// Float→Float cast: f32 as f64 produces FloatingPoint(11,53) via to_fp.
#[test]
fn test_ir_float_cast_f32_to_f64_sort() {
    let f32_ty = TrustVcType::Float { width: 32 };
    let f64_ty = TrustVcType::Float { width: 64 };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), f32_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = TrustVcExpr::Cast {
        expr: Box::new(float_var("x", 32)),
        from_ty: f32_ty,
        to_ty: f64_ty,
    };
    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("f32 as f64 cast should encode");
    assert_eq!(
        parser.solver.term_sort(term),
        Sort::FloatingPoint(11, 53),
        "f32 as f64 should produce FloatingPoint(11, 53)"
    );
}

/// Float→Float cast: f64 as f32 produces FloatingPoint(8,24) (narrowing).
#[test]
fn test_ir_float_cast_f64_to_f32_sort() {
    let f64_ty = TrustVcType::Float { width: 64 };
    let f32_ty = TrustVcType::Float { width: 32 };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), f64_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = TrustVcExpr::Cast {
        expr: Box::new(float_var("x", 64)),
        from_ty: f64_ty,
        to_ty: f32_ty,
    };
    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("f64 as f32 cast should encode");
    assert_eq!(
        parser.solver.term_sort(term),
        Sort::FloatingPoint(8, 24),
        "f64 as f32 should produce FloatingPoint(8, 24)"
    );
}

/// Float→Int cast: f64 as i32 produces BV(32) via fp_to_sbv with RTZ.
#[test]
fn test_ir_float_cast_f64_to_i32_sort() {
    let f64_ty = TrustVcType::Float { width: 64 };
    let i32_ty = TrustVcType::Int { width: 32 };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), f64_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = TrustVcExpr::Cast {
        expr: Box::new(float_var("x", 64)),
        from_ty: f64_ty,
        to_ty: i32_ty,
    };
    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("f64 as i32 cast should encode");
    assert_eq!(
        parser.solver.term_sort(term),
        Sort::bitvec(32),
        "f64 as i32 should produce BV(32)"
    );
}

/// Int→Float cast: u32 as f32 produces FloatingPoint(8,24) via bv_to_fp_unsigned.
#[test]
fn test_ir_int_cast_u32_to_f32_sort() {
    let u32_ty = TrustVcType::Uint { width: 32 };
    let f32_ty = TrustVcType::Float { width: 32 };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), u32_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = TrustVcExpr::Cast {
        expr: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u32_ty.clone(),
        }),
        from_ty: u32_ty,
        to_ty: f32_ty,
    };
    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 as f32 cast should encode");
    assert_eq!(
        parser.solver.term_sort(term),
        Sort::FloatingPoint(8, 24),
        "u32 as f32 should produce FloatingPoint(8, 24)"
    );
}

/// Float→Real cast: f64 as real produces Sort::Real via fp_to_real.
#[test]
fn test_ir_float_cast_f64_to_real_sort() {
    let f64_ty = TrustVcType::Float { width: 64 };
    let real_ty = TrustVcType::Real;

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::FloatingPoint(11, 53));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), f64_ty.clone());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = TrustVcExpr::Cast {
        expr: Box::new(float_var("x", 64)),
        from_ty: f64_ty,
        to_ty: real_ty,
    };
    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("f64 as real cast should encode");
    assert_eq!(
        parser.solver.term_sort(term),
        Sort::Real,
        "f64 as real should produce Sort::Real"
    );
}
