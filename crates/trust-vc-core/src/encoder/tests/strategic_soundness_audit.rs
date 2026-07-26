//! Strategic soundness audit tests — critical implicit invariant verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests discovered during Prover strategic audit (P1-435+). Each test
//! targets a specific implicit invariant in the encoder or verification
//! pipeline that, if violated, could produce unsound verification results.
//!
//! Test categories:
//! - `references_collection` gaps that affect confirmation check gating
//! - Wrapping arithmetic correctness at extreme boundaries
//! - Overflow guard silent failure documentation

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::{CollectionOp, CompareOp, QuantifierKind, TrustVcExpr};

// ========================================================================
// references_collection — confirmation check gating (#2295 fixed)
//
// The confirmation check (#2241) verifies collection-assertion results with
// a fresh encoder to catch ay-dpll non-determinism. It is gated by
// `references_collection()`. After #2295, this checks CollectionOp, Index,
// Var with collection type, and FnCall with collection return type.
// ========================================================================

fn seq_i32_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
}

fn set_i32_ty() -> TrustVcType {
    TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
}

fn map_i32_i32_ty() -> TrustVcType {
    TrustVcType::Map(
        Box::new(TrustVcType::Int { width: 32 }),
        Box::new(TrustVcType::Int { width: 32 }),
    )
}

/// DISCRIMINATING: Seq-typed variables are visible to `references_collection`.
///
/// A `Compare { Var(s: Seq<i32>), Var(t: Seq<i32>) }` expression returns
/// `true` because `Var` checks `ty.is_collection()`. Fixes #2295.
#[test]
fn test_references_collection_seq_vars_visible() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "s".into(),
            ty: seq_i32_ty(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "t".into(),
            ty: seq_i32_ty(),
        }),
    };

    assert!(
        expr.references_collection(),
        "Seq<i32> variables must be visible — confirmation check fires. Fixes #2295."
    );
}

/// DISCRIMINATING: Set-typed variables are visible to `references_collection`. Fixes #2295.
#[test]
fn test_references_collection_set_vars_visible() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "a".into(),
            ty: set_i32_ty(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "b".into(),
            ty: set_i32_ty(),
        }),
    };

    assert!(
        expr.references_collection(),
        "Set<i32> variables must be visible. Fixes #2295."
    );
}

/// DISCRIMINATING: Map-typed variables are visible to `references_collection`. Fixes #2295.
#[test]
fn test_references_collection_map_vars_visible() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "m1".into(),
            ty: map_i32_i32_ty(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "m2".into(),
            ty: map_i32_i32_ty(),
        }),
    };

    assert!(
        expr.references_collection(),
        "Map<i32,i32> variables must be visible. Fixes #2295."
    );
}

/// DISCRIMINATING: FnCall returning Seq with non-collection args is now visible.
///
/// `references_collection` checks `return_ty.is_collection()` in addition to
/// args. Fixes #2295.
#[test]
fn test_references_collection_fncall_returning_seq_visible() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::FnCall {
            name: "make_seq".into(),
            args: vec![TrustVcExpr::IntLit {
                value: 42,
                ty: i32_ty(),
            }],
            return_ty: seq_i32_ty(),
        }),
        right: Box::new(TrustVcExpr::FnCall {
            name: "make_seq".into(),
            args: vec![TrustVcExpr::IntLit {
                value: 43,
                ty: i32_ty(),
            }],
            return_ty: seq_i32_ty(),
        }),
    };

    assert!(
        expr.references_collection(),
        "FnCall with Seq<i32> return_ty must be visible. Fixes #2295."
    );
}

/// CONTROL: FnCall with collection arg IS visible to references_collection.
#[test]
fn test_references_collection_fncall_with_collection_arg_visible() {
    let expr = TrustVcExpr::FnCall {
        name: "process".into(),
        args: vec![TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".into(),
                ty: seq_i32_ty(),
            }),
            receiver_name: Some("s".into()),
            args: vec![],
            ty: TrustVcType::Uint { width: 64 },
        }],
        return_ty: i32_ty(),
    };

    assert!(
        expr.references_collection(),
        "FnCall with CollectionOp in args should be visible"
    );
}

/// DISCRIMINATING: Quantifier over collection-typed bound variable is visible.
///
/// `forall |s: Seq<i32>| f(s) > 0` — the FnCall arg is a `Var` with
/// `Seq<i32>` type, which `Var` now detects via `ty.is_collection()`.
/// Fixes #2295.
#[test]
fn test_references_collection_quantifier_seq_bound_var_fncall_visible() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("s".to_string(), seq_i32_ty())],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::FnCall {
                name: "seq_sum".into(),
                args: vec![TrustVcExpr::Var {
                    name: "s".into(),
                    ty: seq_i32_ty(),
                }],
                return_ty: i32_ty(),
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: i32_ty(),
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    assert!(
        expr.references_collection(),
        "Quantifier with Seq-typed Var arg must be visible. Fixes #2295."
    );
}

// ========================================================================
// Wrapping arithmetic correctness at 128-bit boundaries
//
// The `wrap_int_to_explicit_range` formula is correct for all widths
// (uses BigInt shift). These tests verify correctness at i128/u128
// boundaries where native arithmetic would overflow.
// ========================================================================

/// DISCRIMINATING: u128 wrapping at MAX boundary.
///
/// u128::MAX + 1 must wrap to 0. If the modulus computation (2^128) were
/// done with native u128, it would overflow to 0, producing `x mod 0`
/// (undefined). The BigInt path must handle this correctly.
#[test]
fn test_wrap_int_u128_max_plus_one_wraps_to_zero() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let wrapped;
    let zero;
    {
        let mut parser = AstExpressionParser::new(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        // u128::MAX = 2^128 - 1; u128::MAX + 1 = 2^128
        // We use the BigInt constant directly since i64 can't hold 2^128.
        let two_128 = num_bigint::BigInt::from(1u128) << 128;
        let val_term = parser.solver.int_const_bigint(&two_128);
        wrapped = parser
            .wrap_int_to_explicit_range(val_term, 128, true)
            .expect("u128 wrapping should succeed");
        zero = parser.solver.int_const(0);
    }
    let neq = solver.try_neq(wrapped, zero).unwrap();
    solver.try_assert_term(neq).unwrap();
    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "2^128 mod 2^128 must equal 0 (u128 wrapping)"
    );
}

/// DISCRIMINATING: i128 wrapping at MAX boundary.
///
/// i128::MAX + 1 = 2^127 must wrap to i128::MIN = -2^127.
/// Tests the signed wrapping formula: ((x + 2^127) mod 2^128) - 2^127.
#[test]
fn test_wrap_int_i128_max_plus_one_wraps_to_min() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let wrapped;
    let expected;
    {
        let mut parser = AstExpressionParser::new(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        // i128::MAX + 1 = 2^127
        let two_127 = num_bigint::BigInt::from(1u128) << 127;
        let val_term = parser.solver.int_const_bigint(&two_127);
        wrapped = parser
            .wrap_int_to_explicit_range(val_term, 128, false)
            .expect("i128 wrapping should succeed");
        // Expected: -2^127
        let two_127: num_bigint::BigInt = num_bigint::BigInt::from(1u128) << 127;
        let neg_two_127 = -two_127;
        expected = parser.solver.int_const_bigint(&neg_two_127);
    }
    let neq = solver.try_neq(wrapped, expected).unwrap();
    solver.try_assert_term(neq).unwrap();
    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "i128::MAX + 1 must wrap to i128::MIN"
    );
}

/// DISCRIMINATING: i128 wrapping at MIN boundary.
///
/// i128::MIN - 1 = -(2^127) - 1 must wrap to i128::MAX = 2^127 - 1.
#[test]
fn test_wrap_int_i128_min_minus_one_wraps_to_max() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let wrapped;
    let expected;
    {
        let mut parser = AstExpressionParser::new(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        // i128::MIN - 1 = -(2^127) - 1
        let two_127: num_bigint::BigInt = num_bigint::BigInt::from(1u128) << 127;
        let neg_two_127_minus_1 = -two_127 - 1;
        let val_term = parser.solver.int_const_bigint(&neg_two_127_minus_1);
        wrapped = parser
            .wrap_int_to_explicit_range(val_term, 128, false)
            .expect("i128 wrapping should succeed");
        // Expected: 2^127 - 1 = i128::MAX
        let two_127_minus_1 = (num_bigint::BigInt::from(1u128) << 127) - 1;
        expected = parser.solver.int_const_bigint(&two_127_minus_1);
    }
    let neq = solver.try_neq(wrapped, expected).unwrap();
    solver.try_assert_term(neq).unwrap();
    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "i128::MIN - 1 must wrap to i128::MAX"
    );
}

// ========================================================================
// Shift overflow check width defaults (#2297)
//
// `check_shift_overflow` now requires an explicit `lhs_width: u32`
// parameter. Callers resolve the width from the IR expression type or
// `term_widths`, returning an error if neither source provides a width.
// The previous `unwrap_or(32)` default was removed in #2297.
// ========================================================================

/// DISCRIMINATING: u64 shift by 33 should verify (33 < 64).
///
/// If the shift bound incorrectly defaults to 32, this would fail because
/// 33 >= 32. With correct u64 metadata, 33 < 64 so the check passes.
/// This test confirms u64 metadata is present in the standard pipeline.
#[test]
fn test_u64_shift_by_33_verifies_with_correct_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "shifted",
        "(x << 33) == (x << 33)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u64 << 33 should verify — shift amount 33 < 64 is in range. If this fails, the shift width bound may have defaulted to 32");
}

/// CONTROL: u64 shift by 64 should NOT verify (64 >= 64).
#[test]
fn test_u64_shift_by_64_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "shifted",
        "(x << 64) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u64 << 64 must NOT verify — shift amount 64 >= width 64 is UB",
    );
}

/// DISCRIMINATING: u8 shift by 7 should verify (7 < 8).
///
/// Ensures small widths also use correct bounds (8, not 32).
#[test]
fn test_u8_shift_by_7_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "shifted",
        "(x << 7) == 128",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1u8 << 7 should be 128 and verify");
}

/// DISCRIMINATING: u8 shift by 8 should NOT verify (8 >= 8).
#[test]
fn test_u8_shift_by_8_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "shifted",
        "(x << 8) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u8 << 8 must NOT verify — shift amount 8 >= width 8 is UB",
    );
}

// ========================================================================
// Checked arithmetic signedness — guards for #1987 unwrap_or defaults
// ========================================================================

/// DISCRIMINATING: i32 checked_add detects signed overflow at MAX boundary.
/// If signedness were unsigned, the check would pass (2^31 < 2^32).
#[test]
fn test_checked_add_i32_overflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume(
        "x_max",
        "x == 2147483647",
    ));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "overflows",
        "x.checked_add(1) == -2147483648",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MAX.checked_add(1) should detect signed overflow",
    );
}

/// DISCRIMINATING: u64 checked_add uses unsigned signedness (not the
/// `unwrap_or(true)` signed default from wrapping.rs:105).
#[test]
fn test_checked_add_u64_in_range_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "ok",
        "x.checked_add(200) == 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "100u64.checked_add(200) should verify (300 fits in u64)",
    );
}

/// DISCRIMINATING: i32 checked_sub detects signed underflow at MIN boundary.
#[test]
fn test_checked_sub_i32_underflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume(
        "x_min",
        "x == -2147483648",
    ));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "underflows",
        "x.checked_sub(1) == 2147483647",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i32::MIN.checked_sub(1) should detect signed underflow",
    );
}
