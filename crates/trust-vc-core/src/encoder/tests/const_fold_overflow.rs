//! Constant-fold overflow detection for all-constant fixed-width arithmetic.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Mirrors upstream Verus `source/rust_verify_test/tests/overflow.rs` cases
//! `test_const_ok`, `test_const_fail`, `test_static_fail`, and
//! `test_literal_out_of_range`: an all-constant arithmetic expression that
//! overflows its fixed-width result type (e.g. `255u8 + 1u8`, `0u8 - 1u8`,
//! `const C: u8 = 255 + 1`) must yield a **definite** verdict.
//!
//! Before this path existed, fully-ground overflow obligations returned
//! `Unknown(EmptyModel)` — the ay-dpll solver answers SAT with an empty model
//! for a closed `bvadd_no_overflow`-style query, which the encoder
//! conservatively treats as unknown. The constant-fold path evaluates the
//! exact fixed-width result in Rust and emits a `Counterexample` for an
//! overflow or `Verified` for a safe operation, without deferring to the
//! solver. Non-constant operands are never folded, so symbolic results are
//! unchanged (verified by the broader `overflow*` suites).

use super::*;
use crate::ir::{ArithOp, TrustVcExpr, TrustVcType};

fn verify_const(cond: &str) -> VerifyResult {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert("const_arith", cond));
    AYEncoder::verify(&ctx)
}

// ── Definite overflow → Counterexample (was Unknown(EmptyModel)) ──

#[test]
fn const_u8_add_overflow_is_counterexample() {
    // Upstream test_const_fail: `const C: u8 = 255 + 1`.
    expect_counterexample(
        &verify_const("255u8 + 1u8 == 0u8"),
        "#2778 overflow.rs test_const_fail: 255u8 + 1u8 overflows u8",
    );
}

#[test]
fn const_u8_sub_underflow_is_counterexample() {
    // Upstream test_literal_out_of_range reduces to `0u8 - 1u8`.
    expect_counterexample(
        &verify_const("0u8 - 1u8 == 255u8"),
        "#2778 overflow.rs test_literal_out_of_range: 0u8 - 1u8 underflows u8",
    );
}

#[test]
fn const_i8_add_overflow_is_counterexample() {
    expect_counterexample(
        &verify_const("127i8 + 1i8 == -128i8"),
        "i8 add overflow: 127i8 + 1i8 escapes i8",
    );
}

#[test]
fn const_i8_sub_underflow_is_counterexample() {
    expect_counterexample(
        &verify_const("-100i8 - 100i8 == 56i8"),
        "i8 sub underflow: -100i8 - 100i8 == -200 escapes i8",
    );
}

#[test]
fn const_u32_add_overflow_is_counterexample() {
    expect_counterexample(
        &verify_const("4294967295u32 + 1u32 == 0u32"),
        "u32 add overflow: u32::MAX + 1 escapes u32",
    );
}

#[test]
fn const_u8_mul_overflow_is_counterexample() {
    expect_counterexample(
        &verify_const("16u8 * 16u8 == 0u8"),
        "u8 mul overflow: 16u8 * 16u8 == 256 escapes u8",
    );
}

#[test]
fn const_i64_add_overflow_is_counterexample() {
    expect_counterexample(
        &verify_const("9223372036854775807i64 + 1i64 == 0i64"),
        "i64 add overflow: i64::MAX + 1 escapes i64",
    );
}

// ── Definite safe → Verified ──

#[test]
fn const_u8_add_in_range_verifies() {
    // Upstream test_const_ok: `const C: u8 = 254 + 1` (== 255, fits u8).
    expect_verified(
        &verify_const("254u8 + 1u8 == 255u8"),
        "#2778 overflow.rs test_const_ok: 254u8 + 1u8 == 255 fits u8",
    );
}

#[test]
fn const_i8_add_in_range_verifies() {
    expect_verified(
        &verify_const("126i8 + 1i8 == 127i8"),
        "i8 add safe: 126i8 + 1i8 == 127 fits i8",
    );
}

#[test]
fn const_u8_mul_in_range_verifies() {
    expect_verified(
        &verify_const("15u8 * 17u8 == 255u8"),
        "u8 mul safe: 15u8 * 17u8 == 255 fits u8",
    );
}

#[test]
fn const_i64_add_in_range_verifies() {
    expect_verified(
        &verify_const("100i64 + 100i64 == 200i64"),
        "i64 add safe: 100i64 + 100i64 == 200 fits i64",
    );
}

// ── Exact verdicts from the folding primitive itself ──

fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::IntLit { value, ty }
}

fn i32_default(value: i128) -> TrustVcExpr {
    lit(value, TrustVcType::Int { width: 32 })
}

#[test]
fn fold_primitive_reports_exact_overflow_for_typed_literals() {
    let v = AYEncoder::try_const_fold_arith_overflow(
        ArithOp::Add,
        &lit(255, TrustVcType::Uint { width: 8 }),
        &lit(1, TrustVcType::Uint { width: 8 }),
        &TrustVcType::Uint { width: 8 },
    )
    .expect("all-constant u8 add should fold");
    assert_eq!(v.exact, 256);
    assert!(v.overflows, "256 escapes u8");

    let safe = AYEncoder::try_const_fold_arith_overflow(
        ArithOp::Add,
        &lit(254, TrustVcType::Uint { width: 8 }),
        &lit(1, TrustVcType::Uint { width: 8 }),
        &TrustVcType::Uint { width: 8 },
    )
    .expect("all-constant u8 add should fold");
    assert_eq!(safe.exact, 255);
    assert!(!safe.overflows, "255 fits u8");
}

#[test]
fn fold_primitive_picks_up_result_type_width_for_bare_literals() {
    // Bare (default-i32) literals `255 + 1` in a u8 const context must take the
    // u8 width from the result type and report overflow — the bare-literal
    // width-inference gap noted in #2778.
    let v = AYEncoder::try_const_fold_arith_overflow(
        ArithOp::Add,
        &i32_default(255),
        &i32_default(1),
        &TrustVcType::Uint { width: 8 },
    )
    .expect("bare-literal add with u8 result type should fold");
    assert_eq!(v.exact, 256);
    assert_eq!(v.width, 8);
    assert!(v.overflows, "256 escapes u8 even from bare literals");

    // In an i32 result type the same expression is safe.
    let wide = AYEncoder::try_const_fold_arith_overflow(
        ArithOp::Add,
        &i32_default(255),
        &i32_default(1),
        &TrustVcType::Int { width: 32 },
    )
    .expect("bare-literal add with i32 result type should fold");
    assert_eq!(wide.exact, 256);
    assert!(!wide.overflows, "256 fits i32");
}

#[test]
fn fold_primitive_declines_non_constant_operands() {
    // A variable operand must never be folded; the symbolic check stays.
    let var = TrustVcExpr::Var {
        name: "a".to_string(),
        ty: TrustVcType::Uint { width: 8 },
    };
    assert!(
        AYEncoder::try_const_fold_arith_overflow(
            ArithOp::Add,
            &var,
            &lit(1, TrustVcType::Uint { width: 8 }),
            &TrustVcType::Uint { width: 8 },
        )
        .is_none(),
        "symbolic operand must not constant-fold"
    );
}

#[test]
fn fold_primitive_declines_unbounded_result_type() {
    // MathInt never overflows; folding it as an overflow verdict is unsound.
    assert!(
        AYEncoder::try_const_fold_arith_overflow(
            ArithOp::Add,
            &lit(255, TrustVcType::Uint { width: 8 }),
            &lit(1, TrustVcType::Uint { width: 8 }),
            &TrustVcType::MathInt,
        )
        .is_none(),
        "MathInt result type carries no overflow obligation"
    );
}

#[test]
fn fold_primitive_signed_div_min_by_neg_one_overflows() {
    // i8::MIN / -1 == 128, which escapes i8 — the classic signed-div overflow.
    let v = AYEncoder::try_const_fold_arith_overflow(
        ArithOp::Div,
        &lit(-128, TrustVcType::Int { width: 8 }),
        &lit(-1, TrustVcType::Int { width: 8 }),
        &TrustVcType::Int { width: 8 },
    )
    .expect("i8 MIN/-1 should fold");
    assert_eq!(v.exact, 128);
    assert!(v.overflows, "128 escapes i8");
}
