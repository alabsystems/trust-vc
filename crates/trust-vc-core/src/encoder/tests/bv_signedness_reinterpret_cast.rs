//! Same-width signedness-reinterpret `as`-cast lowering in `by(bit_vector)` mode.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Pins the engine behavior the upstream Verus cast/comparison cases in
//! cluster #2778 (`rust_verify_test/tests/bitvector.rs`, e.g. `test_eq_ineq`,
//! `test_casting`, `test_clipping_and_casting`) depend on: a same-width
//! `as`-cast that only flips signedness (`i8 as u8`, `u8 as i8`, `i32 as u32`,
//! …) preserves the bit pattern *and* must NOT clobber the source variable's
//! tracked signedness.
//!
//! The previous lowering reused the source ay term for the cast result and
//! destructively rewrote its `(width, signed)` metadata. When the same variable
//! was then re-encoded under its declared signedness, `encode_var`'s metadata
//! guard rejected it with a "sort metadata mismatch", fail-closing cases that
//! Verus discharges. The fix mints a fresh, bit-identical BV term for the cast
//! result carrying the new signedness, leaving the source variable's metadata
//! intact (see `cast_int_to_int`).
//!
//! Each case below uses an implication with the cast in the *antecedent* (so the
//! cast is encoded before a bare re-use of the same variable in the consequent),
//! which is exactly the encoding order that tripped the old clobber. Both
//! should-VERIFY (tautology) and should-FAIL (falsifiable, with a concrete
//! counterexample) directions are pinned so neither the bit-preservation nor the
//! non-clobber property can silently regress.

use super::*;

fn bv() -> crate::vc::SolverMode {
    crate::vc::SolverMode::BitVector
}

fn i8_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::Int { width: 8 }
}

// =========================================================================
// i8 -> u8 reinterpret: `(y as u8) == 255` iff `y == -1` (the bits are 0xFF
// either way). Variable `y` appears cast (antecedent) AND bare (consequent).
// =========================================================================

/// `(y as u8) == 255u8 ==> y == -1i8` — tautology, VERIFIES.
///
/// Pre-fix this fail-closed: the `y as u8` cast clobbered `y`'s tracked
/// signedness to unsigned, so re-encoding the signed `y == -1i8` consequent hit
/// the "sort metadata mismatch" guard. The reinterpret must instead preserve
/// `y`'s i8 metadata while exposing an unsigned view for the cast result.
#[test]
fn reinterpret_i8_to_u8_tautology_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", i8_ty());
    ctx.push_obligation(
        ProofObligation::assert("goal", "(y as u8) == 255u8 ==> y == -1i8").with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i8 reinterpret: (y as u8)==255 iff y==-1 (upstream test_eq_ineq shape)",
    );
}

/// `(y as u8) == 255u8 ==> y == 0i8` — false (witness `y = -1`), COUNTEREXAMPLE.
///
/// The discriminating should-FAIL direction: the reinterpret preserves bits, so
/// when `y as u8 == 255` the source `y` is `-1`, never `0`. A sound solver must
/// refute this with a concrete model rather than spuriously verifying it (which
/// an over-eager fold of the reinterpret could do) or erroring out.
#[test]
fn reinterpret_i8_to_u8_false_goal_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", i8_ty());
    ctx.push_obligation(
        ProofObligation::assert("goal", "(y as u8) == 255u8 ==> y == 0i8").with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "i8 reinterpret: (y as u8)==255 does NOT imply y==0",
    );
    assert!(
        result.is_counterexample(),
        "false reinterpret goal must be refuted with a counterexample, got {result:?}",
    );
}

// =========================================================================
// u8 -> i8 reinterpret: `(x as i8) == -1` iff `x == 255` (bits 0xFF). Mirror of
// the above with the opposite source/target signedness.
// =========================================================================

/// `(x as i8) == -1i8 ==> x == 255u8` — tautology, VERIFIES.
#[test]
fn reinterpret_u8_to_i8_tautology_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(
        ProofObligation::assert("goal", "(x as i8) == -1i8 ==> x == 255u8").with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u8 reinterpret: (x as i8)==-1 iff x==255 (upstream test_casting shape)",
    );
}

/// `(x as i8) == -1i8 ==> x == 0u8` — false (witness `x = 255`), COUNTEREXAMPLE.
#[test]
fn reinterpret_u8_to_i8_false_goal_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(
        ProofObligation::assert("goal", "(x as i8) == -1i8 ==> x == 0u8").with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "u8 reinterpret: (x as i8)==-1 does NOT imply x==0");
    assert!(
        result.is_counterexample(),
        "false reinterpret goal must be refuted with a counterexample, got {result:?}",
    );
}

// =========================================================================
// Wider same-width reinterpret (i32 <-> u32) with the variable used both ways
// in a conjunction, to confirm the fresh-term split holds beyond byte widths.
// =========================================================================

/// `(b as u32) == 0x8000_0000u32 ==> b < 0i32` — VERIFIES.
///
/// `b: i32`. The reinterpret's high bit set (`0x8000_0000`) exactly characterizes
/// `b` negative. The cast result is consumed unsigned (equality), while the bare
/// `b < 0i32` consequent must still see `b` as signed for `bvslt` — which only
/// holds if the cast did not clobber `b`'s signedness.
#[test]
fn reinterpret_i32_to_u32_sign_bit_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(
        ProofObligation::assert("goal", "(b as u32) == 0x8000_0000u32 ==> b < 0i32")
            .with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "i32 reinterpret: (b as u32)==0x80000000 implies b<0 (sign-bit set)",
    );
}

/// `(b as u32) == 0x8000_0000u32 ==> b > 0i32` — false (witness `b = i32::MIN`),
/// COUNTEREXAMPLE. Confirms the signed consequent is genuinely refutable and not
/// spuriously verified by a unsigned-mis-tracked `b`.
#[test]
fn reinterpret_i32_to_u32_sign_bit_false_goal_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(
        ProofObligation::assert("goal", "(b as u32) == 0x8000_0000u32 ==> b > 0i32")
            .with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "i32 reinterpret: (b as u32)==0x80000000 does NOT imply b>0",
    );
    assert!(
        result.is_counterexample(),
        "false signed-consequent goal must be refuted with a counterexample, got {result:?}",
    );
}
