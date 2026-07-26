//! `by(bit_vector)` requires-assumption forwarding across differing bitwidths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Locks in the engine-level behavior the upstream Verus tests
//! `bitvector_ineq_different_bitwidth` and `test_casting_to_higher_width_issue386`
//! (cluster #2778, `rust_verify_test/tests/bitvector.rs`) depend on: a
//! `by(bit_vector)` assertion is discharged with scoped `requires` clauses
//! forwarded as solver assumptions, where the requires operands and the goal
//! operands have *different* bit widths (e.g. `u8` against `3u64`, or `u8` cast
//! up to `u64`). At the engine layer the scoped `requires` clauses arrive as
//! ordinary `Assume` obligations preceding the `BitVector`-mode `Assert`, which
//! is exactly what these tests model.
//!
//! Cross-width coercion is handled by `coerce_bv_widths` (zero-extension for
//! unsigned operands, sign-extension for signed operands — see
//! `encoder::width_coercion`). These tests pin the *whole-case* verdict through
//! the obligation pipeline, including the should-FAIL directions, so neither the
//! assumption forwarding nor the extension direction can silently regress.
//!
//! Complements `mixed_unsigned_comparisons.rs`, which checks raw comparison
//! *terms* in isolation (no requires, no `BitVector` solver mode, no obligation
//! pipeline).

use super::*;

fn bv() -> crate::vc::SolverMode {
    crate::vc::SolverMode::BitVector
}

// =========================================================================
// bitvector_ineq_different_bitwidth: u8 variable compared with a u64 literal,
// with a single scoped `requires b == 5`. Upstream asserts 1 of the 3 fails.
// =========================================================================

/// `requires b == 5; assert(b >= 3u64)` — upstream `test`: VERIFIES.
///
/// `b: u8` zero-extends to u64; 5 >= 3 holds. The scoped `requires` must reach
/// the BV goal across the width gap, otherwise `b` is unconstrained and the
/// unsigned `b >= 3` would still hold vacuously — so the should-FAIL case below
/// is what actually discriminates correct forwarding.
#[test]
fn ineq_diff_width_ge_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("req", "b == 5"));
    ctx.push_obligation(ProofObligation::assert("goal", "b >= 3u64").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "b:u8 == 5 implies b >= 3u64 (upstream `test`)");
}

/// `requires b == 5; assert(3u64 <= b)` — upstream `test2`: VERIFIES.
///
/// Same as above with the literal on the left, exercising the width-coercion
/// path when the *wider* operand is the left-hand side.
#[test]
fn ineq_diff_width_lit_left_le_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("req", "b == 5"));
    ctx.push_obligation(ProofObligation::assert("goal", "3u64 <= b").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "b:u8 == 5 implies 3u64 <= b (upstream `test2`)");
}

/// `requires b == 5; assert(b <= 3u64)` — upstream `test3`: FAILS.
///
/// This is the discriminating direction. With the assumption correctly
/// forwarded across the width gap, `b == 5` and `5 <= 3` is false, so the
/// solver must produce a counterexample at `b = 5`. A bug that dropped the
/// scoped `requires` (leaving `b` free) would *also* fail here, but a bug that
/// mis-extended the operands could spuriously verify — this pins the verdict.
#[test]
fn ineq_diff_width_le_fails_with_model() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.push_obligation(ProofObligation::assume("req", "b == 5"));
    ctx.push_obligation(ProofObligation::assert("goal", "b <= 3u64").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "b:u8 == 5 does NOT imply b <= 3u64 (upstream `test3`)",
    );
    if let crate::encoder::VerifyResult::Counterexample { model, .. } = &result {
        assert_eq!(
            model.as_deref(),
            Some("b = 5"),
            "counterexample must witness the forwarded requires (b = 5), got {model:?}"
        );
    } else {
        panic!("expected a counterexample with a concrete model, got {result:?}");
    }
}

// =========================================================================
// test_casting_to_higher_width_issue386: u8 cast up to u64, MULTI-CLAUSE
// `requires b == 20 && w == 20` (and the FAILS variant `w == 276`). The
// power-of-two-vs-not augmentation (8 -> 64 adds 56 bits) is exercised by the
// zero-extension in `coerce_bv_widths` / the cast encoder.
// =========================================================================

/// `requires b == 20 && w == 20; assert((b as u64) == w)` — upstream `test`:
/// VERIFIES. Two scoped requires clauses over operands of *different* widths
/// (`b: u8`, `w: u64`) must BOTH forward to the BV goal.
#[test]
fn cast_higher_width_multiclause_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.declare_var_typed("w", u64_ty());
    ctx.push_obligation(ProofObligation::assume("req_b", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("req_w", "w == 20"));
    ctx.push_obligation(ProofObligation::assert("goal", "(b as u64) == w").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "(b as u64) == w with b == 20 && w == 20 (upstream issue386 `test`)",
    );
}

/// `requires b == 20 && w == 276; assert((b as u64) == w)` — upstream `test2`:
/// FAILS. The second clause now contradicts the goal, and the counterexample
/// must reflect *both* forwarded clauses (`b = 20, w = 276`). If multi-clause
/// forwarding dropped the `w` clause, `w` would be free and the goal would still
/// fail — so the model assertion is what proves both clauses reached the solver.
#[test]
fn cast_higher_width_multiclause_fails_with_model() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.declare_var_typed("w", u64_ty());
    ctx.push_obligation(ProofObligation::assume("req_b", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("req_w", "w == 276"));
    ctx.push_obligation(ProofObligation::assert("goal", "(b as u64) == w").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "(b as u64) == w with b == 20 && w == 276 is false (upstream issue386 `test2`)",
    );
    if let crate::encoder::VerifyResult::Counterexample { model, .. } = &result {
        assert_eq!(
            model.as_deref(),
            Some("b = 20, w = 276"),
            "counterexample must witness BOTH forwarded requires clauses, got {model:?}"
        );
    } else {
        panic!("expected a counterexample with both clauses in the model, got {result:?}");
    }
}

// =========================================================================
// Multi-clause requires whose clauses *themselves* carry differing-width
// literals (e.g. a u8 variable constrained by a `5u64` literal and a u32
// variable constrained by a `5u8` literal). Generalizes the single-width
// requires-forwarding path to genuinely mixed-width clause operands.
// =========================================================================

/// Two requires clauses, each mixing the variable width with a differently
/// suffixed literal, plus a cross-width goal. All three widths (u8, u32, and
/// the u64/u8 literals) must coerce consistently for the goal to verify.
#[test]
fn multiclause_mixed_width_literals_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("req_b", "b == 5u64"));
    ctx.push_obligation(ProofObligation::assume("req_c", "c == 5u8"));
    ctx.push_obligation(ProofObligation::assert("goal", "(b as u32) == c").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "b:u8 == 5u64 && c:u32 == 5u8 implies (b as u32) == c",
    );
}

/// Should-FAIL companion: the same multi-clause mixed-width shape but with a
/// goal that the assumptions do not entail. Confirms the forwarding does not
/// over-constrain (which would spuriously verify a false goal).
#[test]
fn multiclause_mixed_width_literals_fail() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", u8_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("req_b", "b == 5u64"));
    ctx.push_obligation(ProofObligation::assume("req_c", "c == 7u8"));
    ctx.push_obligation(ProofObligation::assert("goal", "(b as u32) == c").with_solver_mode(bv()));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "b:u8 == 5 && c:u32 == 7 does NOT imply (b as u32) == c",
    );
}

// =========================================================================
// Signed differing-width requires forwarding: sign-extension must be used for
// signed operands so a negative requires value reaches a wider signed goal.
// =========================================================================

/// `requires a == -5; assert((a as i32) >= -5i32)` — `a: i8`. The negative
/// requires value must *sign*-extend to i32 (zero-extension would turn -5 into
/// a large positive value and break the goal), confirming the extension
/// direction is selected per operand signedness across the width gap.
#[test]
fn signed_diff_width_requires_sign_extends_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("req", "a == -5"));
    ctx.push_obligation(
        ProofObligation::assert("goal", "(a as i32) >= -5i32").with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a:i8 == -5 implies (a as i32) >= -5 (sign-extension)",
    );
}

/// Should-FAIL companion: a wider lower bound the negative requires value does
/// not satisfy, so the case must produce a counterexample rather than verify.
#[test]
fn signed_diff_width_requires_lower_bound_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("req", "a == -5"));
    ctx.push_obligation(
        ProofObligation::assert("goal", "(a as i32) >= -4i32").with_solver_mode(bv()),
    );
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "a:i8 == -5 does NOT imply (a as i32) >= -4");
}
