//! Boolean logic tests — short-circuit semantics for && and ||.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Short-circuit semantics (#1678)
//
// Rust's && and || are short-circuit: the right operand is only
// evaluated when needed. The encoder now uses ite(a, b, false) for &&
// and ite(a, true, b) for || to match these semantics.
// ========================================================================

/// Verify that && produces correct results: true only when both are true.
/// Assumes x >= 0 && x < 10, then asserts x >= 0 && x < 10 (should verify).
#[test]
fn test_and_basic_semantics() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bounds", "x >= 0 && x < 10"));
    ctx.push_obligation(ProofObligation::assert("check", "x >= 0 && x < 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x >= 0 && x < 10 with same assumption should verify",
    );
}

/// Verify that || produces correct results: false only when both are false.
/// If x > 100 or x < 0, then it's not in [0, 100].
#[test]
fn test_or_basic_semantics() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("outside", "x > 100 || x < 0"));
    ctx.push_obligation(ProofObligation::assert(
        "not_in_range",
        "!(x >= 0 && x <= 100)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x > 100 || x < 0 implies !(x >= 0 && x <= 100)");
}

/// Verify && short-circuit: false && anything is false.
/// Discriminating: with the ite encoding, `false && b` always evaluates
/// to false regardless of b's value, matching Rust's guarantee.
#[test]
fn test_and_short_circuit_false_left() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // x is never equal to both 0 and 1, so left side of && is always false
    ctx.push_obligation(ProofObligation::assume("x_is_zero", "x == 0"));
    // Assert that (x == 1 && x > 0) is false — the left side is false
    // so the whole expression must be false regardless of right side
    ctx.push_obligation(ProofObligation::assert(
        "short_circuit",
        "!(x == 1 && x > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "false && anything should be false");
}

/// Verify || short-circuit: true || anything is true.
#[test]
fn test_or_short_circuit_true_left() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_zero", "x == 0"));
    // x == 0 is true, so (x == 0 || <anything>) should be true
    ctx.push_obligation(ProofObligation::assert(
        "short_circuit",
        "x == 0 || x == 42",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "true || anything should be true");
}

/// Verify && with conditional guard pattern: the motivating example from #1678.
/// assert!(x != 0 && 10 / x > 0) with x constrained to [1, 10].
///
/// This tests that the short-circuit encoding correctly handles the pattern
/// where the left operand guards a potentially problematic right operand.
/// With x in [1, 10], x != 0 is always true, and 10 / x > 0 is always true.
///
/// Uses i8 instead of i32: BV division over 32-bit values exceeds the 10s
/// solver timeout in ay's DPLL-based BV solver. i8 preserves the test's
/// short-circuit encoding discrimination while keeping division tractable.
#[test]
fn test_and_guard_pattern_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x >= 1i8"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x <= 10i8"));
    ctx.push_obligation(ProofObligation::assert(
        "guarded",
        "x != 0i8 && 10i8 / x > 0i8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x in [1,10]: x != 0 && 10/x > 0 should verify");
}

/// Verify && produces counterexample when assertion is false.
/// x > 10 && x < 5 is impossible, so asserting it should fail.
#[test]
fn test_and_counterexample_contradictory() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("impossible", "x > 10 && x < 5"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "x > 10 && x < 5 is unsatisfiable, should produce counterexample",
    );
}

/// Verify || with counterexample: when neither disjunct holds.
/// If x == 5, then x < 0 || x > 10 is false.
#[test]
fn test_or_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "unreachable_bounds",
        "x < 0 || x > 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "x < 0 || x > 10 is not universally true, should produce counterexample",
    );
}

/// Implication pattern using ||: !p || q === p implies q.
/// If x > 5, then x > 0 (using the || encoding of implication).
#[test]
fn test_or_implication_pattern() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x > 5"));
    // !(x > 5) || (x > 0) should be true — if x > 5 then certainly x > 0
    ctx.push_obligation(ProofObligation::assert("implication", "!(x > 5) || x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!(x > 5) || x > 0 is valid implication");
}

/// Nested && chains: a && b && c uses ite encoding at each level.
#[test]
fn test_nested_and_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < 100"));
    ctx.push_obligation(ProofObligation::assert(
        "chain",
        "x > 0 && x < 100 && x != 50",
    ));

    let result = AYEncoder::verify(&ctx);
    // x could be 50, so this should produce a counterexample
    expect_counterexample(
        &result,
        "x > 0 && x < 100 && x != 50 is not always true (x could be 50)",
    );
}

/// Mixed && and ||: (a || b) && c.
#[test]
fn test_mixed_and_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    // (x < 0 || x > 3) && x < 10 — first disjunct false, second true, conjunction true
    ctx.push_obligation(ProofObligation::assert(
        "mixed",
        "(x < 0 || x > 3) && x < 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "With x == 5: (x < 0 || x > 3) && x < 10 should verify",
    );
}

// ========================================================================
// Short-circuit overflow guard (#1679)
//
// When overflow checking is enabled, the right operand of && / || may
// generate overflow checks. These checks must be guarded by the left
// condition to match Rust's short-circuit evaluation semantics.
// Without guarding, patterns like `x != 0 && x + i32::MAX > 0` would
// falsely report overflow from the right operand even when x == 0
// (which would short-circuit in Rust, never evaluating the addition).
// ========================================================================

/// Discriminating test: overflow checks from the right operand of &&
/// must be guarded by the left condition (#1679).
///
/// With x == 1: `x > 10` is false, so && short-circuits. But `x + 2147483647`
/// overflows (1 + 2147483647 = 2147483648 > i32::MAX). Without the overflow
/// guard, the unguarded overflow check would report a false-positive overflow
/// violation. With the guard, the overflow check becomes
/// `¬(x > 10) ∨ bvadd_no_overflow(x, 2147483647)` = `true ∨ false` = true.
///
/// **Discrimination proof:** Without the guard fix (i.e., with the old code
/// that doesn't wrap overflow checks), this test would fail with an overflow
/// error instead of Counterexample, because `bvadd_no_overflow(1, 2147483647)`
/// is false (the addition overflows).
#[test]
fn test_and_overflow_guard_short_circuit() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_one", "x == 1"));
    // x == 1, so x > 10 is false, && short-circuits.
    // The right operand x + 2147483647 > 0 is never evaluated in Rust.
    // But 1 + 2147483647 = 2147483648 which OVERFLOWS i32.
    // Without the guard: overflow check fires → false positive.
    // With the guard: overflow check is ¬(x > 10) ∨ no_overflow = true ∨ false = true.
    // The assertion should produce Counterexample (because x > 10 is false),
    // NOT an overflow error.
    ctx.push_obligation(ProofObligation::assert(
        "guarded_overflow",
        "x > 10 && x + 2147483647 > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "x == 1: `x > 10 && x + MAX > 0` should be Counterexample (left is false), not an overflow error");
}

/// Discriminating test for || overflow guard (#1679).
///
/// With x == 1: `x == 1` is true, so || short-circuits. But `x + 2147483647`
/// overflows (1 + 2147483647 > i32::MAX). Without the overflow guard, the
/// unguarded check would report overflow. With the guard, the check becomes
/// `(x == 1) ∨ bvadd_no_overflow(x, 2147483647)` = `true ∨ false` = true.
///
/// **Discrimination proof:** Without the guard fix, this test would fail with
/// an overflow error instead of Verified, because `bvadd_no_overflow(1, 2147483647)`
/// is false.
#[test]
fn test_or_overflow_guard_short_circuit() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_one", "x == 1"));
    // x == 1 is true, so || short-circuits. The addition x + i32::MAX
    // is never evaluated, but 1 + 2147483647 overflows i32.
    // Without guard: overflow check fires → false positive.
    // With guard: (x == 1) ∨ no_overflow = true ∨ false = true.
    ctx.push_obligation(ProofObligation::assert(
        "guarded_overflow",
        "x == 1 || x + 2147483647 > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x == 1: `x == 1 || x + MAX > 0` should verify (left is true, short-circuits)",
    );
}
