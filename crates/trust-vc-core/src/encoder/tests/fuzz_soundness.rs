// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fuzz-style soundness tests for the encoder (#2736).
//!
//! These tests generate verification queries with known-true and known-false
//! postconditions and assert that the encoder never produces false-verified
//! results. The focus is on:
//!
//! - Arithmetic overflow at type boundaries (i8, i16, i32, i64, u8, u16, u32, u64)
//! - Division and remainder edge cases (division by zero, MIN / -1)
//! - Bit-vector edge cases (shift by bit-width, bitwise identity laws)
//! - Known-false postconditions that must never return Verified
//!
//! Each test has a clear ground-truth oracle: either a mathematically true
//! postcondition (must verify) or a mathematically false one (must not verify).

use super::*;
use proptest::prelude::*;

// ========================================================================
// Section 1: Known-false postconditions must NEVER return Verified
//
// These are the most critical soundness tests. If ANY of these return
// Verified, the encoder has a false-verification bug.
// ========================================================================

/// False postcondition: x + 1 == x (impossible for any integer).
#[test]
fn test_false_verified_add_one_equals_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("impossible", "x + 1 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x + 1 == x is always false — must never return Verified",
    );
}

/// False postcondition: a positive number is negative.
#[test]
fn test_false_verified_positive_is_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("negative", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Positive x cannot be negative — must produce counterexample",
    );
}

/// False postcondition: two distinct values are equal.
#[test]
fn test_false_verified_distinct_values_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 10"));
    ctx.push_obligation(ProofObligation::assert("absurd", "x == y"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "5 != 10 — must produce counterexample");
}

/// False postcondition: zero is nonzero.
#[test]
fn test_false_verified_zero_is_nonzero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("nonzero", "x != 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "0 != 0 is false — must produce counterexample");
}

/// False postcondition: unsigned value is negative.
#[test]
fn test_false_verified_unsigned_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("negative_unsigned", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "u32 cannot be < 0 — must never return Verified");
}

/// False postcondition: x * 0 != 0 (multiplication by zero must always be zero).
#[test]
fn test_false_verified_mul_zero_nonzero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("absurd", "x * 0 != 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x * 0 is always 0 — x * 0 != 0 must never return Verified",
    );
}

// ========================================================================
// Section 2: Known-true postconditions must return Verified
//
// False negatives (failing to verify true statements) are less critical
// than false positives, but still indicate encoder bugs.
// ========================================================================

/// True postcondition: x == x (reflexivity).
#[test]
fn test_true_verified_reflexivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("reflexive", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == x is always true");
}

/// True postcondition: x + 0 == x (additive identity).
#[test]
fn test_true_verified_additive_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume(
        "bounded",
        "x > -1000000 && x < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "x + 0 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x + 0 == x is always true for bounded x");
}

/// True postcondition: x * 1 == x (multiplicative identity).
#[test]
fn test_true_verified_multiplicative_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume(
        "bounded",
        "x > -1000000 && x < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "x * 1 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x * 1 == x is always true for bounded x");
}

/// True postcondition: assumed value matches assertion.
#[test]
fn test_true_verified_assume_equals_assert() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("given", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("check", "x == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Assume x == 42 implies assert x == 42");
}

// ========================================================================
// Section 3: Arithmetic overflow boundary fuzzing
//
// Type boundary values are the most common source of false-verification
// bugs. These tests probe MIN, MAX, and near-boundary values.
// ========================================================================

/// i8::MAX + 1 should not verify as i8::MAX + 1 without overflow wrapping.
#[test]
fn test_overflow_i8_max_plus_one_false_postcondition() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("at_max", "x == 127"));
    // With overflow checks, x + 1 should detect the overflow
    ctx.push_obligation(ProofObligation::assert("no_overflow", "x + 1 == 128"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i8::MAX + 1 should not verify as 128 with overflow checks — 128 is out of i8 range",
    );
}

/// u8::MAX + 1 with overflow checks should not verify.
#[test]
fn test_overflow_u8_max_plus_one() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("at_max", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("overflow", "x + 1 == 256"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u8::MAX + 1 should not verify as 256 with overflow checks — 256 is out of u8 range",
    );
}

/// i16::MIN - 1 with overflow checks should not verify.
#[test]
fn test_overflow_i16_min_minus_one() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i16"));
    ctx.push_obligation(ProofObligation::assume("at_min", "x == -32768"));
    ctx.push_obligation(ProofObligation::assert("underflow", "x - 1 == -32769"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "i16::MIN - 1 should not verify as -32769 with overflow checks",
    );
}

/// Bounded arithmetic that stays in range should verify.
#[test]
fn test_overflow_bounded_addition_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bounded", "x >= 0 && x < 100"));
    ctx.push_obligation(ProofObligation::assert("in_range", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 <= x < 100 ensures x + 1 > x without overflow");
}

// ========================================================================
// Section 4: Division and remainder edge cases
//
// Division by zero and signed MIN / -1 are the two critical division
// edge cases that must never produce false-verified results.
// ========================================================================

/// Division by zero must not verify (encoder may reject at parse time with Error).
#[test]
fn test_div_by_zero_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("div_zero", "x / 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "Division by zero must never return Verified");
}

/// Division by one is identity — should verify.
#[test]
fn test_div_by_one_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume(
        "bounded",
        "x > -1000000 && x < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert("div_one", "x / 1 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x / 1 == x for bounded x");
}

/// Remainder by zero must not verify (encoder may reject at parse time with Error).
#[test]
fn test_rem_by_zero_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("rem_zero", "x % 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "Remainder by zero must never return Verified");
}

// ========================================================================
// Section 5: Bit-vector edge cases
//
// Shift by bit-width, bitwise identity laws, and sign extension must
// all be encoded correctly to avoid false-verification.
// ========================================================================

/// Shift left by exactly the bit-width is UB — must not verify.
#[test]
fn test_bv_shift_left_by_bitwidth_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shift_ub", "(x << 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "u32 << 32 is UB — must never return Verified");
}

/// Shift right by exactly the bit-width is UB — must not verify.
#[test]
fn test_bv_shift_right_by_bitwidth_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("shift_ub", "(x >> 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "u32 >> 32 is UB — must never return Verified");
}

/// Bitwise AND with zero should always be zero — true postcondition.
#[test]
fn test_bv_and_with_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("and_zero", "(x & 0) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x & 0 == 0 for any x");
}

/// Bitwise OR with zero should be identity — true postcondition.
#[test]
fn test_bv_or_with_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("or_zero", "(x | 0) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x | 0 == x for any x");
}

/// XOR with self should be zero — true postcondition.
#[test]
fn test_bv_xor_self_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("xor_self", "(x ^ x) == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x ^ x == 0 for any x");
}

/// False: XOR with self is nonzero — must not verify.
#[test]
fn test_false_verified_xor_self_nonzero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assert("absurd", "(x ^ x) != 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x ^ x is always 0 — x ^ x != 0 must never return Verified",
    );
}

// ========================================================================
// Section 6: Property-based fuzzing with proptest
//
// These use random inputs to probe for false-verification bugs across
// wider input domains. Each test has a mathematical oracle.
// ========================================================================

proptest! {
    /// For any concrete value v, asserting x == v when x IS v should verify.
    #[test]
    fn test_proptest_concrete_value_roundtrip(val in -10000i32..10000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("val", format!("x == {val}")));
        ctx.push_obligation(ProofObligation::assert("roundtrip", format!("x == {val}")));

        let result = AYEncoder::verify(&ctx);
        expect_verified(&result, &format!("x == {val} after assume x == {val}"));
    }
}

proptest! {
    /// For any concrete value v, asserting x != v when x IS v must not verify.
    #[test]
    fn test_proptest_false_inequality(val in -10000i32..10000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("val", format!("x == {val}")));
        ctx.push_obligation(ProofObligation::assert("false_neq", format!("x != {val}")));

        let result = AYEncoder::verify(&ctx);
        expect_counterexample(
            &result,
            &format!("x != {val} when x == {val} must produce counterexample"),
        );
    }
}

proptest! {
    /// For bounded a, b where a + b doesn't overflow, the sum should verify.
    #[test]
    fn test_proptest_bounded_addition_true(a in -1000i32..1000, b in -1000i32..1000) {
        let expected = a as i64 + b as i64;
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("x_val", format!("x == {a}")));
        ctx.push_obligation(ProofObligation::assume("y_val", format!("y == {b}")));
        ctx.push_obligation(ProofObligation::assert(
            "sum",
            format!("x + y == {expected}"),
        ));

        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("{a} + {b} == {expected} should verify"),
        );
    }
}

proptest! {
    /// For any a, b in range, asserting a + b == (wrong value) must not verify.
    #[test]
    fn test_proptest_wrong_sum_not_verified(a in -500i32..500, b in -500i32..500) {
        let correct = a as i64 + b as i64;
        let wrong = correct + 1; // always wrong
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("x_val", format!("x == {a}")));
        ctx.push_obligation(ProofObligation::assume("y_val", format!("y == {b}")));
        ctx.push_obligation(ProofObligation::assert(
            "wrong_sum",
            format!("x + y == {wrong}"),
        ));

        let result = AYEncoder::verify(&ctx);
        expect_counterexample(
            &result,
            &format!("{a} + {b} != {wrong} — must produce counterexample"),
        );
    }
}

proptest! {
    /// Multiplication commutativity: a * b == b * a (known-true).
    #[test]
    fn test_proptest_multiplication_commutative(a in -100i32..100, b in -100i32..100) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("x_val", format!("x == {a}")));
        ctx.push_obligation(ProofObligation::assume("y_val", format!("y == {b}")));
        ctx.push_obligation(ProofObligation::assert("commutative", "x * y == y * x"));

        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("{a} * {b} == {b} * {a} should verify"),
        );
    }
}

proptest! {
    /// Addition commutativity: a + b == b + a (known-true).
    #[test]
    fn test_proptest_addition_commutative(a in -1000i32..1000, b in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("x_val", format!("x == {a}")));
        ctx.push_obligation(ProofObligation::assume("y_val", format!("y == {b}")));
        ctx.push_obligation(ProofObligation::assert("commutative", "x + y == y + x"));

        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("{a} + {b} == {b} + {a} should verify"),
        );
    }
}

proptest! {
    /// For bounded values, subtraction then addition should roundtrip.
    #[test]
    fn test_proptest_sub_add_roundtrip(val in -1000i32..1000, delta in 1i32..100) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("d", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("x_val", format!("x == {val}")));
        ctx.push_obligation(ProofObligation::assume("d_val", format!("d == {delta}")));
        ctx.push_obligation(ProofObligation::assert("roundtrip", "x - d + d == x"));

        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("{val} - {delta} + {delta} == {val} should verify"),
        );
    }
}

proptest! {
    /// u8 values: known upper bound should verify.
    #[test]
    fn test_proptest_u8_upper_bound(val in 0u8..255) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
        ctx.push_obligation(ProofObligation::assume("val", format!("x == {val}")));
        ctx.push_obligation(ProofObligation::assert("bound", "x <= 255"));

        let result = AYEncoder::verify(&ctx);
        expect_verified(&result, &format!("{val}u8 <= 255 should verify"));
    }
}

proptest! {
    /// u8 values: false claim that value equals something else must not verify.
    #[test]
    fn test_proptest_u8_false_equality(val in 0u8..128) {
        let wrong = (val as u16 + 128) as u8; // guaranteed different
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
        ctx.push_obligation(ProofObligation::assume("val", format!("x == {val}")));
        ctx.push_obligation(ProofObligation::assert("false_eq", format!("x == {wrong}")));

        let result = AYEncoder::verify(&ctx);
        expect_counterexample(
            &result,
            &format!("{val}u8 != {wrong}u8 — must produce counterexample"),
        );
    }
}

proptest! {
    /// Comparison transitivity: if a < b and b < c, then a < c.
    #[test]
    fn test_proptest_comparison_transitivity(
        a in -100i32..-1,
        b in 0i32..100,
        c in 100i32..200,
    ) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("a_val", format!("a == {a}")));
        ctx.push_obligation(ProofObligation::assume("b_val", format!("b == {b}")));
        ctx.push_obligation(ProofObligation::assume("c_val", format!("c == {c}")));
        ctx.push_obligation(ProofObligation::assert("transitive", "a < c"));

        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("{a} < {c} should verify when {a} < {b} < {c}"),
        );
    }
}

// ========================================================================
// Section 7: Multi-type boundary exhaustive tests
//
// Exhaustively test type boundary values for all integer widths.
// These catch width-dependent encoder bugs.
// ========================================================================

/// i32::MAX boundary: MAX < MAX is false.
#[test]
fn test_boundary_i32_max_not_less_than_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("at_max", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("false_lt", "x < 2147483647"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "i32::MAX < i32::MAX is false — must produce counterexample",
    );
}

/// i32::MIN boundary: MIN > MIN is false.
#[test]
fn test_boundary_i32_min_not_greater_than_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("at_min", "x == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("false_gt", "x > -2147483648"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "i32::MIN > i32::MIN is false — must produce counterexample",
    );
}

/// u64::MAX boundary: MAX + 1 with overflow checks should fail.
#[test]
fn test_boundary_u64_max_overflow() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume(
        "at_max",
        "x == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "overflow",
        "x + 1 == 18446744073709551616",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "u64::MAX + 1 should not verify with overflow checks",
    );
}

/// u8 in-range subtraction should verify.
#[test]
fn test_boundary_u8_safe_subtraction() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("bounded", "x >= 10 && x <= 200"));
    ctx.push_obligation(ProofObligation::assert("no_underflow", "x - 10 >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x - 10 >= 0 when x >= 10 should verify");
}

// ========================================================================
// Section 8: Boolean logic soundness
//
// Boolean connectives must be encoded correctly.
// ========================================================================

/// True: De Morgan's law — !(a && b) == (!a || !b).
#[test]
fn test_demorgan_and_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert(
        "demorgan",
        "!(a && b) == (!a || !b)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "De Morgan's law !(a && b) == (!a || !b)");
}

/// True: De Morgan's law — !(a || b) == (!a && !b).
#[test]
fn test_demorgan_or_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert(
        "demorgan",
        "!(a || b) == (!a && !b)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "De Morgan's law !(a || b) == (!a && !b)");
}

/// False: a && !a should never be true.
#[test]
fn test_false_verified_contradiction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert("contradiction", "a && !a"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "a && !a is always false — must never return Verified",
    );
}

/// True: excluded middle — a || !a.
#[test]
fn test_excluded_middle_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert("excluded_middle", "a || !a"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a || !a (excluded middle) should verify");
}
