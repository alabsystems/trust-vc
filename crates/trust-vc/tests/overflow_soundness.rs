// tests/overflow_soundness.rs
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache 2.0

//! Overflow soundness tests for #964
//!
//! These tests verify:
//! 1. Wrapping mode: bitvector arithmetic correctly models Rust's wrapping behavior
//! 2. Overflow checking mode: arithmetic overflow is detected and flagged
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests invoke ay verification through `VerificationContext::verify()`

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

mod common;

// ═══════════════════════════════════════════════════════════════════
// Part 1: Wrapping semantics (release-mode behavior)
//
// These tests use new_wrapping() to verify that bitvector arithmetic
// correctly models Rust's two's complement wrapping behavior.
// ═══════════════════════════════════════════════════════════════════

/// i32::MAX + 1 wraps to i32::MIN in Rust. The verifier must NOT prove
/// that (i32::MAX + 1) > 0, because at runtime it's -2147483648.
/// If this test produces Verified, the verifier has a soundness bug.
#[test]
fn test_i32_max_plus_one_wraps_negative() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_max", "x == 2147483647");
        ctx.push_assert("overflow_positive", "x + 1 > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "i32::MAX + 1 > 0 must produce Counterexample (wraps to i32::MIN), got: {:?}",
            result
        );
    })
}

/// x > 0 does NOT imply (x + 1) > x for all i32, because x + 1 can wrap.
/// Specifically, x = i32::MAX -> x + 1 = i32::MIN < x.
#[test]
fn test_x_plus_one_not_always_greater() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_positive", "x > 0");
        ctx.push_assert("x_plus_one_greater", "x + 1 > x");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "(x + 1) > x must produce Counterexample (overflow at i32::MAX), got: {:?}",
            result
        );
    })
}

/// With proper bounds, x + 1 > x SHOULD verify (no overflow possible).
#[test]
fn test_bounded_increment_verifies() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_bounded", "x > 0");
        ctx.push_assume("x_no_overflow", "x < 2147483647"); // x < i32::MAX
        ctx.push_assert("bounded_inc", "x + 1 > x");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Bounded x + 1 > x should verify (no overflow), got: {:?}",
            result
        );
    })
}

/// u32 overflow: u32::MAX + 1 should wrap to 0, not 4294967296.
#[test]
fn test_u32_max_plus_one_wraps_to_zero() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == 4294967295"); // u32::MAX
        ctx.push_assert("wraps_to_zero", "x + 1 == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX + 1 should wrap to 0, got: {:?}",
            result
        );
    })
}

/// u32 subtraction underflow: 0 - 1 should wrap to u32::MAX.
#[test]
fn test_u32_underflow_wraps() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_zero", "x == 0");
        ctx.push_assert("wraps_to_max", "x - 1 == 4294967295");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "0u32 - 1 should wrap to u32::MAX, got: {:?}",
            result
        );
    })
}

/// Multiplication overflow: i32::MAX * 2 wraps.
/// The verifier must NOT prove i32::MAX * 2 > 0.
#[test]
fn test_i32_mul_overflow_wraps() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_max", "x == 2147483647"); // i32::MAX
        ctx.push_assert("mul_positive", "x * 2 > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "i32::MAX * 2 > 0 must produce Counterexample (wraps to -2), got: {:?}",
            result
        );
    })
}

/// Signed underflow: i32::MIN - 1 wraps to i32::MAX.
#[test]
fn test_i32_min_minus_one_wraps_to_max() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_min", "x == -2147483648");
        ctx.push_assert("wraps_to_max", "x - 1 == 2147483647");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "i32::MIN - 1 should wrap to i32::MAX, got: {:?}",
            result
        );
    })
}

// ═══════════════════════════════════════════════════════════════════
// Part 2: Overflow detection (debug-mode behavior)
//
// These tests use with_overflow_checks() to verify that arithmetic
// overflow is detected and reported as counterexamples.
// ═══════════════════════════════════════════════════════════════════

/// Signed addition overflow: i32::MAX + 1 should be detected.
#[test]
fn test_overflow_detected_i32_add() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_max", "x == 2147483647");
        ctx.push_assert("will_overflow", "x + 1 > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "i32::MAX + 1 should be detected as overflow, got: {:?}",
            result
        );
    })
}

/// Unsigned addition overflow: u32::MAX + 1 should be detected.
#[test]
fn test_overflow_detected_u32_add() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == 4294967295");
        // Even though wrapping gives x + 1 == 0, overflow checking should flag this
        ctx.push_assert("will_overflow", "x + 1 == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "u32::MAX + 1 should be detected as overflow, got: {:?}",
            result
        );
    })
}

/// Signed subtraction underflow: i32::MIN - 1 should be detected.
#[test]
fn test_overflow_detected_i32_sub_underflow() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_min", "x == -2147483648");
        // Even though wrapping gives x - 1 == i32::MAX, overflow checking flags it
        ctx.push_assert("will_underflow", "x - 1 == 2147483647");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "i32::MIN - 1 should be detected as underflow, got: {:?}",
            result
        );
    })
}

/// Unsigned subtraction underflow: 0u32 - 1 should be detected.
#[test]
fn test_overflow_detected_u32_sub_underflow() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_zero", "x == 0");
        ctx.push_assert("will_underflow", "x - 1 == 4294967295");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "0u32 - 1 should be detected as underflow, got: {:?}",
            result
        );
    })
}

/// Signed multiplication overflow: i32::MAX * 2 should be detected.
#[test]
fn test_overflow_detected_i32_mul() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_max", "x == 2147483647");
        ctx.push_assert("will_overflow", "x * 2 > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "i32::MAX * 2 should be detected as overflow, got: {:?}",
            result
        );
    })
}

/// Bounded addition with overflow checks: no overflow when properly bounded.
#[test]
fn test_no_overflow_when_bounded_add() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_bounded", "x > 0");
        ctx.push_assume("x_no_overflow", "x < 2147483647"); // x < i32::MAX
        ctx.push_assert("bounded_inc", "x + 1 > x");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Bounded x + 1 > x should verify with overflow checks, got: {:?}",
            result
        );
    })
}

/// Bounded subtraction with overflow checks: no underflow when properly bounded.
#[test]
fn test_no_overflow_when_bounded_sub() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_bounded", "x > 0");
        ctx.push_assert("bounded_dec", "x - 1 >= 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 0 implies x - 1 >= 0 (no underflow), got: {:?}",
            result
        );
    })
}

/// Bounded unsigned addition: no overflow when sum fits in u32.
#[test]
fn test_no_overflow_when_bounded_u32_add() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("a", "u32");
        ctx.declare_var_parsed("b", "u32");
        // Both are small enough that their sum fits in u32
        ctx.push_assume("a_bound", "a < 1000000");
        ctx.push_assume("b_bound", "b < 1000000");
        ctx.push_assert("sum_bounded", "a + b < 2000000");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Small u32 addition should verify with overflow checks, got: {:?}",
            result
        );
    })
}

/// Multiplication with small values: no overflow.
#[test]
fn test_no_overflow_small_mul() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_small", "x > 0");
        ctx.push_assume("x_bounded", "x < 100");
        ctx.push_assert("mul_bounded", "x * 2 < 200");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Small multiplication should verify with overflow checks, got: {:?}",
            result
        );
    })
}

// ═══════════════════════════════════════════════════════════════════
// Part 3: Wrapping arithmetic methods
//
// These tests verify that wrapping_add/sub/mul correctly model
// Rust's explicit wrapping operations.
// ═══════════════════════════════════════════════════════════════════

/// wrapping_add: u32::MAX.wrapping_add(1) == 0
#[test]
fn test_wrapping_add_u32_max_wraps_to_zero() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == 4294967295");
        ctx.push_assert("wraps_to_zero", "x.wrapping_add(1) == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX.wrapping_add(1) should be 0, got: {:?}",
            result
        );
    })
}

/// wrapping_sub: 0u32.wrapping_sub(1) == u32::MAX
#[test]
fn test_wrapping_sub_u32_zero_wraps_to_max() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_zero", "x == 0");
        ctx.push_assert("wraps_to_max", "x.wrapping_sub(1) == 4294967295");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "0u32.wrapping_sub(1) should be u32::MAX, got: {:?}",
            result
        );
    })
}

/// wrapping_mul: i32::MAX.wrapping_mul(2) wraps (should not be > 0).
#[test]
fn test_wrapping_mul_i32_overflow_wraps() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_max", "x == 2147483647");
        ctx.push_assert("mul_positive", "x.wrapping_mul(2) > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "i32::MAX.wrapping_mul(2) > 0 must produce Counterexample, got: {:?}",
            result
        );
    })
}

/// wrapping_add with overflow checks enabled: wrapping_add bypasses overflow checks.
#[test]
fn test_wrapping_add_bypasses_overflow_checks() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == 4294967295");
        // Even with overflow checks, wrapping_add should NOT trigger overflow detection
        ctx.push_assert("wraps_to_zero", "x.wrapping_add(1) == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "wrapping_add should bypass overflow checks, got: {:?}",
            result
        );
    })
}

// ═══════════════════════════════════════════════════════════════════
// Part 4: Checked arithmetic methods
//
// These tests verify that checked_add/sub/mul generate overflow
// obligations that cause verification to fail when overflow is possible.
// ═══════════════════════════════════════════════════════════════════

/// checked_add detects overflow: u32::MAX.checked_add(1) overflows.
#[test]
fn test_checked_add_detects_overflow() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == 4294967295");
        ctx.push_assert("checked_result", "x.checked_add(1) == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "checked_add should detect overflow at u32::MAX + 1, got: {:?}",
            result
        );
    })
}

/// checked_add succeeds when no overflow: bounded addition.
#[test]
fn test_checked_add_succeeds_when_bounded() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_bounded", "x < 4294967295");
        ctx.push_assert("result_greater", "x.checked_add(1) > x");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Bounded checked_add should verify, got: {:?}",
            result
        );
    })
}

/// checked_sub detects underflow: 0u32.checked_sub(1) underflows.
#[test]
fn test_checked_sub_detects_underflow() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_zero", "x == 0");
        ctx.push_assert("checked_result", "x.checked_sub(1) == 4294967295");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "checked_sub should detect underflow at 0u32 - 1, got: {:?}",
            result
        );
    })
}

/// checked_mul detects overflow: i32::MAX.checked_mul(2) overflows.
#[test]
fn test_checked_mul_detects_overflow() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new().with_overflow_checks();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assume("x_is_max", "x == 2147483647");
        ctx.push_assert("checked_result", "x.checked_mul(2) > 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "checked_mul should detect overflow at i32::MAX * 2, got: {:?}",
            result
        );
    })
}

// ═══════════════════════════════════════════════════════════════════
// Part 5: Saturating arithmetic methods
//
// These tests verify that saturating_add/sub/mul clamp results to
// the type's max/min on overflow, instead of wrapping.
// ═══════════════════════════════════════════════════════════════════

/// saturating_add: u32::MAX.saturating_add(1) == u32::MAX (clamps to max).
#[test]
fn test_saturating_add_u32_clamps_to_max() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_max", "x == 4294967295");
        ctx.push_assert("clamps_to_max", "x.saturating_add(1) == 4294967295");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX.saturating_add(1) should clamp to u32::MAX, got: {:?}",
            result
        );
    })
}

/// saturating_sub: 0u32.saturating_sub(1) == 0 (clamps to min).
#[test]
fn test_saturating_sub_u32_clamps_to_zero() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_is_zero", "x == 0");
        ctx.push_assert("clamps_to_zero", "x.saturating_sub(1) == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "0u32.saturating_sub(1) should clamp to 0, got: {:?}",
            result
        );
    })
}

/// saturating_add with bounded values: no clamping needed.
#[test]
fn test_saturating_add_bounded_no_clamp() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.push_assume("x_bounded", "x < 1000");
        ctx.push_assert("no_clamp", "x.saturating_add(1) == x + 1");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Bounded saturating_add should equal normal addition, got: {:?}",
            result
        );
    })
}

/// saturating_add: result is always >= both operands for unsigned.
#[test]
fn test_saturating_add_u32_monotonic() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.declare_var_parsed("y", "u32");
        ctx.push_assert("ge_x", "x.saturating_add(y) >= x");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned saturating_add result should always be >= x, got: {:?}",
            result
        );
    })
}

/// saturating_sub: result is always <= receiver for unsigned.
/// Property: saturating_sub(x, y) = max(x - y, 0) ≤ x for all u32 x, y.
/// Currently BV solver times out on this (#1605). Integer-mode fallback
/// (#2262) should allow proving this. Accept Verified or Unknown (timeout);
/// reject Counterexample which would indicate a soundness bug.
#[test]
fn test_saturating_sub_u32_decreasing() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u32");
        ctx.declare_var_parsed("y", "u32");
        ctx.push_assert("le_x", "x.saturating_sub(y) <= x");

        let result = ctx.verify();
        assert!(
            !matches!(result, VerifyResult::Counterexample { .. }),
            "saturating_sub(x, y) <= x is mathematically true — counterexample is a soundness bug: {:?}",
            result
        );
    })
}

// ═══════════════════════════════════════════════════════════════════
// Part 6: 128-bit integer constants (#1607)
//
// Verify that i128/u128 associated constants (MAX, MIN) are encoded
// with correct values using BigInt, not silently truncated to i64.
// ═══════════════════════════════════════════════════════════════════

/// i128::MAX should be 2^127-1, not 2^63-1 (the truncated i64 value).
/// We verify: i128::MAX > i64::MAX (as i128). If the constant were
/// truncated, this would fail.
#[test]
fn test_i128_max_not_truncated_to_i64() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        // i128::MAX (2^127-1) should be strictly greater than the i64::MAX
        // value (2^63-1) when both are represented as 128-bit bitvectors.
        // If i128::MAX were truncated to i64::MAX, this would be false (equal, not greater).
        ctx.push_assert("i128_max_gt_i64_max", "i128::MAX > 9223372036854775807i128");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "i128::MAX should be > i64::MAX (2^63-1), got: {:?}",
            result
        );
    })
}

/// i128::MIN should be -2^127, not -2^63 (the truncated i64 value).
/// Test: i128::MIN + i128::MAX should be -1 (since -2^127 + (2^127-1) = -1).
/// If i128::MIN were truncated to -2^63, the sum would be different.
#[test]
fn test_i128_min_plus_max_equals_neg_one() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i128");
        ctx.push_assume("is_min", "x == i128::MIN");
        // i128::MIN + i128::MAX = -2^127 + (2^127-1) = -1
        ctx.push_assert("sum_is_neg_one", "x + i128::MAX == -1");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "i128::MIN + i128::MAX should equal -1, got: {:?}",
            result
        );
    })
}

/// u128::MAX should be 2^128-1. Test: u128::MAX + 1 wraps to 0.
/// This works regardless of BigInt fix (since -1 mod 2^128 = 2^128-1),
/// but serves as a regression test.
#[test]
fn test_u128_max_plus_one_wraps_to_zero() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "u128");
        ctx.push_assume("is_max", "x == u128::MAX");
        ctx.push_assert("wraps_to_zero", "x + 1 == 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "u128::MAX + 1 should wrap to 0, got: {:?}",
            result
        );
    })
}

/// i128::MAX + 1 should wrap to i128::MIN (wrapping semantics).
#[test]
fn test_i128_max_plus_one_wraps() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i128");
        ctx.push_assume("is_max", "x == i128::MAX");
        // x + 1 should wrap to MIN, not be > 0
        ctx.push_assert("not_positive", "x + 1 <= 0");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "i128::MAX + 1 should wrap to i128::MIN (<= 0), got: {:?}",
            result
        );
    })
}
