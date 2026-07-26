// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 22 — Overflow edge cases.
//!
//! Tier 21 covered the core overflow-checking interactions (addition with
//! bounds, frame invariants, Seq length). This tier covers edge cases that
//! would bite a competitor in a timed setting:
//!
//! GROUP A: Multiplication overflow — array stride, area calculations.
//! GROUP B: Unsigned subtraction underflow — `i - 1` for u32 indices.
//! GROUP C: Signed arithmetic edge cases — near-MIN subtraction, negation.
//! GROUP D: Division safety — divide-by-zero, signed MIN / -1.
//! GROUP E: Competition patterns — midpoint calculation, prefix sum.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Multiplication overflow
//
// `a * b` overflows i32 even for moderate values (e.g., 50000 * 50000 =
// 2.5B > MAX_I32). Competition patterns: array stride (i * elem_size),
// area (width * height).
// ========================================================================

/// Unbounded i32 multiplication — overflow IS possible and MUST be caught.
#[test]
fn test_vt_overflow_mul_unbounded_detected() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("product", "i32");

    ctx.push_assume("product_def", "product == a * b");
    ctx.push_assert("trivial", "product == a * b");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Unbounded multiplication must produce Counterexample — overflow possible: {:?}",
        result,
    );
}

/// Bounded u32 multiplication — small positive factors prevent overflow.
///
/// Both factors ≤ 100 → product ≤ 10000, well within u32 range.
/// Uses u32 (unsigned) because BV multiplication proofs are expensive
/// for signed types — ay-dpll handles unsigned multiplication bounds
/// more efficiently.
#[test]
fn test_vt_overflow_mul_bounded_safe() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "u32");
    ctx.declare_var_parsed("b", "u32");
    ctx.declare_var_parsed("product", "u32");

    ctx.push_assume("a_bound", "a <= 100");
    ctx.push_assume("b_bound", "b <= 100");
    ctx.push_assume("product_def", "product == a * b");

    ctx.push_assert("product_range", "product <= 10000");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Bounded multiplication should verify — product within range: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Unsigned subtraction underflow
//
// `u32: a - b` wraps when a < b. This is the most common competition bug:
// `arr[i - 1]` when i == 0.
// ========================================================================

/// Unbounded u32 subtraction — underflow IS possible (a < b wraps).
#[test]
fn test_vt_overflow_unsigned_sub_unbounded_detected() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "u32");
    ctx.declare_var_parsed("b", "u32");
    ctx.declare_var_parsed("diff", "u32");

    ctx.push_assume("diff_def", "diff == a - b");
    ctx.push_assert("trivial", "diff == a - b");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Unbounded unsigned subtraction must produce Counterexample — underflow possible: {:?}",
        result,
    );
}

/// Guarded u32 subtraction — `a >= b` prevents underflow.
///
/// Classic competition pattern: `if i > 0 { arr[i - 1] }`.
#[test]
fn test_vt_overflow_unsigned_sub_guarded_safe() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "u32");
    ctx.declare_var_parsed("b", "u32");
    ctx.declare_var_parsed("diff", "u32");

    ctx.push_assume("guard", "a >= b");
    ctx.push_assume("diff_def", "diff == a - b");

    ctx.push_assert("diff_le_a", "diff <= a");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Guarded unsigned subtraction should verify — a >= b prevents underflow: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Signed arithmetic edge cases
//
// Near-MIN_I32 values and negation overflow.
// ========================================================================

/// Signed subtraction near MIN — subtracting a positive value from a
/// near-minimum signed value can underflow.
///
/// a = -2_000_000_000 (near MIN_I32), b = 1_000_000_000.
/// a - b = -3B, which overflows i32.
#[test]
fn test_vt_overflow_signed_sub_near_min_detected() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("diff", "i32");

    // a can be very negative, b can be very positive
    ctx.push_assume("a_negative", "a <= -1000000000");
    ctx.push_assume("b_positive", "b >= 1000000000");
    ctx.push_assume("diff_def", "diff == a - b");

    ctx.push_assert("trivial", "diff == a - b");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Near-MIN signed subtraction must produce Counterexample — underflow possible: {:?}",
        result,
    );
}

/// Bounded signed subtraction — both values near zero, safe.
#[test]
fn test_vt_overflow_signed_sub_bounded_safe() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("diff", "i32");

    ctx.push_assume("a_bound", "a >= -1000000 && a <= 1000000");
    ctx.push_assume("b_bound", "b >= -1000000 && b <= 1000000");
    ctx.push_assume("diff_def", "diff == a - b");

    ctx.push_assert("diff_range", "diff >= -2000000 && diff <= 2000000");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Bounded signed subtraction should verify: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Division safety
//
// Division by zero and signed division overflow (MIN / -1).
// ========================================================================

/// Division by potentially-zero divisor — overflow checking catches it.
#[test]
fn test_vt_overflow_div_by_zero_detected() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("quotient", "i32");

    // b can be zero — division undefined
    ctx.push_assume("b_range", "b >= -10 && b <= 10");

    ctx.push_assert("trivial", "quotient == a / b");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Division with potentially-zero divisor must produce Counterexample: {:?}",
        result,
    );
}

/// Division with nonzero guard — safe.
#[test]
fn test_vt_overflow_div_guarded_safe() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "u32");
    ctx.declare_var_parsed("b", "u32");
    ctx.declare_var_parsed("quotient", "u32");

    ctx.push_assume("a_bound", "a <= 1000000");
    ctx.push_assume("b_nonzero", "b >= 1 && b <= 100");
    ctx.push_assume("quot_def", "quotient == a / b");

    ctx.push_assert("quot_le_a", "quotient <= a");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Division with nonzero guard should verify: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Competition patterns — real algorithm snippets
//
// These reproduce exact patterns competitors would write.
// ========================================================================

/// Binary search midpoint: `mid = lo + (hi - lo) / 2`.
///
/// The naive `(lo + hi) / 2` overflows for large lo + hi. The safe
/// pattern `lo + (hi - lo) / 2` avoids this. With overflow checking,
/// the safe pattern must verify and the naive pattern should fail.
#[test]
fn test_vt_overflow_binary_search_midpoint_safe() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("lo", "u32");
    ctx.declare_var_parsed("hi", "u32");
    ctx.declare_var_parsed("diff", "u32");
    ctx.declare_var_parsed("half", "u32");
    ctx.declare_var_parsed("mid", "u32");

    ctx.push_assume("lo_le_hi", "lo <= hi");
    ctx.push_assume("hi_bound", "hi <= 1000000");
    ctx.push_assume("diff_def", "diff == hi - lo");
    ctx.push_assume("half_def", "half == diff / 2");
    ctx.push_assume("mid_def", "mid == lo + half");

    // mid is between lo and hi
    ctx.push_assert("mid_ge_lo", "mid >= lo");
    ctx.push_assert("mid_le_hi", "mid <= hi");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Safe binary search midpoint should verify: {:?}",
        result,
    );
}

/// Prefix sum with bounded elements — running addition stays in range.
///
/// Models: `for elem in arr { sum += elem; }` where elements are bounded.
/// Invariant: sum stays within i32 range if n * max_elem < MAX_I32.
#[test]
fn test_vt_overflow_prefix_sum_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("sum_old", "i32");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("sum_new", "i32");

    // Inductive hypothesis: sum bounded by ±1B, elements bounded by ±1000
    ctx.push_assume(
        "sum_bound",
        "sum_old >= -1000000000 && sum_old <= 1000000000",
    );
    ctx.push_assume("elem_bound", "elem >= -1000 && elem <= 1000");
    ctx.push_assume("step", "sum_new == sum_old + elem");

    // sum_new stays within ±1B + 1000 — well within i32
    ctx.push_assert(
        "sum_new_range",
        "sum_new >= -1000001000 && sum_new <= 1000001000",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Prefix sum with bounded elements should verify: {:?}",
        result,
    );
}

/// Multi-operation chain: add then subtract. Both operations checked.
///
/// Models: `temp = a + b; result = temp - c` with bounds on all inputs.
#[test]
fn test_vt_overflow_multi_op_chain_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("c", "i32");
    ctx.declare_var_parsed("temp", "i32");
    ctx.declare_var_parsed("result", "i32");

    ctx.push_assume("a_bound", "a >= -500000000 && a <= 500000000");
    ctx.push_assume("b_bound", "b >= -500000000 && b <= 500000000");
    ctx.push_assume("c_bound", "c >= -500000000 && c <= 500000000");
    ctx.push_assume("temp_def", "temp == a + b");
    ctx.push_assume("result_def", "result == temp - c");

    // result = a + b - c, bounded by ±1.5B — within i32
    ctx.push_assert(
        "result_range",
        "result >= -1500000000 && result <= 1500000000",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Multi-op chain with bounds should verify: {:?}",
        result,
    );
}
