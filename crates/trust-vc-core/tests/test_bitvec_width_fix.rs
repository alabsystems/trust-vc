//! Tests for bit-vector width handling in termination measures
//!
//! This file tests the fix for a bug where u64 >= 0 comparisons were failing
//! because the 0 constant was being created as a 32-bit value instead of 64-bit.
//!
//! Copyright 2026 Andrew Yates
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Licensed under the Apache License, Version 2.0
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

#[test]
fn test_u64_measure_nonneg() {
    // This was the failing case - u64 >= 0 where 0 was being created as 32-bit
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.add_measure_nonneg("n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "u64 >= 0 should verify for termination measure, got: {:?}",
        result
    );
}

#[test]
fn test_i64_measure_nonneg() {
    // i64 can be negative, so >= 0 should not always verify
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("m", trust_vc_core::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.add_measure_nonneg("m");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "i64 >= 0 should have counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_u32_measure_nonneg() {
    // u32 should also work correctly
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("k", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.add_measure_nonneg("k");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "u32 >= 0 should verify for termination measure, got: {:?}",
        result
    );
}

#[test]
fn test_mixed_width_measure_decreases() {
    // Test termination measure with decreases
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed(
        "n_entry",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );
    ctx.declare_var_typed(
        "n_recursive",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );

    // Add assumptions that make the decrease valid
    ctx.push_obligation(ProofObligation::assume("entry_positive", "n_entry > 0"));
    ctx.push_obligation(ProofObligation::assume(
        "recursive_less",
        "n_recursive == n_entry - 1",
    ));

    ctx.add_measure_decreases("n", "n_entry", "n_recursive");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Measure decrease with valid assumptions should verify, got: {:?}",
        result
    );
}

/// Regression test for #1726: mixed-width measure expression through ay.
///
/// Simulates `loop_decreases!(n - i)` where `n: u64` and `i: u32`.
/// After the `infer_measure_type` fix, the entry variable is declared at
/// the widest type (u64), preventing sort mismatch errors in ay.
///
/// DISCRIMINATING: if the entry variable were declared as u32 (the old
/// first-match behavior when `i` appears before `n`), the comparison
/// `measure_new < measure_entry` would produce a ay sort mismatch
/// (BV32 vs BV64) or incorrect truncation.
#[test]
fn test_mixed_width_decreases_u32_u64_through_ay() {
    // Scenario: loop counting i (u32) up to n (u64).
    // Measure: n - i (should decrease each iteration).
    // Entry variable declared at u64 (widest) per infer_measure_type fix.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    // Entry and recursive measure values at the WIDEST type (u64)
    ctx.declare_var_typed(
        "measure_entry",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );
    ctx.declare_var_typed(
        "measure_recursive",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );

    // Loop setup: n > 0, i starts at 0, measure = n - i
    ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));
    ctx.push_obligation(ProofObligation::assume("i_bounded", "i < n"));
    // Entry measure: n - i at the start of this iteration
    ctx.push_obligation(ProofObligation::assume(
        "entry_value",
        "measure_entry == n - i",
    ));
    // Recursive measure: n - (i + 1) after incrementing i
    ctx.push_obligation(ProofObligation::assume(
        "recursive_value",
        "measure_recursive == n - i - 1",
    ));

    // The measure must strictly decrease
    ctx.add_measure_decreases("measure", "measure_entry", "measure_recursive");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Mixed-width (u32/u64) measure decrease through ay should verify \
         without sort mismatch — entry declared at widest type. Got: {:?}",
        result
    );
}

/// Test mixed-width decreases where the narrow type appears first in the
/// expression (the exact scenario from the #1726 bug report: `i - n` where
/// `i: u32` is encountered before `n: u64`).
#[test]
fn test_mixed_width_decreases_narrow_first_through_ay() {
    let mut ctx = VerificationContext::new();
    // Declare narrow variable first (the pre-fix ordering that triggered the bug)
    ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));
    // Entry variable at the WIDEST type — this is the fix
    ctx.declare_var_typed(
        "entry",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );
    ctx.declare_var_typed(
        "recursive",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );

    ctx.push_obligation(ProofObligation::assume("n_bound", "n > 1"));
    ctx.push_obligation(ProofObligation::assume("i_bound", "i < n"));
    ctx.push_obligation(ProofObligation::assume("entry_val", "entry == n - i"));
    ctx.push_obligation(ProofObligation::assume(
        "recursive_val",
        "recursive == n - i - 1",
    ));

    ctx.add_measure_decreases("mixed", "entry", "recursive");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Narrow-first mixed-width (u32 before u64) measure decrease \
         should verify through ay. Got: {:?}",
        result
    );
}

#[test]
fn test_large_constant_comparison() {
    // Test that large constants get the correct bit width
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "large_n",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"),
    );

    // 4294967296 is 2^32, requires 64-bit
    ctx.push_obligation(ProofObligation::assert(
        "large_check",
        "large_n >= 4294967296",
    ));

    let result = ctx.verify();
    // This should produce a counterexample (there are u64 values < 2^32)
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Large constant comparison should produce counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_u128_measure_nonneg() {
    // Test 128-bit integers
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "huge",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("u128"),
    );
    ctx.add_measure_nonneg("huge");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "u128 >= 0 should verify for termination measure, got: {:?}",
        result
    );
}

#[test]
fn test_comparison_with_zero_various_widths() {
    // Test that >= 0 works for all unsigned integer widths
    let widths = vec![
        ("u8", 8),
        ("u16", 16),
        ("u32", 32),
        ("u64", 64),
        ("u128", 128),
    ];

    for (ty, _width) in widths {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque(ty));
        ctx.push_obligation(ProofObligation::assert("nonneg", "n >= 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "{} >= 0 should verify, got: {:?}",
            ty,
            result
        );
    }
}

#[test]
fn test_signed_integer_comparisons() {
    // Test that signed integers handle comparisons correctly
    let signed_types = vec!["i8", "i16", "i32", "i64", "i128"];

    for ty in signed_types {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque(ty));
        ctx.push_obligation(ProofObligation::assert("nonneg", "n >= 0"));

        let result = ctx.verify();
        // Signed integers CAN be negative, so this should produce counterexample
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{} >= 0 should produce counterexample for signed types, got: {:?}",
            ty,
            result
        );
    }
}

#[test]
fn test_other_comparison_operators() {
    // Test that other comparison operators also handle bit widths correctly
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));

    // Test <= operator
    ctx.push_obligation(ProofObligation::assert("le_check", "x <= 1000000000000"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "u64 <= large_constant should produce counterexample"
    );

    // Test == operator with mixed widths
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));
    ctx2.push_obligation(ProofObligation::assert("eq_check", "y == 0"));
    let result2 = ctx2.verify();
    assert!(
        matches!(result2, VerifyResult::Counterexample { .. }),
        "u64 == 0 should produce counterexample"
    );

    // Test != operator
    let mut ctx3 = VerificationContext::new();
    ctx3.declare_var_typed("z", trust_vc_core::ir::TrustVcType::parse_or_opaque("u64"));
    ctx3.push_obligation(ProofObligation::assert("ne_check", "z != 0"));
    let result3 = ctx3.verify();
    assert!(
        matches!(result3, VerifyResult::Counterexample { .. }),
        "u64 != 0 should produce counterexample (when z could be 0)"
    );
}

#[test]
fn test_boundary_values() {
    // Test boundary values for different bit widths
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));

    // u8 max is 255
    ctx.push_obligation(ProofObligation::assert("u8_max", "x <= 255"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "u8 <= 255 should verify (all u8 values are <= 255)"
    );

    // Test u16 boundary
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("u16"));
    ctx2.push_obligation(ProofObligation::assert("u16_boundary", "y < 65536"));
    let result2 = ctx2.verify();
    assert!(
        matches!(result2, VerifyResult::Verified),
        "u16 < 65536 should verify (max u16 is 65535)"
    );

    // Test signed boundary
    let mut ctx3 = VerificationContext::new();
    ctx3.declare_var_typed("z", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx3.push_obligation(ProofObligation::assert("i8_range", "z >= -128 && z <= 127"));
    let result3 = ctx3.verify();
    assert!(
        matches!(result3, VerifyResult::Verified),
        "i8 range check should verify"
    );
}

/// Test that negative literals propagate width hints through Unary(Neg).
///
/// Exercises the fix for #1671: `-128` is parsed as Unary(Neg, Lit(128)).
/// Without the fix, the hint from the left operand is lost at the Unary
/// boundary, and `infer_int_width()` may pick a different width (here 32,
/// since i32 vars outnumber i8 vars). With the fix, the hint flows through
/// the negation to produce correctly-sized BV literals.
#[test]
fn test_negative_literal_hint_propagation_mixed_types() {
    // Mixed types: three i32 vars force infer_int_width() → 32.
    // The i8 var `y` should still compare correctly against -128.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("c", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));

    // i8 range: [-128, 127]. y >= -128 should always hold.
    // Without hint propagation, -128 may encode at wrong width.
    ctx.push_obligation(ProofObligation::assert("i8_min_bound", "y >= -128"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "i8 >= -128 should verify even with mixed types (infer_int_width=32), got: {:?}",
        result
    );
}

/// Test negative literal at i16 boundary with mixed types.
///
/// Regression guard for #1671: ensures -32768 (i16 min) works when
/// infer_int_width() would pick 8 (majority i8 vars).
#[test]
fn test_negative_literal_hint_i16_with_i8_majority() {
    // Three i8 vars force infer_int_width() → 8.
    // The i16 var `x` should still handle -32768 correctly via hint.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.declare_var_typed("q", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.declare_var_typed("r", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i16"));

    // i16 range: [-32768, 32767]. x >= -32768 should always hold.
    ctx.push_obligation(ProofObligation::assert("i16_min_bound", "x >= -32768"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "i16 >= -32768 should verify with i8 majority context, got: {:?}",
        result
    );
}

/// Test that simple i8 == -128 comparison verifies with assumption.
///
/// This is the canonical case from #1671: if y == -128, then y == -128.
/// Without hint propagation through Unary(Neg), the two -128 literals
/// may encode at different widths (one via hint, one standalone).
#[test]
fn test_neg_literal_equality_i8() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("is_min", "y == -128"));
    ctx.push_obligation(ProofObligation::assert("check_min", "y == -128"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "i8 == -128 with assumption should verify, got: {:?}",
        result
    );
}

/// Test that wrapping_add result is tracked in term_widths for width coercion.
///
/// DISCRIMINATING for #1649: x.wrapping_add(1) produces a u8 BV result.
/// When compared against a u32 variable y, coerce_bv_widths must extend the
/// u8 result to u32. Without term_widths tracking, the result has no width
/// info and coerce_bv_widths falls through to the no-op branch, causing
/// either a ay sort mismatch error or incorrect comparison semantics.
#[test]
fn test_wrapping_add_result_width_tracked() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < 200"));
    ctx.push_obligation(ProofObligation::assume("y_large", "y == 1000"));
    // wrapping_add result (u8) compared with y (u32) — requires width coercion.
    // x < 200 and x is u8 [0,255], so x.wrapping_add(1) is in [1,256] mod 256 = [0,255].
    // y == 1000 > 255 >= any u8 value, so this should always verify.
    ctx.push_obligation(ProofObligation::assert(
        "method_result_lt_y",
        "x.wrapping_add(1) < y",
    ));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "wrapping_add(u8) < u32 should verify with width coercion, got: {:?}",
        result
    );
}

// ========================================================================
// BV literal hint propagation tests (#1653, design doc test plan)
//
// These tests exercise the context-aware width resolution from
// designs/2026-02-11-bv-literal-encoding-strategy.md Steps 1-3.
// Each test is DISCRIMINATING: it would fail if the hint propagation
// were removed and only the context-free infer_int_width() heuristic
// were used.
// ========================================================================

/// DISCRIMINATING for #1653 Step 2 (binary op hint): widening test.
///
/// 65536 fits in u32 (< 2^32). The variable x: u32 provides a width hint
/// of 32 bits to the literal via parse_syn_expr_with_hint. The literal
/// becomes BV32(65536), matching x's sort.
///
/// Without hint (infer_int_width heuristic with u8-majority context):
/// infer_int_width() → 8. fits_in_bv(65536, 8) → false → widen to BV16(65536).
/// But BV16(65536) = BV16(0) due to 16-bit wraparound! x (u32) would be
/// coerced, but the literal value is already wrong.
///
/// With hint: left side x has width 32 → hint (32, false) propagated to
/// literal → BV32(65536), which is correct.
#[test]
fn test_hint_widening_u32_eq_65536() {
    let mut ctx = VerificationContext::new();
    // u8-majority context forces infer_int_width() → 8 without hints
    ctx.declare_var_typed("p", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("q", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("r", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("p_val", "p == 0"));
    ctx.push_obligation(ProofObligation::assume("q_val", "q == 0"));
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 0"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 65536"));
    // If literal 65536 is correctly BV32(65536), this verifies.
    // If 65536 wraps to 0 in BV16 or BV8, this fails.
    ctx.push_obligation(ProofObligation::assert("check", "x == 65536"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "u32 == 65536 should verify with u8-majority context \
         (hint propagation gives correct BV32 width), got: {:?}",
        result
    );
}

/// DISCRIMINATING for #1653 Step 2 (binary op hint) + casts-bitvec literal-width
/// SOUNDNESS (round-3).
///
/// `128` in an `i8` context: the signed range is `[-128, 127]`, so `128` is NOT
/// representable as `i8`. The predecessor of this test asserted that `x: i8 == 128`
/// should make `x < 0` VERIFY, relying on `128` wrapping to `-128` in BV8 — i.e.
/// on the literal being silently aliased to a DIFFERENT value. That aliasing was
/// the casts-bitvec soundness hole: `x == 128` would be rewritten to `x == -128`,
/// manufacturing a false `Verified` for `x < 0` over a precondition that is in
/// fact unsatisfiable for any `i8`.
///
/// With the fix, `128` is encoded value-preservingly (widened so it stays `128`),
/// so `x: i8 == 128` is correctly recognized as a CONTRADICTORY assumption (no
/// `i8` equals `128`). trust-vc fail-closes with `Unknown(VacuousTruth)` rather
/// than aliasing `128` to `-128` — the `x < 0` goal must NOT verify through the
/// wrap. (A vacuous precondition fail-closing is strictly more conservative than
/// the unsound `Verified`.)
#[test]
fn test_i8_eq_128_is_contradictory_not_wrapped() {
    let mut ctx = VerificationContext::new();
    // i32-majority context forces infer_int_width() → 32 without hints.
    ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("c", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0"));
    // `x == 128` must NOT be aliased to `x == -128`; it is contradictory for i8.
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 128"));
    ctx.push_obligation(ProofObligation::assert("negative", "x < 0"));
    let result = ctx.verify();
    assert!(
        !matches!(result, VerifyResult::Verified),
        "UNSOUND: x: i8 == 128 must NOT verify x < 0 by wrapping 128 to -128; \
         the precondition is contradictory for i8 and must fail closed. Got: {:?}",
        result
    );
}

/// CONTROL for #1653 Step 2 (binary op hint): the BV8 hint propagation itself
/// still works for an IN-RANGE literal. `x: i8 == 100` (100 fits i8) with an
/// i32-majority context: the left operand's width-8 hint must keep `100` at BV8
/// so `x > 0` verifies (no over-rejection from spurious widening).
#[test]
fn test_hint_in_range_i8_eq_100_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("c", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "in-range i8 == 100 should verify x > 0 (hint keeps BV8, no over-rejection). Got: {:?}",
        result
    );
}

/// DISCRIMINATING for #1653 Step 2: overflow protection.
///
/// 256 does NOT fit in u8 (max 255). Even with hint width 8 from x: u8,
/// fits_in_bv(256, 8) → false (256 > unsigned max 255 for 8-bit).
/// parse_lit_with_hint must widen to min_bv_width_for_value(256) = 16.
/// Then coerce_bv_widths extends x (u8) to BV16 for comparison.
///
/// If the overflow protection is broken (literal forced to BV8), 256
/// becomes BV8(0) and the assertion x != 256 would produce a spurious
/// counterexample for x == 0 (since BV8(0) == BV8(0)).
///
/// With correct overflow protection: BV16(256) != any BV16(x) where
/// x is zero-extended from u8 [0,255]. Verifies because 256 > 255.
#[test]
fn test_hint_overflow_protection_u8_eq_256() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    // x is a free u8 variable [0, 255]. 256 > 255 so x can never equal 256.
    // Without overflow protection (256 truncated to BV8(0)), x could be 0 → counterexample.
    ctx.push_obligation(ProofObligation::assert("never_256", "x != 256"));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "u8 != 256 should verify: 256 exceeds u8 range, overflow protection \
         must widen to BV16(256). Got: {:?}",
        result
    );
}

/// DISCRIMINATING for #1653 Step 3 (let-binding hint): type annotation
/// provides width hint to initializer literal.
///
/// `let y: u64 = 0` — the type annotation u64 provides a hint of (64, false)
/// to the literal 0. Without this, in a u8-majority context, 0 would get
/// BV8(0). Subsequent comparison y < big_value would have sort mismatches
/// or incorrect results after coercion.
///
/// With hint: 0 becomes BV64(0), matching the declared u64 type.
/// The assertion y < 2^32+1 is trivially true since y=0.
#[test]
fn test_hint_let_binding_u64_type_annotation() {
    let mut ctx = VerificationContext::new();
    // u8-majority context to make infer_int_width() → 8
    ctx.declare_var_typed("p", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("q", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("r", trust_vc_core::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("p_val", "p == 0"));
    ctx.push_obligation(ProofObligation::assume("q_val", "q == 0"));
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 0"));
    // Use a block with let-binding. The type annotation provides the hint.
    ctx.push_obligation(ProofObligation::assert(
        "let_hint",
        "{ let y: u64 = 0; y < 4294967297 }",
    ));
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "let y: u64 = 0; y < 2^32+1 should verify with let-binding hint \
         (u64 width from type annotation). Got: {:?}",
        result
    );
}
