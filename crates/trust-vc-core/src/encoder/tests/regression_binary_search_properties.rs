// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn midpoint_between_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 3"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("mid_ge_lo", "mid >= lo"));
    ctx.push_obligation(ProofObligation::assert("mid_lt_hi", "mid < hi"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint in [lo, hi)");
}

#[test]
fn midpoint_value() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "mid == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint of [0,10) = 5");
}

#[test]
fn range_shrinks_left() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid", "new_lo", "old_range", "new_range"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assume("new_lo_def", "new_lo == mid + 1"));
    ctx.push_obligation(ProofObligation::assume(
        "old_range_def",
        "old_range == hi - lo",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_range_def",
        "new_range == hi - new_lo",
    ));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_range < old_range"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "moving lo to mid+1 shrinks range");
}

#[test]
fn range_shrinks_right() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid", "new_hi", "old_range", "new_range"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assume("new_hi_def", "new_hi == mid"));
    ctx.push_obligation(ProofObligation::assume(
        "old_range_def",
        "old_range == hi - lo",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_range_def",
        "new_range == new_hi - lo",
    ));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_range < old_range"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "moving hi to mid shrinks range");
}

#[test]
fn single_element_found() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 5"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("mid_is_lo", "mid == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "single element: mid == lo");
}

#[test]
fn three_steps_sufficient_for_8() {
    // Binary search of 8 elements: at most 3 steps (log2(8) = 3)
    let mut ctx = VerificationContext::new();
    for v in &[
        "lo0", "hi0", "mid0", "lo1", "hi1", "mid1", "lo2", "hi2", "mid2",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l0", "lo0 == 0"));
    ctx.push_obligation(ProofObligation::assume("h0", "hi0 == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "m0",
        "mid0 == lo0 + (hi0 - lo0) / 2",
    ));
    // Step 1: go right
    ctx.push_obligation(ProofObligation::assume("l1", "lo1 == mid0 + 1"));
    ctx.push_obligation(ProofObligation::assume("h1", "hi1 == hi0"));
    ctx.push_obligation(ProofObligation::assume(
        "m1",
        "mid1 == lo1 + (hi1 - lo1) / 2",
    ));
    // Step 2: go left
    ctx.push_obligation(ProofObligation::assume("l2", "lo2 == lo1"));
    ctx.push_obligation(ProofObligation::assume("h2", "hi2 == mid1"));
    ctx.push_obligation(ProofObligation::assume(
        "m2",
        "mid2 == lo2 + (hi2 - lo2) / 2",
    ));
    // After 3 steps, range is at most 1
    ctx.push_obligation(ProofObligation::assert("narrow", "hi2 - lo2 <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "binary search: 3 steps narrows 8 to <=1");
}

#[test]
fn safe_midpoint_no_overflow() {
    // lo + (hi - lo) / 2 doesn't overflow even for large values
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "diff", "half", "mid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 2000000000"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 4000000000"));
    ctx.push_obligation(ProofObligation::assume("diff_def", "diff == hi - lo"));
    ctx.push_obligation(ProofObligation::assume("half_def", "half == diff / 2"));
    ctx.push_obligation(ProofObligation::assume("mid_def", "mid == lo + half"));
    ctx.push_obligation(ProofObligation::assert("is_3b", "mid == 3000000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "safe midpoint for large u32 values");
}

#[test]
fn bounds_maintained_left() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid", "new_lo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 2"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assume("new_lo_def", "new_lo == mid + 1"));
    ctx.push_obligation(ProofObligation::assert("still_valid", "new_lo <= hi"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "lo = mid+1 maintains lo <= hi");
}

#[test]
fn empty_range_terminates() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_continue", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 5"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "cont_def",
        "should_continue == if lo < hi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stops", "should_continue == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lo == hi means search terminates");
}

#[test]
fn found_element_index_in_range() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "found_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume("found_val", "found_idx == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "found_idx >= lo && found_idx < hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "found index 42 in [0, 100)");
}
