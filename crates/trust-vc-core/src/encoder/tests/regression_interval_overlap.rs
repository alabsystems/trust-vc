// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn intervals_overlap() {
    let mut ctx = VerificationContext::new();
    for v in &["a_lo", "a_hi", "b_lo", "b_hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("overlaps", i32_ty());
    ctx.push_obligation(ProofObligation::assume("al", "a_lo == 2"));
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 8"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 5"));
    ctx.push_obligation(ProofObligation::assume("bh", "b_hi == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "overlap_def",
        "overlaps == if a_lo < b_hi && b_lo < a_hi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("they_overlap", "overlaps == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "[2,8) and [5,12) overlap");
}

#[test]
fn intervals_disjoint() {
    let mut ctx = VerificationContext::new();
    for v in &["a_lo", "a_hi", "b_lo", "b_hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("overlaps", i32_ty());
    ctx.push_obligation(ProofObligation::assume("al", "a_lo == 1"));
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 5"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 7"));
    ctx.push_obligation(ProofObligation::assume("bh", "b_hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "overlap_def",
        "overlaps == if a_lo < b_hi && b_lo < a_hi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_overlap", "overlaps == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "[1,5) and [7,10) don't overlap");
}

#[test]
fn interval_contains_point() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "point"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("contained", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 3"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("pt", "point == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "contained_def",
        "contained == if point >= lo && point < hi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_in", "contained == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 in [3, 10)");
}

#[test]
fn interval_intersection_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "a_lo", "a_hi", "b_lo", "b_hi", "int_lo", "int_hi", "int_len",
    ] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("al", "a_lo == 2"));
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 8"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 5"));
    ctx.push_obligation(ProofObligation::assume("bh", "b_hi == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "int_lo_def",
        "int_lo == if a_lo >= b_lo { a_lo } else { b_lo }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "int_hi_def",
        "int_hi == if a_hi <= b_hi { a_hi } else { b_hi }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "int_len_def",
        "int_len == int_hi - int_lo",
    ));
    ctx.push_obligation(ProofObligation::assert("len_is_3", "int_len == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "[2,8) ∩ [5,12) = [5,8), length 3");
}

#[test]
fn interval_union_span() {
    let mut ctx = VerificationContext::new();
    for v in &["a_lo", "a_hi", "b_lo", "b_hi", "u_lo", "u_hi", "u_len"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("al", "a_lo == 2"));
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 8"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 5"));
    ctx.push_obligation(ProofObligation::assume("bh", "b_hi == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "u_lo_def",
        "u_lo == if a_lo <= b_lo { a_lo } else { b_lo }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "u_hi_def",
        "u_hi == if a_hi >= b_hi { a_hi } else { b_hi }",
    ));
    ctx.push_obligation(ProofObligation::assume("u_len_def", "u_len == u_hi - u_lo"));
    ctx.push_obligation(ProofObligation::assert("span_is_10", "u_len == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "span of [2,8) ∪ [5,12) = [2,12), length 10");
}

#[test]
fn interval_subset() {
    let mut ctx = VerificationContext::new();
    for v in &["a_lo", "a_hi", "b_lo", "b_hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("is_subset", i32_ty());
    ctx.push_obligation(ProofObligation::assume("al", "a_lo == 3"));
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 7"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 1"));
    ctx.push_obligation(ProofObligation::assume("bh", "b_hi == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "subset_def",
        "is_subset == if a_lo >= b_lo && a_hi <= b_hi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("a_in_b", "is_subset == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "[3,7) ⊂ [1,10)");
}

#[test]
fn adjacent_intervals_no_gap() {
    let mut ctx = VerificationContext::new();
    for v in &["a_hi", "b_lo"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("adjacent", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 5"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "adj_def",
        "adjacent == if a_hi == b_lo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_adjacent", "adjacent == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "[_,5) and [5,_) are adjacent");
}

#[test]
fn interval_split_preserves_total() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid", "left_len", "right_len", "total_len"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 2"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("mid_val", "mid == 6"));
    ctx.push_obligation(ProofObligation::assume("left_def", "left_len == mid - lo"));
    ctx.push_obligation(ProofObligation::assume(
        "right_def",
        "right_len == hi - mid",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total_len == left_len + right_len",
    ));
    ctx.push_obligation(ProofObligation::assert("conserved", "total_len == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "split [2,10) at 6: 4 + 4 = 8");
}

#[test]
fn merge_sorted_intervals() {
    // Two sorted non-overlapping intervals [1,3) [5,8) → total = 2 + 3 = 5
    let mut ctx = VerificationContext::new();
    for v in &["a_lo", "a_hi", "b_lo", "b_hi", "a_len", "b_len", "total"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("al", "a_lo == 1"));
    ctx.push_obligation(ProofObligation::assume("ah", "a_hi == 3"));
    ctx.push_obligation(ProofObligation::assume("bl", "b_lo == 5"));
    ctx.push_obligation(ProofObligation::assume("bh", "b_hi == 8"));
    ctx.push_obligation(ProofObligation::assume("a_len_def", "a_len == a_hi - a_lo"));
    ctx.push_obligation(ProofObligation::assume("b_len_def", "b_len == b_hi - b_lo"));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total == a_len + b_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "total == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total coverage: |[1,3)| + |[5,8)| = 5");
}

#[test]
fn point_outside_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "point"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("contained", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 3"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("pt", "point == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "contained_def",
        "contained == if point >= lo && point < hi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_out", "contained == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "15 not in [3, 10)");
}
