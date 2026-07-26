// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pointers_converge() {
    // left starts at 0, right at n-1; they meet in the middle
    let mut ctx = VerificationContext::new();
    for v in &["left", "right", "n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "left == 0"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 10"));
    ctx.push_obligation(ProofObligation::assume("r", "right == n - 1"));
    ctx.push_obligation(ProofObligation::assert("left_le_right", "left <= right"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 <= 9: pointers ordered");
}

#[test]
fn window_size_constant() {
    // Sliding window: right - left == k
    let mut ctx = VerificationContext::new();
    for v in &["left", "right", "k"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "left == 3"));
    ctx.push_obligation(ProofObligation::assume("k_val", "k == 5"));
    ctx.push_obligation(ProofObligation::assume("r_def", "right == left + k"));
    ctx.push_obligation(ProofObligation::assert("window", "right - left == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window size = 5");
}

#[test]
fn advance_left_shrinks_window() {
    let mut ctx = VerificationContext::new();
    for v in &["left", "right", "new_left", "old_size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "left == 2"));
    ctx.push_obligation(ProofObligation::assume("r", "right == 7"));
    ctx.push_obligation(ProofObligation::assume("nl_def", "new_left == left + 1"));
    ctx.push_obligation(ProofObligation::assume(
        "os_def",
        "old_size == right - left",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_size == right - new_left",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shrunk",
        "new_size == old_size - 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "advance left: window shrinks by 1");
}

#[test]
fn advance_right_grows_window() {
    let mut ctx = VerificationContext::new();
    for v in &["left", "right", "new_right", "old_size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "left == 2"));
    ctx.push_obligation(ProofObligation::assume("r", "right == 5"));
    ctx.push_obligation(ProofObligation::assume("nr_def", "new_right == right + 1"));
    ctx.push_obligation(ProofObligation::assume(
        "os_def",
        "old_size == right - left",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_size == new_right - left",
    ));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == old_size + 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "advance right: window grows by 1");
}

#[test]
fn partition_left_right_sum() {
    // All elements processed: left portion + right portion = total
    let mut ctx = VerificationContext::new();
    for v in &["left_count", "right_count", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lc", "left_count == 4"));
    ctx.push_obligation(ProofObligation::assume("rc", "right_count == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == left_count + right_count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4 + 6 = 10 total");
}

#[test]
fn fast_slow_pointer_meeting() {
    // Tortoise and hare: slow moves 1, fast moves 2
    let mut ctx = VerificationContext::new();
    for v in &["slow_pos", "fast_pos", "steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "slow_pos == 3"));
    ctx.push_obligation(ProofObligation::assume("st", "steps == 3"));
    ctx.push_obligation(ProofObligation::assume("f_def", "fast_pos == steps * 2"));
    ctx.push_obligation(ProofObligation::assert("fast_ahead", "fast_pos > slow_pos"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "fast pointer ahead: 6 > 3");
}

#[test]
fn two_sum_indices_different() {
    // Two-sum: find i, j such that arr[i] + arr[j] == target, i != j
    let mut ctx = VerificationContext::new();
    for v in &["i", "j"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 1"));
    ctx.push_obligation(ProofObligation::assume("j_val", "j == 4"));
    ctx.push_obligation(ProofObligation::assert("different", "i != j"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two-sum indices: 1 != 4");
}

#[test]
fn merge_step_advances_one() {
    // Merge: each step advances exactly one pointer
    let mut ctx = VerificationContext::new();
    for v in &["i_before", "j_before", "i_after", "j_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ib", "i_before == 3"));
    ctx.push_obligation(ProofObligation::assume("jb", "j_before == 5"));
    // Left element smaller: advance i
    ctx.push_obligation(ProofObligation::assume("ia_def", "i_after == i_before + 1"));
    ctx.push_obligation(ProofObligation::assume("ja_def", "j_after == j_before"));
    ctx.push_obligation(ProofObligation::assert("i_advanced", "i_after == 4"));
    ctx.push_obligation(ProofObligation::assert("j_same", "j_after == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "merge: advance i, keep j");
}

#[test]
fn dutch_flag_partition_sizes() {
    // Three-way partition: low + mid + high = total
    let mut ctx = VerificationContext::new();
    for v in &["low", "mid", "high", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo", "low == 3"));
    ctx.push_obligation(ProofObligation::assume("mi", "mid == 4"));
    ctx.push_obligation(ProofObligation::assume("hi", "high == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == low + mid + high",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Dutch flag: 3 + 4 + 3 = 10");
}

#[test]
fn palindrome_check_pointers() {
    // Check palindrome: left and right move toward center
    let mut ctx = VerificationContext::new();
    for v in &["left", "right", "length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "left == 0"));
    ctx.push_obligation(ProofObligation::assume("len", "length == 5"));
    ctx.push_obligation(ProofObligation::assume("r_def", "right == length - 1"));
    // After one step: left=1, right=3; gap decreased by 2
    ctx.push_obligation(ProofObligation::assert("gap_is_4", "right - left == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "palindrome: initial gap = 4");
}
