// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn union_size_upper_bound() {
    // |A ∪ B| <= |A| + |B|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "b_size", "union_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 5"));
    ctx.push_obligation(ProofObligation::assume("b", "b_size == 3"));
    ctx.push_obligation(ProofObligation::assume("u_def", "union_size == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "upper_bound",
        "union_size <= a_size + b_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "|A ∪ B| = 7 <= 5 + 3");
}

#[test]
fn intersection_size_lower_bound() {
    // |A ∩ B| >= 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inter_size", u32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "inter_size == 2"));
    ctx.push_obligation(ProofObligation::assert("non_neg", "inter_size >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "|A ∩ B| >= 0");
}

#[test]
fn inclusion_exclusion() {
    // |A ∪ B| = |A| + |B| - |A ∩ B|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "b_size", "inter_size", "union_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 5"));
    ctx.push_obligation(ProofObligation::assume("b", "b_size == 3"));
    ctx.push_obligation(ProofObligation::assume("i", "inter_size == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "union_size == a_size + b_size - inter_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "union_size == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "|A ∪ B| = 5 + 3 - 1 = 7");
}

#[test]
fn subset_size_constraint() {
    // A ⊆ B implies |A| <= |B|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "b_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_subset", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 3"));
    ctx.push_obligation(ProofObligation::assume("b", "b_size == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sub_def",
        "is_subset == if a_size <= b_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_sub", "is_subset == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "|A|=3 <= |B|=5 → subset");
}

#[test]
fn difference_size() {
    // |A \ B| = |A| - |A ∩ B|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "inter_size", "diff_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 5"));
    ctx.push_obligation(ProofObligation::assume("i", "inter_size == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "diff_def",
        "diff_size == a_size - inter_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "diff_size == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "|A \\ B| = 5 - 2 = 3");
}

#[test]
fn symmetric_difference_size() {
    // |A △ B| = |A| + |B| - 2*|A ∩ B|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "b_size", "inter_size", "sym_diff"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 5"));
    ctx.push_obligation(ProofObligation::assume("b", "b_size == 4"));
    ctx.push_obligation(ProofObligation::assume("i", "inter_size == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "sym_diff == a_size + b_size - 2 * inter_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "sym_diff == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "|A △ B| = 5 + 4 - 2*2 = 5");
}

#[test]
fn empty_set_union_identity() {
    // A ∪ ∅ = A → |A ∪ ∅| = |A|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "empty_size", "union_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 7"));
    ctx.push_obligation(ProofObligation::assume("e", "empty_size == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "u_def",
        "union_size == a_size + empty_size",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "union_size == a_size"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "A ∪ ∅ = A");
}

#[test]
fn empty_set_intersection_annihilator() {
    // A ∩ ∅ = ∅ → |A ∩ ∅| = 0
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "inter_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 7"));
    ctx.push_obligation(ProofObligation::assume("i_def", "inter_size == 0"));
    ctx.push_obligation(ProofObligation::assert("annihilate", "inter_size == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "A ∩ ∅ = ∅");
}

#[test]
fn complement_size() {
    // |A'| = |U| - |A|
    let mut ctx = VerificationContext::new();
    for v in &["universe_size", "a_size", "complement_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("u", "universe_size == 10"));
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "complement_size == universe_size - a_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "complement_size == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "|A'| = 10 - 4 = 6");
}

#[test]
fn partition_covers_universe() {
    // If A, B, C partition U, then |A| + |B| + |C| = |U|
    let mut ctx = VerificationContext::new();
    for v in &["a_size", "b_size", "c_size", "total", "universe_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "a_size == 3"));
    ctx.push_obligation(ProofObligation::assume("b", "b_size == 4"));
    ctx.push_obligation(ProofObligation::assume("c", "c_size == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == a_size + b_size + c_size",
    ));
    ctx.push_obligation(ProofObligation::assume("u", "universe_size == 12"));
    ctx.push_obligation(ProofObligation::assert("covers", "total == universe_size"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 + 4 + 5 = 12 partition");
}
