// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn swap_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("a_orig", i32_ty());
    ctx.declare_var_typed("b_orig", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "swap",
        "a_new == b_orig && b_new == a_orig",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "swap_result",
        "a_new == 10 && b_new == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap should exchange 5 and 10");
}

#[test]
fn swap_preserves_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("a_orig", i32_ty());
    ctx.declare_var_typed("b_orig", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "swap",
        "a_new == b_orig && b_new == a_orig",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sum_preserved",
        "a_new + b_new == a + b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap should preserve the sum");
}

#[test]
fn double_swap_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("t1", i32_ty());
    ctx.declare_var_typed("t2", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("first_swap", "t1 == b && t2 == a"));
    ctx.push_obligation(ProofObligation::assume(
        "second_swap",
        "a_new == t2 && b_new == t1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "identity",
        "a_new == a && b_new == b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swapping twice should restore the original values");
}

#[test]
fn xor_swap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("a_orig", u32_ty());
    ctx.declare_var_typed("b_orig", u32_ty());
    ctx.declare_var_typed("step1", u32_ty());
    ctx.declare_var_typed("step2", u32_ty());
    ctx.declare_var_typed("step3", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "xor_steps",
        "step1 == (a_orig ^ b_orig) && step2 == (b_orig ^ step1) && step3 == (step1 ^ step2)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xor_swap_result",
        "step2 == a_orig && step3 == b_orig",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "xor swap should exchange the original u32 values");
}

#[test]
fn rotate_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.declare_var_typed("c_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "rotate",
        "a_new == b && b_new == c && c_new == a",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rotate_result",
        "a_new == 2 && b_new == 3 && c_new == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "three-way rotation should shift values left");
}

#[test]
fn swap_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("ordered", "a <= b"));
    ctx.push_obligation(ProofObligation::assert("max_order", "b >= a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ordered values should preserve the max relation");
}

#[test]
fn swap_preserves_product() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("a_orig", i32_ty());
    ctx.declare_var_typed("b_orig", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "swap",
        "a_new == b_orig && b_new == a_orig",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "product_preserved",
        "a_new * b_new == a * b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap should preserve the product");
}

#[test]
fn swap_difference() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("a_orig", i32_ty());
    ctx.declare_var_typed("b_orig", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "swap",
        "a_new == b_orig && b_new == a_orig",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "difference_preserved",
        "b_new - a_new == a - b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swapping should preserve the directed difference");
}

#[test]
fn conditional_swap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("a_orig", i32_ty());
    ctx.declare_var_typed("b_orig", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "conditional_swap",
        "if a_orig > b_orig { a_new == b_orig && b_new == a_orig } else { a_new == a_orig && b_new == b_orig }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ordered_after_swap",
        "a_new <= b_new",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conditional swap should order 10 and 3");
}

#[test]
fn swap_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("a_orig", i32_ty());
    ctx.declare_var_typed("b_orig", i32_ty());
    ctx.declare_var_typed("a_new", i32_ty());
    ctx.declare_var_typed("b_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("a_orig_bind", "a_orig == a"));
    ctx.push_obligation(ProofObligation::assume("b_orig_bind", "b_orig == b"));
    ctx.push_obligation(ProofObligation::assume(
        "swap",
        "a_new == b_orig && b_new == a_orig",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "equal_after_swap",
        "a_new == b_new",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swapping equal values should keep them equal");
}
