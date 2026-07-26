// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn swap_via_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "tmp", "a2", "b2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("tmp_def", "tmp == a"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == tmp"));
    ctx.push_obligation(ProofObligation::assert("swapped", "a2 == 20 && b2 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap via temp: (10,20) -> (20,10)");
}

#[test]
fn swap_via_xor() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "a1", "b1", "a2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a ^ b"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == a1 ^ b"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 ^ b1"));
    ctx.push_obligation(ProofObligation::assert("swapped", "a2 == 9 && b1 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR swap: (5,9) -> (9,5)");
}

#[test]
fn swap_via_arithmetic() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "a1", "b1", "a2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 13"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a + b"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == a1 - b"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 - b1"));
    ctx.push_obligation(ProofObligation::assert("swapped", "b1 == 7 && a2 == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "arithmetic swap: (7,13) -> (13,7)");
}

#[test]
fn double_swap_is_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "t1", "a1", "b1", "t2", "a2", "b2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 99"));
    // First swap
    ctx.push_obligation(ProofObligation::assume("t1_def", "t1 == a"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == b"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == t1"));
    // Second swap
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == a1"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b1"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == t2"));
    ctx.push_obligation(ProofObligation::assert("identity", "a2 == a && b2 == b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "double swap restores original values");
}

#[test]
fn three_way_rotation() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "tmp", "a2", "b2", "c2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume("tmp_def", "tmp == a"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == c"));
    ctx.push_obligation(ProofObligation::assume("c2_def", "c2 == tmp"));
    ctx.push_obligation(ProofObligation::assert(
        "rotated",
        "a2 == 2 && b2 == 3 && c2 == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "three-way rotation: (1,2,3) -> (2,3,1)");
}

#[test]
fn swap_preserves_sum() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "a2", "b2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 15"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 25"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == a"));
    ctx.push_obligation(ProofObligation::assert("sum_preserved", "a + b == a2 + b2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap preserves sum");
}

#[test]
fn conditional_swap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 8"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("ordered", "lo == 3 && hi == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conditional swap orders (8,3) to (3,8)");
}

#[test]
fn swap_negative_values() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "a2", "b2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0 - 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0 - 10"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == a"));
    ctx.push_obligation(ProofObligation::assert(
        "swapped",
        "a2 == 0 - 10 && b2 == 0 - 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap works with negative values");
}

#[test]
fn swap_same_value() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "a2", "b2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == a"));
    ctx.push_obligation(ProofObligation::assert("still_equal", "a2 == 7 && b2 == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swapping equal values is identity");
}

#[test]
fn four_way_rotation() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "d", "tmp", "a2", "b2", "c2", "d2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 30"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 40"));
    ctx.push_obligation(ProofObligation::assume("tmp_def", "tmp == a"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == c"));
    ctx.push_obligation(ProofObligation::assume("c2_def", "c2 == d"));
    ctx.push_obligation(ProofObligation::assume("d2_def", "d2 == tmp"));
    ctx.push_obligation(ProofObligation::assert(
        "rotated",
        "a2 == 20 && b2 == 30 && c2 == 40 && d2 == 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4-way rotation: (10,20,30,40) -> (20,30,40,10)");
}
