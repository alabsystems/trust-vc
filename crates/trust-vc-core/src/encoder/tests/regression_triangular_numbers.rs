// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn triangular_0() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t0", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t0_val", "t0 == 0"));
    ctx.push_obligation(ProofObligation::assert("t0_check", "t0 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(0) = 0");
}

#[test]
fn triangular_1() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t1", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t1_val", "t1 == 1"));
    ctx.push_obligation(ProofObligation::assert("t1_check", "t1 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(1) = 1");
}

#[test]
fn triangular_2() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t1", i32_ty());
    ctx.declare_var_typed("t2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t1_val", "t1 == 1"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == t1 + 2"));
    ctx.push_obligation(ProofObligation::assert("t2_check", "t2 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(2) = 1 + 2 = 3");
}

#[test]
fn triangular_3() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t1", i32_ty());
    ctx.declare_var_typed("t2", i32_ty());
    ctx.declare_var_typed("t3", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t1_val", "t1 == 1"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == t1 + 2"));
    ctx.push_obligation(ProofObligation::assume("t3_def", "t3 == t2 + 3"));
    ctx.push_obligation(ProofObligation::assert("t3_check", "t3 == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(3) = 1 + 2 + 3 = 6");
}

#[test]
fn triangular_4() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t1", i32_ty());
    ctx.declare_var_typed("t2", i32_ty());
    ctx.declare_var_typed("t3", i32_ty());
    ctx.declare_var_typed("t4", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t1_val", "t1 == 1"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == t1 + 2"));
    ctx.push_obligation(ProofObligation::assume("t3_def", "t3 == t2 + 3"));
    ctx.push_obligation(ProofObligation::assume("t4_def", "t4 == t3 + 4"));
    ctx.push_obligation(ProofObligation::assert("t4_check", "t4 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(4) = 1 + 2 + 3 + 4 = 10");
}

#[test]
fn triangular_5() {
    let mut ctx = VerificationContext::new();
    for v in &["t1", "t2", "t3", "t4", "t5"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t1_val", "t1 == 1"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == t1 + 2"));
    ctx.push_obligation(ProofObligation::assume("t3_def", "t3 == t2 + 3"));
    ctx.push_obligation(ProofObligation::assume("t4_def", "t4 == t3 + 4"));
    ctx.push_obligation(ProofObligation::assume("t5_def", "t5 == t4 + 5"));
    ctx.push_obligation(ProofObligation::assert("t5_check", "t5 == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(5) = 15");
}

#[test]
fn triangular_6() {
    let mut ctx = VerificationContext::new();
    for v in &["t1", "t2", "t3", "t4", "t5", "t6"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t1_val", "t1 == 1"));
    ctx.push_obligation(ProofObligation::assume("t2_def", "t2 == t1 + 2"));
    ctx.push_obligation(ProofObligation::assume("t3_def", "t3 == t2 + 3"));
    ctx.push_obligation(ProofObligation::assume("t4_def", "t4 == t3 + 4"));
    ctx.push_obligation(ProofObligation::assume("t5_def", "t5 == t4 + 5"));
    ctx.push_obligation(ProofObligation::assume("t6_def", "t6 == t5 + 6"));
    ctx.push_obligation(ProofObligation::assert("t6_check", "t6 == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(6) = 21");
}

#[test]
fn triangular_difference() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t3", i32_ty());
    ctx.declare_var_typed("t4", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t3_val", "t3 == 6"));
    ctx.push_obligation(ProofObligation::assume("t4_val", "t4 == 10"));
    ctx.push_obligation(ProofObligation::assert("diff_is_4", "t4 - t3 == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(4) - T(3) = 4");
}

#[test]
fn sum_of_consecutive_triangular() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t2", i32_ty());
    ctx.declare_var_typed("t3", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t2_val", "t2 == 3"));
    ctx.push_obligation(ProofObligation::assume("t3_val", "t3 == 6"));
    ctx.push_obligation(ProofObligation::assert("sum_is_9", "t2 + t3 == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(2) + T(3) = 3 + 6 = 9");
}

#[test]
fn triangular_increasing() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t3", i32_ty());
    ctx.declare_var_typed("t4", i32_ty());
    ctx.declare_var_typed("t5", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t3_val", "t3 == 6"));
    ctx.push_obligation(ProofObligation::assume("t4_val", "t4 == 10"));
    ctx.push_obligation(ProofObligation::assume("t5_val", "t5 == 15"));
    ctx.push_obligation(ProofObligation::assert("increasing", "t3 < t4 && t4 < t5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T(3) < T(4) < T(5)");
}
