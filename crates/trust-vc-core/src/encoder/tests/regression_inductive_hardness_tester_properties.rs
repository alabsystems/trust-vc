// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_hardness_range_hrc_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hardness", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "hardness == 70"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "hardness >= 20 && hardness <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HRC hardness 70 within [20, 100]");
}

#[test]
fn test_accuracy_x10_hrc_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x10 >= 1 && accuracy_x10 <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 0.5 HRC (x10=5) within [1, 20]");
}

#[test]
fn test_force_newtons_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "force == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "force >= 10 && force <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test force 100N within [10, 3000]");
}

#[test]
fn test_scale_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scale", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "scale == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_scale",
        "scale == 1 || scale == 2 || scale == 3 || scale == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scale type 1=Rockwell in {1,2,3,4}");
}

#[test]
fn test_indenter_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("indenter", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "indenter == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_indenter",
        "indenter == 1 || indenter == 2 || indenter == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "indenter 1=diamond cone in {1,2,3}");
}

#[test]
fn test_measurement_time_ms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "time == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "time >= 100 && time <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement time 2000ms within [100, 10000]");
}

#[test]
fn test_communication_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "comm == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm == 1 || comm == 2 || comm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication 1=USB in {1,2,3}");
}

#[test]
fn test_memory_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("memory", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "memory == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "memory >= 100 && memory <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "memory capacity 5000 within [100, 50000]");
}

#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "temp >= 490 && temp <= 550",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 520 (20C offset+500) within [490, 550]",
    );
}

#[test]
fn test_auto_conversion_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-conversion enabled when flag=1");
}
