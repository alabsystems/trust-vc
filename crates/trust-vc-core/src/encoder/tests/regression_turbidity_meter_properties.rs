// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ntu_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ntu", "ntu_min", "ntu_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Turbidity range in NTU: value 500, valid range [1, 10000]
    ctx.push_obligation(ProofObligation::assume("ntu_val", "ntu == 500"));
    ctx.push_obligation(ProofObligation::assume("ntu_lo", "ntu_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ntu_hi", "ntu_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "ntu_in_range",
        "ntu >= ntu_min && ntu <= ntu_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turbidity 500 NTU in range [1, 10000]");
}

#[test]
fn test_accuracy_x10() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x10", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy as x10 %: value 20 (2.0%), valid range 5 (0.5%) to 50 (5.0%)
    ctx.push_obligation(ProofObligation::assume("ac_val", "acc_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 5"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "acc_x10 >= acc_min && acc_x10 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 20 (2.0%) in range [5, 50] (0.5%-5.0%)");
}

#[test]
fn test_light_source() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_src", u32_ty());
    ctx.declare_var_typed("valid_src", i32_ty());
    // 1=tungsten, 2=LED 860nm, 3=laser
    ctx.push_obligation(ProofObligation::assume("ls_val", "light_src == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ls_valid_def",
        "valid_src == if light_src == 1 || light_src == 2 || light_src == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ls_check", "valid_src == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "light source 2 (LED 860nm) is valid");
}

#[test]
fn test_measurement_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // 1=nephelometric (90 deg), 2=ratio, 3=absorption
    ctx.push_obligation(ProofObligation::assume("mm_val", "method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mm_valid_def",
        "valid_method == if method == 1 || method == 2 || method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mm_check", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement method 1 (nephelometric 90 deg) is valid",
    );
}

#[test]
fn test_response_time_seconds() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_s", "resp_min", "resp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time in seconds: value 10, valid range [1, 120]
    ctx.push_obligation(ProofObligation::assume("rt_val", "resp_s == 10"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "resp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "resp_max == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "resp_s >= resp_min && resp_s <= resp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 10s in range [1, 120]");
}

#[test]
fn test_sample_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_off", "temp_off_min", "temp_off_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sample temperature offset +500: value 520 (20C), min 450 (-50C), max 600 (100C)
    ctx.push_obligation(ProofObligation::assume("st_val", "temp_off == 520"));
    ctx.push_obligation(ProofObligation::assume("st_min", "temp_off_min == 450"));
    ctx.push_obligation(ProofObligation::assume("st_max", "temp_off_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "st_in_range",
        "temp_off >= temp_off_min && temp_off <= temp_off_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample temp 520 (20C) in range [450, 600] (-50C to 100C)",
    );
}

#[test]
fn test_path_length_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["path_mm", "path_min", "path_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Optical path length in mm: value 25, valid range [1, 100]
    ctx.push_obligation(ProofObligation::assume("pl_val", "path_mm == 25"));
    ctx.push_obligation(ProofObligation::assume("pl_min", "path_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pl_max", "path_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "pl_in_range",
        "path_mm >= path_min && path_mm <= path_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "path length 25 mm in range [1, 100]");
}

#[test]
fn test_output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // 1=4-20mA, 2=RS485, 3=Modbus, 4=HART
    ctx.push_obligation(ProofObligation::assume("ot_val", "output == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_valid_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_check", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 3 (Modbus) is valid");
}

#[test]
fn test_calibration_points() {
    let mut ctx = VerificationContext::new();
    for v in &["cal_pts", "cal_min", "cal_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Calibration points: value 3, valid range [1, 10]
    ctx.push_obligation(ProofObligation::assume("cp_val", "cal_pts == 3"));
    ctx.push_obligation(ProofObligation::assume("cp_min", "cal_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cp_max", "cal_max == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "cp_in_range",
        "cal_pts >= cal_min && cal_pts <= cal_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration points 3 in range [1, 10]");
}

#[test]
fn test_auto_cleaning_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_clean", i32_ty());
    ctx.declare_var_typed("cleaning_active", i32_ty());
    // Boolean flag: 1=auto-cleaning enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("ac_val", "auto_clean == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cleaning_active == if auto_clean == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ca_check", "cleaning_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-cleaning flag 1 -> cleaning active");
}
