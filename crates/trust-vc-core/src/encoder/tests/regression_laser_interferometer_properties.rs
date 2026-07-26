// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_measurement_range_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["range", "min_range", "max_range"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("range_val", "range == 40000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_range == 1000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_range == 80000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "range >= min_range && range <= max_range",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement range: 40000mm in [1000, 80000]");
}

#[test]
fn test_resolution_nm() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution", "min_res", "max_res"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution == 1"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_res == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_res == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "resolution >= min_res && resolution <= max_res",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution: 1nm in [1, 100]");
}

#[test]
fn test_accuracy_x1000_ppm() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x1000", "min_acc", "max_acc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 0.500 ppm represented as 500 (x1000 scaling)
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_x1000 == 500"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_acc == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_acc == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "accuracy_x1000 >= min_acc && accuracy_x1000 <= max_acc",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy: 0.500ppm (500 x1000) in [1, 2000]");
}

#[test]
fn test_laser_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", i32_ty());
    // 1=HeNe, 2=diode, 3=frequency-stabilized
    ctx.push_obligation(ProofObligation::assume("lt_val", "laser_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser type: HeNe (1) is valid {1,2,3}");
}

#[test]
fn test_measurement_axis_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axis", i32_ty());
    // 1=single, 2=dual, 3=multi
    ctx.push_obligation(ProofObligation::assume("axis_val", "axis == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_axis",
        "axis == 1 || axis == 2 || axis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement axis: dual (2) is valid {1,2,3}");
}

#[test]
fn test_max_velocity_mm_s() {
    let mut ctx = VerificationContext::new();
    for v in &["velocity", "min_vel", "max_vel"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("vel_val", "velocity == 4000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_vel == 100"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_vel == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "velocity >= min_vel && velocity <= max_vel",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max velocity: 4000mm/s in [100, 10000]");
}

#[test]
fn test_wavelength_nm() {
    let mut ctx = VerificationContext::new();
    for v in &["wavelength", "min_wl", "max_wl"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wl_val", "wavelength == 633"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_wl == 400"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_wl == 1600"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "wavelength >= min_wl && wavelength <= max_wl",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength: 633nm in [400, 1600]");
}

#[test]
fn test_communication_interface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", i32_ty());
    // 1=USB, 2=Ethernet, 3=fiber optic, 4=AXIs
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm == 1 || comm == 2 || comm == 3 || comm == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication: fiber optic (3) is valid {1,2,3,4}");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500 to avoid negative values: 20C -> 520, -10C -> 490, 40C -> 540
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_temp == 490"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_temp == 540"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "temp >= min_temp && temp <= max_temp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp: 20C (520 offset) in [-10C, 40C]");
}

#[test]
fn test_environmental_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "enabled_def",
        "enabled == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_enabled", "enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "environmental compensation: flag=1 -> enabled");
}
