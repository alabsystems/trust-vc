// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_sem_accelerating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accel_kv", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("av", "accel_kv == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if accel_kv >= 1 && accel_kv <= 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: accelerating voltage 15kV in [1,30]");
}

#[test]
fn test_sem_magnification_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magnification", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "magnification == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if magnification >= 10 && magnification <= 1000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: magnification 50000x in [10,1000000]");
}

#[test]
fn test_sem_resolution_scaled() {
    // Resolution scaled x10: 10 = 1.0 nm, 5 = 0.5 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10_nm", u32_ty());
    ctx.declare_var_typed("max_resolution_x10_nm", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "resolution_x10_nm == 10")); // 1.0 nm
    ctx.push_obligation(ProofObligation::assume("mr", "max_resolution_x10_nm == 50")); // 5.0 nm limit
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if resolution_x10_nm <= max_resolution_x10_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: resolution 1.0nm (x10=10) <= 5.0nm limit");
}

#[test]
fn test_sem_working_distance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("working_distance_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wd", "working_distance_mm == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if working_distance_mm >= 1 && working_distance_mm <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: working distance 10mm in [1,50]");
}

#[test]
fn test_sem_beam_current_scaled() {
    // Beam current scaled x100: 100 = 1.00 nA, 50 = 0.50 nA
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_current_x100_na", u32_ty());
    ctx.declare_var_typed("min_current_x100", u32_ty());
    ctx.declare_var_typed("max_current_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bc", "beam_current_x100_na == 100")); // 1.00 nA
    ctx.push_obligation(ProofObligation::assume("mn", "min_current_x100 == 1")); // 0.01 nA
    ctx.push_obligation(ProofObligation::assume("mx", "max_current_x100 == 10000")); // 100.00 nA
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if beam_current_x100_na >= min_current_x100 && beam_current_x100_na <= max_current_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SEM: beam current 1.00nA (x100=100) in [0.01,100.00]",
    );
}

#[test]
fn test_sem_detector_type_disjunction() {
    // 1=SE (secondary electron), 2=BSE (backscatter), 3=EDS (energy dispersive)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "detector == 2")); // BSE
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector == 1 || detector == 2 || detector == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: detector BSE(2) in {SE,BSE,EDS}");
}

#[test]
fn test_sem_vacuum_mode_disjunction() {
    // 1=high vacuum, 2=low vacuum, 3=ESEM (environmental)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vm", "vacuum_mode == 1")); // high vacuum
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if vacuum_mode == 1 || vacuum_mode == 2 || vacuum_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: vacuum high(1) in {high,low,ESEM}");
}

#[test]
fn test_sem_image_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("image_pixels", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ip", "image_pixels == 2048"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if image_pixels >= 512 && image_pixels <= 8192 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: image 2048px in [512,8192]");
}

#[test]
fn test_sem_scan_dwell_time_scaled() {
    // Dwell time scaled x100: 100 = 1.00 us, 50 = 0.50 us
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dwell_x100_us", u32_ty());
    ctx.declare_var_typed("min_dwell_x100", u32_ty());
    ctx.declare_var_typed("max_dwell_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "dwell_x100_us == 100")); // 1.00 us
    ctx.push_obligation(ProofObligation::assume("mn", "min_dwell_x100 == 1")); // 0.01 us
    ctx.push_obligation(ProofObligation::assume("mx", "max_dwell_x100 == 100000")); // 1000.00 us
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dwell_x100_us >= min_dwell_x100 && dwell_x100_us <= max_dwell_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: dwell 1.00us (x100=100) in [0.01,1000.00]");
}

#[test]
fn test_sem_stage_motorized_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motorized", i32_ty());
    ctx.declare_var_typed("can_auto_position", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "motorized == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cap_def",
        "can_auto_position == if motorized == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "can_auto_position == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SEM: motorized=1 -> auto-position enabled");
}
