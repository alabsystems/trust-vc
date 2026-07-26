// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_kiln_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Kiln diameter (mm): value 3000, min 500, max 6000
    ctx.push_obligation(ProofObligation::assume("dv", "diameter_mm == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if diameter_mm >= 500 && diameter_mm <= 6000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary kiln: diameter 3000 mm in [500, 6000]");
}

#[test]
fn test_kiln_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length_m", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Kiln length (m): value 60, min 10, max 200
    ctx.push_obligation(ProofObligation::assume("lv", "length_m == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if length_m >= 10 && length_m <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary kiln: length 60 m in [10, 200]");
}

#[test]
fn test_shell_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shell_temp_c", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Shell temperature (C): value 350, min 200, max 500 (all positive, no offset)
    ctx.push_obligation(ProofObligation::assume("sv", "shell_temp_c == 350"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if shell_temp_c >= 200 && shell_temp_c <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary kiln: shell temp 350 C in [200, 500]");
}

#[test]
fn test_process_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("proc_temp_c", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Process temperature (C): value 1200, min 500, max 2000 (all positive, no offset)
    ctx.push_obligation(ProofObligation::assume("pv", "proc_temp_c == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if proc_temp_c >= 500 && proc_temp_c <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary kiln: process temp 1200 C in [500, 2000]");
}

#[test]
fn test_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Rotation speed (x100 RPM): 2.00 RPM -> 200, min 10 (0.10 RPM), max 500 (5.00 RPM)
    ctx.push_obligation(ProofObligation::assume("sv", "speed_x100 == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_x100 >= 10 && speed_x100 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary kiln: rotation speed 2.00 RPM (200) in [10, 500]",
    );
}

#[test]
fn test_kiln_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kiln_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Kiln type: 1=direct fired, 2=indirect fired, 3=calciner
    ctx.push_obligation(ProofObligation::assume("kt", "kiln_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid == if kiln_type == 1 || kiln_type == 2 || kiln_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary kiln: type 1 (direct fired) in {1,2,3}");
}

#[test]
fn test_drive_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Drive type: 1=gear, 2=friction, 3=direct
    ctx.push_obligation(ProofObligation::assume("dt", "drive_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid == if drive_type == 1 || drive_type == 2 || drive_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotary kiln: drive type 2 (friction) in {1,2,3}");
}

#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_rate_kgh", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Feed rate (kg/h): value 25000, min 100, max 100000
    ctx.push_obligation(ProofObligation::assume("fv", "feed_rate_kgh == 25000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if feed_rate_kgh >= 100 && feed_rate_kgh <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary kiln: feed rate 25000 kg/h in [100, 100000]",
    );
}

#[test]
fn test_inclination_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("incl_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Inclination (x100 degrees): 2.50 deg -> 250, min 50 (0.50 deg), max 500 (5.00 deg)
    ctx.push_obligation(ProofObligation::assume("iv", "incl_x100 == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if incl_x100 >= 50 && incl_x100 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary kiln: inclination 2.50 deg (250) in [50, 500]",
    );
}

#[test]
fn test_shell_alignment_monitoring_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alignment_mon", i32_ty());
    ctx.declare_var_typed("status_ok", i32_ty());
    // Shell alignment monitoring boolean flag: 1=enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("am", "alignment_mon == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "status_ok == if alignment_mon == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "status_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotary kiln: alignment monitoring flag=1 reports ok",
    );
}
