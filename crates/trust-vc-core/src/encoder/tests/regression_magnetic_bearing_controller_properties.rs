// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_bearing_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_n", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Bearing capacity (N): value 5000, min 100, max 50000
    ctx.push_obligation(ProofObligation::assume("fv", "force_n == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if force_n >= 100 && force_n <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: bearing capacity 5000 N in [100, 50000]");
}

#[test]
fn test_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Rotor speed (RPM): value 30000, min 1000, max 150000
    ctx.push_obligation(ProofObligation::assume("sv", "speed_rpm == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_rpm >= 1000 && speed_rpm <= 150000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: rotor speed 30000 RPM in [1000, 150000]");
}

#[test]
fn test_control_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_hz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Control bandwidth (Hz): servo loop value 1000, min 100, max 10000
    ctx.push_obligation(ProofObligation::assume("bv", "bandwidth_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if bandwidth_hz >= 100 && bandwidth_hz <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: control bandwidth 1000 Hz in [100, 10000]");
}

#[test]
fn test_bearing_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Bearing type: 1=radial, 2=axial, 3=combined
    ctx.push_obligation(ProofObligation::assume("bt", "bearing_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid == if bearing_type == 1 || bearing_type == 2 || bearing_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: bearing type 1 (radial) in {1,2,3}");
}

#[test]
fn test_position_sensor_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Position sensor: 1=eddy current, 2=inductive, 3=capacitive, 4=optical
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 || sensor_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AMB: position sensor 1 (eddy current) in {1,2,3,4}",
    );
}

#[test]
fn test_air_gap_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_gap_um", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Air gap (um): clearance value 500, min 100, max 2000
    ctx.push_obligation(ProofObligation::assume("ag", "air_gap_um == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if air_gap_um >= 100 && air_gap_um <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: air gap 500 um in [100, 2000]");
}

#[test]
fn test_coil_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_ma", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Coil current (mA): operating value 5000, min 100, max 20000
    ctx.push_obligation(ProofObligation::assume("cv", "current_ma == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if current_ma >= 100 && current_ma <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: coil current 5000 mA in [100, 20000]");
}

#[test]
fn test_axis_count_non_sequential() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axis_count", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Axis count: non-sequential values 2, 5, 10
    ctx.push_obligation(ProofObligation::assume("ac", "axis_count == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid == if axis_count == 2 || axis_count == 5 || axis_count == 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: axis count 5 in {2, 5, 10}");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Operating temp offset +500: value 525 (25 C), min 460 (-40 C), max 650 (150 C)
    ctx.push_obligation(ProofObligation::assume("tv", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= 460 && temp_offset <= 650 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "AMB: operating temp 25 C (offset 525) in [460, 650]",
    );
}

#[test]
fn test_touchdown_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("touchdown", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    // Touchdown detection boolean flag: 1=detected, 0=not detected
    ctx.push_obligation(ProofObligation::assume("td", "touchdown == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if touchdown == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMB: touchdown detected flag=1 triggers alarm");
}
