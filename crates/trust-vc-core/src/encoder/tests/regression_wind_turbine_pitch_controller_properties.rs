// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Wind turbine blade pitch controller properties.
// Fixed-point scaling: angles ×10 (tenths of degree), speeds ×10 (tenths of °/s),
// wind speeds ×10 (tenths of m/s), times ×10 (tenths of second), voltages in mV.

#[test]
fn test_pitch_angle_range() {
    // Blade pitch angle in tenths of degree: 50 = 5.0°, range [0, 900] (0°–90°)
    let mut ctx = VerificationContext::new();
    for v in &["pitch_angle", "min_angle", "max_angle"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pitch_val", "pitch_angle == 50"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_angle == 0"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_angle == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "angle_in_range",
        "pitch_angle >= min_angle && pitch_angle <= max_angle",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pitch angle 5.0° within [0°, 90°]");
}

#[test]
fn test_pitch_rate_range() {
    // Pitch actuation rate in tenths of °/s: 80 = 8.0°/s, range [10, 200]
    let mut ctx = VerificationContext::new();
    for v in &["pitch_rate", "min_rate", "max_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rate_val", "pitch_rate == 80"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_rate == 10"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_rate == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_in_range",
        "pitch_rate >= min_rate && pitch_rate <= max_rate",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pitch rate 8.0°/s within [1.0°/s, 20.0°/s]");
}

#[test]
fn test_actuator_type_valid() {
    // Actuator type: 1=hydraulic, 2=electric, 3=electro-hydraulic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("actuator_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "actuator_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "actuator_type == 1 || actuator_type == 2 || actuator_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electric actuator (2) is valid type");
}

#[test]
fn test_blade_count_valid() {
    // Blade configuration: 1=two-blade, 2=three-blade, 3=four-blade
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("count_val", "blade_count == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_count",
        "blade_count == 1 || blade_count == 2 || blade_count == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "three-blade config (2) is valid");
}

#[test]
fn test_rated_wind_speed_range() {
    // Rated wind speed in tenths of m/s: 125 = 12.5 m/s, range [80, 200]
    let mut ctx = VerificationContext::new();
    for v in &["rated_wind", "min_wind", "max_wind"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wind_val", "rated_wind == 125"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_wind == 80"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_wind == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "wind_in_range",
        "rated_wind >= min_wind && rated_wind <= max_wind",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rated wind 12.5 m/s within [8.0, 20.0] m/s");
}

#[test]
fn test_emergency_feather_time_range() {
    // Emergency feather time in tenths of second: 50 = 5.0s, range [20, 100]
    let mut ctx = VerificationContext::new();
    for v in &["feather_time", "min_time", "max_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("time_val", "feather_time == 50"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_time == 20"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_time == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "time_in_range",
        "feather_time >= min_time && feather_time <= max_time",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emergency feather 5.0s within [2.0s, 10.0s]");
}

#[test]
fn test_position_feedback_valid() {
    // Position feedback sensor: 1=potentiometer, 2=encoder, 3=resolver
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feedback_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fb_val", "feedback_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_feedback",
        "feedback_type == 1 || feedback_type == 2 || feedback_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolver feedback (3) is valid sensor type");
}

#[test]
fn test_battery_backup_voltage_range() {
    // Battery backup voltage in millivolts: 24000 = 24V, range [12000, 48000]
    let mut ctx = VerificationContext::new();
    for v in &["voltage", "min_voltage", "max_voltage"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("volt_val", "voltage == 24000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_voltage == 12000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_voltage == 48000"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "voltage >= min_voltage && voltage <= max_voltage",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "battery 24V within [12V, 48V]");
}

#[test]
fn test_turbine_class_valid() {
    // IEC turbine classes: 1, 2, 3 (non-sequential values but same set)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("turbine_class", u32_ty());
    ctx.push_obligation(ProofObligation::assume("class_val", "turbine_class == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_class",
        "turbine_class == 1 || turbine_class == 2 || turbine_class == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC class I (1) is valid turbine class");
}

#[test]
fn test_independent_pitch_control() {
    // Independent pitch control: boolean flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("independent_pitch", i32_ty());
    ctx.declare_var_typed("blade_a_angle", u32_ty());
    ctx.declare_var_typed("blade_b_angle", u32_ty());
    ctx.declare_var_typed("angles_may_differ", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_val",
        "independent_pitch == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "blade_a_val",
        "blade_a_angle == 50",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "blade_b_val",
        "blade_b_angle == 70",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "differ_def",
        "angles_may_differ == if independent_pitch == 1 { if blade_a_angle != blade_b_angle { 1 } else { 0 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "independent_allows_different",
        "angles_may_differ == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "independent pitch allows different blade angles");
}
