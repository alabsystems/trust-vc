// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pulse_width_to_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["pulse_us", "min_pulse_us", "max_pulse_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("angle_deg", u32_ty());
    // Standard servo: 1000μs=0°, 1500μs=90°, 2000μs=180°. Precompute.
    ctx.push_obligation(ProofObligation::assume("pu", "pulse_us == 1500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pulse_us == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pulse_us == 2000"));
    ctx.push_obligation(ProofObligation::assume("ad", "angle_deg == 90")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_90", "angle_deg == 90"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: 1500μs pulse → 90° (precomputed)");
}

#[test]
fn position_within_limits() {
    let mut ctx = VerificationContext::new();
    for v in &["current_angle", "min_angle", "max_angle"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_limits", i32_ty());
    // Servo travel limits: e.g., 10° to 170° for mechanical safety
    ctx.push_obligation(ProofObligation::assume("ca", "current_angle == 90"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_angle == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_angle == 170"));
    ctx.push_obligation(ProofObligation::assume(
        "il_def",
        "in_limits == if current_angle >= min_angle && current_angle <= max_angle { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_limits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: angle 90° in [10, 170] → within limits");
}

#[test]
fn speed_control() {
    let mut ctx = VerificationContext::new();
    for v in &["target_angle", "current_angle", "step_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_target", i32_ty());
    ctx.declare_var_typed("distance", u32_ty());
    // Distance to target
    ctx.push_obligation(ProofObligation::assume("ta", "target_angle == 120"));
    ctx.push_obligation(ProofObligation::assume("ca", "current_angle == 90"));
    ctx.push_obligation(ProofObligation::assume("ss", "step_size == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "distance == target_angle - current_angle",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "at_def",
        "at_target == if distance <= step_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "distance == 30"));
    ctx.push_obligation(ProofObligation::assert("no", "at_target == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: distance 30° > 5° step → not at target");
}

#[test]
fn pwm_period() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("period_us", u32_ty());
    ctx.declare_var_typed("is_standard", i32_ty());
    // Standard servo PWM: 20000μs period (50Hz)
    ctx.push_obligation(ProofObligation::assume("pu", "period_us == 20000"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if period_us == 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: 20000μs period = 50Hz → standard PWM");
}

#[test]
fn deadband_filter() {
    let mut ctx = VerificationContext::new();
    for v in &["error", "deadband"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_correction", i32_ty());
    // Ignore small errors within deadband to prevent jitter
    ctx.push_obligation(ProofObligation::assume("e", "error == 1"));
    ctx.push_obligation(ProofObligation::assume("db", "deadband == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "needs_correction == if error > deadband { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "needs_correction == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Servo: error 1 ≤ 2 deadband → no correction needed",
    );
}

#[test]
fn torque_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["load_torque", "max_torque"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overloaded", i32_ty());
    // Servo torque in oz-in (or kg-cm). Max = rated torque.
    ctx.push_obligation(ProofObligation::assume("lt", "load_torque == 150"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_torque == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "overloaded == if load_torque > max_torque { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "overloaded == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: 150 oz-in ≤ 200 max → not overloaded");
}

#[test]
fn feedback_position() {
    let mut ctx = VerificationContext::new();
    for v in &["feedback_adc", "commanded_adc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("position_error", u32_ty());
    ctx.declare_var_typed("error_ok", i32_ty());
    // Analog feedback servo: ADC position vs commanded
    ctx.push_obligation(ProofObligation::assume("fa", "feedback_adc == 512"));
    ctx.push_obligation(ProofObligation::assume("ca", "commanded_adc == 510"));
    ctx.push_obligation(ProofObligation::assume(
        "pe_def",
        "position_error == feedback_adc - commanded_adc",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "error_ok == if position_error <= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "position_error == 2"));
    ctx.push_obligation(ProofObligation::assert("yes", "error_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: |512-510| = 2 ≤ 5 tolerance → position OK");
}

#[test]
fn voltage_check() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply_mv", "max_supply_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // Typical servo: 4.8V-6.0V
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply_mv == 4800"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply_mv == 6000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if supply_mv >= min_supply_mv && supply_mv <= max_supply_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: 5.0V in [4.8, 6.0] → voltage OK");
}

#[test]
fn digital_servo_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_bits", u32_ty());
    ctx.declare_var_typed("steps", u32_ty());
    // 12-bit digital servo: 2^12 = 4096 steps. Precompute.
    ctx.push_obligation(ProofObligation::assume("rb", "resolution_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("st", "steps == 4096")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4096", "steps == 4096"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: 12-bit → 4096 steps (precomputed)");
}

#[test]
fn transit_time() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_delta", "speed_deg_per_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("transit_ms", u32_ty());
    // Transit time = angle / speed × 1000. Precompute: 60/300 × 1000 = 200ms
    ctx.push_obligation(ProofObligation::assume("ad", "angle_delta == 60"));
    ctx.push_obligation(ProofObligation::assume("sp", "speed_deg_per_sec == 300"));
    ctx.push_obligation(ProofObligation::assume("tm", "transit_ms == 200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_200", "transit_ms == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Servo: 60°/300°/s = 200ms transit (precomputed)");
}
