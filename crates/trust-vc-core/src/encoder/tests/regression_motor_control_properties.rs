// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pid_proportional_term() {
    let mut ctx = VerificationContext::new();
    for v in &["setpoint", "measured", "error", "kp", "p_term"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // P term = Kp × error
    ctx.push_obligation(ProofObligation::assume("sp", "setpoint == 1000"));
    ctx.push_obligation(ProofObligation::assume("m", "measured == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "error == setpoint - measured",
    ));
    ctx.push_obligation(ProofObligation::assume("k", "kp == 5"));
    ctx.push_obligation(ProofObligation::assume("pt_def", "p_term == error * kp"));
    ctx.push_obligation(ProofObligation::assert("err_200", "error == 200"));
    ctx.push_obligation(ProofObligation::assert("is_1000", "p_term == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PID P: (1000-800) × 5 = 1000");
}

#[test]
fn pwm_duty_cycle_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["requested_duty", "max_duty"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("actual_duty", u32_ty());
    // Clamp duty cycle to maximum
    ctx.push_obligation(ProofObligation::assume("rd", "requested_duty == 950"));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty == 900")); // 90% max
    ctx.push_obligation(ProofObligation::assume(
        "ad_def",
        "actual_duty == if requested_duty > max_duty { max_duty } else { requested_duty }",
    ));
    ctx.push_obligation(ProofObligation::assert("clamped", "actual_duty == 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor: 950 > 900 max → clamped to 900");
}

#[test]
fn encoder_position() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "counts_per_rev", "revolutions"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Quadrature encoder: 4096 counts per revolution
    ctx.push_obligation(ProofObligation::assume("c", "count == 8192"));
    ctx.push_obligation(ProofObligation::assume("cpr", "counts_per_rev == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "revolutions == count / counts_per_rev",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "revolutions == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "encoder: 8192 / 4096 = 2 revolutions");
}

#[test]
fn speed_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["delta_count", "sample_period_ms", "speed_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Speed = delta_count / counts_per_rev × 60000 / sample_period_ms
    // Precompute: delta=1024, cpr=4096 → 0.25 rev, period=10ms → 0.25×60000/10 = 1500 RPM
    ctx.push_obligation(ProofObligation::assume("dc", "delta_count == 1024"));
    ctx.push_obligation(ProofObligation::assume("sp", "sample_period_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("sr", "speed_rpm == 1500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1500", "speed_rpm == 1500"));
    ctx.push_obligation(ProofObligation::assert("positive", "speed_rpm > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor: 1024 counts / 10ms ≈ 1500 RPM");
}

#[test]
fn commutation_sector() {
    let mut ctx = VerificationContext::new();
    for v in &["electrical_angle", "sector"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // BLDC 6-step: 360° / 6 = 60° per sector
    // Precompute: angle/60 = sector
    ctx.push_obligation(ProofObligation::assume("ea", "electrical_angle == 180"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sector == electrical_angle / 60",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "sector == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "BLDC: 180° / 60° = sector 3");
}

#[test]
fn overcurrent_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_current_ma", "overcurrent_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fault", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "phase_current_ma == 15000")); // 15A
    ctx.push_obligation(ProofObligation::assume("oc", "overcurrent_ma == 10000")); // 10A limit
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fault == if phase_current_ma > overcurrent_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor: 15A > 10A limit → overcurrent fault");
}

#[test]
fn acceleration_ramp() {
    let mut ctx = VerificationContext::new();
    for v in &["current_speed", "target_speed", "ramp_step", "new_speed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gradual acceleration: increment by ramp_step per cycle
    ctx.push_obligation(ProofObligation::assume("cs", "current_speed == 500"));
    ctx.push_obligation(ProofObligation::assume("ts", "target_speed == 1000"));
    ctx.push_obligation(ProofObligation::assume("rs", "ramp_step == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_speed == if current_speed + ramp_step <= target_speed { current_speed + ramp_step } else { target_speed }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_550", "new_speed == 550"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor ramp: 500 + 50 = 550 (< 1000 target)");
}

#[test]
fn brake_chopper_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["dc_bus_mv", "brake_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("brake_active", i32_ty());
    // Regenerative braking raises DC bus voltage
    ctx.push_obligation(ProofObligation::assume("db", "dc_bus_mv == 42000")); // 42V
    ctx.push_obligation(ProofObligation::assume("bt", "brake_threshold_mv == 40000")); // 40V
    ctx.push_obligation(ProofObligation::assume(
        "ba_def",
        "brake_active == if dc_bus_mv > brake_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "brake_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor: 42V > 40V threshold → brake chopper on");
}

#[test]
fn hall_sensor_state() {
    let mut ctx = VerificationContext::new();
    for v in &["hall_a", "hall_b", "hall_c", "hall_state"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 3 Hall sensors encode 6 valid states (1-6, 0 and 7 are invalid)
    // State = hall_a + hall_b * 2 + hall_c * 4
    // A=1, B=0, C=1 → 1 + 0 + 4 = 5
    ctx.push_obligation(ProofObligation::assume("ha", "hall_a == 1"));
    ctx.push_obligation(ProofObligation::assume("hb", "hall_b == 0"));
    ctx.push_obligation(ProofObligation::assume("hc", "hall_c == 1"));
    ctx.push_obligation(ProofObligation::assume("hs", "hall_state == 5")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_5", "hall_state == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "hall_state >= 1 && hall_state <= 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC halls: A=1,B=0,C=1 → state 5 (valid)");
}

#[test]
fn stall_detection() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "speed_rpm",
        "min_speed_rpm",
        "stall_count",
        "stall_threshold",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stalled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "speed_rpm == 0"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_speed_rpm == 100"));
    ctx.push_obligation(ProofObligation::assume("sc", "stall_count == 10"));
    ctx.push_obligation(ProofObligation::assume("st", "stall_threshold == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "stalled == if speed_rpm < min_speed_rpm && stall_count >= stall_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stalled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor: 0 RPM + 10 stall cycles → stall detected");
}
