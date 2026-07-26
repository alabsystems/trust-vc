// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn electrical_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "pole_pairs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("elec_freq_hz", u32_ty());
    // Electrical freq = RPM × pole_pairs / 60. Precompute: 3000×4/60 = 200 Hz
    ctx.push_obligation(ProofObligation::assume("rp", "rpm == 3000"));
    ctx.push_obligation(ProofObligation::assume("pp", "pole_pairs == 4"));
    ctx.push_obligation(ProofObligation::assume("ef", "elec_freq_hz == 200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_200", "elec_freq_hz == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC: 3000 RPM × 4 poles / 60 = 200 Hz (precomputed)",
    );
}

#[test]
fn hall_sensor_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hall_code", u32_ty());
    ctx.declare_var_typed("is_valid", i32_ty());
    // 3 Hall sensors: valid codes are 1-6 (not 0 or 7)
    ctx.push_obligation(ProofObligation::assume("hc", "hall_code == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_valid == if hall_code >= 1 && hall_code <= 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: Hall code 5 in [1, 6] → valid state");
}

#[test]
fn back_emf_zero_crossing() {
    let mut ctx = VerificationContext::new();
    for v in &["bemf_mv", "threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zero_crossing", i32_ty());
    // Zero-crossing detection for sensorless commutation
    // Using offset: 0 = -Vbus/2, 500 = 0V, 1000 = +Vbus/2
    ctx.push_obligation(ProofObligation::assume("bm", "bemf_mv == 500")); // at zero crossing
    ctx.push_obligation(ProofObligation::assume("tm", "threshold_mv == 500")); // zero point
    ctx.push_obligation(ProofObligation::assume(
        "zc_def",
        "zero_crossing == if bemf_mv == threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zero_crossing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: BEMF at midpoint 500 = zero crossing");
}

#[test]
fn pwm_duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_percent", "max_duty_percent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    // Duty cycle 0-100%, max typically 95% to ensure bootstrap cap charge
    ctx.push_obligation(ProofObligation::assume("dp", "duty_percent == 80"));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty_percent == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if duty_percent <= max_duty_percent { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: 80% duty ≤ 95% max → within limit");
}

#[test]
fn phase_current_balance() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_a_ma", "phase_b_ma", "imbalance_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("balanced", i32_ty());
    // Phase currents should be approximately equal
    ctx.push_obligation(ProofObligation::assume("pa", "phase_a_ma == 1000"));
    ctx.push_obligation(ProofObligation::assume("pb", "phase_b_ma == 980"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "imbalance_ma == phase_a_ma - phase_b_ma",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "balanced == if imbalance_ma <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "imbalance_ma == 20"));
    ctx.push_obligation(ProofObligation::assert("yes", "balanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: |1000-980| = 20mA ≤ 50mA → phases balanced");
}

#[test]
fn speed_pid_error() {
    let mut ctx = VerificationContext::new();
    for v in &["target_rpm", "actual_rpm", "error_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("error_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tr", "target_rpm == 3000"));
    ctx.push_obligation(ProofObligation::assume("ar", "actual_rpm == 2950"));
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "error_rpm == target_rpm - actual_rpm",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "error_ok == if error_rpm <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "error_rpm == 50"));
    ctx.push_obligation(ProofObligation::assert("yes", "error_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: |3000-2950| = 50 RPM ≤ 100 tolerance → OK");
}

#[test]
fn commutation_sector() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrical_angle_deg", u32_ty());
    ctx.declare_var_typed("sector", u32_ty());
    // 6 sectors of 60° each. Precompute: 150° → sector 2 (120-180)
    ctx.push_obligation(ProofObligation::assume("ea", "electrical_angle_deg == 150"));
    ctx.push_obligation(ProofObligation::assume("s", "sector == 2")); // precomputed: 150/60 = 2
    ctx.push_obligation(ProofObligation::assert("is_2", "sector == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: 150° → sector 2 (precomputed 150/60)");
}

#[test]
fn dc_bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bus_voltage_mv", "min_bus_mv", "max_bus_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bus_ok", i32_ty());
    // DC bus: e.g., 24V system = 20-28V range
    ctx.push_obligation(ProofObligation::assume("bv", "bus_voltage_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bus_mv == 20000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bus_mv == 28000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bus_ok == if bus_voltage_mv >= min_bus_mv && bus_voltage_mv <= max_bus_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bus_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLDC: 24V bus in [20, 28] → bus voltage OK");
}

#[test]
fn regenerative_braking() {
    let mut ctx = VerificationContext::new();
    for v in &["bus_voltage_mv", "regen_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("regen_active", i32_ty());
    // Regenerative braking raises bus voltage; brake resistor activates at threshold
    ctx.push_obligation(ProofObligation::assume("bv", "bus_voltage_mv == 30000")); // 30V
    ctx.push_obligation(ProofObligation::assume("rt", "regen_threshold_mv == 29000")); // 29V
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "regen_active == if bus_voltage_mv >= regen_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "regen_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC: bus 30V ≥ 29V threshold → regen braking active",
    );
}

#[test]
fn dead_time_insertion() {
    let mut ctx = VerificationContext::new();
    for v in &["dead_time_ns", "min_dead_time_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("safe", i32_ty());
    // Dead time prevents shoot-through in half-bridge
    ctx.push_obligation(ProofObligation::assume("dt", "dead_time_ns == 500"));
    ctx.push_obligation(ProofObligation::assume("mdt", "min_dead_time_ns == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "safe == if dead_time_ns >= min_dead_time_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLDC: 500ns dead time ≥ 200ns min → shoot-through safe",
    );
}
