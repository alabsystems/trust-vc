// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mppt_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["panel_voltage_mv", "mppt_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_mppt", i32_ty());
    // MPPT: operate panel near maximum power point voltage
    ctx.push_obligation(ProofObligation::assume("pv", "panel_voltage_mv == 17500"));
    ctx.push_obligation(ProofObligation::assume("mv", "mppt_voltage_mv == 17800"));
    ctx.push_obligation(ProofObligation::assume(
        "delta",
        "mppt_voltage_mv - panel_voltage_mv <= 500",
    )); // within 500mV
        // Simplified: check if close enough
    ctx.push_obligation(ProofObligation::assume(
        "am_def",
        "at_mppt == if panel_voltage_mv >= 17300 && panel_voltage_mv <= 18300 { 1 } else { 0 }",
    )); // ±500mV of 17800
    ctx.push_obligation(ProofObligation::assert("yes", "at_mppt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: panel 17.5V in [17.3, 18.3] → at MPPT");
}

#[test]
fn charge_stage() {
    let mut ctx = VerificationContext::new();
    for v in &["battery_voltage_mv", "bulk_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_bulk", i32_ty());
    // 3-stage: bulk (CC), absorption (CV), float. Bulk until battery reaches threshold.
    ctx.push_obligation(ProofObligation::assume("bv", "battery_voltage_mv == 13500")); // 13.5V
    ctx.push_obligation(ProofObligation::assume("bt", "bulk_threshold_mv == 14400")); // 14.4V
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bulk == if battery_voltage_mv < bulk_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_bulk == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Solar: 13.5V < 14.4V bulk threshold → in bulk charge",
    );
}

#[test]
fn panel_power() {
    let mut ctx = VerificationContext::new();
    for v in &["panel_voltage_mv", "panel_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_mw", u32_ty());
    // Power = V × I. Precompute: 18000mV × 5000mA = 90000000 μW = 90W → use mW
    // Scaled: (18000 × 5000) / 1000 = 90000 mW. Precompute.
    ctx.push_obligation(ProofObligation::assume("pv", "panel_voltage_mv == 18000"));
    ctx.push_obligation(ProofObligation::assume("pc", "panel_current_ma == 5000"));
    ctx.push_obligation(ProofObligation::assume("pw", "power_mw == 90000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_90000", "power_mw == 90000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: 18V × 5A = 90W panel power (precomputed)");
}

#[test]
fn load_disconnect() {
    let mut ctx = VerificationContext::new();
    for v in &["battery_voltage_mv", "disconnect_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_off", i32_ty());
    // Low voltage disconnect to protect battery
    ctx.push_obligation(ProofObligation::assume("bv", "battery_voltage_mv == 11000")); // 11.0V
    ctx.push_obligation(ProofObligation::assume(
        "dt",
        "disconnect_threshold_mv == 11500",
    )); // 11.5V
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_off == if battery_voltage_mv < disconnect_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_off == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: 11.0V < 11.5V LVD → load disconnected");
}

#[test]
fn float_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_voltage_mv", "float_setpoint_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_float", i32_ty());
    // Float charge: maintain at setpoint (e.g., 13.6V for 12V lead-acid)
    ctx.push_obligation(ProofObligation::assume("cv", "charge_voltage_mv == 13600"));
    ctx.push_obligation(ProofObligation::assume("fs", "float_setpoint_mv == 13600"));
    ctx.push_obligation(ProofObligation::assume(
        "af_def",
        "at_float == if charge_voltage_mv == float_setpoint_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "at_float == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: 13.6V = float setpoint → at float stage");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["base_voltage_mv", "temp_comp_mv", "adjusted_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Temperature compensation: reduce charge voltage at high temp
    // Precompute: 14400 - 150 = 14250 mV (at 30°C above reference)
    ctx.push_obligation(ProofObligation::assume("bv", "base_voltage_mv == 14400"));
    ctx.push_obligation(ProofObligation::assume("tc", "temp_comp_mv == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "av_def",
        "adjusted_voltage_mv == base_voltage_mv - temp_comp_mv",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_14250",
        "adjusted_voltage_mv == 14250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: 14400 - 150 temp comp = 14250 mV adjusted");
}

#[test]
fn equalization_needed() {
    let mut ctx = VerificationContext::new();
    for v in &["days_since_equalize", "equalize_interval_days"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_equalize", i32_ty());
    // Lead-acid: periodic equalization charge every 30 days
    ctx.push_obligation(ProofObligation::assume("ds", "days_since_equalize == 35"));
    ctx.push_obligation(ProofObligation::assume(
        "ei",
        "equalize_interval_days == 30",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ne_def",
        "needs_equalize == if days_since_equalize >= equalize_interval_days { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_equalize == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Solar: 35 days ≥ 30 interval → equalization needed",
    );
}

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["input_voltage_mv", "min_input_mv", "max_input_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("input_ok", i32_ty());
    // Controller input range: e.g., 12-50V for MPPT controller
    ctx.push_obligation(ProofObligation::assume("iv", "input_voltage_mv == 36000")); // 36V
    ctx.push_obligation(ProofObligation::assume("mn", "min_input_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_input_mv == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "input_ok == if input_voltage_mv >= min_input_mv && input_voltage_mv <= max_input_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "input_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: 36V in [12, 50] → input voltage OK");
}

#[test]
fn efficiency_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["output_power_mw", "input_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("efficiency_pct", u32_ty());
    // Efficiency = output/input × 100. Precompute: 85000/90000 × 100 ≈ 94
    ctx.push_obligation(ProofObligation::assume("op", "output_power_mw == 85000"));
    ctx.push_obligation(ProofObligation::assume("ip", "input_power_mw == 90000"));
    ctx.push_obligation(ProofObligation::assume("ep", "efficiency_pct == 94")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_94", "efficiency_pct == 94"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: 85W/90W = 94% efficiency (precomputed)");
}

#[test]
fn night_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["panel_voltage_mv", "night_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_night", i32_ty());
    // Night: panel voltage drops below threshold (no sunlight)
    ctx.push_obligation(ProofObligation::assume("pv", "panel_voltage_mv == 2000")); // 2V
    ctx.push_obligation(ProofObligation::assume("nt", "night_threshold_mv == 5000")); // 5V
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_night == if panel_voltage_mv < night_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_night == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solar: panel 2V < 5V threshold → night detected");
}
