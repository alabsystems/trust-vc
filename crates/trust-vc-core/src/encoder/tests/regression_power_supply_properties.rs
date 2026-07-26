// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn voltage_regulation_within_tolerance() {
    let mut ctx = VerificationContext::new();
    for v in &["target_mv", "actual_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "target_mv == 3300")); // 3.3V
    ctx.push_obligation(ProofObligation::assume("a", "actual_mv == 3280")); // 3.28V
    ctx.push_obligation(ProofObligation::assume("tol", "tolerance_mv == 165")); // 5% of 3300
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if actual_mv >= target_mv - tolerance_mv && actual_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PSU: 3280mV within 3300±165mV");
}

#[test]
fn power_budget_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["rail_12v_ma", "rail_5v_ma", "rail_3v3_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    for v in &["power_12v_mw", "power_5v_mw", "power_3v3_mw", "total_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r12", "rail_12v_ma == 500"));
    ctx.push_obligation(ProofObligation::assume("r5", "rail_5v_ma == 1000"));
    ctx.push_obligation(ProofObligation::assume("r33", "rail_3v3_ma == 200"));
    // P = V * I (milliwatts = millivolts/1000 * milliamps, simplified)
    ctx.push_obligation(ProofObligation::assume("p12", "power_12v_mw == 6000")); // 12V * 500mA
    ctx.push_obligation(ProofObligation::assume("p5", "power_5v_mw == 5000")); // 5V * 1000mA
    ctx.push_obligation(ProofObligation::assume("p33", "power_3v3_mw == 660")); // 3.3V * 200mA
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total_mw == power_12v_mw + power_5v_mw + power_3v3_mw",
    ));
    ctx.push_obligation(ProofObligation::assert("is_11660", "total_mw == 11660"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PSU budget: 6000+5000+660=11660mW");
}

#[test]
fn efficiency_loss() {
    let mut ctx = VerificationContext::new();
    for v in &["input_power_mw", "output_power_mw", "loss_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ip", "input_power_mw == 12000"));
    ctx.push_obligation(ProofObligation::assume("op", "output_power_mw == 10800")); // 90% efficiency
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "loss_mw == input_power_mw - output_power_mw",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1200", "loss_mw == 1200"));
    ctx.push_obligation(ProofObligation::assert("positive_loss", "loss_mw > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PSU loss: 12000-10800=1200mW");
}

#[test]
fn overcurrent_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "ocp_threshold_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trip", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "current_ma == 6000"));
    ctx.push_obligation(ProofObligation::assume("ocp", "ocp_threshold_ma == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "trip == if current_ma > ocp_threshold_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OCP: 6000mA > 5000mA → trip");
}

#[test]
fn undervoltage_lockout() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mv", "uvlo_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume("iv", "input_mv == 10500")); // 10.5V
    ctx.push_obligation(ProofObligation::assume("ut", "uvlo_threshold_mv == 11000")); // 11V threshold
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "shutdown == if input_mv < uvlo_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UVLO: 10500mV < 11000mV → shutdown");
}

#[test]
fn capacitor_hold_time() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "capacitance_uf",
        "load_ma",
        "voltage_drop_mv",
        "hold_time_ms",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // hold_time ≈ C * ΔV / I (simplified with precomputed value)
    ctx.push_obligation(ProofObligation::assume("c", "capacitance_uf == 1000"));
    ctx.push_obligation(ProofObligation::assume("l", "load_ma == 500"));
    ctx.push_obligation(ProofObligation::assume("vd", "voltage_drop_mv == 1000"));
    ctx.push_obligation(ProofObligation::assume("ht", "hold_time_ms == 2")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2", "hold_time_ms == 2"));
    ctx.push_obligation(ProofObligation::assert("positive", "hold_time_ms > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hold time: 2ms for 1000µF/500mA/1V drop");
}

#[test]
fn rail_sequencing_order() {
    let mut ctx = VerificationContext::new();
    for v in &["rail_3v3_start_ms", "rail_5v_start_ms", "rail_12v_start_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("correct_order", i32_ty());
    // Typical sequencing: 3.3V first, then 5V, then 12V
    ctx.push_obligation(ProofObligation::assume("r33", "rail_3v3_start_ms == 0"));
    ctx.push_obligation(ProofObligation::assume("r5", "rail_5v_start_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("r12", "rail_12v_start_ms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "correct_order == if rail_3v3_start_ms < rail_5v_start_ms && rail_5v_start_ms < rail_12v_start_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "correct_order == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sequencing: 3.3V@0ms < 5V@10ms < 12V@20ms");
}

#[test]
fn thermal_derating() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "max_power_mw",
        "temp_c",
        "derating_start_c",
        "derated_power_mw",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("derated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_mw == 10000"));
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 60"));
    ctx.push_obligation(ProofObligation::assume("ds", "derating_start_c == 50"));
    ctx.push_obligation(ProofObligation::assume("dp", "derated_power_mw == 8000")); // derated
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "derated == if temp_c > derating_start_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "derated == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "reduced",
        "derated_power_mw < max_power_mw",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal: 60°C > 50°C → derated 8000 < 10000mW");
}

#[test]
fn ripple_voltage_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_mv", "max_ripple_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "ripple_mv == 30"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_mv == 50")); // 50mV max ripple
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if ripple_mv <= max_ripple_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ripple: 30mV <= 50mV max");
}

#[test]
fn load_sharing_balance() {
    let mut ctx = VerificationContext::new();
    for v in &["total_load_ma", "num_phases", "per_phase_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Balanced load sharing across phases
    ctx.push_obligation(ProofObligation::assume("tl", "total_load_ma == 6000"));
    ctx.push_obligation(ProofObligation::assume("np", "num_phases == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pp_def",
        "per_phase_ma == total_load_ma / num_phases",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2000", "per_phase_ma == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "load sharing: 6000/3=2000mA per phase");
}
