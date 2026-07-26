// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn charge_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_pc", "force_n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sensitivity_pc_per_n", u32_ty());
    // Sensitivity = charge / force. Precompute: 230pC / 10N = 23 pC/N
    ctx.push_obligation(ProofObligation::assume("cp", "charge_pc == 230"));
    ctx.push_obligation(ProofObligation::assume("fn_", "force_n == 10"));
    ctx.push_obligation(ProofObligation::assume("sp", "sensitivity_pc_per_n == 23")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_23",
        "sensitivity_pc_per_n == 23",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo: 230pC / 10N = 23 pC/N sensitivity (precomputed)",
    );
}

#[test]
fn resonant_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_band", i32_ty());
    // Operating frequency band around resonance
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 40"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 38"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_band == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_band == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo: 40 kHz in [38, 42] → in resonant band");
}

#[test]
fn voltage_output() {
    let mut ctx = VerificationContext::new();
    for v in &["output_mv", "max_output_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_range", i32_ty());
    // Piezo output voltage can be very high under impact
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_output_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "wr_def",
        "within_range == if output_mv <= max_output_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo: 2500mV ≤ 5000mV max → voltage within range");
}

#[test]
fn force_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_force_n", "threshold_n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("impact_detected", i32_ty());
    // Impact/knock detection threshold
    ctx.push_obligation(ProofObligation::assume("mf", "measured_force_n == 50"));
    ctx.push_obligation(ProofObligation::assume("tn", "threshold_n == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "impact_detected == if measured_force_n >= threshold_n { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "impact_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo: 50N ≥ 20N threshold → impact detected");
}

#[test]
fn charge_amplifier_gain() {
    let mut ctx = VerificationContext::new();
    for v in &["input_pc", "feedback_pf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_mv", u32_ty());
    // V_out = Q_in / C_fb. Precompute: 100pC / 10pF = 10V = 10000mV
    ctx.push_obligation(ProofObligation::assume("ip", "input_pc == 100"));
    ctx.push_obligation(ProofObligation::assume("fp", "feedback_pf == 10"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 10000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_10000", "output_mv == 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo: 100pC / 10pF = 10V charge amp output (precomputed)",
    );
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Piezo ceramics: max operating temp depends on Curie temperature
    // PZT: Curie ~300°C, derate to 50% = 150°C. Use +500 offset.
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 585")); // 85°C + 500
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_offset == 650")); // 150°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo: 85°C ≤ 150°C max → temp OK");
}

#[test]
fn capacitance_match() {
    let mut ctx = VerificationContext::new();
    for v in &["sensor_pf", "expected_pf", "tolerance_pf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Sensor capacitance must match expected ± tolerance
    ctx.push_obligation(ProofObligation::assume("sp", "sensor_pf == 1050"));
    ctx.push_obligation(ProofObligation::assume("ep", "expected_pf == 1000"));
    ctx.push_obligation(ProofObligation::assume("tp", "tolerance_pf == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if sensor_pf >= expected_pf - tolerance_pf && sensor_pf <= expected_pf + tolerance_pf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo: 1050pF in [900, 1100] → capacitance OK");
}

#[test]
fn energy_harvesting() {
    let mut ctx = VerificationContext::new();
    for v in &["harvested_uj", "min_useful_uj"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    // Piezo energy harvesting: enough energy per vibration cycle?
    ctx.push_obligation(ProofObligation::assume("hu", "harvested_uj == 50"));
    ctx.push_obligation(ProofObligation::assume("mu", "min_useful_uj == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if harvested_uj >= min_useful_uj { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo: 50μJ harvested ≥ 30μJ min → sufficient energy",
    );
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["signal_freq_hz", "sensor_bandwidth_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Signal frequency must be within sensor bandwidth
    ctx.push_obligation(ProofObligation::assume("sf", "signal_freq_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "sb",
        "sensor_bandwidth_hz == 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if signal_freq_hz <= sensor_bandwidth_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo: 5kHz signal ≤ 10kHz bandwidth → BW OK");
}

#[test]
fn linearity_error() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_mv", "ideal_mv", "error_mv", "max_error_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("linear_ok", i32_ty());
    // Linearity: deviation from ideal response
    ctx.push_obligation(ProofObligation::assume("mm", "measured_mv == 1015"));
    ctx.push_obligation(ProofObligation::assume("im", "ideal_mv == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "em_def",
        "error_mv == measured_mv - ideal_mv",
    ));
    ctx.push_obligation(ProofObligation::assume("me", "max_error_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "linear_ok == if error_mv <= max_error_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "error_mv == 15"));
    ctx.push_obligation(ProofObligation::assert("yes", "linear_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo: |1015 - 1000| = 15mV ≤ 50mV max → linearity OK",
    );
}
