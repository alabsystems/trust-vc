// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Operating frequency (kHz): excitation frequency for the inductive loop.
/// Typical value 50 kHz, valid range [20, 200].
#[test]
fn test_operating_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["freq", "min_freq", "max_freq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq == 50"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_freq == 20"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_freq == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "freq_in_range",
        "freq >= min_freq && freq <= max_freq",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating frequency 50 kHz in [20, 200]");
}

/// Sensitivity (x10 %): detection threshold scaled by 10 to avoid decimals.
/// Value 20 represents 2.0%, valid range [5, 100] (i.e. 0.5% to 10.0%).
#[test]
fn test_sensitivity_threshold_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["sens", "min_sens", "max_sens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sens_val", "sens == 20"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_sens == 5"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_sens == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "sens_in_range",
        "sens >= min_sens && sens <= max_sens",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity 20 (2.0%) in [5, 100]");
}

/// Channel count: number of independent detection zones.
/// Value 4 channels, valid range [1, 16].
#[test]
fn test_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_ch", "max_ch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch_val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_ch == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_ch == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "ch_in_range",
        "channels >= min_ch && channels <= max_ch",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count 4 in [1, 16]");
}

/// Detection mode: 4-way disjunction.
/// 1=presence, 2=pulse, 3=count, 4=speed. Mode must be exactly one of these.
#[test]
fn test_detection_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3 || mode == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection mode 1 (presence) is valid 4-way choice");
}

/// Output type: 3-way disjunction.
/// 1=relay, 2=open-collector, 3=solid-state. Must be exactly one.
#[test]
fn test_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.push_obligation(ProofObligation::assume("output_val", "output == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "output_valid",
        "output == 1 || output == 2 || output == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 1 (relay) is valid 3-way choice");
}

/// Loop inductance (uH): the inductance of the detection loop wire.
/// Value 100 uH, valid range [20, 2000].
#[test]
fn test_loop_inductance_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["inductance", "min_ind", "max_ind"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ind_val", "inductance == 100"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_ind == 20"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_ind == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "ind_in_range",
        "inductance >= min_ind && inductance <= max_ind",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "loop inductance 100 uH in [20, 2000]");
}

/// Response time (ms): detection latency from vehicle entry to output assertion.
/// Value 50 ms, valid range [10, 500].
#[test]
fn test_response_time_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_time", "min_resp", "max_resp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("resp_val", "resp_time == 50"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_resp == 10"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_resp == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "resp_in_range",
        "resp_time >= min_resp && resp_time <= max_resp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 50 ms in [10, 500]");
}

/// Operating temperature offset +500 (deg C): temperature shifted to avoid negatives.
/// Value 525 represents 25 deg C (525 - 500 = 25).
/// Min 460 represents -40 deg C, max 585 represents 85 deg C.
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 525"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_temp == 460"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_temp == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= min_temp && temp <= max_temp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temp offset 525 (25 deg C) in [460, 585]");
}

/// Supply voltage (mV): detector power supply in millivolts.
/// Value 24000 mV (24V), valid range [10000, 30000] (10V to 30V).
#[test]
fn test_supply_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage", "min_volt", "max_volt"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("volt_val", "voltage == 24000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_volt == 10000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_volt == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "volt_in_range",
        "voltage >= min_volt && voltage <= max_volt",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "supply voltage 24000 mV (24V) in [10000, 30000]");
}

/// Fail-safe mode (boolean flag): when enabled (1), detector outputs safe state on fault.
/// Uses i32_ty with 0/1 convention. Verifies that the output is forced safe when flag is set.
#[test]
fn test_failsafe_mode_flag() {
    let mut ctx = VerificationContext::new();
    for v in &["failsafe", "fault_detected", "raw_output", "final_output"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("failsafe_enabled", "failsafe == 1"));
    ctx.push_obligation(ProofObligation::assume("fault_yes", "fault_detected == 1"));
    ctx.push_obligation(ProofObligation::assume("raw_val", "raw_output == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "output_def",
        "final_output == if failsafe == 1 { if fault_detected == 1 { 0 } else { raw_output } } else { raw_output }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "safe_on_fault",
        "final_output == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fail-safe mode forces output to 0 on fault");
}
