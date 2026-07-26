// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_surge_gen_output_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    // Output voltage 100-20000 V per IEC 61000-4-5
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 100 && voltage <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 100 && voltage <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output voltage bounded 100-20000 V");
}

#[test]
fn test_surge_gen_short_circuit_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("isc", i32_ty());
    // Short circuit current 100-40000 A
    ctx.push_obligation(ProofObligation::assume(
        "isc_range",
        "isc >= 100 && isc <= 40000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "isc_bounded",
        "isc >= 100 && isc <= 40000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "short circuit current bounded 100-40000 A");
}

#[test]
fn test_surge_gen_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep_rate", i32_ty());
    // Repetition rate 1-60 shots/min
    ctx.push_obligation(ProofObligation::assume(
        "rep_range",
        "rep_rate >= 1 && rep_rate <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rep_bounded",
        "rep_rate >= 1 && rep_rate <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate bounded 1-60 shots/min");
}

#[test]
fn test_surge_gen_rise_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rise_x10", i32_ty());
    // Rise time x10 us (0.1 us precision): range 10-200 representing 1.0-20.0 us
    ctx.push_obligation(ProofObligation::assume(
        "rise_range",
        "rise_x10 >= 10 && rise_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rise_bounded",
        "rise_x10 >= 10 && rise_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rise time x10 bounded 10-200 (1.0-20.0 us)");
}

#[test]
fn test_surge_gen_pulse_duration_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dur_x10", i32_ty());
    // Pulse duration x10 us (0.1 us precision): range 100-1000 representing 10.0-100.0 us
    ctx.push_obligation(ProofObligation::assume(
        "dur_range",
        "dur_x10 >= 100 && dur_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dur_bounded",
        "dur_x10 >= 100 && dur_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pulse duration x10 bounded 100-1000 (10.0-100.0 us)",
    );
}

#[test]
fn test_surge_gen_output_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    // Number of output channels 1-8
    ctx.push_obligation(ProofObligation::assume("ch_range", "ch >= 1 && ch <= 8"));
    ctx.push_obligation(ProofObligation::assert("ch_bounded", "ch >= 1 && ch <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output channels bounded 1-8");
}

#[test]
fn test_surge_gen_waveform_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wf", i32_ty());
    // Waveform type: 1=combination-wave, 2=ring-wave, 3=telecom
    ctx.push_obligation(ProofObligation::assume(
        "wf_enum",
        "wf == 1 || wf == 2 || wf == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_valid",
        "wf == 1 || wf == 2 || wf == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "waveform type three-way (combination-wave/ring-wave/telecom)",
    );
}

#[test]
fn test_surge_gen_coupling_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coupling", i32_ty());
    // Coupling mode: 1=line-to-line, 2=line-to-ground, 3=both
    ctx.push_obligation(ProofObligation::assume(
        "coupling_enum",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coupling_valid",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coupling mode three-way (line-to-line/line-to-ground/both)",
    );
}

#[test]
fn test_surge_gen_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pol", i32_ty());
    // Polarity: 1=positive, 2=negative, 3=alternating
    ctx.push_obligation(ProofObligation::assume(
        "pol_enum",
        "pol == 1 || pol == 2 || pol == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pol_valid",
        "pol == 1 || pol == 2 || pol == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "polarity three-way (positive/negative/alternating)",
    );
}

#[test]
fn test_surge_gen_auto_sequence_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_seq", i32_ty());
    // Automatic test sequencing boolean: 0=disabled, 1=enabled
    ctx.push_obligation(ProofObligation::assume(
        "auto_seq_flag",
        "auto_seq == 0 || auto_seq == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_seq_valid",
        "auto_seq == 0 || auto_seq == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic test sequencing flag boolean (0 or 1)");
}
