// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_signal_gen_max_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    // Max frequency 1-80000000 Hz
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 1 && freq <= 80000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq >= 1 && freq <= 80000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max frequency bounded 1-80000000 Hz");
}

#[test]
fn test_signal_gen_amplitude_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_x1000", i32_ty());
    // Amplitude x1000 V (0.001V precision): valid range 1-20000
    ctx.push_obligation(ProofObligation::assume(
        "amp_range",
        "amp_x1000 >= 1 && amp_x1000 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "amp_bounded",
        "amp_x1000 >= 1 && amp_x1000 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "amplitude x1000 bounded 1-20000 (0.001V precision)",
    );
}

#[test]
fn test_signal_gen_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    // Frequency resolution x100 Hz (0.01 Hz precision): valid range 1-100
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x100 >= 1 && res_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res_x100 >= 1 && res_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "frequency resolution x100 bounded 1-100 (0.01 Hz precision)",
    );
}

#[test]
fn test_signal_gen_output_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z_out", i32_ty());
    // Output impedance 1-600 ohms
    ctx.push_obligation(ProofObligation::assume(
        "z_range",
        "z_out >= 1 && z_out <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "z_bounded",
        "z_out >= 1 && z_out <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output impedance bounded 1-600 ohms");
}

#[test]
fn test_signal_gen_harmonic_distortion_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thd_x10000", i32_ty());
    // THD x10000 (0.0001% precision): valid range 1-500
    ctx.push_obligation(ProofObligation::assume(
        "thd_range",
        "thd_x10000 >= 1 && thd_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thd_bounded",
        "thd_x10000 >= 1 && thd_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "harmonic distortion x10000 bounded 1-500 (0.0001% precision)",
    );
}

#[test]
fn test_signal_gen_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    // Output channels 1-4
    ctx.push_obligation(ProofObligation::assume("ch_range", "ch >= 1 && ch <= 4"));
    ctx.push_obligation(ProofObligation::assert("ch_bounded", "ch >= 1 && ch <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count bounded 1-4");
}

#[test]
fn test_signal_gen_waveform_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wf", i32_ty());
    // Waveform type: 1=sine, 2=square, 3=triangle
    ctx.push_obligation(ProofObligation::assume(
        "wf_enum",
        "wf == 1 || wf == 2 || wf == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_valid",
        "wf == 1 || wf == 2 || wf == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "waveform type three-way (sine/square/triangle)");
}

#[test]
fn test_signal_gen_modulation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_type", i32_ty());
    // Modulation type: 1=AM, 2=FM, 3=PM
    ctx.push_obligation(ProofObligation::assume(
        "mod_enum",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mod_valid",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modulation type three-way (AM/FM/PM)");
}

#[test]
fn test_signal_gen_trigger_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig", i32_ty());
    // Trigger mode: 1=internal, 2=external, 3=manual
    ctx.push_obligation(ProofObligation::assume(
        "trig_enum",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trig_valid",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trigger mode three-way (internal/external/manual)");
}

#[test]
fn test_signal_gen_burst_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burst", i32_ty());
    // Burst mode boolean: 0=off, 1=on
    ctx.push_obligation(ProofObligation::assume(
        "burst_flag",
        "burst == 0 || burst == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "burst_valid",
        "burst == 0 || burst == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "burst mode flag boolean (0 or 1)");
}
