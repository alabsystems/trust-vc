// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Regression tests: precision signal source analyzer property verification

use super::*;

#[test]
fn test_signal_source_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", i32_ty());
    // Frequency range 1-50000 MHz
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq_mhz >= 1 && freq_mhz <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq_mhz == 26500"));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq_mhz >= 1 && freq_mhz <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency 26500 MHz within 1-50000 MHz range");
}

#[test]
fn test_signal_source_phase_noise_floor_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_off200", i32_ty());
    // Phase noise floor with offset +200 dBc/Hz: -170 dBc/Hz -> 30, range 1-200
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise_off200 >= 1 && noise_off200 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("noise_val", "noise_off200 == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "noise_bounded",
        "noise_off200 >= 1 && noise_off200 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase noise floor offset+200 value 30 (meaning -170 dBc/Hz) within 1-200 range",
    );
}

#[test]
fn test_signal_source_spurious_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spur_off200", i32_ty());
    // Spurious level with offset +200 dBc: -80 dBc -> 120, range 1-200
    ctx.push_obligation(ProofObligation::assume(
        "spur_range",
        "spur_off200 >= 1 && spur_off200 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("spur_val", "spur_off200 == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "spur_bounded",
        "spur_off200 >= 1 && spur_off200 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spurious level offset+200 value 120 (meaning -80 dBc) within 1-200 range",
    );
}

#[test]
fn test_signal_source_amplitude_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x1000", i32_ty());
    // Amplitude accuracy x1000 dB (0.001 dB precision): 50 = 0.050 dB, range 1-1000
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x1000 >= 1 && acc_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x1000 >= 1 && acc_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "amplitude accuracy x1000 value 50 (meaning 0.050 dB) within 1-1000 range",
    );
}

#[test]
fn test_signal_source_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    // Number of channels 1-16
    ctx.push_obligation(ProofObligation::assume(
        "ch_range",
        "channels >= 1 && channels <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("ch_val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "ch_bounded",
        "channels >= 1 && channels <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count 4 within 1-16 range");
}

#[test]
fn test_signal_source_measurement_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    // Measurement speed 1-10000 measurements/sec
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1 && speed <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1 && speed <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement speed 1000 within 1-10000 measurements/sec range",
    );
}

#[test]
fn test_signal_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src_type", i32_ty());
    // Source type: 1=synthesized, 2=VCO, 3=DDS
    ctx.push_obligation(ProofObligation::assume(
        "src_valid",
        "src_type == 1 || src_type == 2 || src_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("src_val", "src_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "src_disjunction",
        "src_type == 1 || src_type == 2 || src_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source type is synthesized(1), VCO(2), or DDS(3)");
}

#[test]
fn test_signal_source_modulation_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_type", i32_ty());
    // Modulation type: 1=AM, 2=FM, 3=phase
    ctx.push_obligation(ProofObligation::assume(
        "mod_valid",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("mod_val", "mod_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "mod_disjunction",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modulation type is AM(1), FM(2), or phase(3)");
}

#[test]
fn test_signal_source_reference_oscillator_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_osc", i32_ty());
    // Reference oscillator: 1=OCXO, 2=TCXO, 3=rubidium
    ctx.push_obligation(ProofObligation::assume(
        "ref_valid",
        "ref_osc == 1 || ref_osc == 2 || ref_osc == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("ref_val", "ref_osc == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "ref_disjunction",
        "ref_osc == 1 || ref_osc == 2 || ref_osc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference oscillator is OCXO(1), TCXO(2), or rubidium(3)",
    );
}

#[test]
fn test_signal_source_cross_correlation_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("xcorr_flag", i32_ty());
    // Cross-correlation mode boolean flag: 0=off, 1=on
    ctx.push_obligation(ProofObligation::assume("flag_set", "xcorr_flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "xcorr_active",
        "if xcorr_flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cross-correlation mode flag set implies conditional evaluates to 1",
    );
}
