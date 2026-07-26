// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: precision modulation analyzer property verification

use super::*;

#[test]
fn test_mod_analyzer_carrier_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "carrier_mhz >= 1 && carrier_mhz <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "carrier_mhz == 2400"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "carrier_mhz >= 1 && carrier_mhz <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "carrier frequency 2400 MHz within 1-50000 MHz range",
    );
}

#[test]
fn test_mod_analyzer_modulation_depth_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_depth_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "mod_depth_x1000 >= 1 && mod_depth_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "mod_depth_x1000 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "mod_depth_x1000 >= 1 && mod_depth_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "modulation depth accuracy x1000 value 10 (meaning 0.010%) within 1-500 range",
    );
}

#[test]
fn test_mod_analyzer_frequency_deviation_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_dev_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_dev_x100 >= 1 && freq_dev_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_dev_x100 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_dev_x100 >= 1 && freq_dev_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "frequency deviation accuracy x100 value 100 (meaning 1.00 Hz) within 1-100000 range",
    );
}

#[test]
fn test_mod_analyzer_audio_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("audio_freq_khz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "audio_freq_khz >= 1 && audio_freq_khz <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "audio_freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "audio_freq_khz >= 1 && audio_freq_khz <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "audio frequency range 100 kHz within 1-500 kHz range",
    );
}

#[test]
fn test_mod_analyzer_residual_fm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("residual_fm_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "residual_fm_x10 >= 1 && residual_fm_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "residual_fm_x10 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "residual_fm_x10 >= 1 && residual_fm_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "residual FM x10 value 5 (meaning 0.5 Hz) within 1-1000 range",
    );
}

#[test]
fn test_mod_analyzer_demod_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("demod_channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "demod_channels >= 1 && demod_channels <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "demod_channels == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "demod_channels >= 1 && demod_channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "demodulation channels 2 within 1-8 range");
}

#[test]
fn test_mod_analyzer_modulation_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "mod_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modulation type is AM(1), FM(2), or PM(3)");
}

#[test]
fn test_mod_analyzer_demod_bandwidth_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("demod_bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "demod_bw == 1 || demod_bw == 2 || demod_bw == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "demod_bw == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "demod_bw == 1 || demod_bw == 2 || demod_bw == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "demodulation bandwidth is narrow(1), wide(2), or ultra-wide(3)",
    );
}

#[test]
fn test_mod_analyzer_display_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("display_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "display_mode == 1 || display_mode == 2 || display_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "display_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "display_mode == 1 || display_mode == 2 || display_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "display mode is spectrum(1), time-domain(2), or constellation(3)",
    );
}

#[test]
fn test_mod_analyzer_auto_carrier_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "tracking_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic carrier tracking flag set implies conditional evaluates to 1",
    );
}
