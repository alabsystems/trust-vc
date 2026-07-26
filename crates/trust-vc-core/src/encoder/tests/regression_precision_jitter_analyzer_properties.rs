// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: precision jitter analyzer property verification

use super::*;

#[test]
fn test_jitter_analyzer_clock_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clock_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "clock_mhz >= 1 && clock_mhz <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "clock_mhz == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "clock_mhz >= 1 && clock_mhz <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "clock frequency 10000 MHz within 1-50000 MHz range",
    );
}

#[test]
fn test_jitter_analyzer_timing_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x1000ps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolution_x1000ps >= 1 && resolution_x1000ps <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolution_x1000ps == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resolution_x1000ps >= 1 && resolution_x1000ps <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "timing resolution x1000 ps value 100 (meaning 0.100 ps) within 1-10000 range",
    );
}

#[test]
fn test_jitter_analyzer_rms_jitter_floor_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rms_floor_x100fs", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rms_floor_x100fs >= 1 && rms_floor_x100fs <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rms_floor_x100fs == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rms_floor_x100fs >= 1 && rms_floor_x100fs <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RMS jitter floor x100 fs value 10 (meaning 0.10 fs) within 1-10000 range",
    );
}

#[test]
fn test_jitter_analyzer_record_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("record_length", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "record_length >= 1000 && record_length <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "record_length == 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "record_length >= 1000 && record_length <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "record length 1000000 samples within 1000-10000000 range",
    );
}

#[test]
fn test_jitter_analyzer_number_of_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels 4 within 1-8 range");
}

#[test]
fn test_jitter_analyzer_bit_error_rate_sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ber_sensitivity_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ber_sensitivity_x10 >= 30 && ber_sensitivity_x10 <= 180",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "ber_sensitivity_x10 == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "ber_sensitivity_x10 >= 30 && ber_sensitivity_x10 <= 180",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BER sensitivity x10 value 120 (meaning 12.0 exponent placeholder) within 30-180 range",
    );
}

#[test]
fn test_jitter_analyzer_decomposition_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decomp_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "decomp_mode == 1 || decomp_mode == 2 || decomp_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "decomp_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "decomp_mode == 1 || decomp_mode == 2 || decomp_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jitter decomposition mode is TJ-DJ-RJ(1), spectrum(2), or bathtub(3)",
    );
}

#[test]
fn test_jitter_analyzer_trigger_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trigger_src == 1 || trigger_src == 2 || trigger_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "trigger_src == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trigger_src == 1 || trigger_src == 2 || trigger_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger source is clock-recovery(1), external(2), or pattern-sync(3)",
    );
}

#[test]
fn test_jitter_analyzer_analysis_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analysis_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "analysis_mode == 1 || analysis_mode == 2 || analysis_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "analysis_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "analysis_mode == 1 || analysis_mode == 2 || analysis_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode is real-time(1), equivalent-time(2), or statistical(3)",
    );
}

#[test]
fn test_jitter_analyzer_automatic_pattern_lock_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "lock_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic pattern lock flag set implies conditional evaluates to 1",
    );
}
