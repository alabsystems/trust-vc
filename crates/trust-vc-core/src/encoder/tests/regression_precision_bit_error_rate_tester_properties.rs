// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: precision bit error rate tester (BERT) property verification

use super::*;

#[test]
fn test_bert_data_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_rate_gbps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "data_rate_gbps >= 1 && data_rate_gbps <= 400",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "data_rate_gbps == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "data_rate_gbps >= 1 && data_rate_gbps <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data rate 100 Gbps within 1-400 Gbps range");
}

#[test]
fn test_bert_pattern_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern_length", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pattern_length >= 7 && pattern_length <= 31",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pattern_length == 31"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pattern_length >= 7 && pattern_length <= 31",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PRBS pattern length 31 (PRBS31) within 7-31 range");
}

#[test]
fn test_bert_ber_sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ber_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ber_offset >= 10 && ber_offset <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "ber_offset == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "ber_offset >= 10 && ber_offset <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BER sensitivity offset 80 (meaning exponent -12) within 10-200 range",
    );
}

#[test]
fn test_bert_number_of_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels 4 within 1-16 range");
}

#[test]
fn test_bert_jitter_tolerance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jitter_x100ui", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "jitter_x100ui >= 1 && jitter_x100ui <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "jitter_x100ui == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "jitter_x100ui >= 1 && jitter_x100ui <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jitter tolerance x100 UI value 10 (meaning 0.10 UI) within 1-500 range",
    );
}

#[test]
fn test_bert_clock_recovery_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cr_bw_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "cr_bw_mhz >= 1 && cr_bw_mhz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "cr_bw_mhz == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "cr_bw_mhz >= 1 && cr_bw_mhz <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "clock recovery bandwidth 100 MHz within 1-10000 MHz range",
    );
}

#[test]
fn test_bert_error_injection_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("error_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "error_mode == 1 || error_mode == 2 || error_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "error_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "error_mode == 1 || error_mode == 2 || error_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "error injection mode is single-bit(1), burst(2), or pattern(3)",
    );
}

#[test]
fn test_bert_signal_format_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal_fmt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "signal_fmt == 1 || signal_fmt == 2 || signal_fmt == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "signal_fmt == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "signal_fmt == 1 || signal_fmt == 2 || signal_fmt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signal format is NRZ(1), PAM4(2), or PAM8(3)");
}

#[test]
fn test_bert_equalizer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eq_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "eq_type == 1 || eq_type == 2 || eq_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "eq_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "eq_type == 1 || eq_type == 2 || eq_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equalizer type is CTLE(1), DFE(2), or FFE(3)");
}

#[test]
fn test_bert_automatic_sync_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sync_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic sync detection flag set implies conditional evaluates to 1",
    );
}
