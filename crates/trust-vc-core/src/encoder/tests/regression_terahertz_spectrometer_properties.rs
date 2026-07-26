// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_thz_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_x10_val", "freq_x10 == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "freq_x10_bounded",
        "freq_x10 >= 1 && freq_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency 4.0 THz (x10=40) in [1, 100]");
}

#[test]
fn test_thz_spectral_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_x100_val", "res_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "res_x100_bounded",
        "res_x100 >= 1 && res_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral resolution 0.10 GHz (x100=10) in [1, 10000]",
    );
}

#[test]
fn test_thz_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dynamic_range_val",
        "dynamic_range == 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dynamic_range_bounded",
        "dynamic_range >= 20 && dynamic_range <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range 80 dB in [20, 120]");
}

#[test]
fn test_thz_signal_to_noise_ratio_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("snr", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snr_val", "snr == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "snr_bounded",
        "snr >= 10 && snr <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signal-to-noise ratio 60 dB in [10, 80]");
}

#[test]
fn test_thz_scan_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("scan_rate_val", "scan_rate == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "scan_rate_bounded",
        "scan_rate >= 1 && scan_rate <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan rate 100 scans/sec in [1, 10000]");
}

#[test]
fn test_thz_beam_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("beam_x10_val", "beam_x10 == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "beam_x10_bounded",
        "beam_x10 >= 1 && beam_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam diameter 2.0 mm (x10=20) in [1, 200]");
}

#[test]
fn test_thz_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_type_val",
        "source_type == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_type_valid",
        "source_type == 1 || source_type == 2 || source_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source type 1=photoconductive in {1=photoconductive, 2=optical-rectification, 3=QCL}",
    );
}

#[test]
fn test_thz_detection_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detection", i32_ty());
    ctx.push_obligation(ProofObligation::assume("detection_val", "detection == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "detection_valid",
        "detection == 1 || detection == 2 || detection == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method 1=photoconductive in {1=photoconductive, 2=electro-optic, 3=bolometer}",
    );
}

#[test]
fn test_thz_measurement_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode 1=transmission in {1=transmission, 2=reflection, 3=ATR}",
    );
}

#[test]
fn test_thz_auto_delay_line_scanning_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_delay_line_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic delay line scanning flag=1 yields active (1)",
    );
}
