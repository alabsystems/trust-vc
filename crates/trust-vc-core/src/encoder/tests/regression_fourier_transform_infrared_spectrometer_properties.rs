// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: Fourier transform infrared (FTIR) spectrometer properties

use super::*;

#[test]
fn test_ftir_wavenumber_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wn_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "wn_min >= 200 && wn_min <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "wn_min == 350"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wn_min >= 200 && wn_min <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral range minimum wavenumber 350 cm-1 within 200-600 cm-1",
    );
}

#[test]
fn test_ftir_wavenumber_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wn_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "wn_max >= 4000 && wn_max <= 8000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "wn_max == 7800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wn_max >= 4000 && wn_max <= 8000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral range maximum wavenumber 7800 cm-1 within 4000-8000 cm-1",
    );
}

#[test]
fn test_ftir_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "res_x100 >= 5 && res_x100 <= 1600",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "res_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "res_x100 >= 5 && res_x100 <= 1600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral resolution x100 value 50 (0.50 cm-1) within 5-1600 range",
    );
}

#[test]
fn test_ftir_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scans_per_sec", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "scans_per_sec >= 1 && scans_per_sec <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "scans_per_sec == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "scans_per_sec >= 1 && scans_per_sec <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed 40 scans per second within 1-100 range");
}

#[test]
fn test_ftir_signal_to_noise_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("snr_x10", u64_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "snr_x10 >= 100 && snr_x10 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "snr_x10 == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "snr_x10 >= 100 && snr_x10 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "signal-to-noise ratio x10 value 500000 (50000.0:1) within 100-1000000 range",
    );
}

#[test]
fn test_ftir_detector_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dstar_x100", u64_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dstar_x100 >= 100 && dstar_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dstar_x100 == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dstar_x100 >= 100 && dstar_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector sensitivity D* x100 value 10000 within 100-100000 range",
    );
}

#[test]
fn test_ftir_beam_splitter_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bs", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "bs == 1 || bs == 2 || bs == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("bounded", "bs >= 1 && bs <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam splitter type 1=KBr 2=CaF2 3=ZnSe implies bounded 1-3",
    );
}

#[test]
fn test_ftir_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("bounded", "det >= 1 && det <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type 1=DTGS 2=MCT 3=InGaAs implies bounded 1-3",
    );
}

#[test]
fn test_ftir_sampling_technique_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("samp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "samp == 1 || samp == 2 || samp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("bounded", "samp >= 1 && samp <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sampling technique 1=transmission 2=ATR 3=DRIFTS implies bounded 1-3",
    );
}

#[test]
fn test_ftir_nitrogen_purged_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_true", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nitrogen purge flag set to 1 implies conditional evaluates to 1",
    );
}
