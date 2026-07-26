// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_spectral_range_min_bounded() {
    // FTIR spectral range minimum (cm⁻¹) must be in [350, 500]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_min_cm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rm", "range_min_cm == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if range_min_cm >= 350 && range_min_cm <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: range min 400 cm⁻¹ in [350, 500]");
}

#[test]
fn test_spectral_range_max_bounded() {
    // FTIR spectral range maximum (cm⁻¹) must be in [4000, 8000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_max_cm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rm", "range_max_cm == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if range_max_cm >= 4000 && range_max_cm <= 8000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: range max 4000 cm⁻¹ in [4000, 8000]");
}

#[test]
fn test_resolution_scaled() {
    // Resolution scaled ×100: value 50 represents 0.50 cm⁻¹
    // Valid range: 1 to 400 (i.e. 0.01 to 4.00 cm⁻¹)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x100", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "resolution_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if resolution_x100 >= 1 && resolution_x100 <= 400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: resolution 50 (0.50 cm⁻¹) in [1, 400]");
}

#[test]
fn test_signal_to_noise_ratio_bounded() {
    // SNR must be in [1000, 100000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("snr", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "snr == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if snr >= 1000 && snr <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: SNR 50000 in [1000, 100000]");
}

#[test]
fn test_scan_speed_bounded() {
    // Scan speed (scans/s) must be in [1, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scans_per_sec", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ss", "scans_per_sec == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if scans_per_sec >= 1 && scans_per_sec <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: scan speed 40 scans/s in [1, 100]");
}

#[test]
fn test_beam_splitter_type() {
    // Beam splitter: 1=KBr, 2=CaF2, 3=ZnSe
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_splitter", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bs", "beam_splitter == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if beam_splitter == 1 || beam_splitter == 2 || beam_splitter == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: beam splitter CaF2 (2) is valid");
}

#[test]
fn test_detector_type() {
    // Detector: 1=DTGS, 2=MCT, 3=InGaAs
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "detector == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector == 1 || detector == 2 || detector == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: detector DTGS (1) is valid");
}

#[test]
fn test_sampling_mode() {
    // Sampling mode: 1=transmission, 2=ATR, 3=DRIFTS
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sampling_mode", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sm", "sampling_mode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sampling_mode == 1 || sampling_mode == 2 || sampling_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: sampling mode DRIFTS (3) is valid");
}

#[test]
fn test_interferometer_alignment_steps_bounded() {
    // Auto-alignment steps must be in [1, 64]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alignment_steps", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("as_val", "alignment_steps == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if alignment_steps >= 1 && alignment_steps <= 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: alignment 32 steps in [1, 64]");
}

#[test]
fn test_nitrogen_purge_flag() {
    // Nitrogen purge: i32 boolean flag (1=purged, 0=ambient)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("purge_active", i32_ty());
    ctx.declare_var_typed("chamber_clean", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pa", "purge_active == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "chamber_clean == if purge_active == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "chamber_clean == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FTIR: nitrogen purge active → chamber clean");
}
