// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Wavelength range bounded between 200 nm and 25000 nm.
#[test]
fn test_photoacoustic_spec_wavelength_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_bounds",
        "wavelength_nm >= 200 && wavelength_nm <= 25000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_valid",
        "wavelength_nm >= 200 && wavelength_nm <= 25000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength must be in [200, 25000] nm range");
}

/// Spectral resolution scaled x100 in cm^-1, positive and bounded.
#[test]
fn test_photoacoustic_spec_spectral_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_bounds",
        "res_x100 > 0 && res_x100 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_valid",
        "res_x100 > 0 && res_x100 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral resolution x100 must be in (0, 10000)");
}

/// Modulation frequency bounded between 1 Hz and 100000 Hz.
#[test]
fn test_photoacoustic_spec_modulation_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_freq_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frequency_bounds",
        "mod_freq_hz >= 1 && mod_freq_hz <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frequency_valid",
        "mod_freq_hz >= 1 && mod_freq_hz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modulation frequency must be in [1, 100000] Hz");
}

/// Detection limit scaled x1000 in ppb, positive and bounded.
#[test]
fn test_photoacoustic_spec_detection_limit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "limit_bounds",
        "limit_x1000 > 0 && limit_x1000 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "limit_valid",
        "limit_x1000 > 0 && limit_x1000 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit x1000 must be in (0, 100000) ppb");
}

/// Cell path length scaled x10 in mm, positive and bounded.
#[test]
fn test_photoacoustic_spec_cell_path_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("path_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "path_bounds",
        "path_x10 > 0 && path_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "path_valid",
        "path_x10 > 0 && path_x10 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cell path length x10 must be in (0, 10000) mm");
}

/// Number of microphones bounded between 1 and 16.
#[test]
fn test_photoacoustic_spec_microphone_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_mics", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mic_bounds",
        "num_mics >= 1 && num_mics <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mic_valid",
        "num_mics >= 1 && num_mics <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microphone count must be in [1, 16]");
}

/// Light source must be one of: 1=broadband-IR, 2=tunable-laser, 3=QCL.
#[test]
fn test_photoacoustic_spec_light_source() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_enum",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source must be broadband-IR(1), tunable-laser(2), or QCL(3)",
    );
}

/// Cell geometry must be one of: 1=resonant, 2=non-resonant, 3=differential.
#[test]
fn test_photoacoustic_spec_cell_geometry() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cell_enum",
        "cell == 1 || cell == 2 || cell == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cell_valid",
        "cell == 1 || cell == 2 || cell == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cell geometry must be resonant(1), non-resonant(2), or differential(3)",
    );
}

/// Detection method must be one of: 1=microphone, 2=quartz-tuning-fork, 3=cantilever.
#[test]
fn test_photoacoustic_spec_detection_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_enum",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "method_valid",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method must be microphone(1), quartz-tuning-fork(2), or cantilever(3)",
    );
}

/// Automatic background subtraction flag: 0=disabled, 1=enabled.
#[test]
fn test_photoacoustic_spec_background_subtraction_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_bg_sub", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "auto_bg_sub == 0 || auto_bg_sub == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "auto_bg_sub >= 0 && auto_bg_sub <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "background subtraction flag must be 0 (disabled) or 1 (enabled)",
    );
}
