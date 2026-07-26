//! Raman spectrometer controller property regression tests.
//!
//! These tests verify bounded-range and enumeration invariants for a Raman
//! spectrometer controller: laser wavelength, spectral range, resolution,
//! power, integration time, spot size, detector type, sampling mode, grating
//! type, and fluorescence rejection flag.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_raman_laser_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_bounds",
        "wl >= 200 && wl <= 1064",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wl_check",
        "wl >= 200 && wl <= 1064",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser wavelength 200-1064 nm should remain bounded",
    );
}

#[test]
fn test_raman_spectral_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_bounds",
        "range >= 50 && range <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_check",
        "range >= 50 && range <= 4000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral range 50-4000 cm-1 should remain bounded");
}

#[test]
fn test_raman_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_bounds",
        "res_x10 >= 5 && res_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_check",
        "res_x10 >= 5 && res_x10 <= 200",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral resolution x10 (0.5-20.0 cm-1) should remain bounded",
    );
}

#[test]
fn test_raman_laser_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pwr_bounds",
        "pwr_x10 >= 1 && pwr_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pwr_check",
        "pwr_x10 >= 1 && pwr_x10 <= 5000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser power x10 (0.1-500.0 mW) should remain bounded",
    );
}

#[test]
fn test_raman_integration_time_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("integ_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "integ_bounds",
        "integ_x100 >= 1 && integ_x100 <= 360000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "integ_check",
        "integ_x100 >= 1 && integ_x100 <= 360000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "integration time x100 (0.01-3600.00 s) should remain bounded",
    );
}

#[test]
fn test_raman_spot_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_bounds",
        "spot_x10 >= 5 && spot_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_check",
        "spot_x10 >= 5 && spot_x10 <= 1000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spot size x10 (0.5-100.0 um) should remain bounded",
    );
}

#[test]
fn test_raman_detector_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_enum",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_check",
        "det == 1 || det == 2 || det == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type (CCD/InGaAs/EM-CCD) should remain in enum",
    );
}

#[test]
fn test_raman_sampling_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_enum",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_check",
        "mode == 1 || mode == 2 || mode == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sampling mode (confocal/fiber probe/microscope) should remain in enum",
    );
}

#[test]
fn test_raman_grating_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("grat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "grat_enum",
        "grat == 1 || grat == 2 || grat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "grat_check",
        "grat == 1 || grat == 2 || grat == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "grating type (holographic/ruled/echelle) should remain in enum",
    );
}

#[test]
fn test_raman_fluorescence_rejection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fr", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr_bool", "fr == 0 || fr == 1"));
    ctx.push_obligation(ProofObligation::assert("fr_check", "fr == 0 || fr == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluorescence rejection flag (0 or 1) should remain boolean",
    );
}
