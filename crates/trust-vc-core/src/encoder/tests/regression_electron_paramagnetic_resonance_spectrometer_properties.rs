//! Electron paramagnetic resonance (EPR/ESR) spectrometer property tests.
//!
//! These tests verify bounded and enumerated constraints modeling EPR
//! spectrometer parameters through the trust_vc verification pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// Microwave frequency bounded between 1 and 100 GHz.
#[test]
fn test_epr_microwave_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_bounded",
        "freq >= 1 && freq <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_check",
        "freq >= 1 && freq <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microwave frequency in [1, 100] GHz should verify");
}

/// Magnetic field bounded between 0 and 14000 Gauss.
#[test]
fn test_epr_magnetic_field_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("field", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "field_bounded",
        "field >= 0 && field <= 14000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "field_check",
        "field >= 0 && field <= 14000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field in [0, 14000] Gauss should verify");
}

/// Sensitivity scaled by 100 (representing 0.01 spins/G resolution),
/// bounded between 1 and 100000.
#[test]
fn test_epr_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_bounded",
        "sens_x100 >= 1 && sens_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sens_check",
        "sens_x100 >= 1 && sens_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity x100 in [1, 100000] should verify");
}

/// Modulation amplitude scaled by 100 (representing 0.01 G resolution),
/// bounded between 1 and 10000.
#[test]
fn test_epr_modulation_amplitude_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mod_bounded",
        "mod_x100 >= 1 && mod_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mod_check",
        "mod_x100 >= 1 && mod_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "modulation amplitude x100 in [1, 10000] should verify",
    );
}

/// Microwave power scaled by 10 (representing 0.1 mW resolution),
/// bounded between 1 and 2000.
#[test]
fn test_epr_microwave_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pwr_bounded",
        "pwr_x10 >= 1 && pwr_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pwr_check",
        "pwr_x10 >= 1 && pwr_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "microwave power x10 in [1, 2000] should verify");
}

/// Sweep width bounded between 1 and 10000 Gauss.
#[test]
fn test_epr_sweep_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sweep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sweep_bounded",
        "sweep >= 1 && sweep <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sweep_check",
        "sweep >= 1 && sweep <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sweep width in [1, 10000] Gauss should verify");
}

/// Resonator type: 1 = rectangular, 2 = cylindrical, 3 = dielectric.
#[test]
fn test_epr_resonator_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_enum",
        "res == 1 || res == 2 || res == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_check",
        "res == 1 || res == 2 || res == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resonator type in {1, 2, 3} should verify");
}

/// Frequency band: 1 = X-band, 2 = Q-band, 3 = W-band.
#[test]
fn test_epr_frequency_band_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("band", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "band_enum",
        "band == 1 || band == 2 || band == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "band_check",
        "band == 1 || band == 2 || band == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency band in {1, 2, 3} should verify");
}

/// Detection mode: 1 = CW, 2 = pulsed, 3 = ENDOR.
#[test]
fn test_epr_detection_mode_three_way() {
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
    expect_verified(&result, "detection mode in {1, 2, 3} should verify");
}

/// Cryostat presence as boolean flag: 0 or 1.
#[test]
fn test_epr_cryostat_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cryo", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cryo_bool",
        "cryo == 0 || cryo == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cryo_check",
        "cryo == 0 || cryo == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cryostat flag in {0, 1} should verify");
}
