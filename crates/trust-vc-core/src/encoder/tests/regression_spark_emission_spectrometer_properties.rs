// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Spark OES wavelength range: 130-800 nm (UV to visible).
#[test]
fn test_spark_oes_wavelength_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_bounds",
        "wavelength_nm >= 130 && wavelength_nm <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_valid",
        "wavelength_nm >= 130 && wavelength_nm <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spark OES wavelength must be within 130-800 nm");
}

/// Spectral resolution scaled x1000 to avoid fractional nm.
#[test]
fn test_spark_oes_spectral_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_bounds",
        "res_x1000 > 0 && res_x1000 < 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_positive",
        "res_x1000 > 0 && res_x1000 < 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral resolution x1000 must be in (0, 1000)");
}

/// Spark repetition frequency: 1-1000 Hz.
#[test]
fn test_spark_oes_spark_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_bounds",
        "freq_hz >= 1 && freq_hz <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_valid",
        "freq_hz >= 1 && freq_hz <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spark frequency must be within 1-1000 Hz");
}

/// Spark energy scaled x100 to represent millijoules without fractions.
#[test]
fn test_spark_oes_spark_energy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_bounds",
        "energy_x100 > 0 && energy_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_positive",
        "energy_x100 > 0 && energy_x100 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spark energy x100 must be in (0, 100000)");
}

/// Number of detector channels: 1-100.
#[test]
fn test_spark_oes_number_of_channels() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "channel_bounds",
        "channels >= 1 && channels <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "channels_valid",
        "channels >= 1 && channels <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels must be within 1-100");
}

/// Detection limit scaled x10000 to represent ppm without fractions.
#[test]
fn test_spark_oes_detection_limit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "limit_bounds",
        "limit_x10000 > 0 && limit_x10000 < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "limit_positive",
        "limit_x10000 > 0 && limit_x10000 < 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit x10000 must be in (0, 1000000)");
}

/// Spark source type: 1=unidirectional, 2=multi-source, 3=arc.
#[test]
fn test_spark_oes_spark_source_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_in_range",
        "source >= 1 && source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source must be unidirectional(1), multi-source(2), or arc(3)",
    );
}

/// Optics type: 1=Paschen-Runge, 2=Czerny-Turner, 3=echelle.
#[test]
fn test_spark_oes_optics_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "optics_valid",
        "optics == 1 || optics == 2 || optics == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "optics_in_range",
        "optics >= 1 && optics <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optics must be Paschen-Runge(1), Czerny-Turner(2), or echelle(3)",
    );
}

/// Sample preparation: 1=surface-grind, 2=remelting, 3=none.
#[test]
fn test_spark_oes_sample_prep() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "prep_valid",
        "prep == 1 || prep == 2 || prep == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "prep_in_range",
        "prep >= 1 && prep <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample prep must be surface-grind(1), remelting(2), or none(3)",
    );
}

/// Automatic standardization flag: 0=disabled, 1=enabled (boolean as i32).
#[test]
fn test_spark_oes_auto_standardization() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "auto_std == 0 || auto_std == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "auto_std >= 0 && auto_std <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto standardization flag must be 0 (disabled) or 1 (enabled)",
    );
}
