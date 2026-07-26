// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Time-of-flight mass spectrometer (TOF-MS) property regression tests

use super::*;

#[test]
fn test_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "mz >= 1000 && mz <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "mz == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "mz >= 1000 && mz <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max m/z ratio bounded within 1000-500000");
}

#[test]
fn test_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolving_power", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolving_power >= 5000 && resolving_power <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolving_power == 40000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resolving_power >= 5000 && resolving_power <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FWHM resolving power bounded within 5000-100000");
}

#[test]
fn test_mass_accuracy_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "accuracy_x10 >= 1 && accuracy_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x10 >= 1 && accuracy_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mass accuracy x10 ppm bounded within 1-100 (1.0 ppm)",
    );
}

#[test]
fn test_acquisition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spectra_per_sec", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spectra_per_sec >= 1 && spectra_per_sec <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spectra_per_sec == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spectra_per_sec >= 1 && spectra_per_sec <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "acquisition rate bounded within 1-100000 spectra/s",
    );
}

#[test]
fn test_flight_tube_length_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "length_x10 >= 5 && length_x10 <= 30",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "length_x10 == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "length_x10 >= 5 && length_x10 <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flight tube length x10 m bounded within 5-30 (2.0 m)",
    );
}

#[test]
fn test_accelerating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "voltage_kv == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accelerating voltage bounded within 1-30 kV");
}

#[test]
fn test_ionization_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionization", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionization mode is ESI(1), MALDI(2), or APCI(3)");
}

#[test]
fn test_reflectron_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reflectron", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "reflectron == 1 || reflectron == 2 || reflectron == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "reflectron == 1 || reflectron == 2 || reflectron == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reflectron mode is linear(1), single-reflectron(2), or multi-reflectron(3)",
    );
}

#[test]
fn test_detector_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type is MCP(1), hybrid(2), or electron-multiplier(3)",
    );
}

#[test]
fn test_orthogonal_extraction_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enabled", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "extraction",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orthogonal extraction flag enabled implies extraction active",
    );
}
