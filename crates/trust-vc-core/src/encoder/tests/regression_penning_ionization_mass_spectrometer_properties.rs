// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Penning ionization mass spectrometer – property-based regression tests
// ---------------------------------------------------------------------------

/// Mass range in amu — bounded range.
#[test]
fn test_penning_ionization_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mr_a", "mass >= 1 && mass <= 1000"));
    ctx.push_obligation(ProofObligation::assert("mr_c", "mass >= 1 && mass <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Penning ionization MS mass range bounded");
}

/// Metastable energy at ×100 eV — bounded range.
#[test]
fn test_penning_ionization_ms_metastable_energy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "me_a",
        "energy_x100 >= 100 && energy_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "me_c",
        "energy_x100 >= 100 && energy_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Penning ionization MS metastable energy x100 bounded",
    );
}

/// Gas pressure at ×1000 torr — bounded range.
#[test]
fn test_penning_ionization_ms_gas_pressure_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gp_a",
        "press_x1000 >= 1 && press_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gp_c",
        "press_x1000 >= 1 && press_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Penning ionization MS gas pressure x1000 bounded");
}

/// Ion source temperature with offset +100 °C — bounded range.
#[test]
fn test_penning_ionization_ms_source_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "temp_off >= 50 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "temp_off >= 50 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Penning ionization MS source temperature offset bounded",
    );
}

/// Electron multiplier voltage — bounded range.
#[test]
fn test_penning_ionization_ms_electron_multiplier_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "em_a",
        "voltage >= 500 && voltage <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "em_c",
        "voltage >= 500 && voltage <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Penning ionization MS electron multiplier voltage bounded",
    );
}

/// Reaction chamber length in cm — bounded range.
#[test]
fn test_penning_ionization_ms_chamber_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cl_a",
        "length >= 5 && length <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cl_c",
        "length >= 5 && length <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Penning ionization MS chamber length bounded");
}

/// Metastable atom source — 3-way disjunction.
#[test]
fn test_penning_ionization_ms_metastable_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ms_a",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ms_c",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Penning ionization MS metastable source three-way disjunction",
    );
}

/// Analyzer type — 3-way disjunction.
#[test]
fn test_penning_ionization_ms_analyzer_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Penning ionization MS analyzer type three-way disjunction",
    );
}

/// Carrier gas — 3-way disjunction.
#[test]
fn test_penning_ionization_ms_carrier_gas_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cg_a",
        "carrier == 1 || carrier == 2 || carrier == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cg_c",
        "carrier == 1 || carrier == 2 || carrier == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Penning ionization MS carrier gas three-way disjunction",
    );
}

/// Automatic calibration — boolean flag.
#[test]
fn test_penning_ionization_ms_auto_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ac_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Penning ionization MS auto calibration flag");
}
