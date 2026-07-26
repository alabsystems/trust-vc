// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Auger Electron Spectrometer (AES) property verification tests
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_aes_kinetic_energy_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ke", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_ke_bounds",
        "ke >= 20 && ke <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_ke_range",
        "ke >= 20 && ke <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "kinetic energy must be bounded between 20 and 2500 eV",
    );
}

#[test]
fn test_aes_energy_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_res_bounds",
        "res_x1000 > 0 && res_x1000 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_res_positive",
        "res_x1000 > 0 && res_x1000 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution scaled x1000 must be in valid range",
    );
}

#[test]
fn test_aes_spatial_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spatial_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_spatial_bounds",
        "spatial_x10 > 0 && spatial_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_spatial_positive",
        "spatial_x10 > 0 && spatial_x10 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spatial resolution scaled x10 nm must be in valid range",
    );
}

#[test]
fn test_aes_beam_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_voltage_bounds",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_voltage_range",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam voltage must be bounded between 1 and 30 kV");
}

#[test]
fn test_aes_beam_current_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_current_bounds",
        "curr_x100 > 0 && curr_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_current_positive",
        "curr_x100 > 0 && curr_x100 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam current scaled x100 nA must be in valid range",
    );
}

#[test]
fn test_aes_multiplier_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_stages_bounds",
        "stages >= 1 && stages <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_stages_range",
        "stages >= 1 && stages <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of multiplier stages must be between 1 and 20",
    );
}

#[test]
fn test_aes_electron_gun_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gun", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_gun_type",
        "gun == 1 || gun == 2 || gun == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_gun_valid",
        "gun == 1 || gun == 2 || gun == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "electron gun type must be thermionic (1), field-emission (2), or Schottky (3)",
    );
}

#[test]
fn test_aes_analyzer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_analyzer_type",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_analyzer_valid",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer type must be CMA (1), hemispherical (2), or retarding-field (3)",
    );
}

#[test]
fn test_aes_sputter_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sputter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_sputter_type",
        "sputter == 1 || sputter == 2 || sputter == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_sputter_valid",
        "sputter == 1 || sputter == 2 || sputter == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sputter source must be argon-ion (1), cesium (2), or oxygen (3)",
    );
}

#[test]
fn test_aes_chemical_state_mapping_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("csm_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aes_csm_bool",
        "csm_flag == 0 || csm_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aes_csm_valid",
        "csm_flag == 0 || csm_flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic chemical state mapping flag must be boolean (0 or 1)",
    );
}
