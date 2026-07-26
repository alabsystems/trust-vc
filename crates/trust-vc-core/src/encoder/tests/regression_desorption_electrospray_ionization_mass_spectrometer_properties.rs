// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_desi_ms_spray_voltage_x10_bounded() {
    // Spray voltage in 0.1 kV units: 10..=100 represents 1.0–10.0 kV
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_x10 >= 10 && voltage_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage_x10 >= 10 && voltage_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DESI-MS spray voltage x10 bounded 1.0-10.0 kV");
}

#[test]
fn test_desi_ms_mass_range_bounded() {
    // Mass-to-charge ratio in amu: 50–100000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass >= 50 && mass <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_bounded",
        "mass >= 50 && mass <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DESI-MS mass range bounded 50-100000 amu");
}

#[test]
fn test_desi_ms_spatial_resolution_bounded() {
    // Spatial resolution in micrometers: 10–500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res >= 10 && res <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res >= 10 && res <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DESI-MS spatial resolution bounded 10-500 micrometers",
    );
}

#[test]
fn test_desi_ms_solvent_flow_x10_bounded() {
    // Solvent flow rate in 0.1 uL/min units: 1..=500 represents 0.1–50.0 uL/min
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DESI-MS solvent flow x10 bounded 0.1-50.0 uL/min");
}

#[test]
fn test_desi_ms_incident_angle_bounded() {
    // Incident angle of electrospray in degrees: 10–90
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "angle >= 10 && angle <= 90",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_bounded",
        "angle >= 10 && angle <= 90",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DESI-MS incident angle bounded 10-90 degrees");
}

#[test]
fn test_desi_ms_solvent_system_three_way() {
    // Solvent system: 1=methanol-water, 2=acetonitrile-water, 3=DMF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sol_valid",
        "sol == 1 || sol == 2 || sol == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sol_three_way",
        "sol == 1 || sol == 2 || sol == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DESI-MS solvent system three-way: methanol-water, acetonitrile-water, DMF",
    );
}

#[test]
fn test_desi_ms_analyzer_type_three_way() {
    // Analyzer type: 1=orbitrap, 2=Q-TOF, 3=ion-trap
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_valid",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_three_way",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DESI-MS analyzer type three-way: orbitrap, Q-TOF, ion-trap",
    );
}

#[test]
fn test_desi_ms_imaging_mode_three_way() {
    // Imaging mode: 1=line-scan, 2=raster, 3=mosaic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("im", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_valid",
        "im == 1 || im == 2 || im == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_three_way",
        "im == 1 || im == 2 || im == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DESI-MS imaging mode three-way: line-scan, raster, mosaic",
    );
}

#[test]
fn test_desi_ms_auto_solvent_optimization_flag() {
    // Boolean flag: 0=disabled, 1=enabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_boolean",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DESI-MS auto solvent optimization flag is boolean");
}

#[test]
fn test_desi_ms_nebulizing_gas_pressure_x10_bounded() {
    // Nebulizing gas pressure in 0.1 psi units: 5..=200 represents 0.5–20.0 psi
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 5 && press_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 5 && press_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DESI-MS nebulizing gas pressure x10 bounded 0.5-20.0 psi",
    );
}
