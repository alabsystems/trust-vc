// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Mass range in atomic mass units must be within 50-2000 amu.
#[test]
fn test_thermospray_ms_mass_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mass >= 50 && mass <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mass >= 50 && mass <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermospray MS mass range 50-2000 amu");
}

/// Vaporizer temperature with +100 offset must be within 200-600 (representing 100-500 °C).
#[test]
fn test_thermospray_ms_vaporizer_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vt_a",
        "temp_off >= 200 && temp_off <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vt_c",
        "temp_off >= 200 && temp_off <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermospray MS vaporizer temperature offset 200-600",
    );
}

/// Solvent flow rate scaled by 100 must be within 10-500 (representing 0.1-5.0 mL/min).
#[test]
fn test_thermospray_ms_solvent_flow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sf_a",
        "flow_x100 >= 10 && flow_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sf_c",
        "flow_x100 >= 10 && flow_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermospray MS solvent flow x100 range 10-500");
}

/// Repeller voltage must be within 50-500 V.
#[test]
fn test_thermospray_ms_repeller_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rv_a",
        "voltage >= 50 && voltage <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rv_c",
        "voltage >= 50 && voltage <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermospray MS repeller voltage 50-500 V");
}

/// Source block temperature with +100 offset must be within 200-500 (representing 100-400 °C).
#[test]
fn test_thermospray_ms_block_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("block_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_a",
        "block_off >= 200 && block_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_c",
        "block_off >= 200 && block_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermospray MS source block temperature offset 200-500",
    );
}

/// Jet disruption distance must be within 1-20 mm.
#[test]
fn test_thermospray_ms_jet_disruption_distance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "jd_a",
        "distance >= 1 && distance <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "jd_c",
        "distance >= 1 && distance <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermospray MS jet disruption distance 1-20 mm");
}

/// Ionization mode must be one of: 1=filament, 2=discharge, 3=thermospray-only.
#[test]
fn test_thermospray_ms_ionization_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionization", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_a",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_c",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermospray MS ionization mode is filament, discharge, or thermospray-only",
    );
}

/// Solvent type must be one of: 1=aqueous, 2=organic, 3=mixed.
#[test]
fn test_thermospray_ms_solvent_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solvent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "solvent == 1 || solvent == 2 || solvent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "solvent == 1 || solvent == 2 || solvent == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermospray MS solvent type is aqueous, organic, or mixed",
    );
}

/// Analyzer type must be one of: 1=quadrupole, 2=magnetic-sector, 3=ion-trap.
#[test]
fn test_thermospray_ms_analyzer_type() {
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
        "thermospray MS analyzer type is quadrupole, magnetic-sector, or ion-trap",
    );
}

/// Automatic vaporizer control flag must be boolean (0 or 1).
#[test]
fn test_thermospray_ms_vaporizer_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("vc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermospray MS automatic vaporizer control is boolean flag",
    );
}
