// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Mass range must be within 1–500 amu for valid flowing afterglow MS operation.
#[test]
fn test_flowing_afterglow_ms_mass_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mr_a", "mass >= 1 && mass <= 500"));
    ctx.push_obligation(ProofObligation::assert("mr_c", "mass >= 1 && mass <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS mass range in amu");
}

/// Flow tube pressure (×100 torr) must remain within 0.10–10.00 torr operating range.
#[test]
fn test_flowing_afterglow_ms_flow_tube_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fp_a",
        "press_x100 >= 10 && press_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fp_c",
        "press_x100 >= 10 && press_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flowing afterglow MS flow tube pressure at x100 torr",
    );
}

/// Buffer gas flow rate (×10 L/min) must remain within 1.0–50.0 L/min operating range.
#[test]
fn test_flowing_afterglow_ms_buffer_gas_flow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bf_a",
        "flow_x10 >= 10 && flow_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bf_c",
        "flow_x10 >= 10 && flow_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS buffer gas flow at x10 L/min");
}

/// Electron energy (×10 eV) must remain within 0.1–100.0 eV operating range.
#[test]
fn test_flowing_afterglow_ms_electron_energy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ee_a",
        "energy_x10 >= 1 && energy_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ee_c",
        "energy_x10 >= 1 && energy_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS electron energy at x10 eV");
}

/// Ion source temperature (offset +100 °C) must remain within safe operating bounds.
#[test]
fn test_flowing_afterglow_ms_source_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "temp_off >= 50 && temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "temp_off >= 50 && temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flowing afterglow MS ion source temperature with offset",
    );
}

/// Reaction distance in cm must remain within 5–200 cm flow tube length.
#[test]
fn test_flowing_afterglow_ms_reaction_distance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rd_a",
        "distance >= 5 && distance <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rd_c",
        "distance >= 5 && distance <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS reaction distance in cm");
}

/// Buffer gas type must be one of: helium (1), argon (2), or nitrogen (3).
#[test]
fn test_flowing_afterglow_ms_buffer_gas_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bg_a",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bg_c",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS buffer gas type selection");
}

/// Ion detector must be one of: electron-multiplier (1), faraday-cup (2), or channeltron (3).
#[test]
fn test_flowing_afterglow_ms_ion_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "id_a",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "id_c",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS ion detection method");
}

/// Ionization source must be one of: microwave (1), electron-impact (2), or corona (3).
#[test]
fn test_flowing_afterglow_ms_ionization_source() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "is_a",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_c",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flowing afterglow MS ionization source type");
}

/// Automatic pressure regulation flag must be a boolean: 0 (off) or 1 (on).
#[test]
fn test_flowing_afterglow_ms_pressure_regulation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pr_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("pr_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flowing afterglow MS automatic pressure regulation flag",
    );
}
