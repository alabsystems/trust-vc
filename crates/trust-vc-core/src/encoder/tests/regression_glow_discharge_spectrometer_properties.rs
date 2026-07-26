// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Glow Discharge Optical Emission Spectrometer (GD-OES) property verification
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_sputter_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sputter_rate_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sputter_rate_x100 >= 1 && sputter_rate_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sputter_rate_x100 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sputter_rate_x100 >= 1 && sputter_rate_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sputter rate 5.00 um/min encoded as x100 must be within bounds",
    );
}

#[test]
fn test_crater_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crater_diameter_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "crater_diameter_x10 >= 10 && crater_diameter_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "crater_diameter_x10 == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "crater_diameter_x10 >= 10 && crater_diameter_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "crater diameter 4.0 mm encoded as x10 must be within bounds",
    );
}

#[test]
fn test_depth_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_resolution_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "depth_resolution_x10 >= 1 && depth_resolution_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "depth_resolution_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "depth_resolution_x10 >= 1 && depth_resolution_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "depth resolution 1.0 nm encoded as x10 must be within bounds",
    );
}

#[test]
fn test_rf_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rf_power", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rf_power >= 5 && rf_power <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rf_power == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rf_power >= 5 && rf_power <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RF power 40 watts must be within bounds");
}

#[test]
fn test_argon_pressure_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("argon_pressure_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "argon_pressure_x100 >= 10 && argon_pressure_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "argon_pressure_x100 == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "argon_pressure_x100 >= 10 && argon_pressure_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "argon pressure 3.00 hPa encoded as x100 must be within bounds",
    );
}

#[test]
fn test_wavelength_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "wavelength_channels >= 8 && wavelength_channels <= 64",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "wavelength_channels == 32"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wavelength_channels >= 8 && wavelength_channels <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength channels count must be within bounds");
}

#[test]
fn test_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "source_type == 1 || source_type == 2 || source_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "source_type >= 1 && source_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source type 1=DC 2=RF 3=pulsed-RF must be in valid range",
    );
}

#[test]
fn test_anode_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("anode_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "anode_material == 1 || anode_material == 2 || anode_material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "anode_material >= 1 && anode_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "anode material 1=copper 2=steel 3=tungsten must be in valid range",
    );
}

#[test]
fn test_polychromator_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polychromator", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "polychromator == 1 || polychromator == 2 || polychromator == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "polychromator >= 1 && polychromator <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "polychromator 1=Paschen-Runge 2=Rowland 3=Echelle must be in valid range",
    );
}

#[test]
fn test_hydrogen_analysis_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hydrogen_analysis", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "hydrogen_analysis == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "if hydrogen_analysis == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "hydrogen analysis enabled flag must evaluate to true",
    );
}
