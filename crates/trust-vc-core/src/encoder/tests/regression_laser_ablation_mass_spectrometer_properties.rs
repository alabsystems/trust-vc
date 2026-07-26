// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests for laser ablation inductively coupled plasma mass spectrometer (LA-ICP-MS) properties.

use super::*;

#[test]
fn test_spot_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_size_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spot_size_x10 >= 10 && spot_size_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spot_size_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spot_size_x10 >= 10 && spot_size_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spot size x10 um bounded within 10-5000 (20.0 um)");
}

#[test]
fn test_laser_energy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_energy_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "laser_energy_x100 >= 1 && laser_energy_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "laser_energy_x100 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "laser_energy_x100 >= 1 && laser_energy_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser energy x100 mJ bounded within 1-50000 (5.00 mJ)",
    );
}

#[test]
fn test_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repetition_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "repetition_rate >= 1 && repetition_rate <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "repetition_rate == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "repetition_rate >= 1 && repetition_rate <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate Hz bounded within 1-1000");
}

#[test]
fn test_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_range", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "mass_range >= 200 && mass_range <= 300",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "mass_range == 260"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "mass_range >= 200 && mass_range <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range max amu bounded within 200-300");
}

#[test]
fn test_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensitivity_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sensitivity_x100 >= 100 && sensitivity_x100 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sensitivity_x100 == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sensitivity_x100 >= 100 && sensitivity_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity x100 cps/ppb bounded within 100-1000000 (1000.00 cps/ppb)",
    );
}

#[test]
fn test_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "scan_speed >= 1000 && scan_speed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "scan_speed == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "scan_speed >= 1000 && scan_speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed amu/s bounded within 1000-100000");
}

#[test]
fn test_laser_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser type disjunction: 1=Nd:YAG-266, 2=Nd:YAG-213, 3=ArF-excimer-193",
    );
}

#[test]
fn test_cell_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "cell_type == 1 || cell_type == 2 || cell_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "cell_type == 1 || cell_type == 2 || cell_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cell type disjunction: 1=single-volume, 2=two-volume, 3=constant-geometry",
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
        "detector disjunction: 1=electron-multiplier, 2=Faraday-cup, 3=multi-collector",
    );
}

#[test]
fn test_helium_carrier_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_helium", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "carrier_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "helium carrier flag: flag==1 implies conditional evaluates to 1",
    );
}
