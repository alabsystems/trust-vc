// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: industrial roller compactor (dry granulation) property verification

use super::*;

#[test]
fn test_roll_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roll_diameter_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "roll_diameter_mm >= 100 && roll_diameter_mm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "roll_diameter_mm == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "roll_diameter_mm >= 100 && roll_diameter_mm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roll diameter 250 mm within 100-500 mm range");
}

#[test]
fn test_roll_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roll_width_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "roll_width_mm >= 25 && roll_width_mm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "roll_width_mm == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "roll_width_mm >= 25 && roll_width_mm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roll width 100 mm within 25-200 mm range");
}

#[test]
fn test_roll_force_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roll_force_x10_kn", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "roll_force_x10_kn >= 10 && roll_force_x10_kn <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "roll_force_x10_kn == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "roll_force_x10_kn >= 10 && roll_force_x10_kn <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "roll force 50.0 kN (x10=500) within 1.0-500.0 kN range",
    );
}

#[test]
fn test_roll_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roll_speed_x10_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "roll_speed_x10_rpm >= 10 && roll_speed_x10_rpm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "roll_speed_x10_rpm == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "roll_speed_x10_rpm >= 10 && roll_speed_x10_rpm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "roll speed 6.0 RPM (x10=60) within 1.0-20.0 RPM range",
    );
}

#[test]
fn test_throughput_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_x10_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "throughput_x10_kgh >= 10 && throughput_x10_kgh <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "throughput_x10_kgh == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "throughput_x10_kgh >= 10 && throughput_x10_kgh <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "throughput 400.0 kg/h (x10=4000) within 1.0-5000.0 kg/h range",
    );
}

#[test]
fn test_ribbon_thickness_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ribbon_thickness_x100_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ribbon_thickness_x100_mm >= 10 && ribbon_thickness_x100_mm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "ribbon_thickness_x100_mm == 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "ribbon_thickness_x100_mm >= 10 && ribbon_thickness_x100_mm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ribbon thickness 1.50 mm (x100=150) within 0.10-5.00 mm range",
    );
}

#[test]
fn test_roll_surface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roll_surface", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "roll_surface >= 1 && roll_surface <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "roll_surface == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "roll_surface == 1 || roll_surface == 2 || roll_surface == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "roll surface knurled (2) is one of smooth/knurled/pocket",
    );
}

#[test]
fn test_feed_screw_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_screw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "feed_screw >= 1 && feed_screw <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "feed_screw == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "feed_screw == 1 || feed_screw == 2 || feed_screw == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed screw single (1) is one of single/twin/taper");
}

#[test]
fn test_granulator_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("granulator_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "granulator_type >= 1 && granulator_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "granulator_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "granulator_type == 1 || granulator_type == 2 || granulator_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "granulator rotor (3) is one of oscillating/conical-screen/rotor",
    );
}

#[test]
fn test_vacuum_deaeration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "deaeration_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum deaeration enabled when flag is 1");
}
