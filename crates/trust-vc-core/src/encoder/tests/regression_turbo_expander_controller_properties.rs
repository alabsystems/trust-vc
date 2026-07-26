// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_turbo_expander_wheel_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 5000 && speed <= 120000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 5000 && speed <= 120000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wheel speed must be between 5000 and 120000 RPM");
}

#[test]
fn test_turbo_expander_expansion_ratio_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x10 >= 10 && ratio_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_bounded",
        "ratio_x10 >= 10 && ratio_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "expansion ratio x10 must be between 10 and 100 (1.0-10.0)",
    );
}

#[test]
fn test_turbo_expander_inlet_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 1 && pressure <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet pressure must be between 1 and 300 bar");
}

#[test]
fn test_turbo_expander_power_recovery_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 10 && power <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 10 && power <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power recovery must be between 10 and 50000 kW");
}

#[test]
fn test_turbo_expander_isentropic_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "efficiency_range",
        "efficiency >= 50 && efficiency <= 95",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "efficiency_bounded",
        "efficiency >= 50 && efficiency <= 95",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "isentropic efficiency must be between 50 and 95 percent",
    );
}

#[test]
fn test_turbo_expander_guide_vanes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vanes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vanes_range",
        "vanes >= 8 && vanes <= 36",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vanes_bounded",
        "vanes >= 8 && vanes <= 36",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of guide vanes must be between 8 and 36");
}

#[test]
fn test_turbo_expander_bearing_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bearing_valid",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bearing_disjunction",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type must be tilting-pad (1), magnetic (2), or gas-foil (3)",
    );
}

#[test]
fn test_turbo_expander_wheel_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_disjunction",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wheel material must be aluminum (1), titanium (2), or inconel (3)",
    );
}

#[test]
fn test_turbo_expander_load_device_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "load_valid",
        "load == 1 || load == 2 || load == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "load_disjunction",
        "load == 1 || load == 2 || load == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "load device must be compressor (1), generator (2), or oil-brake (3)",
    );
}

#[test]
fn test_turbo_expander_surge_protection_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("surge_prot", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "surge_prot_bool",
        "surge_prot == 0 || surge_prot == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "surge_prot_flag",
        "surge_prot == 0 || surge_prot == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic surge protection must be a boolean flag (0 or 1)",
    );
}
