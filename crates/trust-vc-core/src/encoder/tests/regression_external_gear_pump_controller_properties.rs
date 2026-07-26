// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// External gear pump controller property regression tests.

use super::*;

#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_rate_x10 == 1200"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x10 = 1200 (120.0 L/min) is within 1-5000",
    );
}

#[test]
fn test_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_pressure >= 10 && max_pressure <= 350",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_pressure == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_pressure >= 10 && max_pressure <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 250 bar is within 10-350");
}

#[test]
fn test_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "displacement_x10 >= 1 && displacement_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "displacement_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "displacement_x10 >= 1 && displacement_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement x10 = 800 (80.0 cc/rev) is within 1-5000",
    );
}

#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed >= 100 && speed <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed == 1800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed >= 100 && speed <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 1800 RPM is within 100-4000");
}

#[test]
fn test_viscosity_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viscosity_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "viscosity_max >= 1 && viscosity_max <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "viscosity_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "viscosity_max >= 1 && viscosity_max <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity max 100000 cSt is within 1-1000000");
}

#[test]
fn test_tooth_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tooth_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "tooth_count >= 6 && tooth_count <= 24",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "tooth_count == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "tooth_count >= 6 && tooth_count <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tooth count 12 teeth per gear is within 6-24");
}

#[test]
fn test_gear_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gear_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "gear_material == 1 || gear_material == 2 || gear_material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "gear_material == 1 || gear_material == 2 || gear_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gear material is one of steel(1), cast-iron(2), stainless(3)",
    );
}

#[test]
fn test_bearing_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "bearing_type == 1 || bearing_type == 2 || bearing_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "bearing_type == 1 || bearing_type == 2 || bearing_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type is one of journal(1), ball(2), needle(3)",
    );
}

#[test]
fn test_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type is one of lip(1), mechanical(2), magnetic(3)",
    );
}

#[test]
fn test_bi_directional_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "bi_dir",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bi-directional flag set to 1 implies conditional evaluates to 1",
    );
}
