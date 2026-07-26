// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_triplex_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 100 && pressure <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 2500 bar within [100, 5000]");
}

#[test]
fn test_triplex_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 750"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 750 (75.0 L/min x10) within [1, 10000]");
}

#[test]
fn test_triplex_pump_crankshaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 450"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 100 && speed <= 1800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crankshaft speed 450 RPM within [100, 1800]");
}

#[test]
fn test_triplex_pump_plunger_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_val",
        "diameter_x10 == 380",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_bounded",
        "diameter_x10 >= 10 && diameter_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plunger diameter 380 (38.0 mm x10) within [10, 1500]",
    );
}

#[test]
fn test_triplex_pump_power_rating_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 1 && power <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power rating 150 kW within [1, 500]");
}

#[test]
fn test_triplex_pump_fluid_end_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("material_val", "material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluid end material 2 (duplex) is one of stainless-316/duplex/super-duplex",
    );
}

#[test]
fn test_triplex_pump_packing_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("packing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("packing_val", "packing == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "packing_valid",
        "packing == 1 || packing == 2 || packing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "packing type 1 (V-ring) is one of V-ring/lip-seal/spring-loaded",
    );
}

#[test]
fn test_triplex_pump_valve_configuration_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve", i32_ty());
    ctx.push_obligation(ProofObligation::assume("valve_val", "valve == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valve_valid",
        "valve == 1 || valve == 2 || valve == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "valve configuration 3 (plate) is one of wing-guided/stem-guided/plate",
    );
}

#[test]
fn test_triplex_pump_stroke_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("stroke_val", "stroke_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_bounded",
        "stroke_x10 >= 20 && stroke_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke length 800 (80.0 mm x10) within [20, 2000]");
}

#[test]
fn test_triplex_pump_pressure_relief_valve_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "relief_valve_enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pressure relief valve flag=1 means valve is enabled",
    );
}
