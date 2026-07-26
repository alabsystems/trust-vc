// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_quintuplex_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 3500"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 200 && pressure <= 7000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 3500 bar within [200, 7000]");
}

#[test]
fn test_quintuplex_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 10 && flow_x10 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate 5000 (500.0 L/min x10) within [10, 20000]",
    );
}

#[test]
fn test_quintuplex_pump_crankshaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 100 && speed <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crankshaft speed 600 RPM within [100, 1200]");
}

#[test]
fn test_quintuplex_pump_plunger_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plunger_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume("count_val", "plunger_count == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "count_bounded",
        "plunger_count >= 3 && plunger_count <= 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "plunger count 5 within [3, 7]");
}

#[test]
fn test_quintuplex_pump_power_consumption_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 750"));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 10 && power <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power consumption 750 kW within [10, 2000]");
}

#[test]
fn test_quintuplex_pump_fluid_end_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("material_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluid end material 1 (forged-steel) is one of forged-steel/stainless/inconel",
    );
}

#[test]
fn test_quintuplex_pump_packing_system_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("packing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("packing_val", "packing == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "packing_valid",
        "packing == 1 || packing == 2 || packing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "packing system 2 (chevron) is one of segmented/chevron/spring-energized",
    );
}

#[test]
fn test_quintuplex_pump_suction_stabilizer_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stabilizer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("stabilizer_val", "stabilizer == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "stabilizer_valid",
        "stabilizer == 1 || stabilizer == 2 || stabilizer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction stabilizer 3 (gas-charged) is one of bladder/piston/gas-charged",
    );
}

#[test]
fn test_quintuplex_pump_stroke_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("stroke_val", "stroke_x10 == 1200"));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_bounded",
        "stroke_x10 >= 30 && stroke_x10 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stroke length 1200 (120.0 mm x10) within [30, 3000]",
    );
}

#[test]
fn test_quintuplex_pump_auto_lubrication_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_lube_enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto lubrication flag=1 means lubrication is enabled",
    );
}
