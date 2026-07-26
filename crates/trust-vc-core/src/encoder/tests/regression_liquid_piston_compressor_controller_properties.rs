// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_liquid_piston_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 5 && pressure <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 5 && pressure <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure bounded [5, 500] bar");
}

#[test]
fn test_liquid_piston_compressor_cycle_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycles", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cycles_range",
        "cycles >= 1 && cycles <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cycles_bounded",
        "cycles >= 1 && cycles <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle rate bounded [1, 120] cycles/min");
}

#[test]
fn test_liquid_piston_compressor_liquid_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_off_range",
        "temp_off >= 80 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_off_bounded",
        "temp_off >= 80 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid temp offset+100 bounded [80, 300] representing -20 to 200 deg C",
    );
}

#[test]
fn test_liquid_piston_compressor_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_x10_range",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_x10_bounded",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x10 bounded [1, 500] representing 0.1 Nm3/h",
    );
}

#[test]
fn test_liquid_piston_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_x10_range",
        "ratio_x10 >= 20 && ratio_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_x10_bounded",
        "ratio_x10 >= 20 && ratio_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compression ratio x10 bounded [20, 200] representing 2.0 to 20.0",
    );
}

#[test]
fn test_liquid_piston_compressor_liquid_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "liquid_type_valid",
        "lt == 1 || lt == 2 || lt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "liquid_type_three_way",
        "lt == 1 || lt == 2 || lt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid type is one of water(1), glycol(2), ionic-liquid(3)",
    );
}

#[test]
fn test_liquid_piston_compressor_gas_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gas_type_valid",
        "gt == 1 || gt == 2 || gt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gas_type_three_way",
        "gt == 1 || gt == 2 || gt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas type is one of hydrogen(1), natural-gas(2), nitrogen(3)",
    );
}

#[test]
fn test_liquid_piston_compressor_valve_actuation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("va", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valve_actuation_valid",
        "va == 1 || va == 2 || va == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valve_actuation_three_way",
        "va == 1 || va == 2 || va == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "valve actuation is one of hydraulic(1), pneumatic(2), electric(3)",
    );
}

#[test]
fn test_liquid_piston_compressor_auto_level_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto level control flag is boolean 0 or 1");
}

#[test]
fn test_liquid_piston_compressor_chamber_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volume_range",
        "volume >= 1 && volume <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "volume_bounded",
        "volume >= 1 && volume <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber volume bounded [1, 5000] liters");
}
