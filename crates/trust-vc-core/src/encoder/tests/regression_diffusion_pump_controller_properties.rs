// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_diffusion_pump_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 100 && speed <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_in_range",
        "speed >= 100 && speed <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pumping speed 30000 (3000.0 L/s) within 100..=500000",
    );
}

#[test]
fn test_diffusion_pump_ultimate_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_in_range",
        "pressure >= 1 && pressure <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ultimate pressure 10 (0.001 mbar) within 1..=1000");
}

#[test]
fn test_diffusion_pump_heater_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 100 && power <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "power_in_range",
        "power >= 100 && power <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heater power 2000 W within 100..=10000");
}

#[test]
fn test_diffusion_pump_number_of_jets_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jets", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "jets_range",
        "jets >= 1 && jets <= 5",
    ));
    ctx.push_obligation(ProofObligation::assume("jets_val", "jets == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "jets_in_range",
        "jets >= 1 && jets <= 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of jets 3 within 1..=5");
}

#[test]
fn test_diffusion_pump_coolant_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 1 && flow <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_range",
        "flow >= 1 && flow <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coolant flow 50 (5.0 L/min) within 1..=500");
}

#[test]
fn test_diffusion_pump_boiler_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 200 && temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= 200 && temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "boiler temperature 300 (offset +100 C so 200 C) within 200..=500",
    );
}

#[test]
fn test_diffusion_pump_fluid_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fluid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fluid_val", "fluid == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "fluid_valid",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump fluid 1 (silicone-oil) is valid 3-way enum");
}

#[test]
fn test_diffusion_pump_baffle_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baffle", i32_ty());
    ctx.push_obligation(ProofObligation::assume("baffle_val", "baffle == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "baffle_valid",
        "baffle == 1 || baffle == 2 || baffle == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "baffle type 2 (chevron) is valid 3-way enum");
}

#[test]
fn test_diffusion_pump_backing_pump_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("backing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("backing_val", "backing == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "backing_valid",
        "backing == 1 || backing == 2 || backing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backing pump 1 (rotary-vane) is valid 3-way enum");
}

#[test]
fn test_diffusion_pump_automatic_interlock_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("interlock_enabled", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic interlock flag==1 implies enabled");
}
