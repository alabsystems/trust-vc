// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn inlet_pressure_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_range",
        "inlet_x10 >= 10 && inlet_x10 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_range_holds",
        "inlet_x10 >= 10 && inlet_x10 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet pressure x10 bar in [10, 3000] (1.0-300.0 bar)",
    );
}

#[test]
fn outlet_pressure_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outlet_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_range",
        "outlet_x10 >= 1 && outlet_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_range_holds",
        "outlet_x10 >= 1 && outlet_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "outlet pressure x10 bar in [1, 500] (0.1-50.0 bar)",
    );
}

#[test]
fn rotor_speed_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 5000 && speed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_range_holds",
        "speed >= 5000 && speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed RPM in [5000, 100000]");
}

#[test]
fn isentropic_efficiency_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "eff_x100 >= 50 && eff_x100 <= 95",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eff_range_holds",
        "eff_x100 >= 50 && eff_x100 <= 95",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "isentropic efficiency x100 in [50, 95] (0.50-0.95)",
    );
}

#[test]
fn inlet_temperature_offset_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 300 && temp_off <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_range_holds",
        "temp_off >= 300 && temp_off <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet temperature offset +500 in [300, 900] (-200 to 400 C cryogenic)",
    );
}

#[test]
fn power_output_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_x10 >= 10 && power_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_range_holds",
        "power_x10 >= 10 && power_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power output x10 kW in [10, 50000] (1.0-5000.0 kW)",
    );
}

#[test]
fn working_fluid_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fluid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fluid_valid",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fluid_valid_holds",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working fluid 3-way: natural-gas/nitrogen/air");
}

#[test]
fn bearing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bearing_valid",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bearing_valid_holds",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bearing type 3-way: oil/magnetic/gas-foil");
}

#[test]
fn control_strategy_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_valid",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_valid_holds",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "control strategy 3-way: speed/pressure/flow");
}

#[test]
fn auto_anti_surge_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bool_holds",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto anti-surge boolean flag");
}
