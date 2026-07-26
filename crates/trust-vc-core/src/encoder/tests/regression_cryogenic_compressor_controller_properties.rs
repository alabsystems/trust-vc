// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_cryogenic_compressor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating speed must be between 1000 and 5000 RPM");
}

#[test]
fn test_cryogenic_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_pressure_range",
        "discharge_pressure >= 5 && discharge_pressure <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_pressure_bounded",
        "discharge_pressure >= 5 && discharge_pressure <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure must be between 5 and 350 bar");
}

#[test]
fn test_cryogenic_compressor_suction_pressure_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suction_pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suction_pressure_range",
        "suction_pressure_x10 >= 1 && suction_pressure_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suction_pressure_bounded",
        "suction_pressure_x10 >= 1 && suction_pressure_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction pressure x10 must be between 1 and 500 representing 0.1-50.0 bar",
    );
}

#[test]
fn test_cryogenic_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "motor_power_range",
        "motor_power >= 1 && motor_power <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motor_power_bounded",
        "motor_power >= 1 && motor_power <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 1 and 500 kW");
}

#[test]
fn test_cryogenic_compressor_cooldown_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooldown_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooldown_time_range",
        "cooldown_time >= 10 && cooldown_time <= 7200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooldown_time_bounded",
        "cooldown_time >= 10 && cooldown_time <= 7200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooldown time must be between 10 and 7200 seconds");
}

#[test]
fn test_cryogenic_compressor_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 1 && stages <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of compression stages must be between 1 and 4",
    );
}

#[test]
fn test_cryogenic_compressor_gas_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gas_type_valid",
        "gas_type == 1 || gas_type == 2 || gas_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gas_type_disjunction",
        "gas_type == 1 || gas_type == 2 || gas_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas type must be helium (1), hydrogen (2), or neon (3)",
    );
}

#[test]
fn test_cryogenic_compressor_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("compressor_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "compressor_type_valid",
        "compressor_type == 1 || compressor_type == 2 || compressor_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "compressor_type_disjunction",
        "compressor_type == 1 || compressor_type == 2 || compressor_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compressor type must be piston (1), scroll (2), or linear (3)",
    );
}

#[test]
fn test_cryogenic_compressor_heat_exchanger_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_exchanger", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_exchanger_valid",
        "heat_exchanger == 1 || heat_exchanger == 2 || heat_exchanger == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_exchanger_disjunction",
        "heat_exchanger == 1 || heat_exchanger == 2 || heat_exchanger == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat exchanger must be plate-fin (1), tube-in-tube (2), or regenerative (3)",
    );
}

#[test]
fn test_cryogenic_compressor_cold_head_monitoring_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cold_head_monitoring", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "monitoring_boolean",
        "cold_head_monitoring == 0 || cold_head_monitoring == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "monitoring_is_boolean",
        "cold_head_monitoring == 0 || cold_head_monitoring == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic cold-head monitoring flag must be boolean (0 or 1)",
    );
}
