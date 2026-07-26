// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_sliding_vane_compressor_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 500 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 500 && speed <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed must be between 500 and 3600 RPM");
}

#[test]
fn test_sliding_vane_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_x10 >= 10 && pressure_x10 <= 130",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure_x10 >= 10 && pressure_x10 <= 130",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be between 10 and 130 (1.0-13.0 bar)",
    );
}

#[test]
fn test_sliding_vane_compressor_free_air_delivery_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fad_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fad_range",
        "fad_x10 >= 10 && fad_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fad_bounded",
        "fad_x10 >= 10 && fad_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "free air delivery x10 must be between 10 and 100000 (1.0-10000.0 L/min)",
    );
}

#[test]
fn test_sliding_vane_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_kw >= 1 && power_kw <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power_kw >= 1 && power_kw <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 1 and 500 kW");
}

#[test]
fn test_sliding_vane_compressor_oil_injection_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_rate_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_rate_range",
        "oil_rate_x100 >= 1 && oil_rate_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_rate_bounded",
        "oil_rate_x100 >= 1 && oil_rate_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil injection rate x100 must be between 1 and 5000 (0.01-50.00 L/min)",
    );
}

#[test]
fn test_sliding_vane_compressor_number_of_vanes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vanes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vanes_range",
        "vanes >= 4 && vanes <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vanes_bounded",
        "vanes >= 4 && vanes <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of vanes must be between 4 and 20");
}

#[test]
fn test_sliding_vane_compressor_vane_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vane_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vane_material_valid",
        "vane_material == 1 || vane_material == 2 || vane_material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vane_material_in_set",
        "vane_material == 1 || vane_material == 2 || vane_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vane material must be 1=phenolic-resin, 2=PEEK, or 3=carbon-fiber",
    );
}

#[test]
fn test_sliding_vane_compressor_lubrication_system_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lubrication", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lubrication_valid",
        "lubrication == 1 || lubrication == 2 || lubrication == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lubrication_in_set",
        "lubrication == 1 || lubrication == 2 || lubrication == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lubrication system must be 1=flooded, 2=oil-injected, or 3=oil-free",
    );
}

#[test]
fn test_sliding_vane_compressor_capacity_control_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_ctrl_valid",
        "capacity_ctrl == 1 || capacity_ctrl == 2 || capacity_ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_ctrl_in_set",
        "capacity_ctrl == 1 || capacity_ctrl == 2 || capacity_ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity control must be 1=inlet-throttle, 2=slide-valve, or 3=VSD",
    );
}

#[test]
fn test_sliding_vane_compressor_automatic_oil_separator_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_separator", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_separator_bool",
        "oil_separator == 0 || oil_separator == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_separator_is_flag",
        "oil_separator == 0 || oil_separator == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic oil separator flag must be 0 (disabled) or 1 (enabled)",
    );
}
