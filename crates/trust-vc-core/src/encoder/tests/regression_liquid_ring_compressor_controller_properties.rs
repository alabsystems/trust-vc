// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_liquid_ring_compressor_impeller_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 300 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 300 && speed <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller speed must be between 300 and 3600 RPM");
}

#[test]
fn test_liquid_ring_compressor_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "displacement_range",
        "displacement_x10 >= 10 && displacement_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "displacement_bounded",
        "displacement_x10 >= 10 && displacement_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement x10 must be between 10 and 50000 (representing 1.0-5000.0 m3/h)",
    );
}

#[test]
fn test_liquid_ring_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_x10 >= 1 && pressure_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure_x10 >= 1 && pressure_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be between 1 and 200 (representing 0.1-20.0 bar)",
    );
}

#[test]
fn test_liquid_ring_compressor_seal_liquid_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal liquid flow x10 must be between 1 and 5000 (representing 0.1-500.0 L/min)",
    );
}

#[test]
fn test_liquid_ring_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 1 && power <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 1 && power <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 1 and 2000 kW");
}

#[test]
fn test_liquid_ring_compressor_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 1 && stages <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages must be between 1 and 3");
}

#[test]
fn test_liquid_ring_compressor_seal_liquid_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_type_valid",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_type_disjunction",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal liquid type must be water(1), oil(2), or solvent(3)",
    );
}

#[test]
fn test_liquid_ring_compressor_impeller_material_disjunction() {
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
        "impeller material must be cast-iron(1), stainless-steel(2), or bronze(3)",
    );
}

#[test]
fn test_liquid_ring_compressor_port_configuration_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port_config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "port_config_valid",
        "port_config == 1 || port_config == 2 || port_config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "port_config_disjunction",
        "port_config == 1 || port_config == 2 || port_config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "port configuration must be single-port(1), dual-port(2), or cone-port(3)",
    );
}

#[test]
fn test_liquid_ring_compressor_auto_temp_control_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_temp_bool",
        "auto_temp == 0 || auto_temp == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_temp_is_boolean",
        "auto_temp == 0 || auto_temp == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic seal liquid temperature control flag must be 0 or 1",
    );
}
