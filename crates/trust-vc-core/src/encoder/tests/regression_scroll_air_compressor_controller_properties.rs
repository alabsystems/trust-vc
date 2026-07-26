// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_scroll_air_compressor_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "press_x10 >= 20 && press_x10 <= 130",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "press_x10 >= 20 && press_x10 <= 130",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure x10 bounded 0.1 bar");
}

#[test]
fn test_scroll_air_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 1 && power <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 1 && power <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power bounded kW");
}

#[test]
fn test_scroll_air_compressor_orbit_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orbit speed bounded RPM");
}

#[test]
fn test_scroll_air_compressor_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 5 && flow_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 5 && flow_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 bounded 0.1 m3/min");
}

#[test]
fn test_scroll_air_compressor_discharge_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 150 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 150 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge temp offset+100 bounded represents 50-250C",
    );
}

#[test]
fn test_scroll_air_compressor_scroll_wrap_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_enum",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scroll wrap material three-way 1=cast-iron 2=aluminum 3=steel",
    );
}

#[test]
fn test_scroll_air_compressor_lubrication_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lubrication_enum",
        "lt == 1 || lt == 2 || lt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lubrication_valid",
        "lt == 1 || lt == 2 || lt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lubrication type three-way 1=oil-free 2=oil-lubricated 3=water-injected",
    );
}

#[test]
fn test_scroll_air_compressor_cooling_system_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cs", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooling_enum",
        "cs == 1 || cs == 2 || cs == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_valid",
        "cs == 1 || cs == 2 || cs == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling system three-way 1=air-cooled 2=water-cooled 3=integrated-heat-recovery",
    );
}

#[test]
fn test_scroll_air_compressor_auto_load_unload_flag() {
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
    expect_verified(&result, "auto load unload flag boolean");
}

#[test]
fn test_scroll_air_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x10 >= 20 && ratio_x10 <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_bounded",
        "ratio_x10 >= 20 && ratio_x10 <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compression ratio x10 bounded 0.1");
}
