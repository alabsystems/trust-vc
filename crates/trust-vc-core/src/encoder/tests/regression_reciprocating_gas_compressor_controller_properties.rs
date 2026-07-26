// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_recip_gas_compressor_suction_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suction_range",
        "pressure >= 1 && pressure <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suction_bounded",
        "pressure >= 1 && pressure <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction pressure bounded 1-200 bar");
}

#[test]
fn test_recip_gas_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_range",
        "pressure >= 2 && pressure <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_bounded",
        "pressure >= 2 && pressure <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure bounded 2-1000 bar");
}

#[test]
fn test_recip_gas_compressor_piston_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed_x10 >= 10 && speed_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed_x10 >= 10 && speed_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piston speed x10 bounded 10-60 representing 1.0-6.0 m/s",
    );
}

#[test]
fn test_recip_gas_compressor_cylinder_bore_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bore", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bore_range",
        "bore >= 50 && bore <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bore_bounded",
        "bore >= 50 && bore <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cylinder bore bounded 50-1500 mm");
}

#[test]
fn test_recip_gas_compressor_gas_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 60 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 60 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas temp offset+100 bounded 60-400 representing -40 to 300 C",
    );
}

#[test]
fn test_recip_gas_compressor_valve_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valve_enum",
        "vt == 1 || vt == 2 || vt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valve_valid",
        "vt == 1 || vt == 2 || vt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve type three-way 1=plate 2=ring 3=poppet");
}

#[test]
fn test_recip_gas_compressor_lubrication_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lub", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lub_enum",
        "lub == 1 || lub == 2 || lub == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lub_valid",
        "lub == 1 || lub == 2 || lub == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lubrication three-way 1=splash 2=force-feed 3=non-lube",
    );
}

#[test]
fn test_recip_gas_compressor_cylinder_arrangement_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arr", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "arr_enum",
        "arr == 1 || arr == 2 || arr == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "arr_valid",
        "arr == 1 || arr == 2 || arr == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cylinder arrangement three-way 1=horizontal 2=vertical 3=balanced-opposed",
    );
}

#[test]
fn test_recip_gas_compressor_auto_capacity_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto capacity control boolean flag 0 or 1");
}

#[test]
fn test_recip_gas_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x10 >= 10 && ratio_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_bounded",
        "ratio_x10 >= 10 && ratio_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compression ratio x10 bounded 10-100 representing 1.0-10.0",
    );
}
