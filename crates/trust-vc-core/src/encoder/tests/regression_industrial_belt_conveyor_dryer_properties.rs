// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Industrial belt conveyor dryer property verification tests
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_belt_conveyor_dryer_belt_speed_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_speed_range",
        "speed_x10 > 0 && speed_x10 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_speed_positive_bounded",
        "speed_x10 >= 1 && speed_x10 <= 4999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt speed scaled by 10 m/min must be in valid range",
    );
}

#[test]
fn test_belt_conveyor_dryer_air_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_offset_range",
        "temp_off > 100 && temp_off < 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_offset_bounded",
        "temp_off >= 101 && temp_off <= 599",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temperature with offset +100 must be in valid range",
    );
}

#[test]
fn test_belt_conveyor_dryer_belt_width_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_width_range",
        "width_x10 > 0 && width_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_width_bounded",
        "width_x10 >= 1 && width_x10 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt width scaled by 10 mm must be in valid range");
}

#[test]
fn test_belt_conveyor_dryer_drying_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drying_length_range",
        "length >= 1 && length <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drying_length_positive_bounded",
        "length > 0 && length < 101",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying length must be between 1 and 100 meters");
}

#[test]
fn test_belt_conveyor_dryer_bed_depth_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bed_depth_range",
        "depth_x10 > 0 && depth_x10 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bed_depth_bounded",
        "depth_x10 >= 1 && depth_x10 <= 4999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed depth scaled by 10 mm must be in valid range");
}

#[test]
fn test_belt_conveyor_dryer_number_of_drying_zones() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zones_range",
        "zones >= 1 && zones <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zones_positive_bounded",
        "zones > 0 && zones < 11",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of drying zones must be between 1 and 10");
}

#[test]
fn test_belt_conveyor_dryer_belt_material_disjunction() {
    // 1=stainless-mesh, 2=perforated-plate, 3=woven-wire
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_material_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_material_in_range",
        "mat >= 1 && mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt material must be stainless-mesh, perforated-plate, or woven-wire",
    );
}

#[test]
fn test_belt_conveyor_dryer_airflow_direction_disjunction() {
    // 1=through-flow, 2=over-flow, 3=combination
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dir", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_direction_valid",
        "dir == 1 || dir == 2 || dir == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_direction_in_range",
        "dir >= 1 && dir <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow direction must be through-flow, over-flow, or combination",
    );
}

#[test]
fn test_belt_conveyor_dryer_heat_source_disjunction() {
    // 1=steam, 2=gas, 3=waste-heat
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_source_in_range",
        "source >= 1 && source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat source must be steam, gas, or waste-heat");
}

#[test]
fn test_belt_conveyor_dryer_automatic_belt_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tracking", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tracking_flag_boolean",
        "tracking == 0 || tracking == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tracking_flag_bounded",
        "tracking >= 0 && tracking <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic belt tracking flag must be 0 or 1");
}
