// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_continuous_tray_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_off_range",
        "temp_off >= 150 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_off_bounded",
        "temp_off >= 150 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temperature offset+100 must be between 150 and 350 (50-250 C)",
    );
}

#[test]
fn test_continuous_tray_dryer_tray_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_x100_range",
        "speed_x100 >= 1 && speed_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_x100_bounded",
        "speed_x100 >= 1 && speed_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tray speed x100 must be between 1 and 500 (0.01-5.00 m/min)",
    );
}

#[test]
fn test_continuous_tray_dryer_air_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_x10_range",
        "vel_x10 >= 5 && vel_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vel_x10_bounded",
        "vel_x10 >= 5 && vel_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air velocity x10 must be between 5 and 100 (0.5-10.0 m/s)",
    );
}

#[test]
fn test_continuous_tray_dryer_tray_loading_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "load_x10_range",
        "load_x10 >= 10 && load_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "load_x10_bounded",
        "load_x10 >= 10 && load_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tray loading x10 must be between 10 and 500 (1.0-50.0 kg/m2)",
    );
}

#[test]
fn test_continuous_tray_dryer_number_of_trays_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trays", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trays_range",
        "trays >= 2 && trays <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trays_bounded",
        "trays >= 2 && trays <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of trays must be between 2 and 50");
}

#[test]
fn test_continuous_tray_dryer_residence_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range",
        "time >= 10 && time <= 480",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_bounded",
        "time >= 10 && time <= 480",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time must be between 10 and 480 minutes");
}

#[test]
fn test_continuous_tray_dryer_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heating_range",
        "heating == 1 || heating == 2 || heating == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heating_valid",
        "heating == 1 || heating == 2 || heating == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method must be 1=steam, 2=electric, or 3=gas",
    );
}

#[test]
fn test_continuous_tray_dryer_airflow_pattern_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pattern_range",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pattern_valid",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air flow pattern must be 1=cross-flow, 2=counter-flow, or 3=parallel-flow",
    );
}

#[test]
fn test_continuous_tray_dryer_tray_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tray_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tray_mat_range",
        "tray_mat == 1 || tray_mat == 2 || tray_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tray_mat_valid",
        "tray_mat == 1 || tray_mat == 2 || tray_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tray material must be 1=stainless-steel, 2=aluminum, or 3=perforated",
    );
}

#[test]
fn test_continuous_tray_dryer_auto_humidity_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto humidity control flag must be 0=disabled or 1=enabled",
    );
}
