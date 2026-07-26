// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Industrial foam mat dryer – property-based regression tests
// ---------------------------------------------------------------------------

/// Air temperature with offset +100 °C — bounded range.
#[test]
fn test_foam_mat_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "temp_off >= 150 && temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "temp_off >= 150 && temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer air temperature offset bounded");
}

/// Belt speed at ×10 m/min — bounded range.
#[test]
fn test_foam_mat_dryer_belt_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bs_a",
        "speed_x10 >= 1 && speed_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bs_c",
        "speed_x10 >= 1 && speed_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer belt speed x10 bounded");
}

/// Foam thickness at ×10 mm — bounded range.
#[test]
fn test_foam_mat_dryer_foam_thickness_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ft_a",
        "thick_x10 >= 5 && thick_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ft_c",
        "thick_x10 >= 5 && thick_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer foam thickness x10 bounded");
}

/// Air velocity in m/s — bounded range.
#[test]
fn test_foam_mat_dryer_air_velocity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "av_a",
        "velocity >= 1 && velocity <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "av_c",
        "velocity >= 1 && velocity <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer air velocity bounded");
}

/// Belt width in mm — bounded range.
#[test]
fn test_foam_mat_dryer_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_a",
        "width >= 200 && width <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bw_c",
        "width >= 200 && width <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer belt width bounded");
}

/// Drying time in minutes — bounded range.
#[test]
fn test_foam_mat_dryer_drying_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_a", "time >= 5 && time <= 120"));
    ctx.push_obligation(ProofObligation::assert("dt_c", "time >= 5 && time <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer drying time bounded");
}

/// Foam stabilizer — 3-way disjunction.
#[test]
fn test_foam_mat_dryer_foam_stabilizer_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stabilizer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fs_a",
        "stabilizer == 1 || stabilizer == 2 || stabilizer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fs_c",
        "stabilizer == 1 || stabilizer == 2 || stabilizer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "foam mat dryer foam stabilizer three-way disjunction",
    );
}

/// Belt type — 3-way disjunction.
#[test]
fn test_foam_mat_dryer_belt_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_a",
        "belt == 1 || belt == 2 || belt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_c",
        "belt == 1 || belt == 2 || belt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer belt type three-way disjunction");
}

/// Heating source — 3-way disjunction.
#[test]
fn test_foam_mat_dryer_heating_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hs_a",
        "heating == 1 || heating == 2 || heating == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hs_c",
        "heating == 1 || heating == 2 || heating == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "foam mat dryer heating source three-way disjunction",
    );
}

/// Automatic foam density control — boolean flag.
#[test]
fn test_foam_mat_dryer_auto_foam_density_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fd_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("fd_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "foam mat dryer auto foam density control flag");
}
