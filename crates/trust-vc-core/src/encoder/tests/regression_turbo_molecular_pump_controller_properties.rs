// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_turbo_pump_rotor_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rs_a",
        "rotor_rpm >= 1000 && rotor_rpm <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rs_c",
        "rotor_rpm >= 1000 && rotor_rpm <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed in [1000, 100000] RPM");
}

#[test]
fn test_turbo_pump_compression_ratio_log10_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cr_log_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cr_a",
        "cr_log_x10 >= 10 && cr_log_x10 <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cr_c",
        "cr_log_x10 >= 10 && cr_log_x10 <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compression ratio log10 x10 in [10, 120] representing 10^1-10^12",
    );
}

#[test]
fn test_turbo_pump_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_lps", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ps_a",
        "speed_lps >= 10 && speed_lps <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ps_c",
        "speed_lps >= 10 && speed_lps <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pumping speed in [10, 10000] L/s");
}

#[test]
fn test_turbo_pump_power_w_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_w", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_a",
        "power_w >= 10 && power_w <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_c",
        "power_w >= 10 && power_w <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power consumption in [10, 5000] W");
}

#[test]
fn test_turbo_pump_blade_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bs_a",
        "stages >= 3 && stages <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bs_c",
        "stages >= 3 && stages <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade stages in [3, 20]");
}

#[test]
fn test_turbo_pump_inlet_flange_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flange_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "if_a",
        "flange_mm >= 16 && flange_mm <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "if_c",
        "flange_mm >= 16 && flange_mm <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet flange in [16, 400] mm (CF/ISO/KF)");
}

#[test]
fn test_turbo_pump_bearing_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_a",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_c",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bearing: ceramic ball, magnetic, or hybrid");
}

#[test]
fn test_turbo_pump_drag_stage_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drag_stage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ds_a",
        "drag_stage == 1 || drag_stage == 2 || drag_stage == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ds_c",
        "drag_stage == 1 || drag_stage == 2 || drag_stage == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drag stage: Holweck, Siegbahn, or Gaede");
}

#[test]
fn test_turbo_pump_backing_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("backing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bk_a",
        "backing == 1 || backing == 2 || backing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bk_c",
        "backing == 1 || backing == 2 || backing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backing pump: scroll, diaphragm, or rotary vane");
}

#[test]
fn test_turbo_pump_venting_valve_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vent_valve", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vv_a",
        "vent_valve == 0 || vent_valve == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vv_c",
        "vent_valve == 0 || vent_valve == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integrated venting valve flag is boolean");
}
