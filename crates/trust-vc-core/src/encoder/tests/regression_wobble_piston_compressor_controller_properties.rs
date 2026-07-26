// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_wobble_piston_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "press_x10 >= 10 && press_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "press_x10 >= 10 && press_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble piston discharge pressure x10 bounded");
}

#[test]
fn test_wobble_piston_motor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ms_a",
        "speed >= 500 && speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ms_c",
        "speed >= 500 && speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble piston motor speed bounded");
}

#[test]
fn test_wobble_piston_cylinder_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cyl_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cyl_temp >= 120 && cyl_temp <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cyl_temp >= 120 && cyl_temp <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble piston cylinder temperature offset+100 bounded",
    );
}

#[test]
fn test_wobble_piston_flow_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "flow_x100 >= 1 && flow_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "flow_x100 >= 1 && flow_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble piston flow rate x100 bounded");
}

#[test]
fn test_wobble_piston_stroke_length_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sl_a",
        "stroke_x100 >= 100 && stroke_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sl_c",
        "stroke_x100 >= 100 && stroke_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble piston stroke length x100 bounded");
}

#[test]
fn test_wobble_piston_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_a",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_c",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble piston power x10 bounded");
}

#[test]
fn test_wobble_piston_sealing_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sealing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "sealing == 1 || sealing == 2 || sealing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "sealing == 1 || sealing == 2 || sealing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble piston sealing method three-way disjunction",
    );
}

#[test]
fn test_wobble_piston_bearing_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bc_a",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bc_c",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble piston bearing configuration three-way disjunction",
    );
}

#[test]
fn test_wobble_piston_cooling_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble piston cooling method three-way disjunction",
    );
}

#[test]
fn test_wobble_piston_auto_unload_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("au_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("au_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble piston auto unload flag");
}
