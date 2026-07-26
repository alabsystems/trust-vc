// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vt_pump_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 100 && dia <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "dia >= 100 && dia <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter bounded to 100-1500mm");
}

#[test]
fn test_vt_pump_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 1 && stages <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stages bounded to 1-30");
}

#[test]
fn test_vt_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 50 && flow <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow >= 50 && flow <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate bounded to 50-200000 L/min");
}

#[test]
fn test_vt_pump_head_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_range",
        "head >= 10 && head <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "head_bounded",
        "head >= 10 && head <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total head bounded to 10-3000 m");
}

#[test]
fn test_vt_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "eff_x10 >= 500 && eff_x10 <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eff_bounded",
        "eff_x10 >= 500 && eff_x10 <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency x10 bounded to 500-900 (50.0-90.0%)");
}

#[test]
fn test_vt_pump_setting_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_range",
        "depth >= 1 && depth <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "depth_bounded",
        "depth >= 1 && depth <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "setting depth bounded to 1-500 m");
}

#[test]
fn test_vt_pump_column_pipe_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pipe", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pipe_enum",
        "pipe == 1 || pipe == 2 || pipe == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pipe_valid",
        "pipe == 1 || pipe == 2 || pipe == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "column pipe is threaded (1), flanged (2), or enclosing tube (3)",
    );
}

#[test]
fn test_vt_pump_bearing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("brg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "brg_enum",
        "brg == 1 || brg == 2 || brg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "brg_valid",
        "brg == 1 || brg == 2 || brg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bearing is rubber (1), bronze (2), or cutlass (3)");
}

#[test]
fn test_vt_pump_discharge_head_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hd_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hd_type_enum",
        "hd_type == 1 || hd_type == 2 || hd_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hd_type_valid",
        "hd_type == 1 || hd_type == 2 || hd_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge head is surface (1), below-grade (2), or can (3)",
    );
}

#[test]
fn test_vt_pump_thrust_bearing_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tb", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tb_bool", "tb == 0 || tb == 1"));
    ctx.push_obligation(ProofObligation::assert("tb_valid", "tb == 0 || tb == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thrust bearing flag is boolean (0 or 1)");
}
