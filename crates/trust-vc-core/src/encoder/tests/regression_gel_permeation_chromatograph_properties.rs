// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_gpc_molecular_weight_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mw_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mw_range",
        "mw_max >= 100 && mw_max <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mw_bounded",
        "mw_max >= 100 && mw_max <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "molecular weight range 100-10000000 Da");
}

#[test]
fn test_gpc_flow_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x100 >= 10 && flow_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x100 >= 10 && flow_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x100 mL/min bounded 10-500");
}

#[test]
fn test_gpc_column_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 520 && temp <= 720",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 520 && temp <= 720",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column temp offset+500 bounded 520-720");
}

#[test]
fn test_gpc_injection_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inj_range",
        "inj_x10 >= 10 && inj_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inj_bounded",
        "inj_x10 >= 10 && inj_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "injection volume x10 uL bounded 10-5000");
}

#[test]
fn test_gpc_column_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cols", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cols_range",
        "cols >= 1 && cols <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cols_bounded",
        "cols >= 1 && cols <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column count bounded 1-4");
}

#[test]
fn test_gpc_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press >= 100 && press <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press >= 100 && press <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure bounded 100-6000 psi");
}

#[test]
fn test_gpc_detector_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_enum",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_valid",
        "det == 1 || det == 2 || det == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type RI/UV/light-scattering");
}

#[test]
fn test_gpc_column_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "col_enum",
        "col == 1 || col == 2 || col == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "col_valid",
        "col == 1 || col == 2 || col == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column type aqueous/organic/mixed-bed");
}

#[test]
fn test_gpc_calibration_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cal_enum",
        "cal == 1 || cal == 2 || cal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cal_valid",
        "cal == 1 || cal == 2 || cal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration conventional/universal/absolute");
}

#[test]
fn test_gpc_degasser_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("deg_bool", "deg == 0 || deg == 1"));
    ctx.push_obligation(ProofObligation::assert("deg_valid", "deg == 0 || deg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "degasser boolean flag 0 or 1");
}
