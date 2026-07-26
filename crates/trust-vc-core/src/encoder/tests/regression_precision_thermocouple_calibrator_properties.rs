// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_temp_range_min_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "t_min_range",
        "t_min >= 100 && t_min <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("t_min_val", "t_min == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "t_min_bounded",
        "t_min >= 100 && t_min <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min temp offset+500: -200C maps to 300");
}

#[test]
fn test_temp_range_max_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "t_max_range",
        "t_max >= 700 && t_max <= 2300",
    ));
    ctx.push_obligation(ProofObligation::assume("t_max_val", "t_max == 2300"));
    ctx.push_obligation(ProofObligation::assert(
        "t_max_bounded",
        "t_max >= 700 && t_max <= 2300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max temp offset+500: 1800C maps to 2300");
}

#[test]
fn test_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x100 >= 1 && acc_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x100 >= 1 && acc_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration accuracy x100: 10 means 0.10C");
}

#[test]
fn test_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x1000 >= 1 && res_x1000 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("res_val", "res_x1000 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res_x1000 >= 1 && res_x1000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "display resolution x1000: 10 means 0.010C");
}

#[test]
fn test_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ch_range", "ch >= 1 && ch <= 24"));
    ctx.push_obligation(ProofObligation::assume("ch_val", "ch == 8"));
    ctx.push_obligation(ProofObligation::assert("ch_bounded", "ch >= 1 && ch <= 24"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of input channels is 8 in [1, 24]");
}

#[test]
fn test_cjc_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cjc_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cjc_range",
        "cjc_x100 >= 1 && cjc_x100 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("cjc_val", "cjc_x100 == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "cjc_bounded",
        "cjc_x100 >= 1 && cjc_x100 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cold junction compensation x100: 25 means 0.25C");
}

#[test]
fn test_tc_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tc_type_valid",
        "tc_type == 1 || tc_type == 2 || tc_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tc_type_bounded",
        "tc_type >= 1 && tc_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermocouple type 1=K, 2=J, 3=T is in [1,3]");
}

#[test]
fn test_simulation_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sim_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sim_mode_valid",
        "sim_mode == 1 || sim_mode == 2 || sim_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sim_mode_bounded",
        "sim_mode >= 1 && sim_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "simulation mode 1=source, 2=measure, 3=source-measure is in [1,3]",
    );
}

#[test]
fn test_reference_junction_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_junc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ref_junc_valid",
        "ref_junc == 1 || ref_junc == 2 || ref_junc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ref_junc_bounded",
        "ref_junc >= 1 && ref_junc <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference junction 1=internal, 2=external, 3=manual is in [1,3]",
    );
}

#[test]
fn test_nist_traceable_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nist", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nist_val", "nist == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "nist_traceable",
        "if nist == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NIST traceable flag: nist==1 yields 1");
}
