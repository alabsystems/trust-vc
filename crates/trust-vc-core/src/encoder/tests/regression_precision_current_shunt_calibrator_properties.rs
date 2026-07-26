// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_shunt_cal_current_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cur", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "cur >= 1 && cur <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "cur >= 1 && cur <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current range 1-1000 A should be bounded");
}

#[test]
fn test_shunt_cal_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "acc_x10000 >= 1 && acc_x10000 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "acc_x10000 >= 1 && acc_x10000 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy x10000 percent 1-200 should be bounded");
}

#[test]
fn test_shunt_cal_resistance_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "res_x10000 >= 1 && res_x10000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "res_x10000 >= 1 && res_x10000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resistance x10000 ohms 1-100000 should be bounded");
}

#[test]
fn test_shunt_cal_temp_coeff_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "tc_x10 >= 1 && tc_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "tc_x10 >= 1 && tc_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temp coeff x10 ppm per C 1-200 should be bounded");
}

#[test]
fn test_shunt_cal_power_dissipation_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pwr_x10 >= 1 && pwr_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pwr_x10 >= 1 && pwr_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power dissipation x10 watts 1-10000 should be bounded",
    );
}

#[test]
fn test_shunt_cal_voltage_drop_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vd_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "vd_x1000 >= 1 && vd_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "vd_x1000 >= 1 && vd_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage drop x1000 mV 1-100000 should be bounded");
}

#[test]
fn test_shunt_cal_connection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "variants",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connection type 4-terminal or 2-terminal or coaxial should hold",
    );
}

#[test]
fn test_shunt_cal_element_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elem", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "variants",
        "elem == 1 || elem == 2 || elem == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "elem == 1 || elem == 2 || elem == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "element type Manganin or Zeranin or Evanohm should hold",
    );
}

#[test]
fn test_shunt_cal_cooling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cool", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "variants",
        "cool == 1 || cool == 2 || cool == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "cool == 1 || cool == 2 || cool == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling natural or forced air or oil immersion should hold",
    );
}

#[test]
fn test_shunt_cal_traceable_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nist", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "nist == 0 || nist == 1"));
    ctx.push_obligation(ProofObligation::assert("bounded", "nist == 0 || nist == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NIST traceable boolean 0 or 1 should hold");
}
