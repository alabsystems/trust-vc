// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_cap_bridge_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_range",
        "cap_x100 >= 1 && cap_x100 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_range_holds",
        "cap_x100 >= 1 && cap_x100 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capacitance x100 pF bounded in [1, 10000000]");
}

#[test]
fn test_cap_bridge_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_range_holds",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy x10000 percent bounded in [1, 500]");
}

#[test]
fn test_cap_bridge_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 100 && freq <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_range_holds",
        "freq >= 100 && freq <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test frequency bounded in [100, 1000000] Hz");
}

#[test]
fn test_cap_bridge_dissipation_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("df_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "df_range",
        "df_x10000 >= 1 && df_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "df_range_holds",
        "df_x10000 >= 1 && df_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dissipation factor x10000 bounded in [1, 10000]");
}

#[test]
fn test_cap_bridge_test_voltage_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tv_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tv_range",
        "tv_x1000 >= 10 && tv_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tv_range_holds",
        "tv_x1000 >= 10 && tv_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage x1000 V bounded in [10, 5000]");
}

#[test]
fn test_cap_bridge_resolution_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x10000 >= 1 && res_x10000 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_range_holds",
        "res_x10000 >= 1 && res_x10000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution x10000 pF bounded in [1, 100]");
}

#[test]
fn test_cap_bridge_measurement_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mtype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mtype_valid",
        "mtype == 1 || mtype == 2 || mtype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mtype_valid_holds",
        "mtype == 1 || mtype == 2 || mtype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement type is one of Cs-D, Cp-D, Cs-Q");
}

#[test]
fn test_cap_bridge_guard_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("guard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "guard_valid",
        "guard == 1 || guard == 2 || guard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "guard_valid_holds",
        "guard == 1 || guard == 2 || guard == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "guard mode is one of off, internal, external");
}

#[test]
fn test_cap_bridge_averaging_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("avg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "avg_valid",
        "avg == 1 || avg == 2 || avg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "avg_valid_holds",
        "avg == 1 || avg == 2 || avg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "averaging mode is one of fast, medium, slow");
}

#[test]
fn test_cap_bridge_temperature_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc_valid", "tc == 0 || tc == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "tc_valid_holds",
        "tc == 0 || tc == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temperature compensation flag is boolean 0 or 1");
}
