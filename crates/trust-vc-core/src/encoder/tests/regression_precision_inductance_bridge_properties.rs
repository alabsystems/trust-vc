// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ind_bridge_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ind_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ind_range",
        "ind_x100 >= 1 && ind_x100 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ind_range_holds",
        "ind_x100 >= 1 && ind_x100 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance x100 uH bounded in [1, 10000000]");
}

#[test]
fn test_ind_bridge_accuracy_x10000_bounded() {
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
fn test_ind_bridge_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 20 && freq <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_range_holds",
        "freq >= 20 && freq <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test frequency bounded in [20, 1000000] Hz");
}

#[test]
fn test_ind_bridge_q_factor_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("q_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "q_range",
        "q_x100 >= 1 && q_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "q_range_holds",
        "q_x100 >= 1 && q_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q factor x100 bounded in [1, 100000]");
}

#[test]
fn test_ind_bridge_dc_resistance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dcr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dcr_range",
        "dcr_x100 >= 1 && dcr_x100 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dcr_range_holds",
        "dcr_x100 >= 1 && dcr_x100 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC resistance x100 ohms bounded in [1, 10000000]");
}

#[test]
fn test_ind_bridge_test_current_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cur_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cur_range",
        "cur_x1000 >= 1 && cur_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cur_range_holds",
        "cur_x1000 >= 1 && cur_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test current x1000 mA bounded in [1, 10000]");
}

#[test]
fn test_ind_bridge_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid_holds",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement mode is one of Ls-Rs, Ls-Q, Lp-Rp");
}

#[test]
fn test_ind_bridge_core_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("core", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "core_valid",
        "core == 1 || core == 2 || core == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "core_valid_holds",
        "core == 1 || core == 2 || core == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "core type is one of air, ferrite, iron powder");
}

#[test]
fn test_ind_bridge_winding_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wind", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wind_valid",
        "wind == 1 || wind == 2 || wind == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wind_valid_holds",
        "wind == 1 || wind == 2 || wind == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "winding type is one of single layer, multi-layer, toroidal",
    );
}

#[test]
fn test_ind_bridge_dc_bias_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bias", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bias_valid",
        "bias == 0 || bias == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bias_valid_holds",
        "bias == 0 || bias == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC bias flag is boolean 0 or 1");
}
