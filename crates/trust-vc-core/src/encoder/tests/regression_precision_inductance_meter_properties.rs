// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_inductance_meter_inductance_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("induct_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ind_a",
        "induct_x1000 >= 1 && induct_x1000 <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ind_c",
        "induct_x1000 >= 1 && induct_x1000 <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter inductance x1000 bounded");
}

#[test]
fn test_inductance_meter_test_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tf_a",
        "freq_x10 >= 1 && freq_x10 <= 20000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tf_c",
        "freq_x10 >= 1 && freq_x10 <= 20000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter test frequency x10 bounded");
}

#[test]
fn test_inductance_meter_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_a",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_c",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter accuracy x10000 bounded");
}

#[test]
fn test_inductance_meter_test_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volt_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tv_a",
        "volt_x100 >= 1 && volt_x100 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tv_c",
        "volt_x100 >= 1 && volt_x100 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter test voltage x100 bounded");
}

#[test]
fn test_inductance_meter_q_factor_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("qfactor_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "qf_a",
        "qfactor_x100 >= 1 && qfactor_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "qf_c",
        "qfactor_x100 >= 1 && qfactor_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter Q factor x100 bounded");
}

#[test]
fn test_inductance_meter_dc_bias_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bias_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "db_a",
        "bias_x1000 >= 0 && bias_x1000 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "db_c",
        "bias_x1000 >= 0 && bias_x1000 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter DC bias current x1000 bounded");
}

#[test]
fn test_inductance_meter_measurement_range_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mrange", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mrange == 1 || mrange == 2 || mrange == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mrange == 1 || mrange == 2 || mrange == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inductance meter measurement range three-way disjunction",
    );
}

#[test]
fn test_inductance_meter_equivalent_circuit_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("circuit", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ec_a",
        "circuit == 1 || circuit == 2 || circuit == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ec_c",
        "circuit == 1 || circuit == 2 || circuit == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inductance meter equivalent circuit three-way disjunction",
    );
}

#[test]
fn test_inductance_meter_averaging_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("avg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "am_a",
        "avg == 1 || avg == 2 || avg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "am_c",
        "avg == 1 || avg == 2 || avg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inductance meter averaging mode three-way disjunction",
    );
}

#[test]
fn test_inductance_meter_auto_range_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ar_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ar_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inductance meter auto range flag");
}
