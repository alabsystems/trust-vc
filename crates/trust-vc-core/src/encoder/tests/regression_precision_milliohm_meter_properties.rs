// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Precision milliohm meter – property-based regression tests
// ---------------------------------------------------------------------------

/// Resistance at ×10000 mΩ — bounded range.
#[test]
fn test_milliohm_meter_resistance_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resist_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_a",
        "resist_x10000 >= 1 && resist_x10000 <= 20000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_c",
        "resist_x10000 >= 1 && resist_x10000 <= 20000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "milliohm meter resistance x10000 bounded");
}

/// Test current at ×1000 A — bounded range.
#[test]
fn test_milliohm_meter_test_current_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cur_a",
        "curr_x1000 >= 1 && curr_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cur_c",
        "curr_x1000 >= 1 && curr_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "milliohm meter test current x1000 bounded");
}

/// Accuracy at ×10000 % — bounded range.
#[test]
fn test_milliohm_meter_accuracy_x10000_bounded() {
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
    expect_verified(&result, "milliohm meter accuracy x10000 bounded");
}

/// Temperature with offset +100 °C — bounded range.
#[test]
fn test_milliohm_meter_temperature_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tmp_a",
        "temp_off >= 50 && temp_off <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tmp_c",
        "temp_off >= 50 && temp_off <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "milliohm meter temperature offset bounded");
}

/// Voltage drop at ×1000 mV — bounded range.
#[test]
fn test_milliohm_meter_voltage_drop_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vdrop_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vd_a",
        "vdrop_x1000 >= 1 && vdrop_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vd_c",
        "vdrop_x1000 >= 1 && vdrop_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "milliohm meter voltage drop x1000 bounded");
}

/// Sampling rate in Hz — bounded range.
#[test]
fn test_milliohm_meter_sampling_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr_a", "rate >= 1 && rate <= 500"));
    ctx.push_obligation(ProofObligation::assert("sr_c", "rate >= 1 && rate <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "milliohm meter sampling rate bounded");
}

/// Measurement range — 3-way disjunction.
#[test]
fn test_milliohm_meter_measurement_range_three_way() {
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
        "milliohm meter measurement range three-way disjunction",
    );
}

/// Connection method — 3-way disjunction.
#[test]
fn test_milliohm_meter_connection_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "milliohm meter connection method three-way disjunction",
    );
}

/// Compensation mode — 3-way disjunction.
#[test]
fn test_milliohm_meter_compensation_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "milliohm meter compensation mode three-way disjunction",
    );
}

/// Automatic zero — boolean flag.
#[test]
fn test_milliohm_meter_auto_zero_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("az_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("az_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "milliohm meter auto zero flag");
}
