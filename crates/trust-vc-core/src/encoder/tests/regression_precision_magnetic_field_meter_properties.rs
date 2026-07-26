// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_magnetic_field_meter_field_strength_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("field_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fs_a",
        "field_x1000 >= 1 && field_x1000 <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fs_c",
        "field_x1000 >= 1 && field_x1000 <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field strength x1000 bounded");
}

#[test]
fn test_magnetic_field_meter_frequency_response_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "freq_x10 >= 0 && freq_x10 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "freq_x10 >= 0 && freq_x10 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnetic field meter frequency response x10 bounded",
    );
}

#[test]
fn test_magnetic_field_meter_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ac_a",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ac_c",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field meter accuracy x10000 bounded");
}

#[test]
fn test_magnetic_field_meter_resolution_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rs_a",
        "res_x10000 >= 1 && res_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rs_c",
        "res_x10000 >= 1 && res_x10000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field meter resolution x10000 bounded");
}

#[test]
fn test_magnetic_field_meter_temp_coeff_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tc_a",
        "tc_x10000 >= 1 && tc_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tc_c",
        "tc_x10000 >= 1 && tc_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnetic field meter temperature coefficient x10000 bounded",
    );
}

#[test]
fn test_magnetic_field_meter_probe_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pl_a",
        "probe_len >= 10 && probe_len <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pl_c",
        "probe_len >= 10 && probe_len <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field meter probe length bounded");
}

#[test]
fn test_magnetic_field_meter_sensor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "sensor == 1 || sensor == 2 || sensor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "sensor == 1 || sensor == 2 || sensor == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnetic field meter sensor type three-way disjunction",
    );
}

#[test]
fn test_magnetic_field_meter_axis_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axis_cfg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ax_a",
        "axis_cfg == 1 || axis_cfg == 2 || axis_cfg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ax_c",
        "axis_cfg == 1 || axis_cfg == 2 || axis_cfg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnetic field meter axis configuration three-way disjunction",
    );
}

#[test]
fn test_magnetic_field_meter_output_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("out_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "om_a",
        "out_mode == 1 || out_mode == 2 || out_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "om_c",
        "out_mode == 1 || out_mode == 2 || out_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnetic field meter output mode three-way disjunction",
    );
}

#[test]
fn test_magnetic_field_meter_auto_zero_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("az_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("az_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetic field meter auto zero flag");
}
