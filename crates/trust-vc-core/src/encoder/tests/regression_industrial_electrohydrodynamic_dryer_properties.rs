// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ehd_dryer_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hv_a",
        "voltage >= 1000 && voltage <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hv_c",
        "voltage >= 1000 && voltage <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer high voltage bounded");
}

#[test]
fn test_ehd_dryer_electrode_gap_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eg_a",
        "gap_x10 >= 10 && gap_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eg_c",
        "gap_x10 >= 10 && gap_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer electrode gap x10 bounded");
}

#[test]
fn test_ehd_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "air_temp >= 120 && air_temp <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "air_temp >= 120 && air_temp <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer air temperature offset+100 bounded");
}

#[test]
fn test_ehd_dryer_corona_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("corona_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "corona_x100 >= 1 && corona_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "corona_x100 >= 1 && corona_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer corona current x100 bounded");
}

#[test]
fn test_ehd_dryer_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "freq >= 50 && freq <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "freq >= 50 && freq <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer frequency bounded");
}

#[test]
fn test_ehd_dryer_power_density_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pd_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pd_a",
        "pd_x100 >= 1 && pd_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pd_c",
        "pd_x100 >= 1 && pd_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer power density x100 bounded");
}

#[test]
fn test_ehd_dryer_electrode_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "et_a",
        "electrode == 1 || electrode == 2 || electrode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "et_c",
        "electrode == 1 || electrode == 2 || electrode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer electrode type three-way disjunction");
}

#[test]
fn test_ehd_dryer_waveform_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer waveform three-way disjunction");
}

#[test]
fn test_ehd_dryer_flow_pattern_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_pat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fp_a",
        "flow_pat == 1 || flow_pat == 2 || flow_pat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fp_c",
        "flow_pat == 1 || flow_pat == 2 || flow_pat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer flow pattern three-way disjunction");
}

#[test]
fn test_ehd_dryer_auto_spark_suppression_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ss_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ss_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EHD dryer auto spark suppression flag");
}
