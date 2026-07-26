use super::*;

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

/// NOx concentration in ppm: bounded [1, 5000], concrete value 1000.
#[test]
fn test_nox_range_ppm() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nox_ppm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("nox_val", "nox_ppm == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "nox_bounded",
        "nox_ppm >= 1 && nox_ppm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NOx 1000 ppm within valid range [1, 5000]");
}

/// CO concentration in ppm: bounded [1, 3000], concrete value 500.
#[test]
fn test_co_range_ppm() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("co_ppm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("co_val", "co_ppm == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "co_bounded",
        "co_ppm >= 1 && co_ppm <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CO 500 ppm within valid range [1, 3000]");
}

/// O2 percentage scaled x10: 250 represents 25.0%, bounded [0, 300].
#[test]
fn test_o2_range_x10_percent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("o2_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("o2_val", "o2_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "o2_bounded",
        "o2_x10 >= 0 && o2_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "O2 25.0% (x10=250) within valid range [0, 300]");
}

/// Analyzer type: 3-way disjunction (1=NDIR, 2=chemiluminescent, 3=paramagnetic).
#[test]
fn test_analyzer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "analyzer_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "analyzer_type == 1 || analyzer_type == 2 || analyzer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chemiluminescent (2) is a valid analyzer type");
}

/// Sample conditioning method: 3-way disjunction (1=hot-wet, 2=cold-dry, 3=dilution).
#[test]
fn test_sample_conditioning_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conditioning", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cond_val", "conditioning == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_conditioning",
        "conditioning == 1 || conditioning == 2 || conditioning == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hot-wet (1) is a valid sample conditioning method");
}

/// Response time T90 in seconds: bounded [1, 120], concrete value 30.
#[test]
fn test_response_time_t90() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t90", u32_ty());
    ctx.push_obligation(ProofObligation::assume("t90_val", "t90 == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "t90_bounded",
        "t90 >= 1 && t90 <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T90 response time 30s within valid range [1, 120]");
}

/// Accuracy as percentage of range scaled x10: 10 represents 1.0%, bounded [5, 50].
#[test]
fn test_accuracy_x10_percent_of_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_bounded",
        "accuracy_x10 >= 5 && accuracy_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 1.0% (x10=10) within valid range [5, 50]");
}

/// Communication protocol: 4-way disjunction (1=4-20mA, 2=Modbus, 3=Profibus, 4=Ethernet).
#[test]
fn test_communication_protocol_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_protocol", u32_ty());
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm_protocol == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_protocol",
        "comm_protocol == 1 || comm_protocol == 2 || comm_protocol == 3 || comm_protocol == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ethernet (4) is a valid communication protocol");
}

/// Gas measurement channels: bounded [1, 12], concrete value 5.
#[test]
fn test_gas_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume("channels_val", "channels == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "channels_bounded",
        "channels >= 1 && channels <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 gas channels within valid range [1, 12]");
}

/// Auto-calibration boolean flag: flag=1 means enabled.
#[test]
fn test_auto_calibration_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_cal_flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "cal_enabled",
        "if auto_cal_flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-calibration flag=1 evaluates to enabled");
}
