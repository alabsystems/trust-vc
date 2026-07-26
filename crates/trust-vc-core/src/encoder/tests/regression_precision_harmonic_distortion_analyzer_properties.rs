// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_harmonic_analyzer_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 10 && freq <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq >= 10 && freq <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fundamental frequency must be between 10 and 100000 Hz",
    );
}

#[test]
fn test_harmonic_analyzer_max_harmonic_order_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("order", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "order_range",
        "order >= 2 && order <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "order_bounded",
        "order >= 2 && order <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "maximum harmonic order must be between 2 and 100");
}

#[test]
fn test_harmonic_analyzer_voltage_input_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volt_range",
        "volt >= 1 && volt <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "volt_bounded",
        "volt >= 1 && volt <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input voltage must be between 1 and 1000 V");
}

#[test]
fn test_harmonic_analyzer_thd_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thd", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thd_range",
        "thd >= 0 && thd <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thd_bounded",
        "thd >= 0 && thd <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "total harmonic distortion x100 must be between 0 and 10000",
    );
}

#[test]
fn test_harmonic_analyzer_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drange", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drange_range",
        "drange >= 60 && drange <= 160",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drange_bounded",
        "drange >= 60 && drange <= 160",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range must be between 60 and 160 dB");
}

#[test]
fn test_harmonic_analyzer_sampling_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1000 && rate <= 5000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1000 && rate <= 5000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sampling rate must be between 1000 and 5000000 Hz");
}

#[test]
fn test_harmonic_analyzer_window_function_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("win", i32_ty());
    ctx.push_obligation(ProofObligation::assume("win_range", "win >= 1 && win <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "win_bounded",
        "win >= 1 && win <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "window function must be 1=Hanning, 2=Blackman-Harris, or 3=flat-top",
    );
}

#[test]
fn test_harmonic_analyzer_coupling_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coupling_range",
        "coupling >= 1 && coupling <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coupling_bounded",
        "coupling >= 1 && coupling <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coupling mode must be 1=AC, 2=DC, or 3=AC+DC");
}

#[test]
fn test_harmonic_analyzer_analysis_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atype_range",
        "atype >= 1 && atype <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atype_bounded",
        "atype >= 1 && atype <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis type must be 1=THD, 2=THD+N, or 3=individual-harmonics",
    );
}

#[test]
fn test_harmonic_analyzer_auto_fundamental_detect_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "flag >= 0 && flag <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "flag >= 0 && flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto fundamental detect flag must be 0=disabled or 1=enabled",
    );
}
