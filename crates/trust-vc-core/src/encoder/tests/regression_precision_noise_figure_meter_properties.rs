// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_noise_figure_meter_noise_figure_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nf_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nf_a",
        "nf_x100 >= 1 && nf_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nf_c",
        "nf_x100 >= 1 && nf_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise figure x100 bounded");
}

#[test]
fn test_noise_figure_meter_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "freq_x10 >= 1 && freq_x10 <= 500000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "freq_x10 >= 1 && freq_x10 <= 500000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise figure meter frequency x10 bounded");
}

#[test]
fn test_noise_figure_meter_gain_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ga_a",
        "gain_x100 >= 0 && gain_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ga_c",
        "gain_x100 >= 0 && gain_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise figure meter gain x100 bounded");
}

#[test]
fn test_noise_figure_meter_enr_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("enr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "en_a",
        "enr_x100 >= 100 && enr_x100 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "en_c",
        "enr_x100 >= 100 && enr_x100 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise figure meter ENR x100 bounded");
}

#[test]
fn test_noise_figure_meter_measurement_uncertainty_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("unc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mu_a",
        "unc_x10000 >= 1 && unc_x10000 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mu_c",
        "unc_x10000 >= 1 && unc_x10000 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise figure meter measurement uncertainty x10000 bounded",
    );
}

#[test]
fn test_noise_figure_meter_if_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("if_bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ib_a",
        "if_bw >= 1 && if_bw <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ib_c",
        "if_bw >= 1 && if_bw <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise figure meter IF bandwidth bounded");
}

#[test]
fn test_noise_figure_meter_noise_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ns_a",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ns_c",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise figure meter noise source three-way disjunction",
    );
}

#[test]
fn test_noise_figure_meter_measurement_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mm_a",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mm_c",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise figure meter measurement method three-way disjunction",
    );
}

#[test]
fn test_noise_figure_meter_display_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("display", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dm_a",
        "display == 1 || display == 2 || display == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dm_c",
        "display == 1 || display == 2 || display == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise figure meter display mode three-way disjunction",
    );
}

#[test]
fn test_noise_figure_meter_auto_cal_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ac_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise figure meter auto calibration flag");
}
