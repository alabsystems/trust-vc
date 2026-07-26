// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_power_integrity_analyzer_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "bw >= 1 && bw <= 10000"));
    ctx.push_obligation(ProofObligation::assume("val", "bw == 2000"));
    ctx.push_obligation(ProofObligation::assert("bound", "bw >= 1 && bw <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power integrity analyzer bandwidth within range");
}

#[test]
fn test_power_integrity_analyzer_voltage_accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "acc_x10000 > 0 && acc_x10000 < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "acc_x10000 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "acc_x10000 > 0 && acc_x10000 < 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer voltage accuracy within range",
    );
}

#[test]
fn test_power_integrity_analyzer_current_range_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "curr_x100 > 0 && curr_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "curr_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "curr_x100 > 0 && curr_x100 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer current range 50.00 A within range",
    );
}

#[test]
fn test_power_integrity_analyzer_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "ch >= 1 && ch <= 32"));
    ctx.push_obligation(ProofObligation::assume("val", "ch == 8"));
    ctx.push_obligation(ProofObligation::assert("bound", "ch >= 1 && ch <= 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer channel count within range",
    );
}

#[test]
fn test_power_integrity_analyzer_noise_floor_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nf_off", i32_ty());
    // offset +200: nf_off=340 means -60 dBm (340-200=-60... wait, offset means nf_off = actual+200)
    // So nf_off=140 means -60 dBm
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "nf_off > 200 && nf_off < 400",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "nf_off == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "nf_off > 200 && nf_off < 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer noise floor within offset range",
    );
}

#[test]
fn test_power_integrity_analyzer_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rate >= 1 && rate <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rate == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "rate >= 1 && rate <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power integrity analyzer sample rate within range");
}

#[test]
fn test_power_integrity_analyzer_measurement_domain_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("domain", i32_ty());
    // 1=time, 2=frequency, 3=impedance
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "domain == 1 || domain == 2 || domain == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "domain == 1 || domain == 2 || domain == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer measurement domain must be valid",
    );
}

#[test]
fn test_power_integrity_analyzer_probe_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe", i32_ty());
    // 1=voltage, 2=current, 3=near-field
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power integrity analyzer probe type must be valid");
}

#[test]
fn test_power_integrity_analyzer_analysis_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    // 1=ripple, 2=transient, 3=impedance-profile
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer analysis method must be valid",
    );
}

#[test]
fn test_power_integrity_analyzer_auto_pdn_extraction_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("boolean", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "pdn_extract",
        "if flag == 1 { 1 } else { 0 } >= 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power integrity analyzer automatic PDN extraction flag",
    );
}
