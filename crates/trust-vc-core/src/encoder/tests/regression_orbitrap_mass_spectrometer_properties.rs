// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mass_range_amu() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass >= 1 && mass <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_range_check",
        "mass >= 1 && mass <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orbitrap mass range 1-6000 amu");
}

#[test]
fn resolution_x10() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "res_x10 >= 10000 && res_x10 <= 5000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_range_check",
        "res_x10 >= 10000 && res_x10 <= 5000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolving power 1000-500000 scaled by 10");
}

#[test]
fn mass_accuracy_x1000_ppm() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_range",
        "acc_x1000 >= 1 && acc_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_range_check",
        "acc_x1000 >= 1 && acc_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass accuracy 0.001-5.000 ppm scaled by 1000");
}

#[test]
fn spray_voltage_x10() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spray_range",
        "spray_x10 >= 5 && spray_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spray_range_check",
        "spray_x10 >= 5 && spray_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray voltage 0.5-6.0 kV scaled by 10");
}

#[test]
fn ion_transfer_tube_temp_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 150 && temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_range_check",
        "temp_off >= 150 && temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ion transfer tube temp 50-400C offset by +100");
}

#[test]
fn scan_rate_hz() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scan_range",
        "scan >= 1 && scan <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scan_range_check",
        "scan >= 1 && scan <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan rate 1-50 Hz");
}

#[test]
fn ionization_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionize", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ionization_mode",
        "ionize == 1 || ionize == 2 || ionize == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ionization_mode_check",
        "ionize == 1 || ionize == 2 || ionize == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionization mode ESI/APCI/APPI");
}

#[test]
fn fragmentation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fragmentation_mode",
        "frag == 1 || frag == 2 || frag == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fragmentation_mode_check",
        "frag == 1 || frag == 2 || frag == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fragmentation mode HCD/CID/ETD");
}

#[test]
fn polarity_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "polarity_mode",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "polarity_mode_check",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "polarity mode positive/negative/switching");
}

#[test]
fn auto_gain_control_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "agc_flag",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "agc_flag_check",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto gain control on/off boolean flag");
}
