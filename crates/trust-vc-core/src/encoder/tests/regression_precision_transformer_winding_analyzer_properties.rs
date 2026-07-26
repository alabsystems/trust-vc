// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_transformer_winding_turns_ratio_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ratio",
        "ratio_x1000 >= 100 && ratio_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ratio",
        "ratio_x1000 >= 100 && ratio_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turns ratio x1000 bounded 0.001 precision");
}

#[test]
fn test_transformer_winding_dc_resistance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_resistance",
        "res_x100 >= 1 && res_x100 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_resistance",
        "res_x100 >= 1 && res_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dc resistance x100 bounded 0.01 milliohm precision",
    );
}

#[test]
fn test_transformer_winding_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_voltage",
        "voltage >= 100 && voltage <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_voltage",
        "voltage >= 100 && voltage <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage bounded in V");
}

#[test]
fn test_transformer_winding_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_freq",
        "freq >= 10 && freq <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_freq",
        "freq >= 10 && freq <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency bounded in Hz");
}

#[test]
fn test_transformer_winding_phase_angle_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_angle",
        "angle_x10 >= 0 && angle_x10 <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_angle",
        "angle_x10 >= 0 && angle_x10 <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "phase angle x10 bounded 0.1 degrees precision");
}

#[test]
fn test_transformer_winding_winding_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_wc",
        "wc == 1 || wc == 2 || wc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_wc",
        "wc == 1 || wc == 2 || wc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "winding config three way 1=star 2=delta 3=zigzag");
}

#[test]
fn test_transformer_winding_test_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_tt",
        "tt == 1 || tt == 2 || tt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_tt",
        "tt == 1 || tt == 2 || tt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test type three way 1=ratio 2=resistance 3=impedance",
    );
}

#[test]
fn test_transformer_winding_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_std",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_std",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "standard three way 1=IEC-60076 2=IEEE-C57 3=ANSI-C57",
    );
}

#[test]
fn test_transformer_winding_auto_tap_changer_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_flag",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_flag",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto tap changer boolean flag");
}

#[test]
fn test_transformer_winding_power_rating_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_power",
        "power >= 1 && power <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_power",
        "power >= 1 && power <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power rating bounded in kVA");
}
