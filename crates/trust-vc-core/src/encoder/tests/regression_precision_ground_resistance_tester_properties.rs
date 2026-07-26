// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ground_resistance_tester_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x100 >= 1 && res_x100 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res_x100 >= 1 && res_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resistance range x100 must be in range 1-1000000 representing 0.01-10000.00 ohms",
    );
}

#[test]
fn test_ground_resistance_tester_test_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 1 && current <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "current >= 1 && current <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test current must be between 1 and 50000 mA");
}

#[test]
fn test_ground_resistance_tester_test_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 10 && freq <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq >= 10 && freq <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test frequency must be between 10 and 5000 Hz");
}

#[test]
fn test_ground_resistance_tester_electrodes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elec", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elec_range",
        "elec >= 2 && elec <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elec_bounded",
        "elec >= 2 && elec <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of measurement electrodes must be between 2 and 4",
    );
}

#[test]
fn test_ground_resistance_tester_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x100 >= 1 && acc_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x100 >= 1 && acc_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x100 must be in range 1-500 representing 0.01-5.00 percent",
    );
}

#[test]
fn test_ground_resistance_tester_probe_spacing_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spacing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spacing_range",
        "spacing >= 1 && spacing <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spacing_bounded",
        "spacing >= 1 && spacing <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe spacing must be between 1 and 100 m");
}

#[test]
fn test_ground_resistance_tester_measurement_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_range",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "method_valid",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement method must be fall-of-potential (1), clamp-on (2), or stakeless (3)",
    );
}

#[test]
fn test_ground_resistance_tester_test_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ttype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ttype_range",
        "ttype == 1 || ttype == 2 || ttype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ttype_valid",
        "ttype == 1 || ttype == 2 || ttype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test type must be 3-pole (1), 4-pole (2), or selective (3)",
    );
}

#[test]
fn test_ground_resistance_tester_soil_model_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("soil", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "soil_range",
        "soil == 1 || soil == 2 || soil == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "soil_valid",
        "soil == 1 || soil == 2 || soil == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "soil model must be wenner (1), schlumberger (2), or driven-rod (3)",
    );
}

#[test]
fn test_ground_resistance_tester_auto_noise_rejection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise == 0 || noise == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "noise_valid",
        "noise == 0 || noise == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic noise rejection flag must be 0 (disabled) or 1 (enabled)",
    );
}
