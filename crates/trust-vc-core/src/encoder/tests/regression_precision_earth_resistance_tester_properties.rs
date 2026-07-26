// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_earth_resistance_tester_resistance_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resistance_range",
        "resistance >= 1 && resistance <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resistance_bounded",
        "resistance >= 1 && resistance <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement range 1-200000 ohms");
}

#[test]
fn test_earth_resistance_tester_test_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_current_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "test_current_x100 >= 1 && test_current_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "test_current_x100 >= 1 && test_current_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test current x100 in range 1-5000 (0.01-50.00 mA)");
}

#[test]
fn test_earth_resistance_tester_test_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_frequency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frequency_range",
        "test_frequency >= 25 && test_frequency <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frequency_bounded",
        "test_frequency >= 25 && test_frequency <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test frequency 25-3000 Hz");
}

#[test]
fn test_earth_resistance_tester_electrode_spacing_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrode_spacing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spacing_range",
        "electrode_spacing >= 1 && electrode_spacing <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spacing_bounded",
        "electrode_spacing >= 1 && electrode_spacing <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrode spacing 1-100 meters");
}

#[test]
fn test_earth_resistance_tester_noise_rejection_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_rejection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise_rejection >= 40 && noise_rejection <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "noise_bounded",
        "noise_rejection >= 40 && noise_rejection <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise rejection 40-100 dB");
}

#[test]
fn test_earth_resistance_tester_num_electrodes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_electrodes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "electrodes_range",
        "num_electrodes >= 2 && num_electrodes <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "electrodes_bounded",
        "num_electrodes >= 2 && num_electrodes <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of electrodes 2-20");
}

#[test]
fn test_earth_resistance_tester_measurement_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_range",
        "method >= 1 && method <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "method_bounded",
        "method >= 1 && method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "method: 1=fall-of-potential, 2=Wenner, 3=Schlumberger",
    );
}

#[test]
fn test_earth_resistance_tester_electrode_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "config_range",
        "config >= 1 && config <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "config_bounded",
        "config >= 1 && config <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "config: 1=inline, 2=rectangular, 3=triangular");
}

#[test]
fn test_earth_resistance_tester_soil_model_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("soil_model", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "soil_range",
        "soil_model >= 1 && soil_model <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "soil_bounded",
        "soil_model >= 1 && soil_model <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "model: 1=uniform, 2=two-layer, 3=multi-layer");
}

#[test]
fn test_earth_resistance_tester_auto_frequency_select_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_freq_select", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "auto_freq_select >= 0 && auto_freq_select <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "auto_freq_select >= 0 && auto_freq_select <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean: 0=disabled, 1=enabled");
}
