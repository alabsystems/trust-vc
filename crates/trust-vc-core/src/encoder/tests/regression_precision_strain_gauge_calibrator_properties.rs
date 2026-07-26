// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: precision strain gauge calibrator properties

use super::*;

#[test]
fn test_strain_gauge_calibrator_strain_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("microstrain", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "microstrain >= 100 && microstrain <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "microstrain == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "microstrain >= 100 && microstrain <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max microstrain range 100-100000 with value 50000");
}

#[test]
fn test_strain_gauge_calibrator_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "accuracy_x10000 >= 1 && accuracy_x10000 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10000 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x10000 >= 1 && accuracy_x10000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy scaled x10000 percent range 1-100 with value 5 representing 0.0005 percent",
    );
}

#[test]
fn test_strain_gauge_calibrator_excitation_voltage_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "excitation_x1000 >= 100 && excitation_x1000 <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "excitation_x1000 == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "excitation_x1000 >= 100 && excitation_x1000 <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bridge excitation voltage scaled x1000 range 100-15000 with value 10000 representing 10.000V");
}

#[test]
fn test_strain_gauge_calibrator_gauge_factor_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gf_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "gf_x100 >= 100 && gf_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "gf_x100 == 207"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "gf_x100 >= 100 && gf_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gauge factor scaled x100 range 100-500 with value 207 representing 2.07",
    );
}

#[test]
fn test_strain_gauge_calibrator_bridge_resistance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance_ohms", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resistance_ohms >= 100 && resistance_ohms <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resistance_ohms == 350"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resistance_ohms >= 100 && resistance_ohms <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nominal bridge resistance range 100-10000 ohms with value 350",
    );
}

#[test]
fn test_strain_gauge_calibrator_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 64",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input channel count range 1-64 with value 16");
}

#[test]
fn test_strain_gauge_calibrator_bridge_config_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bridge_config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "enum",
        "bridge_config == 1 || bridge_config == 2 || bridge_config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "bridge_config >= 1 && bridge_config <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bridge configuration 1=quarter 2=half 3=full implies bounded 1-3",
    );
}

#[test]
fn test_strain_gauge_calibrator_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "enum",
        "output_type == 1 || output_type == 2 || output_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "output_type >= 1 && output_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output type 1=mV/V 2=frequency 3=digital implies bounded 1-3",
    );
}

#[test]
fn test_strain_gauge_calibrator_completion_resistor_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("completion", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "enum",
        "completion == 1 || completion == 2 || completion == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "completion >= 1 && completion <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "completion resistor 1=internal 2=external 3=none implies bounded 1-3",
    );
}

#[test]
fn test_strain_gauge_calibrator_auto_zero_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_zero", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "auto_zero == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "if auto_zero == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto zero boolean flag when enabled evaluates to 1",
    );
}
