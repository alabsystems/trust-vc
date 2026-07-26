// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Precision picoammeter property verification.
// Models key instrument parameters: current range codes, resolution digits,
// accuracy (x1000 scaling), input bias current, reading rate, voltage burden
// (x1000 scaling), measurement mode, guard configuration, ranging mode,
// and zero-check enable flag.

#[test]
fn test_current_range_code_bounded() {
    // Current range encoded as code 1-8 (fA through mA ranges)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_code", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_code_bounds",
        "range_code >= 1 && range_code <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_code_positive",
        "range_code >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_code_upper",
        "range_code <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current range code bounded in [1, 8]");
}

#[test]
fn test_resolution_digits_bounded() {
    // Resolution in significant digits (4 to 8 for precision instruments)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_bounds",
        "resolution >= 4 && resolution <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_positive",
        "resolution >= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_upper",
        "resolution <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution digits bounded in [4, 8]");
}

#[test]
fn test_accuracy_scaled_bounded() {
    // Accuracy encoded as x1000 percentage (1 = 0.001%, 1000 = 1.000%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_bounds",
        "accuracy_x1000 >= 1 && accuracy_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_positive",
        "accuracy_x1000 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_upper",
        "accuracy_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x1000 bounded in [1, 1000] (0.001% to 1.000%)",
    );
}

#[test]
fn test_input_bias_current_bounded() {
    // Input bias current in femtoamperes (1 fA to 1000 fA)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bias_fa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bias_bounds",
        "bias_fa >= 1 && bias_fa <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("bias_positive", "bias_fa >= 1"));
    ctx.push_obligation(ProofObligation::assert("bias_upper", "bias_fa <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input bias current bounded in [1, 1000] fA");
}

#[test]
fn test_reading_rate_bounded() {
    // Reading rate in readings per second (1 to 1000)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_bounds",
        "rate >= 1 && rate <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("rate_positive", "rate >= 1"));
    ctx.push_obligation(ProofObligation::assert("rate_upper", "rate <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reading rate bounded in [1, 1000] readings/s");
}

#[test]
fn test_voltage_burden_scaled_bounded() {
    // Voltage burden encoded as x1000 mV (1 = 0.001 mV, 10000 = 10.000 mV)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burden_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "burden_bounds",
        "burden_x1000 >= 1 && burden_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "burden_positive",
        "burden_x1000 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "burden_upper",
        "burden_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage burden x1000 bounded in [1, 10000] (0.001 to 10.000 mV)",
    );
}

#[test]
fn test_measurement_mode_three_way_disjunction() {
    // Measurement mode: 1=DC, 2=pulsed, 3=alternating
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mode_lower", "mode >= 1"));
    ctx.push_obligation(ProofObligation::assert("mode_upper", "mode <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode is one of DC(1), pulsed(2), alternating(3)",
    );
}

#[test]
fn test_guard_configuration_three_way_disjunction() {
    // Guard configuration: 1=cable-guard, 2=triax, 3=guarded-fixture
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("guard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "guard_valid",
        "guard == 1 || guard == 2 || guard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("guard_lower", "guard >= 1"));
    ctx.push_obligation(ProofObligation::assert("guard_upper", "guard <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "guard config is one of cable-guard(1), triax(2), guarded-fixture(3)",
    );
}

#[test]
fn test_ranging_mode_three_way_disjunction() {
    // Ranging mode: 1=auto, 2=manual, 3=best-fixed
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ranging", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ranging_valid",
        "ranging == 1 || ranging == 2 || ranging == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("ranging_lower", "ranging >= 1"));
    ctx.push_obligation(ProofObligation::assert("ranging_upper", "ranging <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ranging mode is one of auto(1), manual(2), best-fixed(3)",
    );
}

#[test]
fn test_zero_check_boolean_flag() {
    // Zero check enable: i32 flag where 1=enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zero_check", i32_ty());
    ctx.declare_var_typed("active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "zero_check == 0 || zero_check == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("zero_check_on", "zero_check == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "active == if zero_check == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "active_when_enabled",
        "active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zero check flag: enabled(1) produces active=1");
}
