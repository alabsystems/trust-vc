// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_frequency_range_min_hz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_min_hz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fm", "freq_min_hz == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_min_hz >= 1 && freq_min_hz <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: freq min 20 Hz in [1, 100]");
}

#[test]
fn test_frequency_range_max_khz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_max_hz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // kHz range: 1000 Hz to 120000 Hz (1 kHz to 120 kHz)
    ctx.push_obligation(ProofObligation::assume("fmx", "freq_max_hz == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_max_hz >= 1000 && freq_max_hz <= 120000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: freq max 50000 Hz in [1kHz, 120kHz]");
}

#[test]
fn test_impedance_range_ohms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance_ohm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Impedance range: 1 ohm to 100 megaohm
    ctx.push_obligation(ProofObligation::assume("z", "impedance_ohm == 4700"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if impedance_ohm >= 1 && impedance_ohm <= 100000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: 4700 ohm in [1, 100M]");
}

#[test]
fn test_accuracy_scaled_thousandths_percent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    // 0.05% accuracy = 50 in x1000 scale; max 1% = 1000
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if accuracy_x1000 >= 1 && accuracy_x1000 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: accuracy 0.050% (50/1000) in range");
}

#[test]
fn test_signal_level_scaled_hundredths_volt() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal_level_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // 0.50V = 50 in x100 scale; range 1 (0.01V) to 200 (2.00V)
    ctx.push_obligation(ProofObligation::assume("sl", "signal_level_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if signal_level_x100 >= 1 && signal_level_x100 <= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impedance: signal 0.50V (50/100) in [0.01V, 2.00V]",
    );
}

#[test]
fn test_measurement_parameter_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_param", i32_ty());
    // 1=Z/theta, 2=R/X, 3=C/D
    ctx.push_obligation(ProofObligation::assume("mp", "meas_param == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "meas_param == 1 || meas_param == 2 || meas_param == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: meas param R/X (2) valid");
}

#[test]
fn test_equivalent_circuit_model_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eq_circuit", i32_ty());
    // 1=series, 2=parallel, 3=auto
    ctx.push_obligation(ProofObligation::assume("ec", "eq_circuit == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "eq_circuit == 1 || eq_circuit == 2 || eq_circuit == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: eq circuit auto (3) valid");
}

#[test]
fn test_measurement_speed_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    // 1=slow, 2=medium, 3=fast
    ctx.push_obligation(ProofObligation::assume("sp", "speed == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "speed == 1 || speed == 2 || speed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: speed slow (1) valid");
}

#[test]
fn test_dc_bias_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dc_bias_v", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // DC bias: 0V to 40V
    ctx.push_obligation(ProofObligation::assume("db", "dc_bias_v == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dc_bias_v >= 0 && dc_bias_v <= 40 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: DC bias 25V in [0, 40]");
}

#[test]
fn test_compensation_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("open_short_comp", i32_ty());
    ctx.declare_var_typed("compensated", i32_ty());
    // 1=enabled, 0=disabled (open/short compensation)
    ctx.push_obligation(ProofObligation::assume("osc", "open_short_comp == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == if open_short_comp == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("on", "compensated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impedance: open/short compensation enabled");
}
