// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_frequency_range_max_mhz_bounded() {
    // Frequency range: 1 MHz to 120 MHz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f", "freq_mhz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_mhz >= 1 && freq_mhz <= 120 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: freq 50 MHz in [1, 120]");
}

#[test]
fn test_impedance_range_megaohms_bounded() {
    // Impedance range: 1 MOhm to 100 MOhm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance_mohm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("z", "impedance_mohm == 47"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if impedance_mohm >= 1 && impedance_mohm <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: impedance 47 MOhm in [1, 100]");
}

#[test]
fn test_measurement_accuracy_scaled_thousandths_percent() {
    // Accuracy in units of 0.001% (x1000 scaling)
    // 0.100% = 100 scaled units; range 1..500 (0.001% to 0.500%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x1000 == 100")); // 0.100%
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if accuracy_x1000 >= 1 && accuracy_x1000 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: accuracy 0.100% (100/1000) in range");
}

#[test]
fn test_dc_bias_voltage_bounded() {
    // DC bias voltage: 0V to 40V
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dc_bias_v", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("db", "dc_bias_v == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dc_bias_v >= 0 && dc_bias_v <= 40 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: DC bias 15V in [0, 40]");
}

#[test]
fn test_points_per_sweep_bounded() {
    // Points per sweep: 1 to 10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("points", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "points == 201"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if points >= 1 && points <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: 201 points per sweep in [1, 10000]");
}

#[test]
fn test_measurement_topology_disjunction() {
    // Measurement topology: 1=two-terminal, 2=four-terminal, 3=four-terminal-pair
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topology", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "topology == 3")); // four-terminal-pair
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "topology == 1 || topology == 2 || topology == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectroscopy: topology four-terminal-pair (3) valid",
    );
}

#[test]
fn test_equivalent_circuit_model_disjunction() {
    // Equivalent circuit model: 1=series, 2=parallel, 3=custom
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eq_model", i32_ty());
    ctx.push_obligation(ProofObligation::assume("em", "eq_model == 2")); // parallel
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "eq_model == 1 || eq_model == 2 || eq_model == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: eq circuit parallel (2) valid");
}

#[test]
fn test_oscillator_level_scaled_thousandths_volt() {
    // Oscillator level in units of 0.001V (x1000 scaling)
    // 0.500V = 500 scaled units; range 1..20000 (0.001V to 20.000V)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("osc_level_x1000", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ol", "osc_level_x1000 == 500")); // 0.500V
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if osc_level_x1000 >= 1 && osc_level_x1000 <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectroscopy: osc level 0.500V (500/1000) in range",
    );
}

#[test]
fn test_sweep_type_disjunction() {
    // Sweep type: 1=linear, 2=logarithmic, 3=list
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sweep_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sweep_type == 2")); // logarithmic
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "sweep_type == 1 || sweep_type == 2 || sweep_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: sweep logarithmic (2) valid");
}

#[test]
fn test_temperature_compensation_flag() {
    // Temperature compensation: boolean flag as i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_comp", i32_ty());
    ctx.declare_var_typed("compensated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "temp_comp == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == if temp_comp == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "compensated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectroscopy: temp compensation enabled");
}
