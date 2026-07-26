// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_insulation_tester_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 50 && voltage <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 50 && voltage <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage must be between 50 and 15000 V");
}

#[test]
fn test_insulation_tester_resistance_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance_mohm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resistance_range",
        "resistance_mohm >= 1 && resistance_mohm <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resistance_bounded",
        "resistance_mohm >= 1 && resistance_mohm <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "insulation resistance must be between 1 and 1000000 MOhm",
    );
}

#[test]
fn test_insulation_tester_test_steps_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_steps", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "steps_range",
        "num_steps >= 1 && num_steps <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "steps_bounded",
        "num_steps >= 1 && num_steps <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of test steps must be between 1 and 20");
}

#[test]
fn test_insulation_tester_timer_duration_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("timer_sec", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "timer_range",
        "timer_sec >= 1 && timer_sec <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "timer_bounded",
        "timer_sec >= 1 && timer_sec <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer duration must be between 1 and 3600 seconds");
}

#[test]
fn test_insulation_tester_leakage_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leakage_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "leakage_range",
        "leakage_x100 >= 1 && leakage_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "leakage_bounded",
        "leakage_x100 >= 1 && leakage_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "leakage current x100 must be between 1 and 100000 representing 0.01-1000.00 uA",
    );
}

#[test]
fn test_insulation_tester_ramp_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ramp_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ramp_range",
        "ramp_rate >= 1 && ramp_rate <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ramp_bounded",
        "ramp_rate >= 1 && ramp_rate <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ramp rate must be between 1 and 10000 V/s");
}

#[test]
fn test_insulation_tester_test_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "test_mode == 1 || test_mode == 2 || test_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_disjunction",
        "test_mode == 1 || test_mode == 2 || test_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test mode must be 1=spot, 2=time-resistance, or 3=step-voltage",
    );
}

#[test]
fn test_insulation_tester_output_waveform_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "waveform_valid",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "waveform_disjunction",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output waveform must be 1=DC, 2=AC, or 3=DC-with-guard",
    );
}

#[test]
fn test_insulation_tester_measurement_parameter_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_param", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "param_valid",
        "meas_param == 1 || meas_param == 2 || meas_param == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "param_disjunction",
        "meas_param == 1 || meas_param == 2 || meas_param == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement parameter must be 1=resistance, 2=polarization-index, or 3=DAR",
    );
}

#[test]
fn test_insulation_tester_automatic_discharge_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_discharge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_bool",
        "auto_discharge == 0 || auto_discharge == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_is_boolean",
        "auto_discharge == 0 || auto_discharge == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic discharge flag must be 0 (off) or 1 (on)",
    );
}
