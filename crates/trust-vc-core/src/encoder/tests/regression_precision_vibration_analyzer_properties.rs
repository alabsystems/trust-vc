// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vibration_analyzer_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 1 && freq <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq >= 1 && freq <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency range must be between 1 and 100000 Hz");
}

#[test]
fn test_vibration_analyzer_number_of_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ch_range",
        "channels >= 1 && channels <= 64",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ch_bounded",
        "channels >= 1 && channels <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels must be between 1 and 64");
}

#[test]
fn test_vibration_analyzer_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dyn_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_range",
        "dyn_range >= 60 && dyn_range <= 160",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_bounded",
        "dyn_range >= 60 && dyn_range <= 160",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range must be between 60 and 160 dB");
}

#[test]
fn test_vibration_analyzer_sampling_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_range",
        "sample_rate >= 1000 && sample_rate <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_bounded",
        "sample_rate >= 1000 && sample_rate <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sampling rate must be between 1000 and 200000 samples/s",
    );
}

#[test]
fn test_vibration_analyzer_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    // Resolution x100: range 1-10000 representing 0.01-100.00 Hz
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "resolution >= 1 && resolution <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "resolution >= 1 && resolution <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resolution x100 must be between 1 and 10000 (0.01-100.00 Hz)",
    );
}

#[test]
fn test_vibration_analyzer_acceleration_range_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accel", i32_ty());
    // Acceleration range x10: range 1-50000 representing 0.1-5000.0 g
    ctx.push_obligation(ProofObligation::assume(
        "accel_range",
        "accel >= 1 && accel <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accel_bounded",
        "accel >= 1 && accel <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "acceleration range x10 must be between 1 and 50000 (0.1-5000.0 g)",
    );
}

#[test]
fn test_vibration_analyzer_sensor_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", i32_ty());
    ctx.declare_var_typed("valid_sensor", i32_ty());
    // Sensor type: 1=accelerometer, 2=velocity, 3=displacement
    ctx.push_obligation(ProofObligation::assume("sensor_val", "sensor == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sensor_def",
        "valid_sensor == if sensor == 1 || sensor == 2 || sensor == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sensor_chk", "valid_sensor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensor type 1 (accelerometer) is valid sensor type",
    );
}

#[test]
fn test_vibration_analyzer_analysis_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analysis", i32_ty());
    ctx.declare_var_typed("valid_analysis", i32_ty());
    // Analysis type: 1=FFT, 2=order-tracking, 3=envelope
    ctx.push_obligation(ProofObligation::assume("analysis_val", "analysis == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "analysis_def",
        "valid_analysis == if analysis == 1 || analysis == 2 || analysis == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analysis_chk",
        "valid_analysis == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis type 2 (order-tracking) is valid analysis type",
    );
}

#[test]
fn test_vibration_analyzer_window_function_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("window", i32_ty());
    ctx.declare_var_typed("valid_window", i32_ty());
    // Window function: 1=hanning, 2=flat-top, 3=rectangular
    ctx.push_obligation(ProofObligation::assume("window_val", "window == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "window_def",
        "valid_window == if window == 1 || window == 2 || window == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("window_chk", "valid_window == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "window function 3 (rectangular) is valid window function",
    );
}

#[test]
fn test_vibration_analyzer_balancing_recommendation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bal_rec", i32_ty());
    ctx.declare_var_typed("valid_flag", i32_ty());
    // Automatic balancing recommendation: boolean flag (0=no, 1=yes)
    ctx.push_obligation(ProofObligation::assume("br_val", "bal_rec == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "br_def",
        "valid_flag == if bal_rec == 0 || bal_rec == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("br_chk", "valid_flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "balancing recommendation flag 1 (yes) is valid boolean",
    );
}
