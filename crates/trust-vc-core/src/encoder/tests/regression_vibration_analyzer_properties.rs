// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_frequency_range_hz() {
    // Analysis bandwidth: value 20000 Hz within [100, 100000]
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq", "max_freq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("f", "freq_hz == 20000"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_freq == 100"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_freq == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_hz >= min_freq && freq_hz <= max_freq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration: 20000 Hz in [100, 100000]");
}

#[test]
fn test_dynamic_range_db() {
    // Measurement dynamic range: value 120 dB within [80, 160]
    let mut ctx = VerificationContext::new();
    for v in &["dynamic_range_db", "min_db", "max_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dr", "dynamic_range_db == 120"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_db == 80"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_db == 160"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dynamic_range_db >= min_db && dynamic_range_db <= max_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration: 120 dB in [80, 160]");
}

#[test]
fn test_channel_count() {
    // Simultaneous measurement inputs: value 4 within [1, 32]
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_ch", "max_ch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_ch == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_ch == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if channels >= min_ch && channels <= max_ch { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration: 4 channels in [1, 32]");
}

#[test]
fn test_sensor_type_disjunction() {
    // 1=accelerometer, 2=velocity, 3=displacement, 4=proximity
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 2")); // velocity
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 || sensor_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration sensor: velocity(2) is valid type");
}

#[test]
fn test_fft_lines_non_sequential() {
    // Spectral resolution lines: valid values are 800, 1600, 3200, 6400
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fft_lines", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fl", "fft_lines == 3200"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if fft_lines == 800 || fft_lines == 1600 || fft_lines == 3200 || fft_lines == 6400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration FFT: 3200 lines is valid");
}

#[test]
fn test_sample_rate_hz() {
    // ADC sample rate: value 51200 Hz within [1024, 204800]
    let mut ctx = VerificationContext::new();
    for v in &["sample_rate", "min_rate", "max_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate == 51200"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_rate == 1024"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_rate == 204800"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if sample_rate >= min_rate && sample_rate <= max_rate { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration ADC: 51200 Hz in [1024, 204800]");
}

#[test]
fn test_alarm_severity_disjunction() {
    // 1=normal, 2=alert, 3=danger, 4=shutdown
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("severity", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "severity == 3")); // danger
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if severity == 1 || severity == 2 || severity == 3 || severity == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration alarm: danger(3) is valid severity");
}

#[test]
fn test_window_function_disjunction() {
    // 1=Hanning, 2=Hamming, 3=flat-top, 4=rectangular
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("window_fn", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wf", "window_fn == 1")); // Hanning
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if window_fn == 1 || window_fn == 2 || window_fn == 3 || window_fn == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration window: Hanning(1) is valid function");
}

#[test]
fn test_operating_temp_offset() {
    // Temperature offset +500: value 525 (25C), min 460 (-40C), max 585 (85C)
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25C
    ctx.push_obligation(ProofObligation::assume("lo", "min_temp_offset == 460")); // -40C
    ctx.push_obligation(ProofObligation::assume("hi", "max_temp_offset == 585")); // 85C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration temp: 525 (25C) in [460 (-40C), 585 (85C)]",
    );
}

#[test]
fn test_route_based_collection_flag() {
    // Boolean flag for route-based data collection mode
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("route_enabled", i32_ty());
    ctx.declare_var_typed("collection_mode", i32_ty());
    // route_enabled=1 → route-based (1), else continuous (0)
    ctx.push_obligation(ProofObligation::assume("re", "route_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "collection_mode == if route_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_route", "collection_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration: route_enabled=1 → route-based collection",
    );
}
