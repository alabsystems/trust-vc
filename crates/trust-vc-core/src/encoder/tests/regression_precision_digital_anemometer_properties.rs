// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn velocity_range_scaled() {
    // Velocity ×100: 0.01 m/s resolution → 0 to 10000 (0.00–100.00 m/s)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("v", "velocity_x100 == 2550")); // 25.50 m/s
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if velocity_x100 <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "anemometer velocity 25.50 m/s within 0–100.00 range",
    );
}

#[test]
fn accuracy_scaled() {
    // Accuracy ×10: 0.1% resolution → e.g. 15 means 1.5% of reading
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.declare_var_typed("max_accuracy_x10", u32_ty());
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x10 == 15")); // 1.5%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x10 == 50")); // 5.0% max
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer accuracy 1.5% <= 5.0% max");
}

#[test]
fn resolution_scaled() {
    // Resolution ×1000: 0.001 m/s precision → e.g. 1 means 0.001 m/s
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x1000", u32_ty());
    ctx.declare_var_typed("max_resolution_x1000", u32_ty());
    ctx.declare_var_typed("fine_enough", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "resolution_x1000 == 1")); // 0.001 m/s
    ctx.push_obligation(ProofObligation::assume("mr", "max_resolution_x1000 == 10")); // 0.010 m/s
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "fine_enough == if resolution_x1000 <= max_resolution_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "fine_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer resolution 0.001 <= 0.010 m/s");
}

#[test]
fn temperature_range_min_offset() {
    // Temperature offset +500: actual -40C stored as 460, actual -20C stored as 480
    // Valid min range: 400 to 500 (i.e., -100C to 0C actual)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_min_offset", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tm", "temp_min_offset == 460")); // -40C actual
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if temp_min_offset >= 400 && temp_min_offset <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "anemometer temp min -40C (offset 460) in [400,500]",
    );
}

#[test]
fn temperature_range_max_offset() {
    // Temperature offset +500: actual 80C stored as 580, actual 120C stored as 620
    // Valid max range: 500 to 700 (i.e., 0C to 200C actual)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_max_offset", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tm", "temp_max_offset == 580")); // 80C actual
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if temp_max_offset >= 500 && temp_max_offset <= 700 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer temp max 80C (offset 580) in [500,700]");
}

#[test]
fn sensor_type_disjunction() {
    // 1=hot wire, 2=vane, 3=pitot tube
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 2")); // vane
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer sensor type vane (2) is valid");
}

#[test]
fn output_type_disjunction() {
    // 1=analog, 2=digital, 3=wireless
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 3")); // wireless
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if output_type == 1 || output_type == 2 || output_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer output type wireless (3) is valid");
}

#[test]
fn sample_rate_bounded() {
    // Sample rate in Hz: 1 to 10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate_hz", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_hz == 1000")); // 1 kHz
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sample_rate_hz >= 1 && sample_rate_hz <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer sample rate 1000 Hz in [1,10000]");
}

#[test]
fn probe_length_bounded() {
    // Probe length in mm: 100 to 2000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_length_mm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pl", "probe_length_mm == 500")); // 500mm
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if probe_length_mm >= 100 && probe_length_mm <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer probe length 500mm in [100,2000]");
}

#[test]
fn data_logging_flag() {
    // Boolean flag: 1=enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_logging", i32_ty());
    ctx.declare_var_typed("logging_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dl", "data_logging == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "la_def",
        "logging_active == if data_logging == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "logging_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anemometer data logging enabled");
}
