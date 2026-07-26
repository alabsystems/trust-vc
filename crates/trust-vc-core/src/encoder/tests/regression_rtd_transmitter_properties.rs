// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// RTD type selection: nominal resistance values for Pt100, Pt500, Pt1000, Ni2000.
/// 4-way non-sequential enumeration in ohms.
#[test]
fn test_rtd_type_nominal_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rtd_type", "nominal_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // rtd_type: 1=Pt100, 2=Pt500, 3=Pt1000, 4=Ni2000
    ctx.push_obligation(ProofObligation::assume("type_val", "rtd_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nominal_def",
        "nominal_ohms == if rtd_type == 1 { 100 } else { if rtd_type == 2 { 500 } else { if rtd_type == 3 { 1000 } else { 2000 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("pt100_ohms", "nominal_ohms == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD type Pt100 has nominal resistance 100 ohms");
}

/// Wire configuration: 2-wire, 3-wire, or 4-wire connection.
/// 3-way disjunction over valid wire codes.
#[test]
fn test_wire_configuration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wire_cfg", u32_ty());
    // 1=2-wire, 2=3-wire, 3=4-wire
    ctx.push_obligation(ProofObligation::assume("wire_val", "wire_cfg == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_wire",
        "wire_cfg == 1 || wire_cfg == 2 || wire_cfg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wire configuration 3-wire is valid (code 2)");
}

/// Temperature range low bound with +500 offset for unsigned representation.
/// -200C stored as 300, min -300C (200), max 0C (500).
#[test]
fn test_temp_range_low_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_low", "temp_low_min", "temp_low_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // offset +500: actual -200C stored as 300
    ctx.push_obligation(ProofObligation::assume("low_val", "temp_low == 300"));
    ctx.push_obligation(ProofObligation::assume("low_min", "temp_low_min == 200"));
    ctx.push_obligation(ProofObligation::assume("low_max", "temp_low_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "low_in_range",
        "temp_low >= temp_low_min && temp_low <= temp_low_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temp low -200C (offset 300) in range [-300C, 0C] (offset [200, 500])",
    );
}

/// Temperature range high bound with +500 offset for unsigned representation.
/// 650C stored as 1150, min 100C (600), max 850C (1350).
#[test]
fn test_temp_range_high_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_high", "temp_high_min", "temp_high_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // offset +500: actual 650C stored as 1150
    ctx.push_obligation(ProofObligation::assume("high_val", "temp_high == 1150"));
    ctx.push_obligation(ProofObligation::assume("high_min", "temp_high_min == 600"));
    ctx.push_obligation(ProofObligation::assume("high_max", "temp_high_max == 1350"));
    ctx.push_obligation(ProofObligation::assert(
        "high_in_range",
        "temp_high >= temp_high_min && temp_high <= temp_high_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temp high 650C (offset 1150) in range [100C, 850C] (offset [600, 1350])",
    );
}

/// Accuracy specification scaled by 100 to avoid fractional values.
/// 0.10C stored as 10, range [0.01C, 1.00C] stored as [1, 100].
#[test]
fn test_accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // accuracy x100: 0.10C = 10
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy == 10"));
    ctx.push_obligation(ProofObligation::assume("acc_min_val", "acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("acc_max_val", "acc_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "acc_in_range",
        "accuracy >= acc_min && accuracy <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy 0.10C (scaled 10) in [0.01C, 1.00C] (scaled [1, 100])",
    );
}

/// Output type: 3-way disjunction for 4-20mA, 0-10V, or HART protocol.
#[test]
fn test_output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    // 1=4-20mA, 2=0-10V, 3=HART
    ctx.push_obligation(ProofObligation::assume("out_val", "output_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_output",
        "output_type == 1 || output_type == 2 || output_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type HART is valid (code 3)");
}

/// Excitation current for RTD sensor drive in microamps.
/// Nominal 1mA (1000uA), range [100uA, 5000uA].
#[test]
fn test_excitation_current() {
    let mut ctx = VerificationContext::new();
    for v in &["excitation_ua", "exc_min", "exc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("exc_val", "excitation_ua == 1000"));
    ctx.push_obligation(ProofObligation::assume("exc_min_val", "exc_min == 100"));
    ctx.push_obligation(ProofObligation::assume("exc_max_val", "exc_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "exc_in_range",
        "excitation_ua >= exc_min && excitation_ua <= exc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation current 1mA (1000uA) in [100uA, 5000uA]",
    );
}

/// Response time for signal processing filter in milliseconds.
/// Nominal 500ms, range [50ms, 5000ms].
#[test]
fn test_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["response_ms", "resp_min", "resp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("resp_val", "response_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("resp_min_val", "resp_min == 50"));
    ctx.push_obligation(ProofObligation::assume("resp_max_val", "resp_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "resp_in_range",
        "response_ms >= resp_min && response_ms <= resp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 500ms in [50ms, 5000ms]");
}

/// Linearization curve selection: 4-way disjunction for standard RTD curves.
/// 1=Pt385, 2=Pt3916, 3=Pt3926, 4=Ni120.
#[test]
fn test_linearization_curve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lin_curve", u32_ty());
    ctx.push_obligation(ProofObligation::assume("curve_val", "lin_curve == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_curve",
        "lin_curve == 1 || lin_curve == 2 || lin_curve == 3 || lin_curve == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linearization curve Pt3916 is valid (code 2)");
}

/// Sensor burnout detection: boolean flag using i32 (1=enabled, 0=disabled).
/// When enabled, transmitter drives upscale/downscale on open circuit.
#[test]
fn test_sensor_burnout_detect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burnout_en", i32_ty());
    ctx.declare_var_typed("sensor_open", i32_ty());
    ctx.declare_var_typed("output_clamped", i32_ty());
    // burnout detection enabled
    ctx.push_obligation(ProofObligation::assume("burnout_val", "burnout_en == 1"));
    // sensor is open circuit
    ctx.push_obligation(ProofObligation::assume("sensor_val", "sensor_open == 1"));
    // output is clamped when burnout enabled AND sensor open
    ctx.push_obligation(ProofObligation::assume(
        "clamp_def",
        "output_clamped == if burnout_en == 1 && sensor_open == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "burnout_clamps",
        "output_clamped == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "burnout detect enabled + open sensor -> output clamped",
    );
}
