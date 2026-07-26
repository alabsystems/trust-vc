// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_deg_x10", "max_range_deg_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Measurement range in degrees (×10 for 0.1°, offset +900 for ±90°)
    // -90° → 0, 0° → 900, +90° → 1800
    ctx.push_obligation(ProofObligation::assume("rx", "range_deg_x10 == 900")); // 0°
    ctx.push_obligation(ProofObligation::assume("mr", "max_range_deg_x10 == 1800")); // +90°
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_deg_x10 <= max_range_deg_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: 0° ≤ 90° max → OK");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_x1000", "min_resolution_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Resolution in degrees (×1000 for 0.001°)
    ctx.push_obligation(ProofObligation::assume("rx", "resolution_x1000 == 1")); // 0.001°
    ctx.push_obligation(ProofObligation::assume("mr", "min_resolution_x1000 == 1")); // 0.001°
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_x1000 >= min_resolution_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: 0.001° resolution ≥ 0.001° min → OK");
}

#[test]
fn sensor_technology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tech", u32_ty());
    ctx.declare_var_typed("valid_tech", i32_ty());
    // Technologies: 1=MEMS, 2=servo (force-balance), 3=electrolytic, 4=optical, 5=pendulum
    ctx.push_obligation(ProofObligation::assume("t", "tech == 2")); // servo
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_tech == if tech == 1 || tech == 2 || tech == 3 || tech == 4 || tech == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_tech == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Inclinometer: servo force-balance is valid technology",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x1000", "max_accuracy_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy in degrees (×1000 for 0.001°)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x1000 == 5")); // ±0.005°
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x1000 == 100")); // ±0.100°
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x1000 <= max_accuracy_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: ±0.005° accuracy ≤ ±0.100° max → OK");
}

#[test]
fn axes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_axes", u32_ty());
    ctx.declare_var_typed("valid_axes", i32_ty());
    // Number of measurement axes
    ctx.push_obligation(ProofObligation::assume("na", "num_axes == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_axes == if num_axes == 1 || num_axes == 2 || num_axes == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_axes == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: 2-axis is valid configuration");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz", "max_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Measurement bandwidth in Hz
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz && bw_hz <= max_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: 10 Hz bandwidth in [1, 1000] → OK");
}

#[test]
fn cross_axis_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["cross_x100", "max_cross_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cross_ok", i32_ty());
    // Cross-axis sensitivity as % (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("cx", "cross_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume("mc", "max_cross_x100 == 200")); // 2.00%
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cross_ok == if cross_x100 <= max_cross_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cross_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: 0.50% cross-axis ≤ 2.00% max → OK");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature (offset +500): -40°C to 85°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 585")); // 85°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: 20°C in [-40, 85] → OK");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output interfaces: 1=analog (4-20mA), 2=RS-485, 3=CAN, 4=SPI, 5=I2C
    ctx.push_obligation(ProofObligation::assume("o", "output == 2")); // RS-485
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 || output == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Inclinometer: RS-485 is valid output type");
}

#[test]
fn repeatability() {
    let mut ctx = VerificationContext::new();
    for v in &["repeat_x1000", "max_repeat_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rep_ok", i32_ty());
    // Repeatability in degrees (×1000 for 0.001°)
    ctx.push_obligation(ProofObligation::assume("rx", "repeat_x1000 == 2")); // 0.002°
    ctx.push_obligation(ProofObligation::assume("mr", "max_repeat_x1000 == 10")); // 0.010°
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rep_ok == if repeat_x1000 <= max_repeat_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Inclinometer: 0.002° repeatability ≤ 0.010° max → OK",
    );
}
