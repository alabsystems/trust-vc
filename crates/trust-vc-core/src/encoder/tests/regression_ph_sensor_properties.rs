// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["ph_x100", "min_ph_x100", "max_ph_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ph_ok", i32_ty());
    // pH value (×100 for 0.01 precision, offset by +200 to avoid negative)
    // pH 0.00 → 200, pH 7.00 → 900, pH 14.00 → 1600
    ctx.push_obligation(ProofObligation::assume("px", "ph_x100 == 900")); // pH 7.00
    ctx.push_obligation(ProofObligation::assume("mn", "min_ph_x100 == 200")); // pH 0.00
    ctx.push_obligation(ProofObligation::assume("mx", "max_ph_x100 == 1600")); // pH 14.00
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ph_ok == if ph_x100 >= min_ph_x100 && ph_x100 <= max_ph_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ph_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 7.00 in [0.00, 14.00] → OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x1000", "max_accuracy_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy in pH units (×1000 for 0.001 precision)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x1000 == 10")); // ±0.010 pH
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x1000 == 50")); // ±0.050 pH
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x1000 <= max_accuracy_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: ±0.010 accuracy ≤ ±0.050 max → OK");
}

#[test]
fn electrode_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elec_type", u32_ty());
    ctx.declare_var_typed("valid_elec", i32_ty());
    // Electrode types: 1=glass combination, 2=ISFET, 3=antimony, 4=double junction, 5=flat tip
    ctx.push_obligation(ProofObligation::assume("et", "elec_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_elec == if elec_type == 1 || elec_type == 2 || elec_type == 3 || elec_type == 4 || elec_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_elec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: glass combination is valid electrode type");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_sec", "max_resp_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // T95 response time in seconds
    ctx.push_obligation(ProofObligation::assume("rs", "resp_sec == 15"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_sec == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_sec <= max_resp_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 15s T95 response ≤ 60s max → OK");
}

#[test]
fn reference_impedance() {
    let mut ctx = VerificationContext::new();
    for v in &["imp_kohm", "max_imp_kohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("imp_ok", i32_ty());
    // Reference junction impedance in kΩ
    ctx.push_obligation(ProofObligation::assume("ik", "imp_kohm == 5"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_imp_kohm == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "imp_ok == if imp_kohm <= max_imp_kohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "imp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 5 kΩ impedance ≤ 50 kΩ max → OK");
}

#[test]
fn calibration_buffers() {
    let mut ctx = VerificationContext::new();
    for v in &["buffers", "min_buffers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("buf_ok", i32_ty());
    // Number of calibration buffer points
    ctx.push_obligation(ProofObligation::assume("b", "buffers == 3"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_buffers == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "buf_ok == if buffers >= min_buffers { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "buf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 3 cal buffers ≥ 2 min → OK");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature (offset +500): 0°C to 100°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 500")); // 0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 600")); // 100°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 25°C in [0, 100] → OK");
}

#[test]
fn slope_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["slope_x10", "min_slope_x10", "max_slope_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slope_ok", i32_ty());
    // Electrode slope as % of Nernst (×10 for 0.1%)
    // Ideal = 100.0%, acceptable 85.0% - 105.0%
    ctx.push_obligation(ProofObligation::assume("sx", "slope_x10 == 980")); // 98.0%
    ctx.push_obligation(ProofObligation::assume("mn", "min_slope_x10 == 850")); // 85.0%
    ctx.push_obligation(ProofObligation::assume("mx", "max_slope_x10 == 1050")); // 105.0%
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "slope_ok == if slope_x10 >= min_slope_x10 && slope_x10 <= max_slope_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slope_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 98.0% Nernst slope in [85.0, 105.0] → OK");
}

#[test]
fn zero_point_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_mv", "max_offset_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("off_ok", i32_ty());
    // Zero-point (pH 7) offset in mV (absolute value)
    ctx.push_obligation(ProofObligation::assume("om", "offset_mv == 10"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset_mv == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "off_ok == if offset_mv <= max_offset_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "off_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 10mV zero offset ≤ 30mV max → OK");
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Process pressure in bar
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 6"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pH: 6 bar ≤ 16 bar max → OK");
}
