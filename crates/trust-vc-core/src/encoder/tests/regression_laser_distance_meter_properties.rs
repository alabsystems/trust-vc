// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_mm", "range_min", "range_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Max range in mm: value 30000 (30m), valid range 100 (0.1m) to 250000 (250m)
    ctx.push_obligation(ProofObligation::assume("range_val", "range_mm == 30000"));
    ctx.push_obligation(ProofObligation::assume("range_min_val", "range_min == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "range_max_val",
        "range_max == 250000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "range_mm >= range_min && range_mm <= range_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max range 30000mm (30m) in valid range [100,250000] (0.1-250m)",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accuracy_ok", i32_ty());
    // Accuracy in mm x10: value 15 means 1.5mm, max 30 means 3.0mm
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_val",
        "accuracy_x10 == 15",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "max_accuracy_val",
        "max_accuracy == 30",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_ok_def",
        "accuracy_ok == if accuracy_x10 <= max_accuracy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("within_spec", "accuracy_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 15 (1.5mm) within max 30 (3.0mm)");
}

#[test]
fn measurement_principle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("principle", u32_ty());
    ctx.declare_var_typed("valid_principle", i32_ty());
    // 1=time-of-flight, 2=phase-shift, 3=triangulation
    ctx.push_obligation(ProofObligation::assume("principle_val", "principle == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_principle_def",
        "valid_principle == if principle == 1 || principle == 2 || principle == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_principle == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement principle 1 (time-of-flight) is valid");
}

#[test]
fn laser_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // 1=Class 1, 2=Class 1M, 3=Class 2, 4=Class 3R
    ctx.push_obligation(ProofObligation::assume("class_val", "class == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_class_def",
        "valid_class == if class == 1 || class == 2 || class == 3 || class == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser class 1 (Class 1) is valid");
}

#[test]
fn wavelength() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.declare_var_typed("valid_wl", i32_ty());
    // Laser wavelength in nm: value 650 (red), validated as 3-way: 635/650/905
    ctx.push_obligation(ProofObligation::assume("wl_val", "wavelength_nm == 650"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_wl_def",
        "valid_wl == if wavelength_nm == 635 || wavelength_nm == 650 || wavelength_nm == 905 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_wl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength 650nm (red) is valid");
}

#[test]
fn measurement_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate", "rate_min", "rate_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Measurements per second: value 50, range 1-1000
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate == 50"));
    ctx.push_obligation(ProofObligation::assume("rate_min_val", "rate_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rate_max_val", "rate_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "rate >= rate_min && rate <= rate_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement rate 50/s in range [1,1000]");
}

#[test]
fn beam_divergence() {
    let mut ctx = VerificationContext::new();
    for v in &["divergence_x10", "div_min", "div_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Beam divergence in mrad x10: value 3 means 0.3 mrad, range 1 (0.1) to 50 (5.0)
    ctx.push_obligation(ProofObligation::assume("div_val", "divergence_x10 == 3"));
    ctx.push_obligation(ProofObligation::assume("div_min_val", "div_min == 1"));
    ctx.push_obligation(ProofObligation::assume("div_max_val", "div_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "divergence_x10 >= div_min && divergence_x10 <= div_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam divergence 3 (0.3 mrad) in range [1,50] (0.1-5.0 mrad)",
    );
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_x10", "max_resolution"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // Display resolution in mm x10: value 1 means 0.1mm, max 10 means 1.0mm
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution_x10 == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "max_res_val",
        "max_resolution == 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "resolution_ok_def",
        "resolution_ok == if resolution_x10 <= max_resolution { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("within_spec", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 1 (0.1mm) within max 10 (1.0mm)");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: value 520 means 20C, min 490 (-10C), max 550 (50C)
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume("temp_min_val", "temp_min == 490"));
    ctx.push_obligation(ProofObligation::assume("temp_max_val", "temp_max == 550"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 520 (20C) in range [490,550] (-10C to 50C)",
    );
}

#[test]
fn output_interface() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interface", u32_ty());
    ctx.declare_var_typed("valid_iface", i32_ty());
    // 1=analog (4-20mA), 2=RS232, 3=RS485, 4=Ethernet
    ctx.push_obligation(ProofObligation::assume("iface_val", "interface == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_iface_def",
        "valid_iface == if interface == 1 || interface == 2 || interface == 3 || interface == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_iface == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output interface 1 (analog 4-20mA) is valid");
}
