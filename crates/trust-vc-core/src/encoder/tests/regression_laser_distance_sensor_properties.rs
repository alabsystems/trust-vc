// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_measurement_range_bounded() {
    // Laser distance measurement range in mm: value=500, min=10, max=150000
    let mut ctx = VerificationContext::new();
    for v in &["measurement_mm", "min_range_mm", "max_range_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "measurement_mm == 500"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_range_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_range_mm == 150000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if measurement_mm >= min_range_mm && measurement_mm <= max_range_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser: 500mm in [10, 150000]");
}

#[test]
fn test_resolution_bounded() {
    // Sensor resolution in micrometers: value=100, min=1, max=10000
    let mut ctx = VerificationContext::new();
    for v in &["resolution_um", "min_res_um", "max_res_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "resolution_um == 100"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_res_um == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_res_um == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if resolution_um >= min_res_um && resolution_um <= max_res_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser resolution: 100um in [1, 10000]");
}

#[test]
fn test_measurement_principle_disjunction() {
    // Measurement principle: 1=triangulation, 2=time-of-flight, 3=phase-shift
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("principle", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "principle == 2")); // time-of-flight
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if principle == 1 || principle == 2 || principle == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser principle: 2 (ToF) is valid");
}

#[test]
fn test_laser_class_disjunction() {
    // Laser class: 1=class1, 2=class1M, 3=class2, 4=class3R
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_class", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "laser_class == 1")); // class 1 (eye-safe)
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if laser_class == 1 || laser_class == 2 || laser_class == 3 || laser_class == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser class: 1 (class1) is valid");
}

#[test]
fn test_wavelength_bounded() {
    // Laser wavelength in nm: value=650, min=405, max=1550
    let mut ctx = VerificationContext::new();
    for v in &["wavelength_nm", "min_wl_nm", "max_wl_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "wavelength_nm == 650"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_wl_nm == 405"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_wl_nm == 1550"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if wavelength_nm >= min_wl_nm && wavelength_nm <= max_wl_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength: 650nm in [405, 1550]");
}

#[test]
fn test_linearity_bounded() {
    // Linearity as percentage x100: value=10 (0.10%), min=1, max=100
    let mut ctx = VerificationContext::new();
    for v in &["linearity_x100", "min_lin", "max_lin"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "linearity_x100 == 10"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_lin == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_lin == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if linearity_x100 >= min_lin && linearity_x100 <= max_lin { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser linearity: 10 (0.10%) in [1, 100]");
}

#[test]
fn test_sampling_rate_bounded() {
    // Measurement speed / sampling rate in Hz: value=1000, min=10, max=100000
    let mut ctx = VerificationContext::new();
    for v in &["sampling_rate_hz", "min_rate_hz", "max_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "sampling_rate_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_rate_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_rate_hz == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sampling_rate_hz >= min_rate_hz && sampling_rate_hz <= max_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser sampling: 1000Hz in [10, 100000]");
}

#[test]
fn test_output_type_disjunction() {
    // Output type: 1=analog 4-20mA, 2=analog 0-10V, 3=RS422, 4=EtherCAT
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "output_type == 4")); // EtherCAT
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser output: 4 (EtherCAT) is valid");
}

#[test]
fn test_operating_temp_offset_bounded() {
    // Operating temperature with +500 offset: value=525 (25C), min=460 (-40C), max=570 (70C)
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "temp_offset == 525")); // 25C + 500
    ctx.push_obligation(ProofObligation::assume("lo", "min_temp_offset == 460")); // -40C + 500
    ctx.push_obligation(ProofObligation::assume("hi", "max_temp_offset == 570")); // 70C + 500
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser temp: 525 (25C) in [460 (-40C), 570 (70C)]");
}

#[test]
fn test_reflectorless_mode_flag() {
    // Reflectorless mode: boolean flag using i32 with if/else pattern
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reflectorless", i32_ty());
    ctx.declare_var_typed("max_range_mm", u32_ty());
    ctx.declare_var_typed("effective_range_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "reflectorless == 1"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_range_mm == 150000"));
    // Reflectorless mode reduces effective range (e.g., to 30000mm vs 150000mm with reflector)
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "effective_range_mm == if reflectorless == 1 { 30000 } else { 150000 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_30000",
        "effective_range_mm == 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "reduced",
        "effective_range_mm < max_range_mm",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser reflectorless: range 30000 < 150000mm");
}
