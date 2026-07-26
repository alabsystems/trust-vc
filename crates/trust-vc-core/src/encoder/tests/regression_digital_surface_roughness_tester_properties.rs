// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ra_range_scaled() {
    // Ra (arithmetic average roughness) scaled ×1000: 1600 = 1.600 μm
    // Typical Ra range: 0 to 12500 (0.000 to 12.500 μm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ra_x1000", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ra", "ra_x1000 == 1600"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if ra_x1000 >= 1 && ra_x1000 <= 12500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ra: 1600 (1.600 um) in [1, 12500]");
}

#[test]
fn test_resolution_scaled() {
    // Resolution scaled ×10000: 1 = 0.0001 μm
    // Valid range: 1 to 1000 (0.0001 to 0.1000 μm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10000", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res", "resolution_x10000 == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if resolution_x10000 >= 1 && resolution_x10000 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution: 5 (0.0005 um) in [1, 1000]");
}

#[test]
fn test_traverse_length_bounded() {
    // Traverse length in mm, bounded 1 to 50
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("traverse_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tl", "traverse_mm == 17"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if traverse_mm >= 1 && traverse_mm <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "traverse length: 17mm in [1, 50]");
}

#[test]
fn test_cutoff_wavelength_scaled() {
    // Cutoff wavelength scaled ×100: 80 = 0.80 mm
    // Standard cutoffs: 25 (0.25mm), 80 (0.80mm), 250 (2.50mm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cutoff_x100", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("co", "cutoff_x100 == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if cutoff_x100 >= 8 && cutoff_x100 <= 800 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cutoff: 80 (0.80mm) in [8, 800]");
}

#[test]
fn test_stylus_radius_bounded() {
    // Stylus tip radius in μm, bounded 2 to 10
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stylus_radius_um", u32_ty());
    ctx.declare_var_typed("in_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "stylus_radius_um == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_spec == if stylus_radius_um >= 2 && stylus_radius_um <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stylus radius: 5 um in [2, 10]");
}

#[test]
fn test_parameter_type_disjunction() {
    // Parameter type: 1=Ra, 2=Rz, 3=Rq
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("param_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "param_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if param_type == 1 || param_type == 2 || param_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "parameter type: 2 (Rz) is valid");
}

#[test]
fn test_drive_type_disjunction() {
    // Drive type: 1=motorized, 2=manual, 3=external
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "drive_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if drive_type == 1 || drive_type == 2 || drive_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type: 1 (motorized) is valid");
}

#[test]
fn test_filter_type_disjunction() {
    // Filter type: 1=Gaussian, 2=2RC, 3=PC75
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ft", "filter_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if filter_type == 1 || filter_type == 2 || filter_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter type: 3 (PC75) is valid");
}

#[test]
fn test_measurement_speed_scaled() {
    // Measurement speed scaled ×10: 5 = 0.5 mm/s
    // Valid range: 1 to 20 (0.1 to 2.0 mm/s)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.declare_var_typed("traverse_mm", u32_ty());
    ctx.declare_var_typed("time_x10_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sp", "speed_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("tl", "traverse_mm == 17"));
    // time (×10 s) = traverse_mm * 10 / speed_x10 → 17 * 10 / 5 = 34
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "time_x10_s == traverse_mm * 10 / speed_x10",
    ));
    ctx.push_obligation(ProofObligation::assert("is_34", "time_x10_s == 34"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "speed 0.5mm/s over 17mm: 34 (3.4s)");
}

#[test]
fn test_bluetooth_output_flag() {
    // Bluetooth output: i32 flag, 1=enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bt_supported", i32_ty());
    ctx.declare_var_typed("bt_enabled", i32_ty());
    ctx.declare_var_typed("bt_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sup", "bt_supported == 1"));
    ctx.push_obligation(ProofObligation::assume("en", "bt_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ba_def",
        "bt_active == if bt_supported == 1 { if bt_enabled == 1 { 1 } else { 0 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("active", "bt_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bluetooth: supported=1, enabled=1 -> active");
}
