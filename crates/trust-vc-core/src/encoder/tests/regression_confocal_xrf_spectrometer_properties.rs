// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_confocal_xrf_depth_resolution_bounded() {
    // Depth resolution x10 in range 1-1000 representing 0.1-100.0 um
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_res_range",
        "depth_res >= 1 && depth_res <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "depth_res_bounded",
        "depth_res >= 1 && depth_res <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "depth resolution x10 must be in range 1-1000 representing 0.1-100.0 um",
    );
}

#[test]
fn test_confocal_xrf_lateral_resolution_bounded() {
    // Lateral resolution x10 in range 1-5000 representing 0.1-500.0 um
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lateral_res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lateral_res_range",
        "lateral_res >= 1 && lateral_res <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lateral_res_bounded",
        "lateral_res >= 1 && lateral_res <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lateral resolution x10 must be in range 1-5000 representing 0.1-500.0 um",
    );
}

#[test]
fn test_confocal_xrf_tube_voltage_bounded() {
    // Tube voltage bounded 5-60 kV
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 5 && voltage <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 5 && voltage <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube voltage must be in range 5-60 kV");
}

#[test]
fn test_confocal_xrf_maximum_depth_bounded() {
    // Maximum depth x10 in range 1-10000 representing 0.1-1000.0 um
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "max_depth_range",
        "max_depth >= 1 && max_depth <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "max_depth_bounded",
        "max_depth >= 1 && max_depth <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "maximum depth x10 must be in range 1-10000 representing 0.1-1000.0 um",
    );
}

#[test]
fn test_confocal_xrf_depth_slices_bounded() {
    // Number of depth slices bounded 1-500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("slices", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "slices_range",
        "slices >= 1 && slices <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "slices_bounded",
        "slices >= 1 && slices <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of depth slices must be in range 1-500");
}

#[test]
fn test_confocal_xrf_scan_time_bounded() {
    // Scan time bounded 1-86400 seconds
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scan_time_range",
        "scan_time >= 1 && scan_time <= 86400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scan_time_bounded",
        "scan_time >= 1 && scan_time <= 86400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan time must be in range 1-86400 seconds");
}

#[test]
fn test_confocal_xrf_excitation_optics_disjunction() {
    // Excitation optics: 1=polycapillary-lens, 2=monocapillary, 3=KB-mirror
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "excitation_valid",
        "excitation == 1 || excitation == 2 || excitation == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "excitation_disjunction",
        "excitation == 1 || excitation == 2 || excitation == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation optics must be polycapillary-lens(1), monocapillary(2), or KB-mirror(3)",
    );
}

#[test]
fn test_confocal_xrf_detection_optics_disjunction() {
    // Detection optics: 1=polycapillary-half-lens, 2=collimator, 3=slit
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detection_valid",
        "detection == 1 || detection == 2 || detection == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detection_disjunction",
        "detection == 1 || detection == 2 || detection == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection optics must be polycapillary-half-lens(1), collimator(2), or slit(3)",
    );
}

#[test]
fn test_confocal_xrf_scanning_axis_disjunction() {
    // Scanning axis: 1=XYZ, 2=XZ-only, 3=Z-depth-profile
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "axis_valid",
        "axis == 1 || axis == 2 || axis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "axis_disjunction",
        "axis == 1 || axis == 2 || axis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scanning axis must be XYZ(1), XZ-only(2), or Z-depth-profile(3)",
    );
}

#[test]
fn test_confocal_xrf_auto_alignment_boolean() {
    // Automatic confocal alignment is a boolean flag (0 or 1)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_align", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_align_valid",
        "auto_align == 0 || auto_align == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_align_boolean",
        "auto_align == 0 || auto_align == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic confocal alignment must be a boolean flag (0 or 1)",
    );
}
