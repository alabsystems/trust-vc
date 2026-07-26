// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: X-ray tube power bounded (1-4000 W).
#[test]
fn test_wd_xrf_tube_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 1 && power <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 1 && power <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "X-ray tube power must be between 1 and 4000 W");
}

/// Test 2: Number of analyzing crystals bounded (1-10).
#[test]
fn test_wd_xrf_crystal_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crystals", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "crystals_range",
        "crystals >= 1 && crystals <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "crystals_bounded",
        "crystals >= 1 && crystals <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Number of analyzing crystals must be between 1 and 10",
    );
}

/// Test 3: Goniometer angle range bounded (1-150 degrees 2-theta).
#[test]
fn test_wd_xrf_goniometer_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "angle >= 1 && angle <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_bounded",
        "angle >= 1 && angle <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Goniometer angle must be between 1 and 150 degrees 2-theta",
    );
}

/// Test 4: Angular resolution x1000 bounded (1-1000 representing 0.001-1.000 degrees).
#[test]
fn test_wd_xrf_angular_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_x1000 >= 1 && resolution_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_bounded",
        "resolution_x1000 >= 1 && resolution_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Angular resolution x1000 must be between 1 and 1000",
    );
}

/// Test 5: Detection limit x100 bounded (1-5000 representing 0.01-50.00 ppm).
#[test]
fn test_wd_xrf_detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_limit_range",
        "det_limit_x100 >= 1 && det_limit_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_limit_bounded",
        "det_limit_x100 >= 1 && det_limit_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Detection limit x100 must be between 1 and 5000 ppm",
    );
}

/// Test 6: Number of fixed channels bounded (1-40).
#[test]
fn test_wd_xrf_fixed_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "channels_range",
        "channels >= 1 && channels <= 40",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "channels_bounded",
        "channels >= 1 && channels <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Number of fixed channels must be between 1 and 40");
}

/// Test 7: Crystal type 3-way disjunction (1=LiF, 2=PET, 3=Ge).
#[test]
fn test_wd_xrf_crystal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crystal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "crystal_type_valid",
        "crystal_type == 1 || crystal_type == 2 || crystal_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "crystal_type_in_range",
        "crystal_type >= 1 && crystal_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Crystal type must be one of LiF(1), PET(2), or Ge(3)",
    );
}

/// Test 8: Detector type 3-way disjunction (1=scintillation, 2=flow-proportional, 3=sealed-proportional).
#[test]
fn test_wd_xrf_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_type_valid",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_type_in_range",
        "detector_type >= 1 && detector_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Detector type must be one of scintillation(1), flow-proportional(2), or sealed-proportional(3)");
}

/// Test 9: Sample preparation 3-way disjunction (1=pressed-pellet, 2=fused-bead, 3=liquid-cup).
#[test]
fn test_wd_xrf_sample_preparation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_prep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sample_prep_valid",
        "sample_prep == 1 || sample_prep == 2 || sample_prep == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sample_prep_in_range",
        "sample_prep >= 1 && sample_prep <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Sample preparation must be one of pressed-pellet(1), fused-bead(2), or liquid-cup(3)",
    );
}

/// Test 10: Automatic crystal changer boolean flag (== 0 || == 1).
#[test]
fn test_wd_xrf_auto_crystal_changer_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_changer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_changer_bool",
        "auto_changer == 0 || auto_changer == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_changer_bounded",
        "auto_changer >= 0 && auto_changer <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Automatic crystal changer flag must be boolean (0 or 1)",
    );
}
