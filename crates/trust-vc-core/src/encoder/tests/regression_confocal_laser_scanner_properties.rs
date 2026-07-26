// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_confocal_scanner_laser_wavelength_bounded() {
    // Laser wavelength must be within common confocal range: 405nm to 785nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_range",
        "wavelength_nm >= 405 && wavelength_nm <= 785",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "wavelength_nm >= 405"));
    ctx.push_obligation(ProofObligation::assert("upper", "wavelength_nm <= 785"));
    ctx.push_obligation(ProofObligation::assert("positive", "wavelength_nm > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength bounded [405, 785] nm");
}

#[test]
fn test_confocal_scanner_scanning_speed_bounded() {
    // Scanning speed in frames per second: 1 to 30 fps
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_fps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fps_range",
        "speed_fps >= 1 && speed_fps <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "speed_fps >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_thirty", "speed_fps <= 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scanning speed bounded [1, 30] fps");
}

#[test]
fn test_confocal_scanner_lateral_resolution_scaled() {
    // Lateral resolution scaled x1000: 200 means 200nm (0.200um)
    // Typical confocal lateral resolution: 150nm to 300nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lateral_res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lr_range",
        "lateral_res_x1000 >= 150 && lateral_res_x1000 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "above_min",
        "lateral_res_x1000 >= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "below_max",
        "lateral_res_x1000 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "lateral_res_x1000 > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lateral resolution bounded [150, 300] x1000 nm");
}

#[test]
fn test_confocal_scanner_axial_resolution_scaled() {
    // Axial resolution scaled x1000: 500 means 500nm (0.500um)
    // Typical confocal axial resolution: 400nm to 1500nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axial_res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ar_range",
        "axial_res_x1000 >= 400 && axial_res_x1000 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "above_min",
        "axial_res_x1000 >= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "below_max",
        "axial_res_x1000 <= 1500",
    ));
    // Axial resolution is always worse (larger) than lateral
    ctx.declare_var_typed("lateral_res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lr_bound",
        "lateral_res_x1000 >= 150 && lateral_res_x1000 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "axial_ge_lateral",
        "axial_res_x1000 >= lateral_res_x1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "axial resolution bounded [400, 1500] x1000 nm and >= lateral",
    );
}

#[test]
fn test_confocal_scanner_pinhole_diameter_bounded() {
    // Pinhole diameter in micrometers: 25 to 600
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pinhole_um", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ph_range",
        "pinhole_um >= 25 && pinhole_um <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert("above_min", "pinhole_um >= 25"));
    ctx.push_obligation(ProofObligation::assert("below_max", "pinhole_um <= 600"));
    ctx.push_obligation(ProofObligation::assert("positive", "pinhole_um > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pinhole diameter bounded [25, 600] um");
}

#[test]
fn test_confocal_scanner_scanning_mode_disjunction() {
    // Scanning mode: 1=raster, 2=resonant, 3=spinning disk
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "scan_mode == 1 || scan_mode == 2 || scan_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "scan_mode >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_3", "scan_mode <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scanning mode is raster(1), resonant(2), or spinning disk(3)",
    );
}

#[test]
fn test_confocal_scanner_detector_type_disjunction() {
    // Detector type: 1=PMT, 2=hybrid, 3=GaAsP
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_detector",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "detector >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_3", "detector <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type is PMT(1), hybrid(2), or GaAsP(3)");
}

#[test]
fn test_confocal_scanner_image_size_bounded() {
    // Image size in pixels per axis: 256 to 4096
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("image_px", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "img_range",
        "image_px >= 256 && image_px <= 4096",
    ));
    ctx.push_obligation(ProofObligation::assert("above_min", "image_px >= 256"));
    ctx.push_obligation(ProofObligation::assert("below_max", "image_px <= 4096"));
    ctx.push_obligation(ProofObligation::assert("positive", "image_px > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "image size bounded [256, 4096] pixels");
}

#[test]
fn test_confocal_scanner_spectral_channels_bounded() {
    // Spectral channels: 1 to 32
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ch_range",
        "channels >= 1 && channels <= 32",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "channels >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_32", "channels <= 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral channels bounded [1, 32]");
}

#[test]
fn test_confocal_scanner_motorized_pinhole_flag() {
    // Motorized pinhole: boolean flag encoded as i32 (0 or 1)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motorized", i32_ty());
    ctx.declare_var_typed("pinhole_adjustable", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "motorized == 0 || motorized == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "adj_def",
        "pinhole_adjustable == if motorized == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "consistent",
        "pinhole_adjustable == motorized",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motorized pinhole flag: adjustable iff motorized == 1",
    );
}
