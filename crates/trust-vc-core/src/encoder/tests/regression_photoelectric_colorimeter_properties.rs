// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_wavelength_range_min_bounded() {
    // Minimum wavelength must be between 340nm and 400nm (UV-visible boundary)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_min_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_min_nm == 380"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wavelength_min_nm >= 340 && wavelength_min_nm <= 400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: min wavelength 380nm in [340, 400]");
}

#[test]
fn test_wavelength_range_max_bounded() {
    // Maximum wavelength must be between 800nm and 1100nm (visible-NIR boundary)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_max_nm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_max_nm == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wavelength_max_nm >= 800 && wavelength_max_nm <= 1100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: max wavelength 1000nm in [800, 1100]");
}

#[test]
fn test_absorbance_range_scaled() {
    // Absorbance scaled x1000: 0-3000 means 0.000-3.000 AU
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("absorbance_x1000", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "absorbance_x1000 == 1500")); // 1.500 AU
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if absorbance_x1000 <= 3000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    ctx.push_obligation(ProofObligation::assert("positive", "absorbance_x1000 > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "colorimeter: absorbance 1.500 AU within [0, 3.000]",
    );
}

#[test]
fn test_photometric_accuracy_scaled() {
    // Photometric accuracy scaled x10000: e.g., 5 = 0.0005 AU, must be <= 50 (0.005 AU)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10000", u32_ty());
    ctx.declare_var_typed("max_accuracy_x10000", u32_ty());
    ctx.declare_var_typed("meets_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x10000 == 5")); // 0.0005 AU
    ctx.push_obligation(ProofObligation::assume(
        "max_acc",
        "max_accuracy_x10000 == 50",
    )); // 0.005 AU
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "meets_spec == if accuracy_x10000 <= max_accuracy_x10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: accuracy 0.0005 AU <= 0.005 AU spec");
}

#[test]
fn test_bandwidth_scaled() {
    // Spectral bandwidth scaled x10: e.g., 20 = 2.0nm, must be in [5, 100] (0.5-10.0nm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bw", "bandwidth_x10 == 20")); // 2.0 nm
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if bandwidth_x10 >= 5 && bandwidth_x10 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: bandwidth 2.0nm in [0.5, 10.0]nm");
}

#[test]
fn test_light_source_type_valid() {
    // Light source: 1=tungsten, 2=deuterium, 3=LED
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_source", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ls", "light_source == 1")); // tungsten
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if light_source == 1 || light_source == 2 || light_source == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: tungsten is valid light source");
}

#[test]
fn test_detector_type_valid() {
    // Detector type: 1=photodiode, 2=photomultiplier, 3=CCD
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "detector_type == 2")); // photomultiplier
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector_type == 1 || detector_type == 2 || detector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "colorimeter: photomultiplier is valid detector type",
    );
}

#[test]
fn test_sample_cell_path_bounded() {
    // Sample cell optical path length in mm, must be in [1, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_path_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "cell_path_mm == 10")); // standard 10mm cuvette
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if cell_path_mm >= 1 && cell_path_mm <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: 10mm cell path in [1, 100]mm");
}

#[test]
fn test_measurement_channels_bounded() {
    // Number of measurement channels must be in [1, 8]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if channels >= 1 && channels <= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: 4 channels in [1, 8]");
}

#[test]
fn test_auto_zero_flag() {
    // Auto-zero capability: boolean flag encoded as i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_zero_enabled", i32_ty());
    ctx.declare_var_typed("zeroed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("az", "auto_zero_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "z_def",
        "zeroed == if auto_zero_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "zeroed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "colorimeter: auto-zero enabled → zeroed");
}
