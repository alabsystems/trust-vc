// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_fluorescence_microscope_excitation_wavelength_bounded() {
    // Excitation wavelength must be in [340, 700] nm (UV to far-red)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ex_val", "excitation_nm == 488"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "excitation_nm >= 340 && excitation_nm <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "excitation 488nm in [340, 700]");
}

#[test]
fn test_fluorescence_microscope_emission_wavelength_bounded() {
    // Emission wavelength must be in [400, 800] nm (visible to near-IR)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emission_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("em_val", "emission_nm == 525"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "emission_nm >= 400 && emission_nm <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emission 525nm in [400, 800]");
}

#[test]
fn test_fluorescence_microscope_magnification_bounded() {
    // Objective magnification must be in [4, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magnification", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mag_val", "magnification == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "magnification >= 4 && magnification <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnification 40x in [4, 100]");
}

#[test]
fn test_fluorescence_microscope_numerical_aperture_scaled() {
    // Numerical aperture scaled x100: 140 = 1.40 NA, valid range [10, 170]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("na_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("na_val", "na_x100 == 140"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "na_x100 >= 10 && na_x100 <= 170",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NA 1.40 (x100=140) in [10, 170]");
}

#[test]
fn test_fluorescence_microscope_exposure_time_bounded() {
    // Exposure time in ms, valid range [1, 30000] (1ms to 30s)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exposure_ms", u32_ty());
    ctx.push_obligation(ProofObligation::assume("exp_val", "exposure_ms == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "exposure_ms >= 1 && exposure_ms <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exposure 500ms in [1, 30000]");
}

#[test]
fn test_fluorescence_microscope_light_source_valid() {
    // Light source: 1=mercury arc, 2=LED, 3=laser
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_source", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ls_val", "light_source == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "light_source == 1 || light_source == 2 || light_source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "light source LED (2) in {1, 2, 3}");
}

#[test]
fn test_fluorescence_microscope_filter_type_valid() {
    // Filter type: 1=bandpass, 2=longpass, 3=multiband
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ft_val", "filter_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_filter",
        "filter_type == 1 || filter_type == 2 || filter_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter bandpass (1) in {1, 2, 3}");
}

#[test]
fn test_fluorescence_microscope_camera_resolution_bounded() {
    // Camera resolution in megapixels, valid range [1, 20]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_mp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution_mp == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "resolution_mp >= 1 && resolution_mp <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "camera 5MP in [1, 20]");
}

#[test]
fn test_fluorescence_microscope_z_stack_step_size_scaled() {
    // Z-stack step size scaled x1000: 100 = 0.100 um, valid range [10, 10000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("step_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("step_val", "step_x1000 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "step_x1000 >= 10 && step_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "z-step 0.100um (x1000=100) in [10, 10000]");
}

#[test]
fn test_fluorescence_microscope_motorized_stage_flag() {
    // Motorized stage: boolean flag encoded as i32 (0 or 1)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_motor", i32_ty());
    ctx.declare_var_typed("motorized", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "has_motor == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mot_def",
        "motorized == if has_motor == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_motorized", "motorized == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motorized stage flag: enabled");
}
