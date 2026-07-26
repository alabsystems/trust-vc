// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_nir_wavelength_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_min_val", "wl_min == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "wl_min_bounded",
        "wl_min >= 700 && wl_min <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength min 900 nm in [700, 1100]");
}

#[test]
fn test_nir_wavelength_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_max_val", "wl_max == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "wl_max_bounded",
        "wl_max >= 1500 && wl_max <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength max 2500 nm in [1500, 3000]");
}

#[test]
fn test_nir_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_x10_val", "res_x10 == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "res_x10_bounded",
        "res_x10 >= 1 && res_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 2.0 nm (x10=20) in [1, 100]");
}

#[test]
fn test_nir_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("detector_val", "detector == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type 1=InGaAs in {1=InGaAs, 2=PbS, 3=DTGS}",
    );
}

#[test]
fn test_nir_measurement_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode 1=reflectance in {1=reflectance, 2=transmittance, 3=transflectance}",
    );
}

#[test]
fn test_nir_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1 && speed <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed 30 scans/s in [1, 100]");
}

#[test]
fn test_nir_light_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume("source_val", "source == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source 1=tungsten halogen in {1=tungsten halogen, 2=LED, 3=supercontinuum}",
    );
}

#[test]
fn test_nir_signal_to_noise_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("snr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snr_x10_val", "snr_x10 == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "snr_x10_bounded",
        "snr_x10 >= 1000 && snr_x10 <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "signal-to-noise 10000.0 (x10=100000) in [1000, 500000]",
    );
}

#[test]
fn test_nir_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 490 && temp <= 545",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20C (offset+500=520) in [490, 545]");
}

#[test]
fn test_nir_fiber_optic_probe_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "fiber_optic_probe_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fiber optic probe flag=1 yields active (1)");
}
