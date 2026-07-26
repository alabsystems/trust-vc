// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_raman_laser_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_val",
        "wavelength == 785",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_bounded",
        "wavelength >= 200 && wavelength <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength 785 nm in [200, 1100]");
}

#[test]
fn test_raman_spectral_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range_val", "range == 3500"));
    ctx.push_obligation(ProofObligation::assert(
        "range_bounded",
        "range >= 100 && range <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral range 3500 cm-1 in [100, 5000]");
}

#[test]
fn test_raman_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_x10_val", "res_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "res_x10_bounded",
        "res_x10 >= 5 && res_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 3.0 cm-1 (x10=30) in [5, 100]");
}

#[test]
fn test_raman_laser_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("laser_type_val", "laser_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "laser_type_valid",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser type 1=diode 785nm in {1=diode 785nm, 2=HeNe 633nm, 3=Nd:YAG 532nm}",
    );
}

#[test]
fn test_raman_detector_type_disjunction() {
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
        "detector type 1=CCD in {1=CCD, 2=InGaAs, 3=TE-cooled CCD}",
    );
}

#[test]
fn test_raman_laser_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 1 && power <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser power 500 mW in [1, 2000]");
}

#[test]
fn test_raman_integration_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("int_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("int_time_val", "int_time == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "int_time_bounded",
        "int_time >= 10 && int_time <= 60000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integration time 1000 ms in [10, 60000]");
}

#[test]
fn test_raman_sampling_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3 || mode == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sampling mode 1=probe in {1=probe, 2=microscope, 3=fiber, 4=vial holder}",
    );
}

#[test]
fn test_raman_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 490 && temp <= 540",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20C (offset+500=520) in [490, 540]");
}

#[test]
fn test_raman_fluorescence_rejection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "fluorescence_rejection_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fluorescence rejection flag=1 yields active (1)");
}
