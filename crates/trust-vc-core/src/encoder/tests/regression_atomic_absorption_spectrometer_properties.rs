// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_aas_wavelength_range_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_min_val", "wl_min == 190"));
    ctx.push_obligation(ProofObligation::assert(
        "wl_min_bounded",
        "wl_min >= 180 && wl_min <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength range min 190 nm in [180, 300]");
}

#[test]
fn test_aas_wavelength_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_max_val", "wl_max == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "wl_max_bounded",
        "wl_max >= 600 && wl_max <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength range max 900 nm in [600, 1100]");
}

#[test]
fn test_aas_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_x1000_val", "res_x1000 == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "res_x1000_bounded",
        "res_x1000 >= 10 && res_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 0.200 nm (x1000=200) in [10, 500]");
}

#[test]
fn test_aas_atomization_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomization", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atomization_val",
        "atomization == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atomization_valid",
        "atomization == 1 || atomization == 2 || atomization == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomization 1=flame in {1=flame, 2=graphite furnace, 3=cold vapor}",
    );
}

#[test]
fn test_aas_light_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume("light_src_val", "light_src == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "light_src_valid",
        "light_src == 1 || light_src == 2 || light_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source 1=hollow cathode in {1=hollow cathode, 2=EDL, 3=continuum}",
    );
}

#[test]
fn test_aas_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sens_x100_val", "sens_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "sens_x100_bounded",
        "sens_x100 >= 1 && sens_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity 0.10 ug/L (x100=10) in [1, 1000]");
}

#[test]
fn test_aas_sample_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "throughput_val",
        "throughput == 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "throughput_bounded",
        "throughput >= 10 && throughput <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample throughput 300 samples/h in [10, 1000]");
}

#[test]
fn test_aas_detector_type_disjunction() {
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
        "detector type 1=PMT in {1=PMT, 2=CCD, 3=solid-state}",
    );
}

#[test]
fn test_aas_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 490 && temp <= 535",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20C (offset+500=520) in [490, 535]");
}

#[test]
fn test_aas_autosampler_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "autosampler_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "autosampler flag=1 yields active (1)");
}
