// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_oes_wavelength_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_min_val", "wl_min == 130"));
    ctx.push_obligation(ProofObligation::assert(
        "wl_min_bounded",
        "wl_min >= 100 && wl_min <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength min 130 nm in [100, 300]");
}

#[test]
fn test_oes_wavelength_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_max_val", "wl_max == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "wl_max_bounded",
        "wl_max >= 500 && wl_max <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength max 800 nm in [500, 1100]");
}

#[test]
fn test_oes_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_x1000_val", "res_x1000 == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "res_x1000_bounded",
        "res_x1000 >= 1 && res_x1000 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 0.008 nm (x1000=8) in [1, 50]");
}

#[test]
fn test_oes_excitation_source_disjunction() {
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
        "excitation source 1=spark in {1=spark, 2=arc, 3=glow discharge}",
    );
}

#[test]
fn test_oes_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("detector_val", "detector == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type 1=CCD in {1=CCD, 2=CMOS, 3=PMT}");
}

#[test]
fn test_oes_element_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume("channels_val", "channels == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "channels_bounded",
        "channels >= 10 && channels <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "element channels 60 in [10, 80]");
}

#[test]
fn test_oes_repeatability_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeat_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "repeat_x100_val",
        "repeat_x100 == 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "repeat_x100_bounded",
        "repeat_x100 >= 1 && repeat_x100 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repeatability 0.50% RSD (x100=50) in [1, 200]");
}

#[test]
fn test_oes_optics_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics", i32_ty());
    ctx.push_obligation(ProofObligation::assume("optics_val", "optics == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "optics_valid",
        "optics == 1 || optics == 2 || optics == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optics type 1=Paschen-Runge in {1=Paschen-Runge, 2=Czerny-Turner, 3=Echelle}",
    );
}

#[test]
fn test_oes_operating_temp_offset_bounded() {
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
fn test_oes_argon_purge_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "argon_purge_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "argon purge flag=1 yields active (1)");
}
