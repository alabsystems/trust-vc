// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Ion trap mass spectrometer property verification tests.

use super::*;

#[test]
fn test_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "mz >= 100 && mz <= 6000"));
    ctx.push_obligation(ProofObligation::assume("val", "mz == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "mz >= 100 && mz <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max m/z range bounded 100-6000");
}

#[test]
fn test_ms_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "stages >= 1 && stages <= 11",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "stages == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "stages >= 1 && stages <= 11",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MS^n stages bounded 1-11");
}

#[test]
fn test_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fwhm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "fwhm >= 1000 && fwhm <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "fwhm == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "fwhm >= 1000 && fwhm <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FWHM resolution bounded 1000-50000");
}

#[test]
fn test_sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "fg >= 1 && fg <= 1000"));
    ctx.push_obligation(ProofObligation::assume("val", "fg == 5"));
    ctx.push_obligation(ProofObligation::assert("bounded", "fg >= 1 && fg <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity femtograms on column bounded 1-1000");
}

#[test]
fn test_scan_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rate >= 1000 && rate <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rate == 52000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rate >= 1000 && rate <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan rate amu/s bounded 1000-100000");
}

#[test]
fn test_trap_volume_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "vol >= 1 && vol <= 1000"));
    ctx.push_obligation(ProofObligation::assume("val", "vol == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "vol >= 1 && vol <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trap volume x100 cm3 bounded 1-1000");
}

#[test]
fn test_trap_geometry_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geom", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "geom >= 1 && geom <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trap geometry 1=3D-paul 2=linear 3=orbitrap");
}

#[test]
fn test_ion_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "src >= 1 && src <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "src == 1 || src == 2 || src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ion source 1=ESI 2=APCI 3=APPI");
}

#[test]
fn test_activation_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "method >= 1 && method <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "activation method 1=CID 2=HCD 3=ETD");
}

#[test]
fn test_automatic_gain_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "agc",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic gain control flag enabled");
}
