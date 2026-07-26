// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// MP-AES (Microwave Plasma Atomic Emission Spectrometer) property regression tests

use super::*;

#[test]
fn test_wavelength_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "wl_min >= 150 && wl_min <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "wl_min == 178"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wl_min >= 150 && wl_min <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral minimum wavelength 178 nm within 150-200 nm range",
    );
}

#[test]
fn test_wavelength_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "wl_max >= 700 && wl_max <= 900",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "wl_max == 780"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wl_max >= 700 && wl_max <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral maximum wavelength 780 nm within 700-900 nm range",
    );
}

#[test]
fn test_plasma_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "power >= 500 && power <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "power == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "power >= 500 && power <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microwave plasma power 1000 W within 500-2000 W range",
    );
}

#[test]
fn test_detection_limit_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lod_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "lod_x100 >= 1 && lod_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "lod_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "lod_x100 >= 1 && lod_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit 0.50 ppb (x100=50) within 1-10000 range",
    );
}

#[test]
fn test_read_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("read_time_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "read_time_x10 >= 1 && read_time_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "read_time_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "read_time_x10 >= 1 && read_time_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement read time 3.0 s (x10=30) within 1-600 range",
    );
}

#[test]
fn test_sample_uptake_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("uptake_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "uptake_x10 >= 1 && uptake_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "uptake_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "uptake_x10 >= 1 && uptake_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample uptake rate 5.0 mL/min (x10=50) within 1-100 range",
    );
}

#[test]
fn test_nebulizer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neb_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "neb_type == 1 || neb_type == 2 || neb_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "neb_type >= 1 && neb_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nebulizer type (1=concentric, 2=cross-flow, 3=ultrasonic) within valid range",
    );
}

#[test]
fn test_spray_chamber_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "chamber == 1 || chamber == 2 || chamber == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "chamber >= 1 && chamber <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray chamber type (1=scott, 2=cyclonic, 3=double-pass) within valid range",
    );
}

#[test]
fn test_viewing_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("view_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "view_mode == 1 || view_mode == 2 || view_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "view_mode >= 1 && view_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "viewing mode (1=axial, 2=radial, 3=dual) within valid range",
    );
}

#[test]
fn test_nitrogen_generator_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n2_gen", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_enabled", "n2_gen == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_true",
        "if n2_gen == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nitrogen generator enabled flag evaluates to true");
}
