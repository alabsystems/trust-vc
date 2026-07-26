// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_libs_wavelength_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "wl >= 190 && wl <= 900"));
    ctx.push_obligation(ProofObligation::assume("val", "wl == 532"));
    ctx.push_obligation(ProofObligation::assert("bound", "wl >= 190 && wl <= 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS wavelength within valid spectral range");
}

#[test]
fn test_libs_spectral_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "res_x1000 > 0 && res_x1000 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "res_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "res_x1000 > 0 && res_x1000 < 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS spectral resolution 0.050 nm within range");
}

#[test]
fn test_libs_laser_energy_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "energy_x10 > 0 && energy_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "energy_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "energy_x10 > 0 && energy_x10 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS laser energy 100.0 mJ within range");
}

#[test]
fn test_libs_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "rep >= 1 && rep <= 1000"));
    ctx.push_obligation(ProofObligation::assume("val", "rep == 20"));
    ctx.push_obligation(ProofObligation::assert("bound", "rep >= 1 && rep <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS repetition rate within valid range");
}

#[test]
fn test_libs_gate_delay_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delay_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "delay_x100 > 0 && delay_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "delay_x100 == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "delay_x100 > 0 && delay_x100 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS gate delay 100.00 ns within range");
}

#[test]
fn test_libs_accumulations_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "acc >= 1 && acc <= 10000"));
    ctx.push_obligation(ProofObligation::assume("val", "acc == 100"));
    ctx.push_obligation(ProofObligation::assert("bound", "acc >= 1 && acc <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS accumulation count within valid range");
}

#[test]
fn test_libs_laser_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser", i32_ty());
    // 1=Nd:YAG, 2=excimer, 3=fiber
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "laser == 1 || laser == 2 || laser == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "laser == 1 || laser == 2 || laser == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS laser type must be one of three valid options",
    );
}

#[test]
fn test_libs_detection_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    // 1=CCD, 2=ICCD, 3=EMCCD
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "det == 1 || det == 2 || det == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS detection mode must be one of three valid options",
    );
}

#[test]
fn test_libs_sampling_geometry_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geom", i32_ty());
    // 1=single-pulse, 2=double-pulse, 3=standoff
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LIBS sampling geometry must be one of three valid options",
    );
}

#[test]
fn test_libs_auto_focus_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("boolean", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_focus",
        "if flag == 1 { 1 } else { 0 } >= 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIBS automatic focus tracking boolean flag");
}
