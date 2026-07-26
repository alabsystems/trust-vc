// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_size_range_min_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("min_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "min_range",
        "min_x100 >= 1 && min_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_x100 == 1"));
    ctx.push_obligation(ProofObligation::assert("min_is_001um", "min_x100 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min detectable size x100 should be 1 (0.01 um)");
}

#[test]
fn test_size_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_sz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "max_range",
        "max_sz >= 500 && max_sz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_sz == 3500"));
    ctx.push_obligation(ProofObligation::assert("max_is_3500um", "max_sz == 3500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max detectable size should be 3500 um");
}

#[test]
fn test_detector_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dets", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_range",
        "dets >= 16 && dets <= 128",
    ));
    ctx.push_obligation(ProofObligation::assume("det_val", "dets == 64"));
    ctx.push_obligation(ProofObligation::assert("det_is_64", "dets == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector count should be 64");
}

#[test]
fn test_laser_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_range",
        "wl >= 400 && wl <= 900",
    ));
    ctx.push_obligation(ProofObligation::assume("wl_val", "wl == 632"));
    ctx.push_obligation(ProofObligation::assert("wl_is_hene", "wl == 632"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength should be 632 nm (HeNe)");
}

#[test]
fn test_measurement_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mtime_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mtime_range",
        "mtime_x10 >= 5 && mtime_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("mtime_val", "mtime_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("mtime_is_10s", "mtime_x10 == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement time x10 should be 100 (10.0 seconds)");
}

#[test]
fn test_obscuration_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("obs_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "obs_range",
        "obs_x10 >= 10 && obs_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assume("obs_val", "obs_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("obs_is_15pct", "obs_x10 == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "obscuration x10 should be 150 (15.0 percent)");
}

#[test]
fn test_dispersion_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_valid",
        "disp == 1 || disp == 2 || disp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disp_in_range",
        "disp >= 1 && disp <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dispersion type (1=wet, 2=dry, 3=spray) should be in [1,3]",
    );
}

#[test]
fn test_optical_model_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("model", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "model_valid",
        "model == 1 || model == 2 || model == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "model_in_range",
        "model >= 1 && model <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optical model (1=Fraunhofer, 2=Mie, 3=modified-Mie) should be in [1,3]",
    );
}

#[test]
fn test_sample_recirculation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recirc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "recirc_valid",
        "recirc == 1 || recirc == 2 || recirc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "recirc_in_range",
        "recirc >= 1 && recirc <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "recirculation (1=peristaltic, 2=centrifugal, 3=ultrasonic) should be in [1,3]",
    );
}

#[test]
fn test_auto_alignment_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto", i32_ty());
    ctx.push_obligation(ProofObligation::assume("auto_true", "auto == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_one",
        "if auto == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto-alignment flag should evaluate to 1 when enabled",
    );
}
