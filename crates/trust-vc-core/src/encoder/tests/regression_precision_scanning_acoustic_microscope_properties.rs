// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_sam_frequency_mhz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fm_a",
        "freq_mhz >= 5 && freq_mhz <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fm_c",
        "freq_mhz >= 5 && freq_mhz <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency in [5, 2000] MHz");
}

#[test]
fn test_sam_resolution_um_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rs_a",
        "res_x10 >= 5 && res_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rs_c",
        "res_x10 >= 5 && res_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resolution x10 in [5, 10000] representing 0.5-1000.0 um",
    );
}

#[test]
fn test_sam_scan_area_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sa_a",
        "scan_mm >= 1 && scan_mm <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sa_c",
        "scan_mm >= 1 && scan_mm <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan area side in [1, 300] mm");
}

#[test]
fn test_sam_penetration_depth_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pd_a",
        "depth_um >= 1 && depth_um <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pd_c",
        "depth_um >= 1 && depth_um <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "penetration depth in [1, 50000] um (1um-50mm)");
}

#[test]
fn test_sam_pulse_width_ns_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_ns", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_a",
        "pulse_ns >= 1 && pulse_ns <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_c",
        "pulse_ns >= 1 && pulse_ns <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse width in [1, 1000] ns");
}

#[test]
fn test_sam_couplant_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coup_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "coup_temp >= 5 && coup_temp <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "coup_temp >= 5 && coup_temp <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "couplant temperature in [5, 80] C");
}

#[test]
fn test_sam_transducer_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("xducer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xt_a",
        "xducer == 1 || xducer == 2 || xducer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xt_c",
        "xducer == 1 || xducer == 2 || xducer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "transducer: focused spherical, cylindrical, or planar",
    );
}

#[test]
fn test_sam_imaging_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("img_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_a",
        "img_mode == 1 || img_mode == 2 || img_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_c",
        "img_mode == 1 || img_mode == 2 || img_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "imaging: C-scan (surface), B-scan (cross-section), or A-scan (waveform)",
    );
}

#[test]
fn test_sam_couplant_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("couplant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "couplant == 1 || couplant == 2 || couplant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "couplant == 1 || couplant == 2 || couplant == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "couplant: deionized water, glycerin, or silicone oil",
    );
}

#[test]
fn test_sam_gating_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gt_a",
        "gating == 0 || gating == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gt_c",
        "gating == 0 || gating == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time-gating flag is boolean");
}
