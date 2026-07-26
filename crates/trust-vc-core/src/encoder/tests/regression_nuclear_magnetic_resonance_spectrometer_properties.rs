//! Nuclear magnetic resonance (NMR) spectrometer property tests.
//!
//! Verifies bounded constraints on NMR spectrometer parameters through the
//! trust_vc verification pipeline: field strength, resolution, sensitivity,
//! probe geometry, spectral width, acquisition timing, magnet/probe/lock
//! channel classification, and autosampler flag.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// Field strength bounded to 60-1200 MHz (standard NMR range).
#[test]
fn test_nmr_field_strength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("field", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "field_range",
        "field >= 60 && field <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "field_check",
        "field >= 60 && field <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR field strength 60-1200 MHz should verify");
}

/// Resolution x1000 bounded to 1-500 (representing 0.001-0.500 Hz).
#[test]
fn test_nmr_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x1000 >= 1 && res_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_check",
        "res_x1000 >= 1 && res_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR resolution x1000 1-500 should verify");
}

/// Sensitivity x100 bounded to 100-100000 (representing 1.00-1000.00 S/N).
#[test]
fn test_nmr_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sns_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sns_range",
        "sns_x100 >= 100 && sns_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sns_check",
        "sns_x100 >= 100 && sns_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR sensitivity x100 100-100000 should verify");
}

/// Probe diameter bounded to 1-10 mm.
#[test]
fn test_nmr_probe_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "probe_range",
        "probe >= 1 && probe <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "probe_check",
        "probe >= 1 && probe <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR probe diameter 1-10 mm should verify");
}

/// Spectral width bounded to 1-500 ppm.
#[test]
fn test_nmr_spectral_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sw", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sw_range", "sw >= 1 && sw <= 500"));
    ctx.push_obligation(ProofObligation::assert("sw_check", "sw >= 1 && sw <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR spectral width 1-500 ppm should verify");
}

/// Acquisition time x100 bounded to 1-10000 (representing 0.01-100.00 seconds).
#[test]
fn test_nmr_acquisition_time_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acq_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acq_range",
        "acq_x100 >= 1 && acq_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acq_check",
        "acq_x100 >= 1 && acq_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR acquisition time x100 1-10000 should verify");
}

/// Magnet type three-way: 1=permanent, 2=superconducting, 3=cryogen-free.
#[test]
fn test_nmr_magnet_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mag_enum",
        "mag == 1 || mag == 2 || mag == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mag_check",
        "mag == 1 || mag == 2 || mag == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR magnet type three-way should verify");
}

/// Probe type three-way: 1=broadband, 2=multinuclear, 3=cryoprobe.
#[test]
fn test_nmr_probe_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pt_enum",
        "pt == 1 || pt == 2 || pt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pt_check",
        "pt == 1 || pt == 2 || pt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR probe type three-way should verify");
}

/// Lock channel three-way: 1=deuterium, 2=fluorine, 3=lithium.
#[test]
fn test_nmr_lock_channel_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lock", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lock_enum",
        "lock == 1 || lock == 2 || lock == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lock_check",
        "lock == 1 || lock == 2 || lock == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR lock channel three-way should verify");
}

/// Autosampler boolean flag: 0=absent, 1=present.
#[test]
fn test_nmr_autosampler_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_bool",
        "auto_s == 0 || auto_s == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_check",
        "auto_s == 0 || auto_s == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMR autosampler boolean flag should verify");
}
