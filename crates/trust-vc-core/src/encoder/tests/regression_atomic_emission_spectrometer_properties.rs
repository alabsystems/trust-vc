// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Atomic emission spectrometer (AES/OES) property verification.
// Encodes key parameters of an atomic emission spectrometer and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Minimum wavelength (nm) — bounded [100, 200].
/// Value 130 nm (typical vacuum UV lower bound for ICP-OES).
#[test]
fn test_wavelength_range_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_min_val", "wl_min == 130"));
    ctx.push_obligation(ProofObligation::assert("wl_min_lo", "wl_min >= 100"));
    ctx.push_obligation(ProofObligation::assert("wl_min_hi", "wl_min <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min wavelength 130 nm in [100, 200]");
}

/// Test 2: Maximum wavelength (nm) — bounded [700, 900].
/// Value 800 nm (typical NIR upper bound for ICP-OES).
#[test]
fn test_wavelength_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_max_val", "wl_max == 800"));
    ctx.push_obligation(ProofObligation::assert("wl_max_lo", "wl_max >= 700"));
    ctx.push_obligation(ProofObligation::assert("wl_max_hi", "wl_max <= 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max wavelength 800 nm in [700, 900]");
}

/// Test 3: Spectral resolution x1000 (nm) — bounded [1, 100].
/// Value 5 represents 0.005 nm resolution. Typical high-resolution ICP-OES.
#[test]
fn test_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "res_x1000 == 5"));
    ctx.push_obligation(ProofObligation::assert("res_min", "res_x1000 >= 1"));
    ctx.push_obligation(ProofObligation::assert("res_max", "res_x1000 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 0.005 nm (5 x1000) in [1, 100]");
}

/// Test 4: Detection limit x100 (ppb) — bounded [1, 1000].
/// Value 10 represents 0.10 ppb LOD. Typical sub-ppb ICP-OES detection.
#[test]
fn test_detection_limit_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lod_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lod_val", "lod_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert("lod_min", "lod_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("lod_max", "lod_x100 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit 0.10 ppb (10 x100) in [1, 1000]");
}

/// Test 5: CCD pixel count — bounded [1000, 1000000].
/// Value 200000 (200k pixels, typical megapixel-class CCD detector).
#[test]
fn test_pixel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pix", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pix_val", "pix == 200000"));
    ctx.push_obligation(ProofObligation::assert("pix_min", "pix >= 1000"));
    ctx.push_obligation(ProofObligation::assert("pix_max", "pix <= 1000000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pixel count 200000 in [1000, 1000000]");
}

/// Test 6: Integration time x10 (ms) — bounded [1, 10000].
/// Value 100 represents 10.0 ms integration time. Typical fast acquisition.
#[test]
fn test_integration_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("itime_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("itime_val", "itime_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("itime_min", "itime_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("itime_max", "itime_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integration time 10.0 ms (100 x10) in [1, 10000]");
}

/// Test 7: Source type — 3-way disjunction.
/// 1=ICP, 2=spark, 3=arc. Value 1 (ICP plasma source).
#[test]
fn test_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("src_val", "source_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "source_type == 1 || source_type == 2 || source_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source type 1 (ICP) is valid 3-way disjunction");
}

/// Test 8: Optics type — 3-way disjunction.
/// 1=Paschen-Runge, 2=Echelle, 3=Czerny-Turner. Value 2 (Echelle grating).
#[test]
fn test_optics_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("opt_val", "optics_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_optics",
        "optics_type == 1 || optics_type == 2 || optics_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optics type 2 (Echelle) is valid 3-way disjunction",
    );
}

/// Test 9: Detector type — 3-way disjunction.
/// 1=CCD, 2=CMOS, 3=PMT. Value 1 (CCD detector).
#[test]
fn test_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("det_val", "detector_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_detector",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type 1 (CCD) is valid 3-way disjunction");
}

/// Test 10: Argon purged — boolean flag using i32 with if/else pattern.
/// Flag 1 = argon purge active, purge_active = 1.
#[test]
fn test_argon_purged_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("argon", i32_ty());
    ctx.declare_var_typed("purge_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "argon == 0 || argon == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "argon == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "purge_def",
        "purge_active == if argon == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("purge_on", "purge_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "argon purge flag enables purge active");
}
