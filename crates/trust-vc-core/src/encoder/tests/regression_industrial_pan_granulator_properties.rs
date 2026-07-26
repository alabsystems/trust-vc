// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pan granulator property verification.
// Encodes key parameters of a pan (disc) granulator and verifies
// that they satisfy bounded, scaled, disjunctive, and boolean-flag constraints.

/// Test 1: Disc diameter (mm) — bounded [500, 6000], value 3000.
#[test]
fn test_disc_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "disc_dia_mm >= 500 && disc_dia_mm <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "disc_dia_mm == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "disc_dia_mm >= 500 && disc_dia_mm <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc diameter 3000 mm in [500, 6000]");
}

/// Test 2: Rim height (mm) — bounded [100, 800], value 400.
#[test]
fn test_rim_height_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rim_height_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rim_height_mm >= 100 && rim_height_mm <= 800",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rim_height_mm == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rim_height_mm >= 100 && rim_height_mm <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rim height 400 mm in [100, 800]");
}

/// Test 3: Tilt angle (x10 degrees) — 0.1 deg resolution, bounded [300, 550].
/// Value 480 represents 48.0 degrees.
#[test]
fn test_tilt_angle_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tilt_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "tilt_x10 >= 300 && tilt_x10 <= 550",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "tilt_x10 == 480"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "tilt_x10 >= 300 && tilt_x10 <= 550",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tilt angle 48.0 deg (480 x10) in [300, 550]");
}

/// Test 4: Rotation speed (x10 RPM) — 0.1 RPM resolution, bounded [50, 200].
/// Value 120 represents 12.0 RPM.
#[test]
fn test_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed_x10 >= 50 && speed_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed_x10 == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed_x10 >= 50 && speed_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 12.0 RPM (120 x10) in [50, 200]");
}

/// Test 5: Throughput (x10 t/h) — 0.1 t/h resolution, bounded [10, 500].
/// Value 100 represents 10.0 t/h.
#[test]
fn test_throughput_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "throughput_x10 >= 10 && throughput_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "throughput_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "throughput_x10 >= 10 && throughput_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 10.0 t/h (100 x10) in [10, 500]");
}

/// Test 6: Spray rate (x10 L/min) — 0.1 L/min resolution, bounded [1, 500].
/// Value 50 represents 5.0 L/min.
#[test]
fn test_spray_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spray_rate_x10 >= 1 && spray_rate_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spray_rate_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spray_rate_x10 >= 1 && spray_rate_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray rate 5.0 L/min (50 x10) in [1, 500]");
}

/// Test 7: Liner material — 3-way disjunction.
/// 1=rubber, 2=polyurethane, 3=stainless.
#[test]
fn test_liner_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liner_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "liner_mat == 1 || liner_mat == 2 || liner_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "liner_mat >= 1 && liner_mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liner material disjunction implies bounded [1, 3]");
}

/// Test 8: Scraper type — 3-way disjunction.
/// 1=fixed, 2=adjustable, 3=pneumatic.
#[test]
fn test_scraper_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scraper_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "scraper_type == 1 || scraper_type == 2 || scraper_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "scraper_type >= 1 && scraper_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scraper type disjunction implies bounded [1, 3]");
}

/// Test 9: Drive type — 3-way disjunction.
/// 1=gear, 2=belt, 3=direct.
#[test]
fn test_drive_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "drive_type == 1 || drive_type == 2 || drive_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "drive_type >= 1 && drive_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type disjunction implies bounded [1, 3]");
}

/// Test 10: Dust collection — boolean flag using i32 with if/else pattern.
/// Flag 1 = dust collection enabled.
#[test]
fn test_dust_collection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dust_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "domain",
        "dust_flag == 0 || dust_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dust_flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "active",
        "if dust_flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dust collection flag active when set to 1");
}
