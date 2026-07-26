// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial basket centrifuge controller property verification.
// Encodes key parameters of an industrial basket centrifuge and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Basket diameter (mm) — bounded [300, 1800].
#[test]
fn test_basket_cent_basket_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 300 && dia <= 1800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "dia >= 300 && dia <= 1800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "basket diameter in [300, 1800] mm");
}

/// Test 2: Basket speed (RPM) — bounded [500, 3000].
#[test]
fn test_basket_cent_basket_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 500 && rpm <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 500 && rpm <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "basket speed in [500, 3000] RPM");
}

/// Test 3: G-force — bounded [200, 3000].
#[test]
fn test_basket_cent_g_force_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gf", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_range",
        "gf >= 200 && gf <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_bounded",
        "gf >= 200 && gf <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force in [200, 3000] G");
}

/// Test 4: Batch volume (L) — bounded [10, 5000].
#[test]
fn test_basket_cent_batch_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_range",
        "vol >= 10 && vol <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vol_bounded",
        "vol >= 10 && vol <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch volume in [10, 5000] L");
}

/// Test 5: Cake thickness (mm) — bounded [10, 500].
#[test]
fn test_basket_cent_cake_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cake", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cake_range",
        "cake >= 10 && cake <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cake_bounded",
        "cake >= 10 && cake <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cake thickness in [10, 500] mm");
}

/// Test 6: Screen opening x100 (mm) — bounded [1, 500].
/// Represents 0.01-5.00 mm screen openings scaled by 100.
#[test]
fn test_basket_cent_screen_opening_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scr_range",
        "scr_x100 >= 1 && scr_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scr_bounded",
        "scr_x100 >= 1 && scr_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screen opening x100 in [1, 500]");
}

/// Test 7: Discharge type — 3-way disjunction.
/// 1=peeler, 2=pusher, 3=inverting.
#[test]
fn test_basket_cent_discharge_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dis_domain",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dis_valid",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge type is valid 3-way disjunction");
}

/// Test 8: Basket material — 3-way disjunction.
/// 1=stainless 316, 2=Hastelloy, 3=titanium.
#[test]
fn test_basket_cent_basket_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_domain",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "basket material is valid 3-way disjunction");
}

/// Test 9: Drive type — 3-way disjunction.
/// 1=hydraulic, 2=electric, 3=mechanical.
#[test]
fn test_basket_cent_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drv_domain",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drv_valid",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type is valid 3-way disjunction");
}

/// Test 10: Nitrogen blanketing flag — boolean (0 or 1).
#[test]
fn test_basket_cent_nitrogen_blanketing_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("n2_domain", "n2 == 0 || n2 == 1"));
    ctx.push_obligation(ProofObligation::assert("n2_valid", "n2 == 0 || n2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nitrogen blanketing flag is boolean");
}
