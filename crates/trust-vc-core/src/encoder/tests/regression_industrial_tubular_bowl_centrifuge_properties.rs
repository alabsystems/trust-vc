// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial tubular bowl centrifuge property verification.
// Encodes key parameters of an industrial tubular bowl centrifuge and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bowl diameter (mm) — bounded [50, 300].
#[test]
fn test_tubular_cent_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 50 && dia <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_check",
        "dia >= 50 && dia <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter in [50, 300] mm");
}

/// Test 2: Bowl length (mm) — bounded [200, 1500].
#[test]
fn test_tubular_cent_bowl_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_range",
        "len >= 200 && len <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_check",
        "len >= 200 && len <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl length in [200, 1500] mm");
}

/// Test 3: Speed (RPM) — bounded [10000, 65000].
#[test]
fn test_tubular_cent_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 10000 && rpm <= 65000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_check",
        "rpm >= 10000 && rpm <= 65000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed in [10000, 65000] RPM");
}

/// Test 4: G-force — bounded [10000, 100000].
#[test]
fn test_tubular_cent_g_force_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gf", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_range",
        "gf >= 10000 && gf <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_check",
        "gf >= 10000 && gf <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force in [10000, 100000] G");
}

/// Test 5: Feed rate x10 (0.1 L/h units) — bounded [1, 50000].
#[test]
fn test_tubular_cent_feed_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_range",
        "feed_x10 >= 1 && feed_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_check",
        "feed_x10 >= 1 && feed_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate x10 in [1, 50000]");
}

/// Test 6: Bowl volume x10 (0.1 L units) — bounded [1, 500].
#[test]
fn test_tubular_cent_bowl_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_range",
        "vol_x10 >= 1 && vol_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vol_check",
        "vol_x10 >= 1 && vol_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl volume x10 in [1, 500]");
}

/// Test 7: Separation type — 3-way disjunction.
/// 1=liquid-liquid, 2=liquid-solid, 3=three-phase.
#[test]
fn test_tubular_cent_separation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sep_range",
        "sep == 1 || sep == 2 || sep == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sep_check",
        "sep == 1 || sep == 2 || sep == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "separation type is valid 3-way disjunction");
}

/// Test 8: Material — 3-way disjunction.
/// 1=stainless 316, 2=titanium, 3=Hastelloy.
#[test]
fn test_tubular_cent_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_range",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material is valid 3-way disjunction");
}

/// Test 9: Orientation — 3-way disjunction.
/// 1=vertical, 2=horizontal, 3=inclined.
#[test]
fn test_tubular_cent_orientation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orient", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "orient_range",
        "orient == 1 || orient == 2 || orient == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "orient_check",
        "orient == 1 || orient == 2 || orient == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orientation is valid 3-way disjunction");
}

/// Test 10: Continuous discharge flag — boolean (0 or 1).
#[test]
fn test_tubular_cent_continuous_discharge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cd", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cd_range", "cd == 0 || cd == 1"));
    ctx.push_obligation(ProofObligation::assert("cd_check", "cd == 0 || cd == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "continuous discharge flag is boolean (0 or 1)");
}
