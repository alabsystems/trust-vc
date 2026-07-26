// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial disc stack separator property verification.
// Encodes key parameters of an industrial disc stack separator and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bowl diameter (mm) — bounded [150, 800].
#[test]
fn test_disc_sep_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 150 && dia <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_check",
        "dia >= 150 && dia <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter in [150, 800] mm");
}

/// Test 2: Bowl speed (RPM) — bounded [3000, 12000].
#[test]
fn test_disc_sep_bowl_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 3000 && rpm <= 12000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_check",
        "rpm >= 3000 && rpm <= 12000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl speed in [3000, 12000] RPM");
}

/// Test 3: Disc count — bounded [30, 200].
#[test]
fn test_disc_sep_disc_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discs", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discs_range",
        "discs >= 30 && discs <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discs_check",
        "discs >= 30 && discs <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc count in [30, 200]");
}

/// Test 4: Throughput (L/h) — bounded [100, 100000].
#[test]
fn test_disc_sep_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tp_range",
        "tp >= 100 && tp <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tp_check",
        "tp >= 100 && tp <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput in [100, 100000] L/h");
}

/// Test 5: G-force — bounded [3000, 15000].
#[test]
fn test_disc_sep_g_force_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gf", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_range",
        "gf >= 3000 && gf <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_check",
        "gf >= 3000 && gf <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force in [3000, 15000] G");
}

/// Test 6: Disc angle (degrees) — bounded [33, 50].
#[test]
fn test_disc_sep_disc_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "angle >= 33 && angle <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_check",
        "angle >= 33 && angle <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc angle in [33, 50] degrees");
}

/// Test 7: Discharge type — 3-way disjunction.
/// 1=nozzle, 2=intermittent, 3=self-cleaning.
#[test]
fn test_disc_sep_discharge_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dis_range",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dis_check",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge type is valid 3-way disjunction");
}

/// Test 8: Feed type — 3-way disjunction.
/// 1=open, 2=hermetic, 3=semi-hermetic.
#[test]
fn test_disc_sep_feed_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_range",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_check",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed type is valid 3-way disjunction");
}

/// Test 9: Application type — 3-way disjunction.
/// 1=clarification, 2=purification, 3=concentration.
#[test]
fn test_disc_sep_application_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("app", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "app_range",
        "app == 1 || app == 2 || app == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "app_check",
        "app == 1 || app == 2 || app == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "application type is valid 3-way disjunction");
}

/// Test 10: CIP (clean-in-place) flag — boolean (0 or 1).
#[test]
fn test_disc_sep_cip_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cip", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cip_range", "cip == 0 || cip == 1"));
    ctx.push_obligation(ProofObligation::assert("cip_check", "cip == 0 || cip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CIP flag is boolean (0 or 1)");
}
