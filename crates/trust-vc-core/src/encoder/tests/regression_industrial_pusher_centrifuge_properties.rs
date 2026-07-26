// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial pusher centrifuge controller property verification.
// Encodes key parameters of an industrial pusher centrifuge and verifies
// that they satisfy bounded, disjunctive, and scaled-value constraints.

/// Test 1: Basket diameter (mm) — bounded [200, 1200], value 600.
#[test]
fn test_pusher_cent_basket_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "dia == 600"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "dia >= 200"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "dia <= 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "basket diameter 600 mm in [200, 1200]");
}

/// Test 2: Speed (RPM) — bounded [500, 3000], value 1800.
#[test]
fn test_pusher_cent_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 1800"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "speed >= 500"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "speed <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 1800 RPM in [500, 3000]");
}

/// Test 3: G-force — bounded [100, 3000], value 1500.
#[test]
fn test_pusher_cent_g_force_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gf", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gf_val", "gf == 1500"));
    ctx.push_obligation(ProofObligation::assert("gf_min", "gf >= 100"));
    ctx.push_obligation(ProofObligation::assert("gf_max", "gf <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force 1500 G in [100, 3000]");
}

/// Test 4: Feed rate x10 (L/h) — bounded [0, 10000], value 500 (50.0 L/h).
#[test]
fn test_pusher_cent_feed_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_x10 >= 0"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 50.0 L/h (500 x10) in [0, 10000]");
}

/// Test 5: Cake thickness (mm) — bounded [5, 150], value 50.
#[test]
fn test_pusher_cent_cake_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick", i32_ty());
    ctx.push_obligation(ProofObligation::assume("thick_val", "thick == 50"));
    ctx.push_obligation(ProofObligation::assert("thick_min", "thick >= 5"));
    ctx.push_obligation(ProofObligation::assert("thick_max", "thick <= 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cake thickness 50 mm in [5, 150]");
}

/// Test 6: Screen mesh — bounded [20, 400], value 200.
#[test]
fn test_pusher_cent_screen_mesh_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mesh", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mesh_val", "mesh == 200"));
    ctx.push_obligation(ProofObligation::assert("mesh_min", "mesh >= 20"));
    ctx.push_obligation(ProofObligation::assert("mesh_max", "mesh <= 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screen mesh 200 in [20, 400]");
}

/// Test 7: Filtrate clarity x10 (NTU) — bounded [0, 1000], value 15 (1.5 NTU).
#[test]
fn test_pusher_cent_filtrate_clarity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clar_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("clar_val", "clar_x10 == 15"));
    ctx.push_obligation(ProofObligation::assert("clar_min", "clar_x10 >= 0"));
    ctx.push_obligation(ProofObligation::assert("clar_max", "clar_x10 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filtrate clarity 1.5 NTU (15 x10) in [0, 1000]");
}

/// Test 8: Stage type — 3-way disjunction.
/// 1=single-stage, 2=multi-stage, 3=continuous.
#[test]
fn test_pusher_cent_stage_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stage_domain",
        "stage == 1 || stage == 2 || stage == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stage_valid",
        "stage == 1 || stage == 2 || stage == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stage type is valid 3-way disjunction");
}

/// Test 9: Discharge method — 3-way disjunction.
/// 1=reciprocating-pusher, 2=scroll, 3=peeler.
#[test]
fn test_pusher_cent_discharge_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_domain",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_valid",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge method is valid 3-way disjunction");
}

/// Test 10: Screen material — 3-way disjunction.
/// 1=stainless, 2=hastelloy, 3=titanium.
#[test]
fn test_pusher_cent_screen_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scrmat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "scrmat_domain",
        "scrmat == 1 || scrmat == 2 || scrmat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scrmat_valid",
        "scrmat == 1 || scrmat == 2 || scrmat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screen material is valid 3-way disjunction");
}
