// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Industrial capsule filling machine property verification tests.

use super::*;

#[test]
fn test_output_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capsules_per_hour", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "capsules_per_hour >= 1000 && capsules_per_hour <= 400000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "capsules_per_hour == 150000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "capsules_per_hour >= 1000 && capsules_per_hour <= 400000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output rate 150000 capsules/hour within bounds");
}

#[test]
fn test_fill_weight_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fill_weight_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "fill_weight_x100 >= 100 && fill_weight_x100 <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "fill_weight_x100 == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "fill_weight_x100 >= 100 && fill_weight_x100 <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fill weight 500.00 mg (x100) within bounds");
}

#[test]
fn test_weight_variation_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("weight_variation_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "weight_variation_x10 >= 5 && weight_variation_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "weight_variation_x10 == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "weight_variation_x10 >= 5 && weight_variation_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weight variation 1.5% RSD (x10) within bounds");
}

#[test]
fn test_dosator_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dosator_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dosator_count >= 1 && dosator_count <= 40",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dosator_count == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dosator_count >= 1 && dosator_count <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dosator count 16 stations within bounds");
}

#[test]
fn test_turret_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("turret_speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "turret_speed_x10 >= 10 && turret_speed_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "turret_speed_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "turret_speed_x10 >= 10 && turret_speed_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turret speed 20.0 RPM (x10) within bounds");
}

#[test]
fn test_capsule_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capsule_size", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "capsule_size >= 1 && capsule_size <= 7",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "capsule_size == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "capsule_size >= 1 && capsule_size <= 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capsule size 3 (size 1) within bounds");
}

#[test]
fn test_filling_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filling_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "filling_method >= 1 && filling_method <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "filling_method == 1 || filling_method == 2 || filling_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "filling method is dosator, tamping-pin, or dosing-disc",
    );
}

#[test]
fn test_capsule_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capsule_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "capsule_material >= 1 && capsule_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "capsule_material == 1 || capsule_material == 2 || capsule_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capsule material is gelatin, HPMC, or pullulan");
}

#[test]
fn test_orientation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orientation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "orientation >= 1 && orientation <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "orientation == 1 || orientation == 2 || orientation == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orientation is horizontal, vertical, or intermittent",
    );
}

#[test]
fn test_vacuum_closing_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "vacuum_closing",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum closing enabled when flag is 1");
}
