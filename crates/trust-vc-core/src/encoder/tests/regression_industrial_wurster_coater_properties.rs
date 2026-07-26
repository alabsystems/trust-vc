// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Industrial Wurster coater (fluid bed bottom-spray coating) property verification.

use super::*;

#[test]
fn test_batch_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_size_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "batch_size_x10 >= 10 && batch_size_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "batch_size_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "batch_size_x10 >= 10 && batch_size_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch size x10 (100.0 kg) within valid range");
}

#[test]
fn test_air_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "air_flow_x10 >= 100 && air_flow_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "air_flow_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "air_flow_x10 >= 100 && air_flow_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow x10 (500.0 m3/h) within valid range");
}

#[test]
fn test_spray_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spray_rate_x10 >= 10 && spray_rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spray_rate_x10 == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spray_rate_x10 >= 10 && spray_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray rate x10 (30.0 mL/min) within valid range");
}

#[test]
fn test_inlet_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "inlet_temp_offset >= 130 && inlet_temp_offset <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "inlet_temp_offset == 380"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "inlet_temp_offset >= 130 && inlet_temp_offset <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet temp offset+100 (280 C) within valid range");
}

#[test]
fn test_partition_gap_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("partition_gap_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "partition_gap_x10 >= 10 && partition_gap_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "partition_gap_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "partition_gap_x10 >= 10 && partition_gap_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "partition gap x10 (20.0 mm) within valid range");
}

#[test]
fn test_nozzle_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "nozzle_count >= 1 && nozzle_count <= 24",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "nozzle_count == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "nozzle_count >= 1 && nozzle_count <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle count within valid range");
}

#[test]
fn test_coating_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coating_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "coating_material == 1 || coating_material == 2 || coating_material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "coating_material == 1 || coating_material == 2 || coating_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coating material is polymer(1), wax(2), or shellac(3)",
    );
}

#[test]
fn test_partition_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("partition_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "partition_type == 1 || partition_type == 2 || partition_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "partition_type == 1 || partition_type == 2 || partition_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "partition type is cylindrical(1), conical(2), or swirl(3)",
    );
}

#[test]
fn test_air_distribution_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_distribution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "air_distribution == 1 || air_distribution == 2 || air_distribution == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "air_distribution == 1 || air_distribution == 2 || air_distribution == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air distribution is single-plate(1), multi-zone(2), or tangential(3)",
    );
}

#[test]
fn test_continuous_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_continuous", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "continuous mode flag active when flag is 1");
}
