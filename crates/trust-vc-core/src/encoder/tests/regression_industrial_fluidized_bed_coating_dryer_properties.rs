// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial fluidized bed coating dryer (Wurster coater / top-spray coater)
// property verification for pharmaceutical tablet/particle coating and drying.

/// Test 1: Batch size in kg, valid range [1, 2000].
#[test]
fn test_batch_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_size", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "batch_size >= 1 && batch_size <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "batch_size == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "batch_size >= 1 && batch_size <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch size 500 kg within [1, 2000] range");
}

/// Test 2: Coating spray rate x10, valid range [1, 5000] representing 0.1-500.0 g/min.
#[test]
fn test_coating_spray_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spray_rate_x10 >= 1 && spray_rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spray_rate_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spray_rate_x10 >= 1 && spray_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray rate 25.0 g/min (x10=250) within [1, 5000]");
}

/// Test 3: Inlet air temperature as offset+100, valid range [130, 400] representing 30-300 deg C.
#[test]
fn test_inlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "inlet_temp_offset >= 130 && inlet_temp_offset <= 400",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "inlet_temp_offset == 280"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "inlet_temp_offset >= 130 && inlet_temp_offset <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet air temp 180C (offset+100=280) within 30-300C range",
    );
}

/// Test 4: Fluidization air volume in m3/h, valid range [100, 50000].
#[test]
fn test_fluidization_air_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "air_volume >= 100 && air_volume <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "air_volume == 8000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "air_volume >= 100 && air_volume <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluidization air volume 8000 m3/h within [100, 50000]",
    );
}

/// Test 5: Product temperature as offset+100, valid range [120, 250] representing 20-150 deg C.
#[test]
fn test_product_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("product_temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "product_temp_offset >= 120 && product_temp_offset <= 250",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "product_temp_offset == 160"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "product_temp_offset >= 120 && product_temp_offset <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product temp 60C (offset+100=160) within 20-150C range",
    );
}

/// Test 6: Number of spray guns, valid range [1, 12].
#[test]
fn test_spray_gun_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_guns", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spray_guns >= 1 && spray_guns <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spray_guns == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spray_guns >= 1 && spray_guns <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray gun count 4 within [1, 12] range");
}

/// Test 7: Coating process type: 1=Wurster, 2=top-spray, 3=tangential.
#[test]
fn test_coating_process_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coating_process", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "coating_process == 1 || coating_process == 2 || coating_process == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "coating_process == 1 || coating_process == 2 || coating_process == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coating process is one of Wurster(1), top-spray(2), tangential(3)",
    );
}

/// Test 8: Nozzle type: 1=two-fluid, 2=ultrasonic, 3=pressure.
#[test]
fn test_nozzle_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "nozzle_type == 1 || nozzle_type == 2 || nozzle_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "nozzle_type == 1 || nozzle_type == 2 || nozzle_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nozzle type is one of two-fluid(1), ultrasonic(2), pressure(3)",
    );
}

/// Test 9: Partition type: 1=column, 2=swirl, 3=none.
#[test]
fn test_partition_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("partition_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "partition_type == 1 || partition_type == 2 || partition_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "partition_type == 1 || partition_type == 2 || partition_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "partition type is one of column(1), swirl(2), none(3)",
    );
}

/// Test 10: Automatic weight gain monitoring boolean flag (0 or 1).
#[test]
fn test_weight_gain_monitoring_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("monitoring_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "domain",
        "monitoring_flag == 0 || monitoring_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_boolean",
        "monitoring_flag == 0 || monitoring_flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weight gain monitoring flag is boolean (0 or 1)");
}
