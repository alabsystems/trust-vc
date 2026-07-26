// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial granulator controller property verification.
// Encodes key parameters of an industrial granulator system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bowl diameter (mm) — bounded [200, 3000], value 1200.
#[test]
fn test_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "bowl_dia_mm == 1200"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "bowl_dia_mm >= 200"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "bowl_dia_mm <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter 1200 mm in [200, 3000]");
}

/// Test 2: Throughput (kg/h) — bounded [10, 5000], value 500.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tput_val", "throughput_kgh == 500"));
    ctx.push_obligation(ProofObligation::assert("tput_min", "throughput_kgh >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "tput_max",
        "throughput_kgh <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 500 kg/h in [10, 5000]");
}

/// Test 3: Rotor speed (RPM) — bounded [50, 1500], value 300.
#[test]
fn test_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "rotor_rpm == 300"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "rotor_rpm >= 50"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "rotor_rpm <= 1500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed 300 RPM in [50, 1500]");
}

/// Test 4: Granulator type — 3-way disjunction.
/// 1=high-shear, 2=fluid bed, 3=roller compactor. Value 1 (high-shear).
#[test]
fn test_granulator_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("granulator_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gtype_val", "granulator_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_granulator_type",
        "granulator_type == 1 || granulator_type == 2 || granulator_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "granulator type 1 (high-shear) is valid 3-way disjunction",
    );
}

/// Test 5: Binder type — 3-way disjunction.
/// 1=water, 2=PVP solution, 3=HPMC solution. Value 2 (PVP solution).
#[test]
fn test_binder_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("binder_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("binder_val", "binder_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_binder_type",
        "binder_type == 1 || binder_type == 2 || binder_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "binder type 2 (PVP solution) is valid 3-way disjunction",
    );
}

/// Test 6: Spray rate (x10 mL/min) — e.g., 50.0 mL/min encoded as 500, bounded [10, 5000].
/// Value 500 represents 50.0 mL/min.
#[test]
fn test_spray_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spray_val", "spray_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("spray_min", "spray_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("spray_max", "spray_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray rate 50.0 mL/min (500 x10) in [10, 5000]");
}

/// Test 7: Product temperature (deg C) — bounded [20, 80], value 45.
/// All positive range; no offset encoding needed.
#[test]
fn test_product_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("product_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "product_temp_c == 45"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "product_temp_c >= 20"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "product_temp_c <= 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product temp 45 C in [20, 80]");
}

/// Test 8: Impeller type — 3-way disjunction.
/// 1=star, 2=mushroom, 3=chopper. Value 3 (chopper).
#[test]
fn test_impeller_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("imp_val", "impeller_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_impeller_type",
        "impeller_type == 1 || impeller_type == 2 || impeller_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller type 3 (chopper) is valid 3-way disjunction",
    );
}

/// Test 9: Granule size target (um) — bounded [100, 5000], value 500.
#[test]
fn test_granule_size_target_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("granule_size_um", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "size_val",
        "granule_size_um == 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "size_min",
        "granule_size_um >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "size_max",
        "granule_size_um <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "granule size target 500 um in [100, 5000]");
}

/// Test 10: Endpoint detection — boolean flag using i32 with if/else pattern.
/// Flag 1 = endpoint reached, which triggers batch completion (complete = 1).
#[test]
fn test_endpoint_detection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("endpoint_flag", i32_ty());
    ctx.declare_var_typed("batch_complete", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "endpoint_flag == 0 || endpoint_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "endpoint_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "complete_def",
        "batch_complete == if endpoint_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "complete_triggered",
        "batch_complete == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "endpoint flag triggers batch completion");
}
