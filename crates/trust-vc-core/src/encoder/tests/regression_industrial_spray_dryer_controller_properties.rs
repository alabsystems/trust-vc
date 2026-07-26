// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial spray dryer controller property verification.
// Encodes key parameters of an industrial spray drying system
// and verifies that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Evaporation rate (×10 kg/h) — bounded [100, 100000].
/// 5000 represents 500.0 kg/h. Value 5000 (500.0 kg/h).
#[test]
fn test_evaporation_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap_rate_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap_rate_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "evap_max",
        "evap_rate_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "evaporation rate 500.0 kg/h (5000 x10) in [100, 100000]",
    );
}

/// Test 2: Inlet air temperature offset +100 (deg C) — bounded [200, 700].
/// 200 represents 100 C, 700 represents 600 C. Value 500 (400 C).
#[test]
fn test_inlet_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_val",
        "inlet_temp_offset == 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_min",
        "inlet_temp_offset >= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_max",
        "inlet_temp_offset <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet temp 400 C (offset 500) in [200, 700]");
}

/// Test 3: Outlet air temperature offset +100 (deg C) — bounded [150, 400].
/// 150 represents 50 C, 400 represents 300 C. Value 280 (180 C).
#[test]
fn test_outlet_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_val",
        "outlet_temp_offset == 280",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_min",
        "outlet_temp_offset >= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_max",
        "outlet_temp_offset <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "outlet temp 180 C (offset 280) in [150, 400]");
}

/// Test 4: Feed rate (×10 L/h) — bounded [10, 50000].
/// 2000 represents 200.0 L/h. Value 2000 (200.0 L/h).
#[test]
fn test_feed_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_rate_x10 == 2000"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_rate_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "feed_max",
        "feed_rate_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 200.0 L/h (2000 x10) in [10, 50000]");
}

/// Test 5: Drying air flow (×10 m3/h) — bounded [100, 500000].
/// 50000 represents 5000.0 m3/h. Value 50000 (5000.0 m3/h).
#[test]
fn test_air_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("air_val", "air_flow_x10 == 50000"));
    ctx.push_obligation(ProofObligation::assert("air_min", "air_flow_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("air_max", "air_flow_x10 <= 500000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow 5000.0 m3/h (50000 x10) in [100, 500000]");
}

/// Test 6: Atomized droplet size (×10 um) — bounded [10, 5000].
/// 500 represents 50.0 um. Value 500 (50.0 um).
#[test]
fn test_droplet_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("droplet_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drop_val", "droplet_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("drop_min", "droplet_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("drop_max", "droplet_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "droplet size 50.0 um (500 x10) in [10, 5000]");
}

/// Test 7: Atomizer type — 3-way disjunction.
/// 1=rotary, 2=pressure-nozzle, 3=two-fluid-nozzle. Value 1 (rotary).
#[test]
fn test_atomizer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomizer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("atom_val", "atomizer_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_atomizer",
        "atomizer_type == 1 || atomizer_type == 2 || atomizer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomizer type 1 (rotary) is valid 3-way disjunction",
    );
}

/// Test 8: Chamber shape — 3-way disjunction.
/// 1=conical, 2=cylindrical, 3=flat-bottom. Value 2 (cylindrical).
#[test]
fn test_chamber_shape_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_shape", u32_ty());
    ctx.push_obligation(ProofObligation::assume("shape_val", "chamber_shape == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_shape",
        "chamber_shape == 1 || chamber_shape == 2 || chamber_shape == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chamber shape 2 (cylindrical) is valid 3-way disjunction",
    );
}

/// Test 9: Product recovery method — 3-way disjunction.
/// 1=cyclone, 2=bag-filter, 3=electrostatic. Value 1 (cyclone).
#[test]
fn test_product_recovery_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recovery_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("recov_val", "recovery_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_recovery",
        "recovery_method == 1 || recovery_method == 2 || recovery_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "recovery method 1 (cyclone) is valid 3-way disjunction",
    );
}

/// Test 10: Co-current flow — boolean flag using i32 with if/else pattern.
/// Flag 1 = co-current flow enabled, which means air and feed travel in same direction.
#[test]
fn test_co_current_flow_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("co_current_flag", i32_ty());
    ctx.declare_var_typed("same_direction", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "co_current_flag == 0 || co_current_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "co_current_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dir_def",
        "same_direction == if co_current_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "same_dir_active",
        "same_direction == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "co-current flow flag activates same-direction airflow",
    );
}
