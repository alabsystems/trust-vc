// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial spin flash dryer property verification.
// Encodes key parameters of an industrial spin flash dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Chamber diameter (mm) — bounded [200, 3000].
#[test]
fn test_spin_flash_dryer_chamber_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_assume",
        "diameter >= 200 && diameter <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_check",
        "diameter >= 200 && diameter <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber diameter bounded in [200, 3000] mm");
}

/// Test 2: Inlet air temperature offset +100 (deg C) — bounded [200, 800].
/// 200 represents 100 C, 800 represents 700 C.
#[test]
fn test_spin_flash_dryer_inlet_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_assume",
        "temp_off >= 200 && temp_off <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_check",
        "temp_off >= 200 && temp_off <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet air temp offset+100 bounded in [200, 800]");
}

/// Test 3: Rotor speed (RPM) — bounded [100, 5000].
#[test]
fn test_spin_flash_dryer_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_assume",
        "speed >= 100 && speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "speed >= 100 && speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed bounded in [100, 5000] RPM");
}

/// Test 4: Feed rate x10 (0.1 kg/h) — bounded [10, 10000].
/// 10 represents 1.0 kg/h, 10000 represents 1000.0 kg/h.
#[test]
fn test_spin_flash_dryer_feed_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_assume",
        "rate_x10 >= 10 && rate_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_check",
        "rate_x10 >= 10 && rate_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate x10 bounded in [10, 10000]");
}

/// Test 5: Outlet air temperature offset +100 (deg C) — bounded [140, 300].
/// 140 represents 40 C, 300 represents 200 C.
#[test]
fn test_spin_flash_dryer_outlet_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_assume",
        "temp_off >= 140 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_check",
        "temp_off >= 140 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "outlet air temp offset+100 bounded in [140, 300]");
}

/// Test 6: Classifier type — 3-way disjunction.
/// 1=mechanical, 2=air, 3=combined.
#[test]
fn test_spin_flash_dryer_classifier_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ct", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct_assume", "ct == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_check",
        "ct == 1 || ct == 2 || ct == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "classifier type valid 3-way disjunction");
}

/// Test 7: Feed mechanism — 3-way disjunction.
/// 1=screw, 2=gravity, 3=pump.
#[test]
fn test_spin_flash_dryer_feed_mechanism_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fm_assume", "fm == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "fm_check",
        "fm == 1 || fm == 2 || fm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed mechanism valid 3-way disjunction");
}

/// Test 8: Heating source — 3-way disjunction.
/// 1=gas-burner, 2=steam-coil, 3=electric.
#[test]
fn test_spin_flash_dryer_heating_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hs", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hs_assume", "hs == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "hs_check",
        "hs == 1 || hs == 2 || hs == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating source valid 3-way disjunction");
}

/// Test 9: Automatic feed control — boolean flag (0 or 1).
#[test]
fn test_spin_flash_dryer_auto_feed_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_assume", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_check",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto feed control flag is boolean");
}

/// Test 10: Residence time x10 (0.1 seconds) — bounded [1, 300].
/// 1 represents 0.1 sec, 300 represents 30.0 sec.
#[test]
fn test_spin_flash_dryer_residence_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_assume",
        "time_x10 >= 1 && time_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_check",
        "time_x10 >= 1 && time_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time x10 bounded in [1, 300]");
}
