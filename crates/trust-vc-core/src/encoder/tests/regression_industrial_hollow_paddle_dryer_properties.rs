// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// Industrial hollow paddle dryer property verification.
// A horizontal agitated dryer with hollow heated paddles for indirect drying
// of pastes, powders, and granules. Encodes key parameters and verifies
// bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Trough length (mm) — bounded [1000, 15000], value 6000.
#[test]
fn test_hollow_paddle_dryer_trough_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "length == 6000"));
    ctx.push_obligation(ProofObligation::assert(
        "len_range",
        "length >= 1000 && length <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trough length 6000 mm in [1000, 15000]");
}

/// Test 2: Heat transfer area (m2) — bounded [5, 500], value 80.
#[test]
fn test_hollow_paddle_dryer_heat_transfer_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area", i32_ty());
    ctx.push_obligation(ProofObligation::assume("area_val", "area == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "area_range",
        "area >= 5 && area <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat transfer area 80 m2 in [5, 500]");
}

/// Test 3: Paddle speed x10 (0.1 RPM) — bounded [10, 200], value 80.
/// 80 represents 8.0 RPM.
#[test]
fn test_hollow_paddle_dryer_paddle_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "rpm_x10 == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_range",
        "rpm_x10 >= 10 && rpm_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle speed 8.0 RPM (80 x10) in [10, 200]");
}

/// Test 4: Steam pressure x10 (0.1 bar) — bounded [10, 100], value 60.
/// 60 represents 6.0 bar.
#[test]
fn test_hollow_paddle_dryer_steam_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("press_val", "press_x10 == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steam pressure 6.0 bar (60 x10) in [10, 100]");
}

/// Test 5: Product temperature offset+100 (deg C) — bounded [120, 400].
/// Represents actual range 20-300 deg C. Value 250 (actual 150 deg C).
#[test]
fn test_hollow_paddle_dryer_product_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_off == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_range",
        "temp_off >= 120 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product temperature offset+100 250 (150 C) in [120, 400]",
    );
}

/// Test 6: Shaft type — 3-way disjunction.
/// 1=single-shaft, 2=twin-shaft, 3=four-shaft. Value 2 (twin-shaft).
#[test]
fn test_hollow_paddle_dryer_shaft_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("st", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st_val", "st == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_st",
        "st == 1 || st == 2 || st == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shaft type 2 (twin-shaft) is valid 3-way disjunction",
    );
}

/// Test 7: Paddle shape — 3-way disjunction.
/// 1=wedge, 2=disc, 3=hollow-blade. Value 1 (wedge).
#[test]
fn test_hollow_paddle_dryer_paddle_shape_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ps", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ps_val", "ps == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ps",
        "ps == 1 || ps == 2 || ps == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle shape 1 (wedge) is valid 3-way disjunction");
}

/// Test 8: Heating medium — 3-way disjunction.
/// 1=steam, 2=hot-oil, 3=hot-water. Value 1 (steam).
#[test]
fn test_hollow_paddle_dryer_heating_medium_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "hm == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_hm",
        "hm == 1 || hm == 2 || hm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium 1 (steam) is valid 3-way disjunction",
    );
}

/// Test 9: Automatic moisture control — boolean flag (0 or 1), value 1 (enabled).
#[test]
fn test_hollow_paddle_dryer_auto_moisture_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_boolean",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto moisture control flag 1 is valid boolean (0 or 1)",
    );
}

/// Test 10: Throughput x10 (0.1 kg/h) — bounded [10, 50000], value 5000.
/// 5000 represents 500.0 kg/h.
#[test]
fn test_hollow_paddle_dryer_throughput_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_range",
        "rate_x10 >= 10 && rate_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 500.0 kg/h (5000 x10) in [10, 50000]");
}
