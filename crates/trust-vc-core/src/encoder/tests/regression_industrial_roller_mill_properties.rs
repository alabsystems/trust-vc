// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Roll diameter in millimeters — bounded within [100, 1500].
#[test]
fn test_roll_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diameter_val", "diameter == 500"));
    ctx.push_obligation(ProofObligation::assert("diameter_lower", "diameter >= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_upper",
        "diameter <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roll diameter 500 mm within [100, 1500]");
}

/// Roll length in millimeters — bounded within [200, 3000].
#[test]
fn test_roll_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", u32_ty());
    ctx.push_obligation(ProofObligation::assume("length_val", "length == 1200"));
    ctx.push_obligation(ProofObligation::assert("length_lower", "length >= 200"));
    ctx.push_obligation(ProofObligation::assert("length_upper", "length <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roll length 1200 mm within [200, 3000]");
}

/// Roll speed in RPM — bounded within [10, 500].
#[test]
fn test_roll_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 150"));
    ctx.push_obligation(ProofObligation::assert("speed_lower", "speed >= 10"));
    ctx.push_obligation(ProofObligation::assert("speed_upper", "speed <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roll speed 150 RPM within [10, 500]");
}

/// Mill type as 3-way disjunction: 1=two-high, 2=three-roll, 3=four-high.
#[test]
fn test_mill_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mill_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mill_type_valid",
        "mill_type == 1 || mill_type == 2 || mill_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mill_type_lower", "mill_type >= 1"));
    ctx.push_obligation(ProofObligation::assert("mill_type_upper", "mill_type <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mill type disjunction {1=two-high, 2=three-roll, 3=four-high} implies [1, 3]",
    );
}

/// Feed rate in kg/h — bounded within [50, 20000].
#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed == 2000"));
    ctx.push_obligation(ProofObligation::assert("feed_lower", "feed >= 50"));
    ctx.push_obligation(ProofObligation::assert("feed_upper", "feed <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 2000 kg/h within [50, 20000]");
}

/// Gap setting as x100 mm — 50 represents 0.50 mm, bounded within [1, 500].
#[test]
fn test_gap_setting_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gap_val", "gap_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert("gap_lower", "gap_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("gap_upper", "gap_x100 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gap setting 0.50 mm (50) within [1, 500]");
}

/// Roll material as 3-way disjunction: 1=chilled iron, 2=chrome steel, 3=ceramic.
#[test]
fn test_roll_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("material_lower", "material >= 1"));
    ctx.push_obligation(ProofObligation::assert("material_upper", "material <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "roll material disjunction {1=chilled iron, 2=chrome steel, 3=ceramic} implies [1, 3]",
    );
}

/// Motor power in kW — bounded within [10, 2000].
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", u32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 200"));
    ctx.push_obligation(ProofObligation::assert("power_lower", "power >= 10"));
    ctx.push_obligation(ProofObligation::assert("power_upper", "power <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 200 kW within [10, 2000]");
}

/// Nip angle as x10 degrees — 150 represents 15.0 degrees, bounded within [50, 300].
#[test]
fn test_nip_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nip_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("nip_val", "nip_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("nip_lower", "nip_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("nip_upper", "nip_x10 <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nip angle 15.0 deg (150) within [50, 300]");
}

/// Roll cooling as boolean flag — i32 flag where 1=enabled, 0=disabled.
#[test]
fn test_roll_cooling_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("cooling_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cooling_def",
        "cooling_active == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cooling_on", "cooling_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roll cooling flag=1 implies cooling active");
}
