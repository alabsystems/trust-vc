// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Max temperature in degrees Celsius — 500 represents 500°C, bounded [50, 3000].
#[test]
fn test_max_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "chamber_temp == 500"));
    ctx.push_obligation(ProofObligation::assert("temp_lower", "chamber_temp >= 50"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_upper",
        "chamber_temp <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber temp 500 C within [50, 3000]");
}

/// Temperature uniformity in tenths of a degree — 30 represents 3.0°C variation, bounded [5, 200].
#[test]
fn test_temperature_uniformity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("variation", u32_ty());
    ctx.push_obligation(ProofObligation::assume("var_val", "variation == 30"));
    ctx.push_obligation(ProofObligation::assert("var_lower", "variation >= 5"));
    ctx.push_obligation(ProofObligation::assert("var_upper", "variation <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temperature uniformity 3.0 C (30) within [5, 200]");
}

/// Heating element type as 3-way disjunction: 1=resistance, 2=gas, 3=infrared.
#[test]
fn test_heating_element_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("element_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "element_type_valid",
        "element_type == 1 || element_type == 2 || element_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "element_type_lower",
        "element_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "element_type_upper",
        "element_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating element disjunction {1=resistance, 2=gas, 3=infrared} implies [1, 3]",
    );
}

/// Chamber volume in liters — 500 represents 500L, bounded [10, 50000].
#[test]
fn test_chamber_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("internal_vol", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "internal_vol == 500"));
    ctx.push_obligation(ProofObligation::assert("vol_lower", "internal_vol >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_upper",
        "internal_vol <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber volume 500 L within [10, 50000]");
}

/// Ramp rate in tenths of degrees per minute — 50 represents 5.0°C/min, bounded [5, 500].
#[test]
fn test_ramp_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ramp_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ramp_val", "ramp_rate == 50"));
    ctx.push_obligation(ProofObligation::assert("ramp_lower", "ramp_rate >= 5"));
    ctx.push_obligation(ProofObligation::assert("ramp_upper", "ramp_rate <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ramp rate 5.0 C/min (50) within [5, 500]");
}

/// Atmosphere type as 4-way disjunction: 1=air, 2=nitrogen, 3=vacuum, 4=hydrogen.
#[test]
fn test_atmosphere_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atmosphere", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atmosphere_valid",
        "atmosphere == 1 || atmosphere == 2 || atmosphere == 3 || atmosphere == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atmosphere_lower",
        "atmosphere >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atmosphere_upper",
        "atmosphere <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atmosphere type disjunction {1=air, 2=nitrogen, 3=vacuum, 4=hydrogen} implies [1, 4]",
    );
}

/// Zone count — 3 temperature zones, bounded [1, 12].
#[test]
fn test_zone_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("zone_val", "zone_count == 3"));
    ctx.push_obligation(ProofObligation::assert("zone_lower", "zone_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("zone_upper", "zone_count <= 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zone count 3 within [1, 12]");
}

/// Safety class as 3-way disjunction: 1=class A, 2=class B, 3=class C.
#[test]
fn test_safety_class_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safety_class", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "safety_class_valid",
        "safety_class == 1 || safety_class == 2 || safety_class == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "safety_class_lower",
        "safety_class >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "safety_class_upper",
        "safety_class <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "safety class disjunction {1=class A, 2=class B, 3=class C} implies [1, 3]",
    );
}

/// Door interlock as boolean flag — i32 flag where 1=engaged, 0=disengaged.
#[test]
fn test_door_interlock_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("door_interlock", i32_ty());
    ctx.declare_var_typed("heater_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "interlock_flag",
        "door_interlock == 0 || door_interlock == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "interlock_active",
        "door_interlock == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "heater_def",
        "heater_enabled == if door_interlock == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heater_on_when_locked",
        "heater_enabled == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "door interlock engaged enables heater");
}

/// Cooling method as 3-way disjunction: 1=natural, 2=forced air, 3=water quench.
#[test]
fn test_cooling_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooling_method_valid",
        "cooling_method == 1 || cooling_method == 2 || cooling_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_method_lower",
        "cooling_method >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_method_upper",
        "cooling_method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method disjunction {1=natural, 2=forced air, 3=water quench} implies [1, 3]",
    );
}
