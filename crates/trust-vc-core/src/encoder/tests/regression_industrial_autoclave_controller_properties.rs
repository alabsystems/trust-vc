// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Chamber pressure in kPa — 700 represents 700 kPa, bounded [100, 2000].
#[test]
fn test_chamber_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 700"));
    ctx.push_obligation(ProofObligation::assert("pressure_lower", "pressure >= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_upper",
        "pressure <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber pressure 700 kPa within [100, 2000]");
}

/// Chamber temperature in degrees Celsius — 134 represents 134°C, bounded [100, 200].
#[test]
fn test_chamber_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 134"));
    ctx.push_obligation(ProofObligation::assert("temp_lower", "temp >= 100"));
    ctx.push_obligation(ProofObligation::assert("temp_upper", "temp <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber temp 134 C within [100, 200]");
}

/// Cycle time in minutes — 30 represents 30 min, bounded [3, 120].
#[test]
fn test_cycle_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_time", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cycle_val", "cycle_time == 30"));
    ctx.push_obligation(ProofObligation::assert("cycle_lower", "cycle_time >= 3"));
    ctx.push_obligation(ProofObligation::assert("cycle_upper", "cycle_time <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time 30 min within [3, 120]");
}

/// Autoclave type as 3-way disjunction: 1=gravity displacement, 2=prevacuum, 3=steam-flush.
#[test]
fn test_autoclave_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("autoclave_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "autoclave_type_valid",
        "autoclave_type == 1 || autoclave_type == 2 || autoclave_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "autoclave_type_lower",
        "autoclave_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "autoclave_type_upper",
        "autoclave_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "autoclave type disjunction {1=gravity displacement, 2=prevacuum, 3=steam-flush} implies [1, 3]",
    );
}

/// Load type as 4-way disjunction: 1=wrapped, 2=unwrapped, 3=liquid, 4=prion.
#[test]
fn test_load_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "load_type_valid",
        "load_type == 1 || load_type == 2 || load_type == 3 || load_type == 4",
    ));
    ctx.push_obligation(ProofObligation::assert("load_type_lower", "load_type >= 1"));
    ctx.push_obligation(ProofObligation::assert("load_type_upper", "load_type <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "load type disjunction {1=wrapped, 2=unwrapped, 3=liquid, 4=prion} implies [1, 4]",
    );
}

/// Chamber volume in liters — 500 represents 500L, bounded [10, 5000].
#[test]
fn test_chamber_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "volume == 500"));
    ctx.push_obligation(ProofObligation::assert("vol_lower", "volume >= 10"));
    ctx.push_obligation(ProofObligation::assert("vol_upper", "volume <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber volume 500 L within [10, 5000]");
}

/// Vacuum depth in tenths of kPa — 200 represents 20.0 kPa, bounded [10, 500].
#[test]
fn test_vacuum_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vacuum_val", "vacuum_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("vacuum_lower", "vacuum_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("vacuum_upper", "vacuum_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum depth 20.0 kPa (200) within [10, 500]");
}

/// Dry time in minutes — 20 represents 20 min, bounded [0, 60].
#[test]
fn test_dry_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_time", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dry_val", "dry_time == 20"));
    ctx.push_obligation(ProofObligation::assert("dry_lower", "dry_time >= 0"));
    ctx.push_obligation(ProofObligation::assert("dry_upper", "dry_time <= 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry time 20 min within [0, 60]");
}

/// Door type as 3-way disjunction: 1=hinged, 2=sliding, 3=radial-lock.
#[test]
fn test_door_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("door_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "door_type_valid",
        "door_type == 1 || door_type == 2 || door_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("door_type_lower", "door_type >= 1"));
    ctx.push_obligation(ProofObligation::assert("door_type_upper", "door_type <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "door type disjunction {1=hinged, 2=sliding, 3=radial-lock} implies [1, 3]",
    );
}

/// Bowie-Dick test as boolean flag — i32 flag where 1=passed, 0=failed.
#[test]
fn test_bowie_dick_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bd_flag", i32_ty());
    ctx.declare_var_typed("bd_result", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bd_flag_valid",
        "bd_flag == 0 || bd_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("bd_flag_set", "bd_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "bd_result_def",
        "bd_result == if bd_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bd_test_passed", "bd_result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Bowie-Dick test flag passed enables result");
}
