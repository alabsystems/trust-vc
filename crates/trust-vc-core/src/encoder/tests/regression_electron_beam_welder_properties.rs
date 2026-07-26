// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Electron beam welder (EBW) parameter verification.
// Validates safety-critical bounds, enumerated configurations,
// and boolean interlock flags for an EBW control system.

#[test]
fn accelerating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_kv >= 30 && voltage_kv <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert("voltage_nonneg", "voltage_kv >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accelerating voltage in [30, 200] kV implies non-negative",
    );
}

#[test]
fn beam_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_ma", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current_ma >= 1 && current_ma <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_positive",
        "current_ma >= 1 && current_ma <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam current in [1, 1000] mA is strictly positive and bounded",
    );
}

#[test]
fn beam_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_kw >= 1 && power_kw <= 100",
    ));
    // Power must be at least 1 kW and cannot exceed 100 kW safety limit
    ctx.push_obligation(ProofObligation::assert(
        "power_within_safety_limit",
        "power_kw >= 1 && power_kw <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam power in [1, 100] kW stays within safety envelope",
    );
}

#[test]
fn vacuum_level_bounded() {
    // Vacuum level encoded as integer ×100 mbar (e.g., 0.01 mbar → 1)
    // Range: [1, 10000] representing 0.01 to 100.00 mbar
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vacuum_range",
        "vacuum_x100 >= 1 && vacuum_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vacuum_positive",
        "vacuum_x100 >= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vacuum level (×100 mbar) in [1, 10000] is positive",
    );
}

#[test]
fn gun_type_disjunction() {
    // Gun type: 1=thermionic, 2=plasma cathode, 3=field emission
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gun_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gun_type_valid",
        "gun_type == 1 || gun_type == 2 || gun_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gun_type_in_range",
        "gun_type >= 1 && gun_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gun type {thermionic, plasma cathode, field emission} implies [1, 3]",
    );
}

#[test]
fn weld_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_mm_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed_mm_min >= 10 && speed_mm_min <= 5000",
    ));
    // Weld speed must remain within operational window
    ctx.push_obligation(ProofObligation::assert(
        "speed_positive_and_bounded",
        "speed_mm_min >= 1 && speed_mm_min <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "weld speed in [10, 5000] mm/min implies positive and bounded",
    );
}

#[test]
fn focus_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("focus_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "focus_range",
        "focus_mm >= 1 && focus_mm <= 300",
    ));
    // Focus depth must be positive and not exceed maximum penetration depth
    ctx.push_obligation(ProofObligation::assert(
        "focus_within_limits",
        "focus_mm >= 1 && focus_mm <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "focus depth in [1, 300] mm stays within penetration limits",
    );
}

#[test]
fn chamber_size_disjunction() {
    // Chamber size: 1=small (<1m³), 2=medium (1–10m³), 3=large (>10m³)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_size", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "chamber_size_valid",
        "chamber_size == 1 || chamber_size == 2 || chamber_size == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "chamber_size_in_range",
        "chamber_size >= 1 && chamber_size <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chamber size {small, medium, large} implies [1, 3]",
    );
}

#[test]
fn beam_deflection_disjunction() {
    // Beam deflection: 1=electromagnetic, 2=electrostatic, 3=hybrid
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deflection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deflection_valid",
        "deflection == 1 || deflection == 2 || deflection == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deflection_in_range",
        "deflection >= 1 && deflection <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam deflection {electromagnetic, electrostatic, hybrid} implies [1, 3]",
    );
}

#[test]
fn xray_shielding_boolean_flag() {
    // X-ray shielding interlock: 0=disabled, 1=enabled (i32 boolean flag)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shielding", i32_ty());
    ctx.declare_var_typed("beam_allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shielding_is_boolean",
        "shielding == 0 || shielding == 1",
    ));
    // Beam is only allowed when shielding is active
    ctx.push_obligation(ProofObligation::assume(
        "interlock",
        "beam_allowed == if shielding == 1 { 1 } else { 0 }",
    ));
    // With shielding enabled, beam must be allowed
    ctx.push_obligation(ProofObligation::assume("shielding_on", "shielding == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "beam_permitted",
        "beam_allowed == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "X-ray shielding enabled implies beam is permitted");
}
