// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_rotary_airlock_valve_rotor_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter_mm == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bound",
        "diameter_mm >= 150 && diameter_mm <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Rotary airlock: 300 mm rotor diameter in [150, 800]",
    );
}

#[test]
fn test_rotary_airlock_valve_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "spd_bound",
        "speed_rpm >= 5 && speed_rpm <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary airlock: 20 RPM rotor speed in [5, 40]");
}

#[test]
fn test_rotary_airlock_valve_pocket_volume_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "volume_x100 == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_bound",
        "volume_x100 >= 50 && volume_x100 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Rotary airlock: 2.50 L pocket volume in [0.50, 20.00] (x100)",
    );
}

#[test]
fn test_rotary_airlock_valve_operating_pressure_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("prs_val", "pressure_x10 == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "prs_bound",
        "pressure_x10 >= 100 && pressure_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Rotary airlock: 150.0 kPa operating pressure in [10.0, 500.0] (x10)",
    );
}

#[test]
fn test_rotary_airlock_valve_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_w", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "power_w == 750"));
    ctx.push_obligation(ProofObligation::assert(
        "pwr_bound",
        "power_w >= 100 && power_w <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary airlock: 750 W motor power in [100, 5000]");
}

#[test]
fn test_rotary_airlock_valve_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary airlock: adjustable is valid seal type");
}

#[test]
fn test_rotary_airlock_valve_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary airlock: stainless steel is valid material");
}

#[test]
fn test_rotary_airlock_valve_operating_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bound",
        "temp >= 460 && temp <= 620",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Rotary airlock: 20 C operating temp in [-40, 120] (offset +500)",
    );
}

#[test]
fn test_rotary_airlock_valve_pocket_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pocket_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pc_val", "pocket_count == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "pc_bound",
        "pocket_count >= 6 && pocket_count <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary airlock: 8 pockets in [6, 12]");
}

#[test]
fn test_rotary_airlock_valve_explosion_proof_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "exproof_on",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary airlock: explosion proof enabled");
}
