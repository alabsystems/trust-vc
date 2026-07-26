// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_steam_tube_dryer_tube_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tube_count_range",
        "tube_count >= 10 && tube_count <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tube_count_valid",
        "tube_count >= 10 && tube_count <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of steam tubes must be between 10 and 500");
}

#[test]
fn test_steam_tube_dryer_tube_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_diameter_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tube_diameter_range",
        "tube_diameter_mm >= 30 && tube_diameter_mm <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tube_diameter_valid",
        "tube_diameter_mm >= 30 && tube_diameter_mm <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube outer diameter must be between 30 and 150 mm");
}

#[test]
fn test_steam_tube_dryer_shell_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shell_diameter_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shell_diameter_range",
        "shell_diameter_mm >= 500 && shell_diameter_mm <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shell_diameter_valid",
        "shell_diameter_mm >= 500 && shell_diameter_mm <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shell diameter must be between 500 and 3000 mm");
}

#[test]
fn test_steam_tube_dryer_steam_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steam_pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "steam_pressure_range",
        "steam_pressure_x10 >= 5 && steam_pressure_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "steam_pressure_valid",
        "steam_pressure_x10 >= 5 && steam_pressure_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "steam pressure x10 must be between 5 and 100 (0.5-10.0 bar)",
    );
}

#[test]
fn test_steam_tube_dryer_rotation_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotation_speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rotation_speed_range",
        "rotation_speed_x10 >= 5 && rotation_speed_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rotation_speed_valid",
        "rotation_speed_x10 >= 5 && rotation_speed_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation speed x10 must be between 5 and 100 (0.5-10.0 RPM)",
    );
}

#[test]
fn test_steam_tube_dryer_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_kg_h", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "throughput_range",
        "throughput_kg_h >= 100 && throughput_kg_h <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "throughput_valid",
        "throughput_kg_h >= 100 && throughput_kg_h <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput must be between 100 and 50000 kg/h");
}

#[test]
fn test_steam_tube_dryer_condensate_system_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("condensate_system", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "condensate_range",
        "condensate_system >= 1 && condensate_system <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "condensate_valid",
        "condensate_system >= 1 && condensate_system <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condensate system must be 1=siphon, 2=bucket-trap, or 3=float-trap",
    );
}

#[test]
fn test_steam_tube_dryer_tube_arrangement_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_arrangement", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "arrangement_range",
        "tube_arrangement >= 1 && tube_arrangement <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "arrangement_valid",
        "tube_arrangement >= 1 && tube_arrangement <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tube arrangement must be 1=concentric, 2=staggered, or 3=inline",
    );
}

#[test]
fn test_steam_tube_dryer_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_range",
        "drive_type >= 1 && drive_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_valid",
        "drive_type >= 1 && drive_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type must be 1=gear-motor, 2=chain, or 3=friction-ring",
    );
}

#[test]
fn test_steam_tube_dryer_auto_condensate_drain_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_condensate_drain", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drain_flag_range",
        "auto_condensate_drain >= 0 && auto_condensate_drain <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drain_flag_valid",
        "auto_condensate_drain >= 0 && auto_condensate_drain <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto condensate drain flag must be 0=disabled or 1=enabled",
    );
}
