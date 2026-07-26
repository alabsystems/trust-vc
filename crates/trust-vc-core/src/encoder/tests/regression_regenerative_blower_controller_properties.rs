// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_regen_blower_airflow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_range",
        "flow >= 50 && flow <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_check",
        "flow >= 50 && flow <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "airflow 50-5000 CFM bounded");
}

#[test]
fn test_regen_blower_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "press_x10 >= 10 && press_x10 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_check",
        "press_x10 >= 10 && press_x10 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure x10 inches WC bounded");
}

#[test]
fn test_regen_blower_motor_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "pwr_x10 >= 5 && pwr_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_check",
        "pwr_x10 >= 5 && pwr_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power x10 HP bounded");
}

#[test]
fn test_regen_blower_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "rpm >= 1000 && rpm <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "rpm >= 1000 && rpm <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 1000-3600 RPM bounded");
}

#[test]
fn test_regen_blower_inlet_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_range",
        "inlet >= 25 && inlet <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_check",
        "inlet >= 25 && inlet <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet size 25-200mm bounded");
}

#[test]
fn test_regen_blower_noise_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise >= 50 && noise <= 95",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "noise_check",
        "noise >= 50 && noise <= 95",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise level 50-95 dB bounded");
}

#[test]
fn test_regen_blower_impeller_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impeller_type",
        "imp == 1 || imp == 2 || imp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impeller_check",
        "imp == 1 || imp == 2 || imp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller type three-way (single/dual/multi-stage)");
}

#[test]
fn test_regen_blower_mounting_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mnt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mounting_type",
        "mnt == 1 || mnt == 2 || mnt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mounting_check",
        "mnt == 1 || mnt == 2 || mnt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mounting type three-way (base/flange/inline)");
}

#[test]
fn test_regen_blower_motor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mot", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "motor_type",
        "mot == 1 || mot == 2 || mot == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motor_check",
        "mot == 1 || mot == 2 || mot == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor type three-way (TEFC/explosion-proof/inverter duty)",
    );
}

#[test]
fn test_regen_blower_silencer_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "silencer_flag",
        "sil == 0 || sil == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "silencer_check",
        "sil == 0 || sil == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "silencer boolean flag (0 or 1)");
}
