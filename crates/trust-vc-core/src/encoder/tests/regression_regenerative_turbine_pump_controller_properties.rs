// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_regen_pump_head_pressure_kpa_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_kpa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hp_a",
        "head_kpa >= 10 && head_kpa <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hp_c",
        "head_kpa >= 10 && head_kpa <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head pressure in [10, 3000] kPa");
}

#[test]
fn test_regen_pump_flow_rate_lpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_lpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "flow_lpm >= 1 && flow_lpm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "flow_lpm >= 1 && flow_lpm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate in [1, 500] L/min");
}

#[test]
fn test_regen_pump_impeller_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "is_a",
        "imp_rpm >= 500 && imp_rpm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_c",
        "imp_rpm >= 500 && imp_rpm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller speed in [500, 10000] RPM");
}

#[test]
fn test_regen_pump_fluid_viscosity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fv_a",
        "visc_x100 >= 10 && visc_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fv_c",
        "visc_x100 >= 10 && visc_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "viscosity x100 in [10, 100000] representing 0.10-1000.00 cP",
    );
}

#[test]
fn test_regen_pump_power_w_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_w", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_a",
        "power_w >= 10 && power_w <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_c",
        "power_w >= 10 && power_w <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power in [10, 50000] W");
}

#[test]
fn test_regen_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ef_a",
        "eff_x10 >= 100 && eff_x10 <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ef_c",
        "eff_x10 >= 100 && eff_x10 <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "efficiency x10 in [100, 700] representing 10.0-70.0%",
    );
}

#[test]
fn test_regen_pump_impeller_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "it_a",
        "imp_type == 1 || imp_type == 2 || imp_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "it_c",
        "imp_type == 1 || imp_type == 2 || imp_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller: open vane, semi-open, or closed channel");
}

#[test]
fn test_regen_pump_seal_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sl_a",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sl_c",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seal: mechanical, magnetic drive, or canned motor");
}

#[test]
fn test_regen_pump_application_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("application", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ap_a",
        "application == 1 || application == 2 || application == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ap_c",
        "application == 1 || application == 2 || application == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "application: boiler feed, fuel transfer, or chemical dosing",
    );
}

#[test]
fn test_regen_pump_self_priming_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("self_prime", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "self_prime == 0 || self_prime == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "self_prime == 0 || self_prime == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-priming flag is boolean");
}
