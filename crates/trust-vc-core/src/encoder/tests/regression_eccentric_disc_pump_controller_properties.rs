// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ecc_disc_pump_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_check",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 in [1, 5000] should be bounded");
}

#[test]
fn test_ecc_disc_pump_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press >= 1 && press <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "press >= 1 && press <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure in [1, 1000] psi should be bounded");
}

#[test]
fn test_ecc_disc_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 50 && rpm <= 1750",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_check",
        "rpm >= 50 && rpm <= 1750",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed in [50, 1750] RPM should be bounded");
}

#[test]
fn test_ecc_disc_pump_viscosity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "visc_range",
        "visc >= 1 && visc <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "visc_check",
        "visc >= 1 && visc <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity in [1, 500000] cP should be bounded");
}

#[test]
fn test_ecc_disc_pump_solids_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sol_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sol_range",
        "sol_x10 >= 0 && sol_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sol_check",
        "sol_x10 >= 0 && sol_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solids x10 in [0, 600] should be bounded");
}

#[test]
fn test_ecc_disc_pump_port_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "port_range",
        "port >= 15 && port <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "port_check",
        "port >= 15 && port <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "port size in [15, 150] mm should be bounded");
}

#[test]
fn test_ecc_disc_pump_disc_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_range",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc material should be stainless, PTFE, or PEEK");
}

#[test]
fn test_ecc_disc_pump_sealing_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_range",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_check",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sealing should be single, double, or sealless");
}

#[test]
fn test_ecc_disc_pump_drive_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drv_range",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drv_check",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive should be direct, belt, or gear");
}

#[test]
fn test_ecc_disc_pump_self_priming_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sp_range", "sp == 0 || sp == 1"));
    ctx.push_obligation(ProofObligation::assert("sp_check", "sp == 0 || sp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-priming flag should be 0 or 1");
}
