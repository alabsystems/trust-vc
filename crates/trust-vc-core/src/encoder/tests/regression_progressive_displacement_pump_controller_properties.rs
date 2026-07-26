// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_pd_pump_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x10 >= 1 && disp_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disp_bounded",
        "disp_x10 >= 1 && disp_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement x10 cc/rev bounded [1, 50000]");
}

#[test]
fn test_pd_pump_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 L/min bounded [1, 10000]");
}

#[test]
fn test_pd_pump_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press >= 10 && press <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press >= 10 && press <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure psi bounded [10, 5000]");
}

#[test]
fn test_pd_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 50 && rpm <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 50 && rpm <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed RPM bounded [50, 3000]");
}

#[test]
fn test_pd_pump_viscosity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "visc_range",
        "visc >= 1 && visc <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "visc_bounded",
        "visc >= 1 && visc <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity cP bounded [1, 1000000]");
}

#[test]
fn test_pd_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "eff_x10 >= 500 && eff_x10 <= 980",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eff_bounded",
        "eff_x10 >= 500 && eff_x10 <= 980",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency x10 percent bounded [500, 980]");
}

#[test]
fn test_pd_pump_rotor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rotor_enum",
        "rotor == 1 || rotor == 2 || rotor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rotor_valid",
        "rotor == 1 || rotor == 2 || rotor == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor type three-way: gear, lobe, screw");
}

#[test]
fn test_pd_pump_seal_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_enum",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seal type three-way: lip, mechanical, mag drive");
}

#[test]
fn test_pd_pump_relief_valve_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rv_enum",
        "rv == 1 || rv == 2 || rv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rv_valid",
        "rv == 1 || rv == 2 || rv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "relief valve three-way: internal, external, none");
}

#[test]
fn test_pd_pump_heated_jacket_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hj", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hj_bool", "hj == 0 || hj == 1"));
    ctx.push_obligation(ProofObligation::assert("hj_valid", "hj == 0 || hj == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heated jacket boolean flag: 0 or 1");
}
