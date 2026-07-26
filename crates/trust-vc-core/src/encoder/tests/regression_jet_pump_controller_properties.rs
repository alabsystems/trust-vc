// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_jet_pump_suction_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suction_flow_range",
        "flow >= 1 && flow <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suction_flow_bounded",
        "flow >= 1 && flow <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction flow 1-50000 L/min bounded");
}

#[test]
fn test_jet_pump_motive_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "motive_pressure_range",
        "press >= 10 && press <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motive_pressure_bounded",
        "press >= 10 && press <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motive pressure 10-5000 psi bounded");
}

#[test]
fn test_jet_pump_suction_lift_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lift_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suction_lift_range",
        "lift_x10 >= 10 && lift_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suction_lift_bounded",
        "lift_x10 >= 10 && lift_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction lift x10 meters bounded");
}

#[test]
fn test_jet_pump_entrainment_ratio_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "entrainment_ratio_range",
        "ratio_x100 >= 10 && ratio_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "entrainment_ratio_bounded",
        "ratio_x100 >= 10 && ratio_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "entrainment ratio x100 bounded");
}

#[test]
fn test_jet_pump_nozzle_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noz_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nozzle_diameter_range",
        "noz_x10 >= 10 && noz_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nozzle_diameter_bounded",
        "noz_x10 >= 10 && noz_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle diameter x10 mm bounded");
}

#[test]
fn test_jet_pump_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_pressure_range",
        "dp >= 1 && dp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_pressure_bounded",
        "dp >= 1 && dp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure 1-500 psi bounded");
}

#[test]
fn test_jet_pump_motive_fluid_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fluid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "motive_fluid_enum",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motive_fluid_valid",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motive fluid three-way: water, steam, air");
}

#[test]
fn test_jet_pump_construction_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("const_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "construction_enum",
        "const_mat == 1 || const_mat == 2 || const_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "construction_valid",
        "const_mat == 1 || const_mat == 2 || const_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "construction three-way: cast iron, stainless, PVDF",
    );
}

#[test]
fn test_jet_pump_configuration_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cfg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "configuration_enum",
        "cfg == 1 || cfg == 2 || cfg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "configuration_valid",
        "cfg == 1 || cfg == 2 || cfg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "configuration three-way: single stage, multi-stage, annular",
    );
}

#[test]
fn test_jet_pump_self_priming_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "self_priming_bool",
        "sp == 0 || sp == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "self_priming_valid",
        "sp == 0 || sp == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-priming boolean flag: 0 or 1");
}
