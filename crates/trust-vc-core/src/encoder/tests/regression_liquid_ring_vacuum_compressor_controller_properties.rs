// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_liquid_ring_suction_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suction_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "suction_x10 >= 1 && suction_x10 <= 10130",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "suction_x10 >= 1 && suction_x10 <= 10130",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor suction pressure x10 bounded",
    );
}

#[test]
fn test_liquid_ring_seal_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "seal_temp >= 110 && seal_temp <= 170",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "seal_temp >= 110 && seal_temp <= 170",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor seal temp offset bounded",
    );
}

#[test]
fn test_liquid_ring_motor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ms_a",
        "speed >= 300 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ms_c",
        "speed >= 300 && speed <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid ring vacuum compressor motor speed bounded");
}

#[test]
fn test_liquid_ring_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disp_x10 >= 10 && disp_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disp_x10 >= 10 && disp_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor displacement x10 bounded",
    );
}

#[test]
fn test_liquid_ring_seal_flow_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sf_a",
        "flow_x100 >= 1 && flow_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sf_c",
        "flow_x100 >= 1 && flow_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor seal flow x100 bounded",
    );
}

#[test]
fn test_liquid_ring_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_a",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_c",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid ring vacuum compressor power x10 bounded");
}

#[test]
fn test_liquid_ring_seal_liquid_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liquid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lt_a",
        "liquid == 1 || liquid == 2 || liquid == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lt_c",
        "liquid == 1 || liquid == 2 || liquid == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor seal liquid three-way disjunction",
    );
}

#[test]
fn test_liquid_ring_impeller_design_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "id_a",
        "impeller == 1 || impeller == 2 || impeller == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "id_c",
        "impeller == 1 || impeller == 2 || impeller == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor impeller design three-way disjunction",
    );
}

#[test]
fn test_liquid_ring_capacity_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor capacity control three-way disjunction",
    );
}

#[test]
fn test_liquid_ring_auto_cavitation_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("cp_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid ring vacuum compressor auto cavitation protection flag",
    );
}
