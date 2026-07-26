// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_centrifugal_refrig_evaporator_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "evap_range",
        "temp_off >= 50 && temp_off <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "evap_bounded",
        "temp_off >= 50 && temp_off <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporator temp offset+100 bounded -50 to 20 C");
}

#[test]
fn test_centrifugal_refrig_condenser_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_range",
        "temp_off >= 120 && temp_off <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cond_bounded",
        "temp_off >= 120 && temp_off <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "condenser temp offset+100 bounded 20 to 100 C");
}

#[test]
fn test_centrifugal_refrig_impeller_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 3000 && speed <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 3000 && speed <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller speed bounded 3000 to 50000 RPM");
}

#[test]
fn test_centrifugal_refrig_cooling_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_range",
        "capacity >= 100 && capacity <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_bounded",
        "capacity >= 100 && capacity <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling capacity bounded 100 to 50000 kW");
}

#[test]
fn test_centrifugal_refrig_cop_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cop_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cop_range",
        "cop_x10 >= 20 && cop_x10 <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cop_bounded",
        "cop_x10 >= 20 && cop_x10 <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "COP x10 bounded 2.0 to 8.0");
}

#[test]
fn test_centrifugal_refrig_refrigerant_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ref_enum",
        "ref_type == 1 || ref_type == 2 || ref_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ref_valid",
        "ref_type == 1 || ref_type == 2 || ref_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refrigerant type three-way R134a R1234ze R513A");
}

#[test]
fn test_centrifugal_refrig_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_enum",
        "dt == 1 || dt == 2 || dt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_valid",
        "dt == 1 || dt == 2 || dt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type three-way direct gear magnetic-bearing");
}

#[test]
fn test_centrifugal_refrig_capacity_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_enum",
        "cc == 1 || cc == 2 || cc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_valid",
        "cc == 1 || cc == 2 || cc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity control three-way inlet-guide-vane variable-speed hot-gas-bypass",
    );
}

#[test]
fn test_centrifugal_refrig_auto_surge_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto surge protection flag boolean");
}

#[test]
fn test_centrifugal_refrig_suction_superheat_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sh_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sh_range",
        "sh_x10 >= 10 && sh_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sh_bounded",
        "sh_x10 >= 10 && sh_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction superheat x10 bounded 1.0 to 20.0 K");
}
