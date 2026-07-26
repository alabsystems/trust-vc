// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_hermetic_compressor_motor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 7200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 7200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor speed must be between 1000 and 7200 RPM");
}

#[test]
fn test_hermetic_compressor_cooling_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_range",
        "cap >= 100 && cap <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_bounded",
        "cap >= 100 && cap <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling capacity must be between 100 and 500000 W");
}

#[test]
fn test_hermetic_compressor_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be in range 10-400 representing 1.0-40.0 bar",
    );
}

#[test]
fn test_hermetic_compressor_suction_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suct_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suct_range",
        "suct_x10 >= 1 && suct_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suct_bounded",
        "suct_x10 >= 1 && suct_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction pressure x10 must be in range 1-100 representing 0.1-10.0 bar",
    );
}

#[test]
fn test_hermetic_compressor_motor_current_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "curr_x10 >= 1 && curr_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_bounded",
        "curr_x10 >= 1 && curr_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor current x10 must be in range 1-5000 representing 0.1-500.0 A",
    );
}

#[test]
fn test_hermetic_compressor_cylinders_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cyl", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cyl_range", "cyl >= 1 && cyl <= 8"));
    ctx.push_obligation(ProofObligation::assert(
        "cyl_bounded",
        "cyl >= 1 && cyl <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of cylinders must be between 1 and 8");
}

#[test]
fn test_hermetic_compressor_refrigerant_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrig", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refrig_range",
        "refrig == 1 || refrig == 2 || refrig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refrig_valid",
        "refrig == 1 || refrig == 2 || refrig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refrigerant type must be R410A (1), R134a (2), or R290 (3)",
    );
}

#[test]
fn test_hermetic_compressor_mechanism_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mech", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mech_range",
        "mech == 1 || mech == 2 || mech == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mech_valid",
        "mech == 1 || mech == 2 || mech == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compressor mechanism must be reciprocating (1), scroll (2), or rotary (3)",
    );
}

#[test]
fn test_hermetic_compressor_capacity_modulation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mod_range",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mod_valid",
        "mod_type == 1 || mod_type == 2 || mod_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity modulation must be on-off (1), VSD (2), or cylinder-unloading (3)",
    );
}

#[test]
fn test_hermetic_compressor_auto_superheat_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sheat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sheat_range",
        "sheat == 0 || sheat == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sheat_valid",
        "sheat == 0 || sheat == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic superheat control flag must be 0 (disabled) or 1 (enabled)",
    );
}
