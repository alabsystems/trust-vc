// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_lyophilizer_shelf_area_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area_x10 >= 5 && area_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area_x10 >= 5 && area_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shelf area x10 must be in range 5-5000 representing 0.5-500.0 m2",
    );
}

#[test]
fn test_lyophilizer_condenser_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_range",
        "cond_off >= 400 && cond_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cond_bounded",
        "cond_off >= 400 && cond_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser temperature offset+500 must be in range 400-500 representing -100 to 0 C",
    );
}

#[test]
fn test_lyophilizer_chamber_vacuum_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vac_range",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vac_bounded",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chamber vacuum x10 must be in range 1-10000 representing 0.1-1000.0 mbar",
    );
}

#[test]
fn test_lyophilizer_shelf_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelf_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shelf_range",
        "shelf_off >= 20 && shelf_off <= 280",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shelf_bounded",
        "shelf_off >= 20 && shelf_off <= 280",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shelf temperature offset+100 must be in range 20-280 representing -80 to 180 C",
    );
}

#[test]
fn test_lyophilizer_shelves_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelves", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shelves_range",
        "shelves >= 1 && shelves <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shelves_bounded",
        "shelves >= 1 && shelves <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of shelves must be between 1 and 30");
}

#[test]
fn test_lyophilizer_sublimation_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sub_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sub_range",
        "sub_x100 >= 1 && sub_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sub_bounded",
        "sub_x100 >= 1 && sub_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sublimation rate x100 must be in range 1-10000 representing 0.01-100.00 kg/h",
    );
}

#[test]
fn test_lyophilizer_refrigeration_type_three_way() {
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
        "refrigeration type must be mechanical (1), LN2 (2), or cascade (3)",
    );
}

#[test]
fn test_lyophilizer_loading_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "load_range",
        "load == 1 || load == 2 || load == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "load_valid",
        "load == 1 || load == 2 || load == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "loading method must be manual (1), automatic (2), or stoppering (3)",
    );
}

#[test]
fn test_lyophilizer_vacuum_pump_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pump_range",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pump_valid",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vacuum pump type must be rotary-vane (1), scroll (2), or roots (3)",
    );
}

#[test]
fn test_lyophilizer_auto_cycle_optimization_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("opt_range", "opt == 0 || opt == 1"));
    ctx.push_obligation(ProofObligation::assert("opt_valid", "opt == 0 || opt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic cycle optimization flag must be 0 (disabled) or 1 (enabled)",
    );
}
