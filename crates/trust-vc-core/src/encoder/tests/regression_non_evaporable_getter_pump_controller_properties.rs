// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_neg_pump_activation_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("act_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "act_temp >= 200 && act_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "act_temp >= 200 && act_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "activation temperature in [200, 500] C");
}

#[test]
fn test_neg_pump_sorption_capacity_torr_l_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sc_a",
        "capacity >= 1 && capacity <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sc_c",
        "capacity >= 1 && capacity <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sorption capacity in [1, 100000] Torr*L");
}

#[test]
fn test_neg_pump_base_pressure_x1000000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bp_x1e6", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bp_a",
        "bp_x1e6 >= 1 && bp_x1e6 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bp_c",
        "bp_x1e6 >= 1 && bp_x1e6 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "base pressure x1e6 in [1, 1000] representing 1e-12 to 1e-9 Torr",
    );
}

#[test]
fn test_neg_pump_surface_area_cm2_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_cm2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sa_a",
        "area_cm2 >= 10 && area_cm2 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sa_c",
        "area_cm2 >= 10 && area_cm2 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "getter surface area in [10, 100000] cm^2");
}

#[test]
fn test_neg_pump_activation_cycles_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycles", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ac_a",
        "cycles >= 1 && cycles <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ac_c",
        "cycles >= 1 && cycles <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "activation cycles in [1, 1000]");
}

#[test]
fn test_neg_pump_heating_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hr_a",
        "heat_rate >= 1 && heat_rate <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hr_c",
        "heat_rate >= 1 && heat_rate <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating rate in [1, 100] C/min");
}

#[test]
fn test_neg_pump_alloy_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alloy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "al_a",
        "alloy == 1 || alloy == 2 || alloy == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "al_c",
        "alloy == 1 || alloy == 2 || alloy == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alloy: ZrVFe (St707), ZrAl (St101), or TiZrV");
}

#[test]
fn test_neg_pump_form_factor_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("form", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ff_a",
        "form == 1 || form == 2 || form == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ff_c",
        "form == 1 || form == 2 || form == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "form: strip cartridge, disk module, or thin film coating",
    );
}

#[test]
fn test_neg_pump_heating_method_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hm_a",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hm_c",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating: resistive heater, RF induction, or electron bombardment",
    );
}

#[test]
fn test_neg_pump_passive_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("passive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pm_a",
        "passive == 0 || passive == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pm_c",
        "passive == 0 || passive == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "passive (room-temp) mode flag is boolean");
}
