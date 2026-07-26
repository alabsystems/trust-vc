// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_ahu_air_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow >= 1000 && flow <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow 20000 m3/h within [1000, 100000]");
}

#[test]
fn test_ahu_supply_temp_setpoint_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 522"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 490 && temp <= 540",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply temp setpoint 522 (22C offset+500) within [490, 540]",
    );
}

#[test]
fn test_ahu_filter_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("filter_val", "filter_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "filter_valid",
        "filter_type == 1 || filter_type == 2 || filter_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter type 2 (bag) is one of panel/bag/HEPA");
}

#[test]
fn test_ahu_cooling_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cooling_val", "cooling == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_bounded",
        "cooling >= 5 && cooling <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling capacity 100 kW within [5, 1000]");
}

#[test]
fn test_ahu_heating_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating", i32_ty());
    ctx.push_obligation(ProofObligation::assume("heating_val", "heating == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "heating_bounded",
        "heating >= 5 && heating <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating capacity 80 kW within [5, 500]");
}

#[test]
fn test_ahu_fan_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fan_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fan_val", "fan_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "fan_valid",
        "fan_type == 1 || fan_type == 2 || fan_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fan type 1 (centrifugal) is one of centrifugal/plug/axial",
    );
}

#[test]
fn test_ahu_humidity_setpoint_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rh_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rh_val", "rh_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "rh_bounded",
        "rh_x10 >= 200 && rh_x10 <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "humidity setpoint 500 (50.0% x10) within [200, 800]",
    );
}

#[test]
fn test_ahu_static_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 50 && pressure <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "static pressure 500 Pa within [50, 2500]");
}

#[test]
fn test_ahu_control_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control mode 3 (demand control) is one of CV/VV/DC",
    );
}

#[test]
fn test_ahu_heat_recovery_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "recovery_enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat recovery flag=1 means recovery is enabled");
}
