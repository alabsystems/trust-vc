// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn chilled_water_temperature_offset_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_off_range",
        "temp_off >= 96 && temp_off <= 116",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_off_valid",
        "temp_off >= 96 && temp_off <= 116",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chilled water temperature offset +100 in [96, 116] representing -4 to 16 deg C",
    );
}

#[test]
fn motor_speed_rpm_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_valid",
        "speed >= 1000 && speed <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor speed RPM in [1000, 15000]");
}

#[test]
fn cooling_capacity_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_range",
        "capacity_x10 >= 100 && capacity_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_valid",
        "capacity_x10 >= 100 && capacity_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling capacity x10 kW in [100, 50000] representing 10.0-5000.0 kW",
    );
}

#[test]
fn condenser_pressure_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 50 && press_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_valid",
        "press_x10 >= 50 && press_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser pressure x10 bar in [50, 300] representing 5.0-30.0 bar",
    );
}

#[test]
fn evaporator_pressure_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "evap_range",
        "evap_x10 >= 10 && evap_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "evap_valid",
        "evap_x10 >= 10 && evap_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "evaporator pressure x10 bar in [10, 100] representing 1.0-10.0 bar",
    );
}

#[test]
fn cop_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cop_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cop_range",
        "cop_x100 >= 200 && cop_x100 <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cop_valid",
        "cop_x100 >= 200 && cop_x100 <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "COP x100 in [200, 800] representing 2.00-8.00");
}

#[test]
fn refrigerant_three_way_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrig", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refrig_enum",
        "refrig == 1 || refrig == 2 || refrig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refrig_valid",
        "refrig == 1 || refrig == 2 || refrig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refrigerant selection R134a/R513A/R1234ze as 1/2/3",
    );
}

#[test]
fn impeller_type_three_way_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impeller_enum",
        "impeller == 1 || impeller == 2 || impeller == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impeller_valid",
        "impeller == 1 || impeller == 2 || impeller == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller type open/semi-open/shrouded as 1/2/3");
}

#[test]
fn capacity_control_three_way_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_enum",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_valid",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capacity control inlet-vane/VFD/hybrid as 1/2/3");
}

#[test]
fn auto_surge_protection_boolean() {
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
    expect_verified(&result, "auto surge protection boolean flag 0 or 1");
}
