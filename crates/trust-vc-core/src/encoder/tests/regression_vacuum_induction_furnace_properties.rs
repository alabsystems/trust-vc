// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_crucible_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_in_range",
        "capacity >= 10 && capacity <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crucible capacity 500 kg in [10, 5000]");
}

#[test]
fn test_melt_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 1650"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= 800 && temp <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "melt temperature 1650 C in [800, 2000]");
}

#[test]
fn test_vacuum_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vacuum_val", "vacuum == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vacuum_in_range",
        "vacuum >= 1 && vacuum <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 10 Pa in [1, 1000]");
}

#[test]
fn test_furnace_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ftype", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ftype_val", "ftype == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "ftype == 1 || ftype == 2 || ftype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "furnace type 1=coreless is valid (1|2|3)");
}

#[test]
fn test_power_supply_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("psupply", u32_ty());
    ctx.push_obligation(ProofObligation::assume("psupply_val", "psupply == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_supply",
        "psupply == 1 || psupply == 2 || psupply == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power supply 2=medium frequency is valid (1|2|3)");
}

#[test]
fn test_coil_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", u32_ty());
    ctx.push_obligation(ProofObligation::assume("voltage_val", "voltage == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "voltage >= 100 && voltage <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coil voltage 800 V in [100, 3000]");
}

#[test]
fn test_tilt_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("angle_val", "angle_x10 == 450"));
    ctx.push_obligation(ProofObligation::assert(
        "angle_in_range",
        "angle_x10 >= 0 && angle_x10 <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tilt angle 45.0 deg (x10=450) in [0, 900]");
}

#[test]
fn test_stirring_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power_x10 == 350"));
    ctx.push_obligation(ProofObligation::assert(
        "power_in_range",
        "power_x10 >= 0 && power_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stirring power 35.0% (x10=350) in [0, 1000]");
}

#[test]
fn test_cooling_water_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_range",
        "flow >= 50 && flow <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling water flow 200 L/min in [50, 500]");
}

#[test]
fn test_leak_detection_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "leak_detected",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leak detection flag is active");
}
