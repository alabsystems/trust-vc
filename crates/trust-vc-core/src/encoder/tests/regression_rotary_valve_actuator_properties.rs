// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_torque_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque", u32_ty());
    ctx.push_obligation(ProofObligation::assume("torque_val", "torque == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "torque_bound",
        "torque >= 10 && torque <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: 500 Nm torque in [10, 10000]");
}

#[test]
fn test_travel_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("angle_val", "angle_x10 == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "angle_bound",
        "angle_x10 >= 0 && angle_x10 <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: 90.0 deg travel angle in [0, 360.0]");
}

#[test]
fn test_cycle_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("time_val", "time_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "time_bound",
        "time_x10 >= 10 && time_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: 5.0 s cycle time in [1.0, 60.0]");
}

#[test]
fn test_actuator_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("act_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("at_val", "act_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "act_type == 1 || act_type == 2 || act_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: pneumatic is valid actuator type");
}

#[test]
fn test_action_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("action", u32_ty());
    ctx.push_obligation(ProofObligation::assume("action_val", "action == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_action",
        "action == 1 || action == 2 || action == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: on/off is valid action type");
}

#[test]
fn test_supply_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply", u32_ty());
    ctx.push_obligation(ProofObligation::assume("supply_val", "supply == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "supply_bound",
        "supply >= 200 && supply <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Rotary valve: 600 kPa supply pressure in [200, 1000]",
    );
}

#[test]
fn test_duty_rating_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duty_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("duty_val", "duty_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "duty_bound",
        "duty_x10 >= 100 && duty_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: 100.0% duty rating in [10.0, 100.0]");
}

#[test]
fn test_signal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal", u32_ty());
    ctx.push_obligation(ProofObligation::assume("signal_val", "signal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_signal",
        "signal == 1 || signal == 2 || signal == 3 || signal == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: 4-20mA is valid signal type");
}

#[test]
fn test_operating_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 530"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bound",
        "temp >= 460 && temp <= 580",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Rotary valve: 30 C operating temp in [-40, 80] (offset +500)",
    );
}

#[test]
fn test_position_feedback_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "feedback_on",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Rotary valve: position feedback enabled");
}
