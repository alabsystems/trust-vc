// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_phase_current_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "min_ma", "max_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("current_val", "current_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_ma == 100"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_ma == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "current_in_range",
        "current_ma >= min_ma && current_ma <= max_ma",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "phase current 2000 mA in [100, 10000]");
}

#[test]
fn test_microstep_resolution_four_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steps_per_rev", u32_ty());
    ctx.push_obligation(ProofObligation::assume("steps_val", "steps_per_rev == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_resolution",
        "steps_per_rev == 200 || steps_per_rev == 400 || steps_per_rev == 3200 || steps_per_rev == 51200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "microstep resolution 200 is valid (200/400/3200/51200)",
    );
}

#[test]
fn test_supply_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_mv", "max_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "voltage_val",
        "voltage_mv == 24000",
    ));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_mv == 80000"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "voltage_mv >= min_mv && voltage_mv <= max_mv",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "supply voltage 24000 mV (24V) in [12000, 80000]");
}

#[test]
fn test_step_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_hz", "max_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq_hz == 200000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_hz == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "freq_in_range",
        "freq_hz >= min_hz && freq_hz <= max_hz",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "step frequency 200000 Hz in [1000, 500000]");
}

#[test]
fn test_motor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "motor_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "motor_type == 1 || motor_type == 2 || motor_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor type 1 (bipolar) is valid (1=bipolar/2=unipolar/3=hybrid)",
    );
}

#[test]
fn test_holding_torque_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["torque_mnm", "min_mnm", "max_mnm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("torque_val", "torque_mnm == 500"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_mnm == 10"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_mnm == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "torque_in_range",
        "torque_mnm >= min_mnm && torque_mnm <= max_mnm",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "holding torque 500 mNm in [10, 20000]");
}

#[test]
fn test_driver_mode_four_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("driver_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "driver_mode == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "driver_mode == 1 || driver_mode == 2 || driver_mode == 3 || driver_mode == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "driver mode 3 (microstep) is valid (1=full/2=half/3=micro/4=closed-loop)",
    );
}

#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: value 525 = 25C, min 460 = -40C, max 585 = 85C
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_offset == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp_offset >= min_offset && temp_offset <= max_offset",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 525 (25C+500) in [460 (-40C), 585 (85C)]",
    );
}

#[test]
fn test_stall_detection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stall_detected", i32_ty());
    ctx.declare_var_typed("motor_response", u32_ty());
    ctx.push_obligation(ProofObligation::assume("stall_val", "stall_detected == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "response_def",
        "motor_response == if stall_detected == 1 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motor_stopped",
        "motor_response == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stall detected (flag=1) stops motor (response=0)");
}

#[test]
fn test_decay_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decay_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("decay_val", "decay_mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_decay",
        "decay_mode == 1 || decay_mode == 2 || decay_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "decay mode 2 (fast) is valid (1=slow/2=fast/3=mixed)",
    );
}
