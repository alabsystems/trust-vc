// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn setpoint_error() {
    let mut ctx = VerificationContext::new();
    for v in &["setpoint_x10", "measured_x10", "error_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Error = setpoint - measured (both offset +500 for signed, ×10 for 0.1°C)
    // SP=50.0°C(1000), PV=48.5°C(985) → error=15 (1.5°C)
    ctx.push_obligation(ProofObligation::assume("sp", "setpoint_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assume("mv", "measured_x10 == 985"));
    ctx.push_obligation(ProofObligation::assume(
        "er",
        "error_x10 == setpoint_x10 - measured_x10",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "error_x10 == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: SP 50°C - PV 48.5°C = 1.5°C error");
}

#[test]
fn output_clamping() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_output", "min_output", "max_output"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("clamped_ok", i32_ty());
    // PID output clamped to [0, 1000] (0-100.0% × 10)
    ctx.push_obligation(ProofObligation::assume("ro", "raw_output == 850"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_output == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_output == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "clamped_ok == if raw_output >= min_output && raw_output <= max_output { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "clamped_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: output 850 in [0, 1000] → clamped OK");
}

#[test]
fn proportional_band() {
    let mut ctx = VerificationContext::new();
    for v in &["pb_x10", "min_pb_x10", "max_pb_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pb_ok", i32_ty());
    // Proportional band: typically 5-200°C (×10 scale)
    ctx.push_obligation(ProofObligation::assume("pb", "pb_x10 == 100")); // 10.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_pb_x10 == 50")); // 5.0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_pb_x10 == 2000")); // 200.0°C
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pb_ok == if pb_x10 >= min_pb_x10 && pb_x10 <= max_pb_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: PB 10°C in [5, 200] → OK");
}

#[test]
fn integral_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ti_sec", "min_ti_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ti_ok", i32_ty());
    // Integral time constant (seconds)
    ctx.push_obligation(ProofObligation::assume("ts", "ti_sec == 60"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_ti_sec == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "ti_ok == if ti_sec >= min_ti_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ti_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: Ti 60s ≥ 1s min → integral time OK");
}

#[test]
fn derivative_time() {
    let mut ctx = VerificationContext::new();
    for v in &["td_sec", "max_td_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("td_ok", i32_ty());
    // Derivative time constant (seconds)
    ctx.push_obligation(ProofObligation::assume("ts", "td_sec == 15"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_td_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "td_ok == if td_sec <= max_td_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "td_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: Td 15s ≤ 120s max → derivative time OK");
}

#[test]
fn heater_duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["heater_pct", "max_heater_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("heater_ok", i32_ty());
    // Heater output duty cycle
    ctx.push_obligation(ProofObligation::assume("hp", "heater_pct == 85"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_heater_pct == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "heater_ok == if heater_pct <= max_heater_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "heater_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: 85% heater ≤ 100% max → OK");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_ms", "min_cycle_ms", "max_cycle_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // PID calculation cycle time
    ctx.push_obligation(ProofObligation::assume("cm", "cycle_ms == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycle_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycle_ms == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_ms >= min_cycle_ms && cycle_ms <= max_cycle_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: 250ms cycle in [50, 2000] → OK");
}

#[test]
fn alarm_high() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_x10", "alarm_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm_active", i32_ty());
    // High temperature alarm (offset +500)
    ctx.push_obligation(ProofObligation::assume("tx", "temp_x10 == 1250")); // 75.0°C
    ctx.push_obligation(ProofObligation::assume("ax", "alarm_x10 == 1200")); // 70.0°C
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if temp_x10 >= alarm_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: 75°C ≥ 70°C alarm → active");
}

#[test]
fn anti_windup() {
    let mut ctx = VerificationContext::new();
    for v in &["integral_sum", "max_integral"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("windup_ok", i32_ty());
    // Anti-windup: clamp integral accumulator
    ctx.push_obligation(ProofObligation::assume("is", "integral_sum == 5000"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_integral == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "windup_ok == if integral_sum <= max_integral { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "windup_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: integral 5000 ≤ 10000 max → no windup");
}

#[test]
fn control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("is_auto", i32_ty());
    // Control modes: 0=manual, 1=auto (PID), 2=cascade, 3=ratio
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_auto == if mode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_auto == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PID temp: mode=1 → auto PID control");
}
