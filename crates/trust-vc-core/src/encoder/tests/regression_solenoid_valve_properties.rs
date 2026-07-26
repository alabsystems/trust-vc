// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn coil_energized() {
    let mut ctx = VerificationContext::new();
    for v in &["coil_voltage_mv", "min_pull_in_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valve_open", i32_ty());
    // Solenoid opens when coil voltage exceeds pull-in threshold
    ctx.push_obligation(ProofObligation::assume("cv", "coil_voltage_mv == 24000")); // 24V
    ctx.push_obligation(ProofObligation::assume("mp", "min_pull_in_mv == 19200")); // 80% of 24V
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valve_open == if coil_voltage_mv >= min_pull_in_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valve_open == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: 24V ≥ 19.2V pull-in → valve open");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["response_ms", "max_response_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fast_enough", i32_ty());
    // Response time: energize to full open
    ctx.push_obligation(ProofObligation::assume("rm", "response_ms == 15"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_response_ms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "fast_enough == if response_ms <= max_response_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fast_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: 15ms ≤ 20ms max response → fast enough");
}

#[test]
fn pressure_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["system_pressure_kpa", "valve_rating_kpa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_rating", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sp", "system_pressure_kpa == 500"));
    ctx.push_obligation(ProofObligation::assume("vr", "valve_rating_kpa == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "wr_def",
        "within_rating == if system_pressure_kpa <= valve_rating_kpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_rating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Solenoid: 500 kPa ≤ 1000 kPa rating → within rating",
    );
}

#[test]
fn duty_cycle_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["on_time_ms", "cycle_time_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_percent", u32_ty());
    ctx.declare_var_typed("duty_ok", i32_ty());
    // Duty cycle limit for thermal protection. Precompute: 500/1000 × 100 = 50%
    ctx.push_obligation(ProofObligation::assume("ot", "on_time_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("ct", "cycle_time_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("dp", "duty_percent == 50")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_percent <= 80 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "duty_percent == 50"));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: 50% duty ≤ 80% limit → OK");
}

#[test]
fn hold_current() {
    let mut ctx = VerificationContext::new();
    for v in &["pull_in_current_ma", "hold_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("reduced", i32_ty());
    // PWM current reduction: hold current < pull-in current
    ctx.push_obligation(ProofObligation::assume("pi", "pull_in_current_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume("hc", "hold_current_ma == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "reduced == if hold_current_ma < pull_in_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "reduced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Solenoid: hold 500mA < 2000mA pull-in → current reduced",
    );
}

#[test]
fn cycle_count_life() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_count", "rated_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    // Solenoid life: typically 10M-100M cycles
    ctx.push_obligation(ProofObligation::assume("cc", "cycle_count == 5000000")); // 5M
    ctx.push_obligation(ProofObligation::assume("rc", "rated_cycles == 10000000")); // 10M
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if cycle_count < rated_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: 5M cycles < 10M rated → within life");
}

#[test]
fn flyback_diode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_flyback", u32_ty());
    ctx.declare_var_typed("protection_ok", i32_ty());
    // Flyback diode required for inductive load protection
    ctx.push_obligation(ProofObligation::assume("hf", "has_flyback == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "protection_ok == if has_flyback == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "protection_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: flyback diode present → protection OK");
}

#[test]
fn flow_coefficient() {
    let mut ctx = VerificationContext::new();
    for v in &["required_cv", "valve_cv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cv_adequate", i32_ty());
    // Cv (flow coefficient): valve Cv must exceed system requirement
    ctx.push_obligation(ProofObligation::assume("rc", "required_cv == 15")); // scaled ×10
    ctx.push_obligation(ProofObligation::assume("vc", "valve_cv == 25")); // scaled ×10
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cv_adequate == if valve_cv >= required_cv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cv_adequate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: Cv 2.5 ≥ 1.5 required → adequate");
}

#[test]
fn ambient_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["ambient_temp_c", "max_ambient_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("at", "ambient_temp_c == 40"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_ambient_c == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if ambient_temp_c <= max_ambient_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: 40°C ≤ 60°C max ambient → OK");
}

#[test]
fn normally_open_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_type", u32_ty());
    ctx.declare_var_typed("coil_state", u32_ty());
    ctx.declare_var_typed("flow_allowed", i32_ty());
    // NO valve: flow when de-energized (coil_state=0), blocked when energized (1)
    ctx.push_obligation(ProofObligation::assume("vt", "valve_type == 1")); // 1=NO
    ctx.push_obligation(ProofObligation::assume("cs", "coil_state == 0")); // de-energized
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "flow_allowed == if valve_type == 1 && coil_state == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_allowed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Solenoid: NO valve + de-energized → flow allowed");
}
