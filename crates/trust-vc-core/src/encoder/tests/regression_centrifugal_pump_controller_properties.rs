// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_flow_rate_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate", "flow_min", "flow_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flow_rate_val", "flow_rate == 500"));
    ctx.push_obligation(ProofObligation::assume("flow_min_val", "flow_min == 10"));
    ctx.push_obligation(ProofObligation::assume("flow_max_val", "flow_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_range",
        "flow_rate >= flow_min && flow_rate <= flow_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 500 L/min within [10, 50000]");
}

#[test]
fn test_head_pressure_discharge() {
    let mut ctx = VerificationContext::new();
    for v in &["head_pressure", "head_min", "head_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("head_val", "head_pressure == 400"));
    ctx.push_obligation(ProofObligation::assume("head_min_val", "head_min == 10"));
    ctx.push_obligation(ProofObligation::assume("head_max_val", "head_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "head_in_range",
        "head_pressure >= head_min && head_pressure <= head_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head pressure 400 kPa within [10, 5000]");
}

#[test]
fn test_motor_power_drive() {
    let mut ctx = VerificationContext::new();
    for v in &["motor_power", "power_min", "power_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("power_val", "motor_power == 75"));
    ctx.push_obligation(ProofObligation::assume("power_min_val", "power_min == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "power_max_val",
        "power_max == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_in_range",
        "motor_power >= power_min && motor_power <= power_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75 kW within [1, 5000]");
}

#[test]
fn test_pump_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pump_type_val", "pump_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_pump_type",
        "pump_type == 1 || pump_type == 2 || pump_type == 3 || pump_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pump type 1=end-suction is valid (4-way disjunction)",
    );
}

#[test]
fn test_impeller_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impeller_val",
        "impeller_type == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_impeller",
        "impeller_type == 1 || impeller_type == 2 || impeller_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller type 1=closed is valid (3-way disjunction)",
    );
}

#[test]
fn test_speed_control_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_control", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_control == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_speed_control",
        "speed_control == 1 || speed_control == 2 || speed_control == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "speed control 1=fixed is valid (3-way disjunction)",
    );
}

#[test]
fn test_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal_type",
        "seal_type == 1 || seal_type == 2 || seal_type == 3 || seal_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 1=mechanical is valid (4-way disjunction)",
    );
}

#[test]
fn test_efficiency_pump() {
    let mut ctx = VerificationContext::new();
    for v in &["efficiency", "eff_min", "eff_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eff_val", "efficiency == 850"));
    ctx.push_obligation(ProofObligation::assume("eff_min_val", "eff_min == 500"));
    ctx.push_obligation(ProofObligation::assume("eff_max_val", "eff_max == 950"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_in_range",
        "efficiency >= eff_min && efficiency <= eff_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency 850 (85.0%) within [500, 950]");
}

#[test]
fn test_npsh_required_cavitation() {
    let mut ctx = VerificationContext::new();
    for v in &["npsh_required", "npsh_min", "npsh_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("npsh_val", "npsh_required == 30"));
    ctx.push_obligation(ProofObligation::assume("npsh_min_val", "npsh_min == 5"));
    ctx.push_obligation(ProofObligation::assume("npsh_max_val", "npsh_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "npsh_in_range",
        "npsh_required >= npsh_min && npsh_required <= npsh_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NPSH required 30 (3.0m) within [5, 200]");
}

#[test]
fn test_dry_run_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_run_protection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_enabled",
        "dry_run_protection == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "protection_active",
        "dry_run_protection == 1 || dry_run_protection == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry run protection flag is boolean (enabled)");
}
