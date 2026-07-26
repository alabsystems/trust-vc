// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial chiller controller property verification.
// Encodes key parameters of an industrial chiller system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Cooling capacity (kW) — chiller rated capacity bounded [1, 5000], value 500.
#[test]
fn test_cooling_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "cooling_kw == 500"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "cooling_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "cooling_kw <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling capacity 500 kW in [1, 5000]");
}

/// Test 2: Setpoint temperature offset +500 (deg C) — bounded [250, 850].
/// 250 represents -250+500=-250 is wrong; 250 represents -25 C (250-500=-250? No).
/// Offset +500: -25 C = 475, +35 C = 535. Value 507 (7 C).
#[test]
fn test_setpoint_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("setpoint_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sp_val", "setpoint_offset == 507"));
    ctx.push_obligation(ProofObligation::assert("sp_min", "setpoint_offset >= 475"));
    ctx.push_obligation(ProofObligation::assert("sp_max", "setpoint_offset <= 535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "setpoint temp 7 C (offset 507) in [475, 535]");
}

/// Test 3: Compressor type — 3-way disjunction.
/// 1=scroll, 2=screw, 3=centrifugal. Value 2 (screw).
#[test]
fn test_compressor_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("compressor_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("comp_val", "compressor_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_compressor",
        "compressor_type == 1 || compressor_type == 2 || compressor_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compressor type 2 (screw) is valid 3-way disjunction",
    );
}

/// Test 4: Refrigerant type — 4-way disjunction.
/// 1=R410A, 2=R134a, 3=R407C, 4=R744. Value 4 (R744 / CO2).
#[test]
fn test_refrigerant_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", u32_ty());
    ctx.push_obligation(ProofObligation::assume("refr_val", "refrigerant == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_refrigerant",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3 || refrigerant == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refrigerant type 4 (R744) is valid 4-way disjunction",
    );
}

/// Test 5: Flow rate (L/min) — chilled water flow bounded [10, 10000], value 800.
#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_lpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_lpm == 800"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_lpm >= 10"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_lpm <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 800 L/min in [10, 10000]");
}

/// Test 6: COP (x10) — coefficient of performance bounded [20, 80], value 45 (4.5).
#[test]
fn test_cop_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cop_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cop_val", "cop_x10 == 45"));
    ctx.push_obligation(ProofObligation::assert("cop_min", "cop_x10 >= 20"));
    ctx.push_obligation(ProofObligation::assert("cop_max", "cop_x10 <= 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "COP 4.5 (45 x10) in [20, 80]");
}

/// Test 7: Evaporator temperature offset +500 (deg C) — bounded [450, 520].
/// 450 represents -50 C, 520 represents 20 C. Value 494 (-6 C).
#[test]
fn test_evaporator_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap_offset == 494"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("evap_max", "evap_offset <= 520"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporator temp -6 C (offset 494) in [450, 520]");
}

/// Test 8: Condenser pressure (kPa) — bounded [500, 4000], value 1800.
#[test]
fn test_condenser_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_kpa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cond_val", "cond_kpa == 1800"));
    ctx.push_obligation(ProofObligation::assert("cond_min", "cond_kpa >= 500"));
    ctx.push_obligation(ProofObligation::assert("cond_max", "cond_kpa <= 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "condenser pressure 1800 kPa in [500, 4000]");
}

/// Test 9: Pump type — 3-way disjunction.
/// 1=centrifugal, 2=positive displacement, 3=turbine. Value 1 (centrifugal).
#[test]
fn test_pump_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pump_val", "pump_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_pump",
        "pump_type == 1 || pump_type == 2 || pump_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pump type 1 (centrifugal) is valid 3-way disjunction",
    );
}

/// Test 10: Low flow alarm — boolean flag using i32 with if/else pattern.
/// Flag 1 = low flow detected, which triggers alarm (alarm_active = 1).
#[test]
fn test_low_flow_alarm_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("low_flow_flag", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "low_flow_flag == 0 || low_flow_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "low_flow_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm_active == if low_flow_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alarm_triggered",
        "alarm_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "low flow flag triggers alarm");
}
