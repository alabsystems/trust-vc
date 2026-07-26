// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_max_pv_voltage_mv() {
    let mut ctx = VerificationContext::new();
    for v in &["pv_voltage", "min_pv", "max_pv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pv_val", "pv_voltage == 150000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_pv == 12000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_pv == 600000"));
    ctx.push_obligation(ProofObligation::assert(
        "pv_in_range",
        "pv_voltage >= min_pv && pv_voltage <= max_pv",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PV voltage 150V (150000 mV) in [12000, 600000]");
}

#[test]
fn test_battery_voltage_four_way_mv() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batt_voltage", u32_ty());
    ctx.push_obligation(ProofObligation::assume("batt_val", "batt_voltage == 24000"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_batt",
        "batt_voltage == 12000 || batt_voltage == 24000 || batt_voltage == 36000 || batt_voltage == 48000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "battery 24V is one of {12, 24, 36, 48} V");
}

#[test]
fn test_charge_current_ma() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_current", "min_current", "max_current"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cc_val", "charge_current == 30000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_current == 1000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_current == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "current_in_range",
        "charge_current >= min_current && charge_current <= max_current",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "charge current 30A (30000 mA) in [1000, 100000]");
}

#[test]
fn test_charge_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("charge_mode", u32_ty());
    // 1=MPPT, 2=PWM, 3=direct
    ctx.push_obligation(ProofObligation::assume("mode_val", "charge_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "charge_mode == 1 || charge_mode == 2 || charge_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "charge mode MPPT (1) is one of {1=MPPT, 2=PWM, 3=direct}",
    );
}

#[test]
fn test_battery_type_four_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batt_type", u32_ty());
    // 1=lead-acid, 2=AGM, 3=gel, 4=lithium
    ctx.push_obligation(ProofObligation::assume("type_val", "batt_type == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "batt_type == 1 || batt_type == 2 || batt_type == 3 || batt_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery type lithium (4) is one of {1=lead-acid, 2=AGM, 3=gel, 4=lithium}",
    );
}

#[test]
fn test_efficiency_tenths_percent() {
    let mut ctx = VerificationContext::new();
    for v in &["efficiency", "min_eff", "max_eff"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eff_val", "efficiency == 985"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_eff == 900"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_eff == 999"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_in_range",
        "efficiency >= min_eff && efficiency <= max_eff",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency 98.5% (985 x0.1%) in [900, 999]");
}

#[test]
fn test_load_output_ma() {
    let mut ctx = VerificationContext::new();
    for v in &["load_current", "min_load", "max_load"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("load_val", "load_current == 20000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_load == 0"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_load == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "load_in_range",
        "load_current >= min_load && load_current <= max_load",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load output 20A (20000 mA) in [0, 50000]");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: actual = value - 500, so 525 = 25C, 460 = -40C, 585 = 85C
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_temp == 460"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_temp == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp_offset >= min_temp && temp_offset <= max_temp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temp 25C (offset 525) in [460 (-40C), 585 (85C)]");
}

#[test]
fn test_communication_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_type", u32_ty());
    // 1=RS485, 2=Bluetooth, 3=WiFi
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm_type == 1 || comm_type == 2 || comm_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "comm Bluetooth (2) is one of {1=RS485, 2=Bluetooth, 3=WiFi}",
    );
}

#[test]
fn test_night_disconnect_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("night_disconnect", i32_ty());
    ctx.declare_var_typed("load_active", i32_ty());
    // Boolean flag: 1 = enabled, 0 = disabled
    ctx.push_obligation(ProofObligation::assume("flag_val", "night_disconnect == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "load_def",
        "load_active == if night_disconnect == 1 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("load_off", "load_active == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "night disconnect enabled => load off");
}
