// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_drive_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Piezo excitation voltage in mV: 150000 (150V), range [0, 200000]
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 150000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 200000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_mv >= min_voltage_mv && voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: 150V drive in [0, 200V] -> OK");
}

#[test]
fn test_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_us", "min_resp_us", "max_resp_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Valve switching response time in us: 500, range [50, 5000]
    ctx.push_obligation(ProofObligation::assume("ru", "resp_us == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_resp_us == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_resp_us == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_us >= min_resp_us && resp_us <= max_resp_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: 500us response in [50, 5000] -> OK");
}

#[test]
fn test_flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_ul_min", "min_flow_ul_min", "max_flow_ul_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Micro flow rate in uL/min: 1000, range [1, 100000]
    ctx.push_obligation(ProofObligation::assume("fm", "flow_ul_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow_ul_min == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow_ul_min == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_ul_min >= min_flow_ul_min && flow_ul_min <= max_flow_ul_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo valve: 1000 uL/min flow in [1, 100000] -> OK",
    );
}

#[test]
fn test_valve_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Valve types: 1=normally closed, 2=normally open, 3=proportional
    ctx.push_obligation(ProofObligation::assume("vt", "valve_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_type == if valve_type == 1 || valve_type == 2 || valve_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: proportional is valid valve type");
}

#[test]
fn test_orifice_size() {
    let mut ctx = VerificationContext::new();
    for v in &["orifice_um", "min_orifice_um", "max_orifice_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("orifice_ok", i32_ty());
    // Orifice port diameter in um: 200, range [10, 5000]
    ctx.push_obligation(ProofObligation::assume("ou", "orifice_um == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_orifice_um == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_orifice_um == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "orifice_ok == if orifice_um >= min_orifice_um && orifice_um <= max_orifice_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "orifice_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: 200um orifice in [10, 5000] -> OK");
}

#[test]
fn test_pressure_range() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_kpa", "min_pressure_kpa", "max_pressure_kpa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Operating pressure in kPa: 500, range [10, 35000]
    ctx.push_obligation(ProofObligation::assume("pk", "pressure_kpa == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure_kpa == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure_kpa == 35000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_kpa >= min_pressure_kpa && pressure_kpa <= max_pressure_kpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: 500 kPa in [10, 35000] -> OK");
}

#[test]
fn test_linearity() {
    let mut ctx = VerificationContext::new();
    for v in &["linearity_x100", "min_linearity_x100", "max_linearity_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lin_ok", i32_ty());
    // Linearity x100 (% of span): value 50 (0.50%), range [10, 500]
    ctx.push_obligation(ProofObligation::assume("lx", "linearity_x100 == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_linearity_x100 == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_linearity_x100 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lin_ok == if linearity_x100 >= min_linearity_x100 && linearity_x100 <= max_linearity_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo valve: 0.50% linearity in [0.10%, 5.00%] -> OK",
    );
}

#[test]
fn test_operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Temperature with +500 offset: 525 (25C), min 460 (-40C), max 585 (85C)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 585"));
    ctx.push_obligation(ProofObligation::assume(
        "tk_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo valve: 25C (offset 525) in [-40C, 85C] -> OK",
    );
}

#[test]
fn test_cycle_life() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_k", "min_cycles_k", "max_cycles_k"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // Cycle life in x1000 cycles: 1000000 (1B), range [100000, 10000000]
    ctx.push_obligation(ProofObligation::assume("ck", "cycles_k == 1000000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycles_k == 100000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycles_k == 10000000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if cycles_k >= min_cycles_k && cycles_k <= max_cycles_k { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: 1B cycles in [100M, 10B] -> OK");
}

#[test]
fn test_leak_rate_tight() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_tight", i32_ty());
    ctx.declare_var_typed("seal_ok", i32_ty());
    // Boolean flag: leak rate within tight specification (1=yes, 0=no)
    ctx.push_obligation(ProofObligation::assume("lt", "leak_tight == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "seal_ok == if leak_tight == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "seal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo valve: leak rate tight -> seal OK");
}
