// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn stack_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // Fuel cell stack voltage: sum of individual cell voltages
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 48000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 30000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 60000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if voltage_mv >= min_voltage_mv && voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 48V stack in [30, 60] → voltage OK");
}

#[test]
fn cell_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cells", "min_cells", "max_cells"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // Number of cells in series stack
    ctx.push_obligation(ProofObligation::assume("c", "cells == 60"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cells == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cells == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if cells >= min_cells && cells <= max_cells { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 60 cells in [10, 200] → count OK");
}

#[test]
fn membrane_humidity() {
    let mut ctx = VerificationContext::new();
    for v in &["rh_pct", "min_rh_pct", "max_rh_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rh_ok", i32_ty());
    // PEM membrane humidity: must stay hydrated but not flooded
    ctx.push_obligation(ProofObligation::assume("rp", "rh_pct == 80"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rh_pct == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rh_pct == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rh_ok == if rh_pct >= min_rh_pct && rh_pct <= max_rh_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rh_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 80% RH in [50, 100] → membrane OK");
}

#[test]
fn hydrogen_flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_slpm", "max_flow_slpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // H2 flow in standard liters per minute
    ctx.push_obligation(ProofObligation::assume("fs", "flow_slpm == 50"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_flow_slpm == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_slpm <= max_flow_slpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 50 SLPM H2 ≤ 200 max → flow OK");
}

#[test]
fn air_stoichiometry() {
    let mut ctx = VerificationContext::new();
    for v in &["stoich_x10", "min_stoich_x10", "max_stoich_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stoich_ok", i32_ty());
    // Air stoichiometric ratio (×10): typically 1.5-3.0
    ctx.push_obligation(ProofObligation::assume("sx", "stoich_x10 == 20")); // 2.0
    ctx.push_obligation(ProofObligation::assume("mn", "min_stoich_x10 == 15")); // 1.5
    ctx.push_obligation(ProofObligation::assume("mx", "max_stoich_x10 == 30")); // 3.0
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stoich_ok == if stoich_x10 >= min_stoich_x10 && stoich_x10 <= max_stoich_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stoich_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 2.0 stoichiometry in [1.5, 3.0] → OK");
}

#[test]
fn coolant_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c", "min_temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // PEM stack temperature: 60-80°C typical
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 70"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_c == 60"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_c == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c >= min_temp_c && temp_c <= max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 70°C coolant in [60, 80] → temp OK");
}

#[test]
fn power_output() {
    let mut ctx = VerificationContext::new();
    for v in &["power_w", "max_power_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Stack power output
    ctx.push_obligation(ProofObligation::assume("pw", "power_w == 5000"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_w == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_w <= max_power_w { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 5kW output ≤ 10kW max → OK");
}

#[test]
fn degradation_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["degrad_uv_per_h", "max_degrad_uv_per_h"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("degrad_ok", i32_ty());
    // Voltage degradation rate: μV/h per cell
    ctx.push_obligation(ProofObligation::assume("du", "degrad_uv_per_h == 5"));
    ctx.push_obligation(ProofObligation::assume("md", "max_degrad_uv_per_h == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "degrad_ok == if degrad_uv_per_h <= max_degrad_uv_per_h { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "degrad_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 5μV/h degradation ≤ 20 max → OK");
}

#[test]
fn startup_time() {
    let mut ctx = VerificationContext::new();
    for v in &["startup_sec", "max_startup_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("start_ok", i32_ty());
    // Time to reach operating temperature/power
    ctx.push_obligation(ProofObligation::assume("ss", "startup_sec == 30"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_startup_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "start_ok == if startup_sec <= max_startup_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "start_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 30s startup ≤ 120s max → OK");
}

#[test]
fn stack_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_pct", "min_eff_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Electrical efficiency (PEM: typically 40-60%)
    ctx.push_obligation(ProofObligation::assume("ep", "eff_pct == 55"));
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_pct == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_pct >= min_eff_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Fuel cell: 55% efficiency ≥ 40% min → OK");
}
