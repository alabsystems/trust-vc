// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn capacitance() {
    let mut ctx = VerificationContext::new();
    for v in &["capacitance_f", "min_cap", "max_cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Capacitance in farads: value 3000F, range 1-12000F
    ctx.push_obligation(ProofObligation::assume("cf", "capacitance_f == 3000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cap == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cap == 12000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if capacitance_f >= min_cap && capacitance_f <= max_cap { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Supercapacitor: 3000F capacitance in [1, 12000] range",
    );
}

#[test]
fn rated_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Rated voltage in mV: 2700mV = 2.7V per cell, range 2500-3000mV
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 2700"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_mv >= min_voltage_mv && voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Supercapacitor: 2.7V rated voltage in [2.5, 3.0] V range",
    );
}

#[test]
fn esr() {
    let mut ctx = VerificationContext::new();
    for v in &["esr_mohm", "max_esr_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("esr_ok", i32_ty());
    // Equivalent series resistance in milliohms: 300mΩ = 0.3Ω, max 1000mΩ
    ctx.push_obligation(ProofObligation::assume("em", "esr_mohm == 300"));
    ctx.push_obligation(ProofObligation::assume("me", "max_esr_mohm == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "esr_ok == if esr_mohm <= max_esr_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "esr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Supercapacitor: 0.3Ω ESR ≤ 1.0Ω max → OK");
}

#[test]
fn cycle_life() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_k", "min_cycles_k"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // Charge/discharge cycles in thousands: 500 = 500k cycles, min 100 = 100k
    ctx.push_obligation(ProofObligation::assume("ck", "cycles_k == 500"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cycles_k == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if cycles_k >= min_cycles_k { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Supercapacitor: 500k cycles ≥ 100k min → OK");
}

#[test]
fn leakage_current() {
    let mut ctx = VerificationContext::new();
    for v in &["leakage_ua", "max_leakage_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("leak_ok", i32_ty());
    // Self-discharge leakage in μA: value 50μA, max 500μA
    ctx.push_obligation(ProofObligation::assume("lu", "leakage_ua == 50"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_leakage_ua == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "leak_ok == if leakage_ua <= max_leakage_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "leak_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Supercapacitor: 50μA leakage ≤ 500μA max → OK");
}

#[test]
fn cell_chemistry() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chemistry", u32_ty());
    ctx.declare_var_typed("valid_chem", i32_ty());
    // Cell chemistry: 1=EDLC (electric double-layer), 2=pseudocapacitor, 3=hybrid, 4=lithium-ion capacitor
    ctx.push_obligation(ProofObligation::assume("ch", "chemistry == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_chem == if chemistry == 1 || chemistry == 2 || chemistry == 3 || chemistry == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_chem == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Supercapacitor: EDLC is valid cell chemistry");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature offset +500: -40°C=460, 20°C=520, 65°C=565
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 565"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Supercapacitor: 20°C in [-40, 65] → in operating range",
    );
}

#[test]
fn series_cells() {
    let mut ctx = VerificationContext::new();
    for v in &["num_cells", "min_cells", "max_cells"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cells_ok", i32_ty());
    // Number of cells in series: value 6, range 1-100
    ctx.push_obligation(ProofObligation::assume("nc", "num_cells == 6"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cells == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cells == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cells_ok == if num_cells >= min_cells && num_cells <= max_cells { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cells_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Supercapacitor: 6 series cells in [1, 100] range");
}

#[test]
fn balancing_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", u32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // Balancing method: 1=passive resistive, 2=active switched, 3=none
    ctx.push_obligation(ProofObligation::assume("bm", "method == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_method == if method == 1 || method == 2 || method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Supercapacitor: active switched is valid balancing method",
    );
}

#[test]
fn energy_density() {
    let mut ctx = VerificationContext::new();
    for v in &["density_x10", "min_density_x10", "max_density_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("density_ok", i32_ty());
    // Energy density in Wh/kg ×10: value 50 = 5.0 Wh/kg, range 10-100 (1.0-10.0 Wh/kg)
    ctx.push_obligation(ProofObligation::assume("dx", "density_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_density_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_density_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "density_ok == if density_x10 >= min_density_x10 && density_x10 <= max_density_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "density_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Supercapacitor: 5.0 Wh/kg energy density in [1.0, 10.0] range",
    );
}
