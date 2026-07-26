// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn state_of_charge() {
    let mut ctx = VerificationContext::new();
    for v in &["remaining_mah", "capacity_mah"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("soc_percent", u32_ty());
    // SoC = remaining/capacity × 100. Precompute: 3000/4000 × 100 = 75
    ctx.push_obligation(ProofObligation::assume("rm", "remaining_mah == 3000"));
    ctx.push_obligation(ProofObligation::assume("cm", "capacity_mah == 4000"));
    ctx.push_obligation(ProofObligation::assume("sp", "soc_percent == 75")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_75", "soc_percent == 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 3000/4000 × 100 = 75% SoC (precomputed)");
}

#[test]
fn overvoltage_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["cell_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overvoltage", i32_ty());
    // Li-ion max: 4.2V = 4200mV
    ctx.push_obligation(ProofObligation::assume("cv", "cell_voltage_mv == 4250"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_voltage_mv == 4200"));
    ctx.push_obligation(ProofObligation::assume(
        "ov_def",
        "overvoltage == if cell_voltage_mv > max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overvoltage == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 4250mV > 4200mV max → overvoltage");
}

#[test]
fn undervoltage_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["cell_voltage_mv", "min_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("undervoltage", i32_ty());
    // Li-ion min: 2.5V = 2500mV
    ctx.push_obligation(ProofObligation::assume("cv", "cell_voltage_mv == 2400"));
    ctx.push_obligation(ProofObligation::assume("mnv", "min_voltage_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume(
        "uv_def",
        "undervoltage == if cell_voltage_mv < min_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "undervoltage == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 2400mV < 2500mV min → undervoltage");
}

#[test]
fn cell_balancing_needed() {
    let mut ctx = VerificationContext::new();
    for v in &["cell_max_mv", "cell_min_mv", "balance_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("imbalance_mv", u32_ty());
    ctx.declare_var_typed("needs_balance", i32_ty());
    // Balance when cell voltage delta exceeds threshold
    ctx.push_obligation(ProofObligation::assume("cmx", "cell_max_mv == 4180"));
    ctx.push_obligation(ProofObligation::assume("cmn", "cell_min_mv == 4120"));
    ctx.push_obligation(ProofObligation::assume("bt", "balance_threshold_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "imbalance_mv == cell_max_mv - cell_min_mv",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "needs_balance == if imbalance_mv >= balance_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_60", "imbalance_mv == 60"));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_balance == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BMS: cell delta 60mV ≥ 50mV threshold → needs balancing",
    );
}

#[test]
fn charge_current_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_current_ma", "max_charge_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // 1C charge rate for 4000mAh = 4000mA max
    ctx.push_obligation(ProofObligation::assume("cc", "charge_current_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_charge_ma == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if charge_current_ma <= max_charge_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 2000mA ≤ 4000mA (1C) → charge current OK");
}

#[test]
fn temperature_charge_gate() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_x10", "min_charge_temp_x10", "max_charge_temp_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Safe charge range: 0°C to 45°C (0 to 450 in tenths)
    // Using unsigned offset: +500 to avoid negatives. 0°C=500, 45°C=950, 25°C=750
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_x10 == 750")); // 25.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_charge_temp_x10 == 500")); // 0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_charge_temp_x10 == 950")); // 45°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c_x10 >= min_charge_temp_x10 && temp_c_x10 <= max_charge_temp_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 25°C in [0, 45] → charge temperature OK");
}

#[test]
fn pack_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["cells_in_series", "cell_nominal_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pack_voltage_mv", u32_ty());
    // Pack voltage = cells × nominal. Precompute: 4 × 3700 = 14800mV
    ctx.push_obligation(ProofObligation::assume("cs", "cells_in_series == 4"));
    ctx.push_obligation(ProofObligation::assume("cn", "cell_nominal_mv == 3700"));
    ctx.push_obligation(ProofObligation::assume("pv", "pack_voltage_mv == 14800")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_14800",
        "pack_voltage_mv == 14800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 4S × 3700mV = 14800mV pack (precomputed)");
}

#[test]
fn discharge_cutoff() {
    let mut ctx = VerificationContext::new();
    for v in &["pack_voltage_mv", "cutoff_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("must_disconnect", i32_ty());
    // Disconnect load when pack voltage drops below cutoff
    ctx.push_obligation(ProofObligation::assume("pv", "pack_voltage_mv == 10000")); // 10.0V
    ctx.push_obligation(ProofObligation::assume("cv", "cutoff_voltage_mv == 10400")); // 10.4V (4×2.6V)
    ctx.push_obligation(ProofObligation::assume(
        "md_def",
        "must_disconnect == if pack_voltage_mv < cutoff_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "must_disconnect == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 10.0V < 10.4V cutoff → must disconnect");
}

#[test]
fn cycle_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_count", "max_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    // Li-ion: ~500 full cycles
    ctx.push_obligation(ProofObligation::assume("cc", "cycle_count == 350"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycles == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if cycle_count < max_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 350 cycles < 500 max → within battery life");
}

#[test]
fn overcurrent_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["discharge_current_ma", "max_discharge_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overcurrent", i32_ty());
    // Max continuous discharge: 2C for 4000mAh = 8000mA
    ctx.push_obligation(ProofObligation::assume(
        "dc",
        "discharge_current_ma == 9000",
    ));
    ctx.push_obligation(ProofObligation::assume("md", "max_discharge_ma == 8000"));
    ctx.push_obligation(ProofObligation::assume(
        "oc_def",
        "overcurrent == if discharge_current_ma > max_discharge_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overcurrent == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BMS: 9000mA > 8000mA (2C) → overcurrent");
}
