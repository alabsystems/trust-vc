// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn charge_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_mv", "max_charge_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cv_ok", i32_ty());
    // Per-cell charge voltage in millivolts
    ctx.push_obligation(ProofObligation::assume("cm", "charge_mv == 4200")); // 4.2V Li-ion
    ctx.push_obligation(ProofObligation::assume("mc", "max_charge_mv == 4250")); // absolute max
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cv_ok == if charge_mv <= max_charge_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cv_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: 4.2V charge ≤ 4.25V max → OK");
}

#[test]
fn charge_current() {
    let mut ctx = VerificationContext::new();
    for v in &["charge_ma", "max_charge_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ci_ok", i32_ty());
    // Charge current in milliamps
    ctx.push_obligation(ProofObligation::assume("ca", "charge_ma == 2000")); // 2A (1C for 2Ah)
    ctx.push_obligation(ProofObligation::assume("mc", "max_charge_ma == 5000")); // 5A max
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ci_ok == if charge_ma <= max_charge_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ci_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: 2A charge ≤ 5A max → OK");
}

#[test]
fn chemistry_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chemistry", u32_ty());
    ctx.declare_var_typed("valid_chem", i32_ty());
    // Battery chemistries: 1=LiCoO2, 2=LiFePO4, 3=NMC, 4=NCA, 5=LTO
    ctx.push_obligation(ProofObligation::assume("c", "chemistry == 3")); // NMC
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_chem == if chemistry == 1 || chemistry == 2 || chemistry == 3 || chemistry == 4 || chemistry == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_chem == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: NMC is valid battery chemistry");
}

#[test]
fn cell_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cells", "min_cells", "max_cells"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cell_ok", i32_ty());
    // Series cell count
    ctx.push_obligation(ProofObligation::assume("c", "cells == 4")); // 4S = 14.8V nominal
    ctx.push_obligation(ProofObligation::assume("mn", "min_cells == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cells == 16")); // 16S = 59.2V
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cell_ok == if cells >= min_cells && cells <= max_cells { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cell_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: 4S cells in [1, 16] → OK");
}

#[test]
fn termination_current() {
    let mut ctx = VerificationContext::new();
    for v in &["term_ma", "min_term_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("term_ok", i32_ty());
    // CV phase termination current (typically C/10 to C/20)
    ctx.push_obligation(ProofObligation::assume("tm", "term_ma == 100")); // 100mA
    ctx.push_obligation(ProofObligation::assume("mt", "min_term_ma == 50")); // 50mA min
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "term_ok == if term_ma >= min_term_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "term_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: 100mA termination ≥ 50mA min → OK");
}

#[test]
fn precharge_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["precharge_mv", "min_precharge_mv", "max_precharge_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pre_ok", i32_ty());
    // Pre-charge to CC transition threshold per cell in mV
    ctx.push_obligation(ProofObligation::assume("pm", "precharge_mv == 3000")); // 3.0V
    ctx.push_obligation(ProofObligation::assume("mn", "min_precharge_mv == 2500")); // 2.5V
    ctx.push_obligation(ProofObligation::assume("mx", "max_precharge_mv == 3200")); // 3.2V
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pre_ok == if precharge_mv >= min_precharge_mv && precharge_mv <= max_precharge_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pre_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Charger: 3.0V precharge threshold in [2.5, 3.2] → OK",
    );
}

#[test]
fn charge_phase() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase", u32_ty());
    ctx.declare_var_typed("valid_phase", i32_ty());
    // Charge phases: 1=trickle/precharge, 2=CC (constant current), 3=CV (constant voltage), 4=done
    ctx.push_obligation(ProofObligation::assume("p", "phase == 2")); // CC phase
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_phase == if phase == 1 || phase == 2 || phase == 3 || phase == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_phase == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: CC is valid charge phase");
}

#[test]
fn safety_timer() {
    let mut ctx = VerificationContext::new();
    for v in &["timer_min", "max_timer_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timer_ok", i32_ty());
    // Safety charge timer in minutes
    ctx.push_obligation(ProofObligation::assume("tm", "timer_min == 120")); // 2 hours
    ctx.push_obligation(ProofObligation::assume("mt", "max_timer_min == 480")); // 8 hours
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timer_ok == if timer_min <= max_timer_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timer_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: 120min timer ≤ 480min max → OK");
}

#[test]
fn voltage_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_mv", "max_accuracy_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Charge voltage regulation accuracy in mV
    ctx.push_obligation(ProofObligation::assume("am", "accuracy_mv == 10")); // ±10mV
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_mv == 50")); // ±50mV max
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_mv <= max_accuracy_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: ±10mV accuracy ≤ ±50mV max → OK");
}

#[test]
fn thermal_shutdown() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // IC junction temperature (offset +500 for unsigned, 45°C = 545)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 545")); // 45°C
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_offset == 650")); // 150°C shutdown
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charger: 45°C IC temp ≤ 150°C shutdown → OK");
}
