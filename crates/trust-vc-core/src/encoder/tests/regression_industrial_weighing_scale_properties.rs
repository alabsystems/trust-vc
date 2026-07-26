// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["load_g", "max_load_g"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Weighing capacity in grams
    ctx.push_obligation(ProofObligation::assume("lg", "load_g == 5000")); // 5kg
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_g == 30000")); // 30kg
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_g <= max_load_g { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 5kg load ≤ 30kg capacity → OK");
}

#[test]
fn readability() {
    let mut ctx = VerificationContext::new();
    for v in &["division_mg", "min_division_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("div_ok", i32_ty());
    // Scale division (readability) in milligrams
    ctx.push_obligation(ProofObligation::assume("dm", "division_mg == 100")); // 0.1g
    ctx.push_obligation(ProofObligation::assume("md", "min_division_mg == 10")); // 0.01g
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "div_ok == if division_mg >= min_division_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "div_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 0.1g division ≥ 0.01g min → OK");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // OIML accuracy classes: 1=Special (I), 2=High (II), 3=Medium (III), 4=Ordinary (IIII)
    ctx.push_obligation(ProofObligation::assume("ac", "acc_class == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if acc_class == 1 || acc_class == 2 || acc_class == 3 || acc_class == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: Medium (III) is valid OIML class");
}

#[test]
fn tare_range() {
    let mut ctx = VerificationContext::new();
    for v in &["tare_g", "max_tare_g"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tare_ok", i32_ty());
    // Tare weight capability
    ctx.push_obligation(ProofObligation::assume("tg", "tare_g == 2000")); // 2kg
    ctx.push_obligation(ProofObligation::assume("mt", "max_tare_g == 15000")); // 50% of capacity
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tare_ok == if tare_g <= max_tare_g { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tare_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 2kg tare ≤ 15kg max → OK");
}

#[test]
fn linearity_error() {
    let mut ctx = VerificationContext::new();
    for v in &["linearity_mg", "max_linearity_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lin_ok", i32_ty());
    // Linearity error in milligrams
    ctx.push_obligation(ProofObligation::assume("lm", "linearity_mg == 50"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_linearity_mg == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lin_ok == if linearity_mg <= max_linearity_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 50mg linearity ≤ 200mg max → OK");
}

#[test]
fn settling_time() {
    let mut ctx = VerificationContext::new();
    for v in &["settle_ms", "max_settle_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("settle_ok", i32_ty());
    // Time to stable reading
    ctx.push_obligation(ProofObligation::assume("sm", "settle_ms == 1500"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_settle_ms == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "settle_ok == if settle_ms <= max_settle_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "settle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 1.5s settling ≤ 3s max → OK");
}

#[test]
fn load_cell_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_type", u32_ty());
    ctx.declare_var_typed("valid_cell", i32_ty());
    // Load cell types: 1=strain gauge, 2=piezoelectric, 3=capacitive, 4=hydraulic, 5=EMFR
    ctx.push_obligation(ProofObligation::assume("ct", "cell_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cell == if cell_type == 1 || cell_type == 2 || cell_type == 3 || cell_type == 4 || cell_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cell == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: strain gauge is valid load cell type");
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["excitation_mv", "min_excitation_mv", "max_excitation_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("exc_ok", i32_ty());
    // Load cell excitation voltage in mV
    ctx.push_obligation(ProofObligation::assume("em", "excitation_mv == 5000")); // 5V
    ctx.push_obligation(ProofObligation::assume("mn", "min_excitation_mv == 3000")); // 3V
    ctx.push_obligation(ProofObligation::assume("mx", "max_excitation_mv == 12000")); // 12V
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "exc_ok == if excitation_mv >= min_excitation_mv && excitation_mv <= max_excitation_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "exc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 5V excitation in [3, 12] → OK");
}

#[test]
fn verification_intervals() {
    let mut ctx = VerificationContext::new();
    for v in &["n_intervals", "min_intervals"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("int_ok", i32_ty());
    // Number of verification scale intervals (nmax)
    ctx.push_obligation(ProofObligation::assume("ni", "n_intervals == 3000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_intervals == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "int_ok == if n_intervals >= min_intervals { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "int_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 3000 intervals ≥ 500 min → OK");
}

#[test]
fn temperature_effect() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_drift_mg", "max_temp_drift_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Temperature effect on zero in mg per °C
    ctx.push_obligation(ProofObligation::assume("td", "temp_drift_mg == 5"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_drift_mg == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if temp_drift_mg <= max_temp_drift_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Scale: 5mg/°C temp drift ≤ 30mg max → OK");
}
