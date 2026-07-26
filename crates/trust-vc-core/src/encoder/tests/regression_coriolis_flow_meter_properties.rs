// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mass_flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_gph", "min_flow_gph", "max_flow_gph"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Mass flow rate in grams per hour
    ctx.push_obligation(ProofObligation::assume("fg", "flow_gph == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow_gph == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow_gph == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_gph >= min_flow_gph && flow_gph <= max_flow_gph { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 5000 g/h flow in [100, 100000] → OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Mass flow accuracy in % of reading (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x100 == 10")); // 0.10%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 0.10% accuracy ≤ 0.50% max → OK");
}

#[test]
fn density_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["dens_acc_x10000", "max_dens_acc_x10000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dens_ok", i32_ty());
    // Density accuracy in g/cm³ (×10000 for 0.0001 precision)
    ctx.push_obligation(ProofObligation::assume("dx", "dens_acc_x10000 == 5")); // 0.0005 g/cm³
    ctx.push_obligation(ProofObligation::assume("md", "max_dens_acc_x10000 == 20")); // 0.0020
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dens_ok == if dens_acc_x10000 <= max_dens_acc_x10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dens_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Coriolis: 0.0005 g/cm³ density acc ≤ 0.0020 max → OK",
    );
}

#[test]
fn tube_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Natural tube vibration frequency
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 800"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 200"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 800Hz tube freq in [200, 2000] → OK");
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Maximum process pressure
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 100"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 100 bar ≤ 400 max → OK");
}

#[test]
fn zero_stability() {
    let mut ctx = VerificationContext::new();
    for v in &["zero_gph", "max_zero_gph"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zero_ok", i32_ty());
    // Zero-point stability in g/h
    ctx.push_obligation(ProofObligation::assume("zg", "zero_gph == 2"));
    ctx.push_obligation(ProofObligation::assume("mz", "max_zero_gph == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "zero_ok == if zero_gph <= max_zero_gph { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zero_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 2 g/h zero stability ≤ 10 max → OK");
}

#[test]
fn tube_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_mat", i32_ty());
    // Tube materials: 1=316L SS, 2=Hastelloy C-276, 3=Titanium, 4=Tantalum
    ctx.push_obligation(ProofObligation::assume("m", "material == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mat == if material == 1 || material == 2 || material == 3 || material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mat == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: Hastelloy C-276 is valid tube material");
}

#[test]
fn repeatability() {
    let mut ctx = VerificationContext::new();
    for v in &["repeat_x100", "max_repeat_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rep_ok", i32_ty());
    // Repeatability as % of reading (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("rx", "repeat_x100 == 5")); // 0.05%
    ctx.push_obligation(ProofObligation::assume("mr", "max_repeat_x100 == 25")); // 0.25%
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rep_ok == if repeat_x100 <= max_repeat_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 0.05% repeatability ≤ 0.25% max → OK");
}

#[test]
fn temperature_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature: -50°C to +200°C (offset +500)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 575")); // 75°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 450")); // -50°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 700")); // 200°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 75°C process temp in [-50, 200] → OK");
}

#[test]
fn turndown_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["turndown", "min_turndown"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("td_ok", i32_ty());
    // Turndown ratio (max:min flow)
    ctx.push_obligation(ProofObligation::assume("t", "turndown == 100")); // 100:1
    ctx.push_obligation(ProofObligation::assume("mt", "min_turndown == 20")); // 20:1
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "td_ok == if turndown >= min_turndown { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "td_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Coriolis: 100:1 turndown ≥ 20:1 min → OK");
}
