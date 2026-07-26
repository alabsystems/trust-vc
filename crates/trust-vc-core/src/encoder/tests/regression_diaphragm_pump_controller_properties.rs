// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_ml_hr", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Dosing flow rate in mL/hr
    ctx.push_obligation(ProofObligation::assume("fv", "flow_ml_hr == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_ml_hr >= min_flow && flow_ml_hr <= max_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: 5000 mL/hr flow rate in [1, 50000] range");
}

#[test]
fn max_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "min_pressure", "max_pressure_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Max discharge pressure in bar
    ctx.push_obligation(ProofObligation::assume("pv", "pressure_bar == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure_limit == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar >= min_pressure && pressure_bar <= max_pressure_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: 10 bar discharge pressure in [1, 25] range");
}

#[test]
fn stroke_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["strokes_per_min", "min_strokes", "max_strokes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stroke_ok", i32_ty());
    // Strokes per minute
    ctx.push_obligation(ProofObligation::assume("sv", "strokes_per_min == 120"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_strokes == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_strokes == 360"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stroke_ok == if strokes_per_min >= min_strokes && strokes_per_min <= max_strokes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stroke_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: 120 strokes/min in [1, 360] range");
}

#[test]
fn diaphragm_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_material", i32_ty());
    // Diaphragm materials: 1=PTFE, 2=EPDM, 3=Viton, 4=Hypalon
    ctx.push_obligation(ProofObligation::assume("mv", "material == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_material == if material == 1 || material == 2 || material == 3 || material == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_material == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: PTFE is valid diaphragm material");
}

#[test]
fn control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Control modes: 1=manual, 2=analog (4-20mA), 3=pulse input, 4=fieldbus
    ctx.push_obligation(ProofObligation::assume("mv", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: analog 4-20mA is valid control mode");
}

#[test]
fn stroke_length() {
    let mut ctx = VerificationContext::new();
    for v in &["stroke_len_x10", "min_len_x10", "max_len_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // Stroke length adjustment x10 (%): 1000 = 100.0%, range 100-1000 (10.0-100.0%)
    ctx.push_obligation(ProofObligation::assume("sv", "stroke_len_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_len_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_len_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if stroke_len_x10 >= min_len_x10 && stroke_len_x10 <= max_len_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pump: 100.0% stroke length in [10.0, 100.0]% range",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Dosing accuracy x10 (%): 20 = 2.0%, max 50 = 5.0%
    ctx.push_obligation(ProofObligation::assume("av", "accuracy_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: 2.0% dosing accuracy <= 5.0% max");
}

#[test]
fn degassing_valve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_degassing", u32_ty());
    ctx.declare_var_typed("valid_degassing", i32_ty());
    // Degassing valve: 0=no, 1=yes
    ctx.push_obligation(ProofObligation::assume("dv", "has_degassing == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_degassing == if has_degassing == 0 || has_degassing == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_degassing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: degassing valve present is valid boolean");
}

#[test]
fn turndown_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["turndown", "min_turndown", "max_turndown"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("td_ok", i32_ty());
    // Turndown ratio (e.g., 100:1 encoded as 100), range 10-1000
    ctx.push_obligation(ProofObligation::assume("tv", "turndown == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_turndown == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_turndown == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "td_ok == if turndown >= min_turndown && turndown <= max_turndown { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "td_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pump: 100:1 turndown ratio in [10, 1000] range");
}

#[test]
fn chemical_compatibility() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chem_class", u32_ty());
    ctx.declare_var_typed("valid_chem", i32_ty());
    // Chemical compatibility: 1=acids, 2=bases, 3=oxidizers, 4=solvents, 5=slurries
    ctx.push_obligation(ProofObligation::assume("cv", "chem_class == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_chem == if chem_class == 1 || chem_class == 2 || chem_class == 3 || chem_class == 4 || chem_class == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_chem == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pump: oxidizers is valid chemical compatibility class",
    );
}
