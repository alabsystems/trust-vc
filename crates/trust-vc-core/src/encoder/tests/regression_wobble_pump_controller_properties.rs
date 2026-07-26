// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_x10", "min_flow_x10", "max_flow_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Flow rate x10 (L/min): 150 = 15.0 L/min, range [1, 5000]
    ctx.push_obligation(ProofObligation::assume("fv", "flow_x10 == 150"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow_x10 == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_x10 >= min_flow_x10 && flow_x10 <= max_flow_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wobble pump: 15.0 L/min flow rate in [0.1, 500.0] range",
    );
}

#[test]
fn max_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "min_pressure", "max_pressure_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Max operating pressure in bar, range [1, 50]
    ctx.push_obligation(ProofObligation::assume("pv", "pressure_bar == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure_limit == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar >= min_pressure && pressure_bar <= max_pressure_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wobble pump: 10 bar pressure in [1, 50] range");
}

#[test]
fn stroke_length() {
    let mut ctx = VerificationContext::new();
    for v in &["stroke_x10", "min_stroke_x10", "max_stroke_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stroke_ok", i32_ty());
    // Stroke length x10 (mm): 80 = 8.0 mm, range [10, 500]
    ctx.push_obligation(ProofObligation::assume("sv", "stroke_x10 == 80"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_stroke_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_stroke_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stroke_ok == if stroke_x10 >= min_stroke_x10 && stroke_x10 <= max_stroke_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stroke_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wobble pump: 8.0 mm stroke length in [1.0, 50.0] range",
    );
}

#[test]
fn wobble_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_x10", "min_angle_x10", "max_angle_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("angle_ok", i32_ty());
    // Wobble angle x10 (degrees): 150 = 15.0 degrees, range [10, 300]
    ctx.push_obligation(ProofObligation::assume("av", "angle_x10 == 150"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_angle_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_angle_x10 == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "angle_ok == if angle_x10 >= min_angle_x10 && angle_x10 <= max_angle_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "angle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wobble pump: 15.0 deg wobble angle in [1.0, 30.0] range",
    );
}

#[test]
fn cycle_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_per_min", "min_cycles", "max_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // Cycle rate in cycles/min, range [10, 3000]
    ctx.push_obligation(ProofObligation::assume("cv", "cycles_per_min == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycles == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycles == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycles_per_min >= min_cycles && cycles_per_min <= max_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wobble pump: 500 cycles/min in [10, 3000] range");
}

#[test]
fn diaphragm_diameter() {
    let mut ctx = VerificationContext::new();
    for v in &["dia_x10", "min_dia_x10", "max_dia_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dia_ok", i32_ty());
    // Diaphragm diameter x10 (mm): 500 = 50.0 mm, range [50, 2000]
    ctx.push_obligation(ProofObligation::assume("dv", "dia_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_dia_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_dia_x10 == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dia_ok == if dia_x10 >= min_dia_x10 && dia_x10 <= max_dia_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dia_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wobble pump: 50.0 mm diaphragm diameter in [5.0, 200.0] range",
    );
}

#[test]
fn pump_body_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("body_material", u32_ty());
    ctx.declare_var_typed("valid_body", i32_ty());
    // Pump body materials: 1=polypropylene, 2=PVDF, 3=stainless steel
    ctx.push_obligation(ProofObligation::assume("bv", "body_material == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_body == if body_material == 1 || body_material == 2 || body_material == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_body == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wobble pump: polypropylene is valid body material");
}

#[test]
fn diaphragm_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia_material", u32_ty());
    ctx.declare_var_typed("valid_dia", i32_ty());
    // Diaphragm materials: 1=PTFE, 2=EPDM, 3=Viton
    ctx.push_obligation(ProofObligation::assume("dv", "dia_material == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dia == if dia_material == 1 || dia_material == 2 || dia_material == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dia == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wobble pump: EPDM is valid diaphragm material");
}

#[test]
fn drive_mechanism() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", u32_ty());
    ctx.declare_var_typed("valid_drive", i32_ty());
    // Drive mechanisms: 1=eccentric-cam, 2=wobble-plate, 3=nutating-disc
    ctx.push_obligation(ProofObligation::assume("drv", "drive == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vdr_def",
        "valid_drive == if drive == 1 || drive == 2 || drive == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_drive == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wobble pump: nutating-disc is valid drive mechanism",
    );
}

#[test]
fn leak_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_flag", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    // Leak detection flag: 1=leak detected, 0=no leak
    ctx.push_obligation(ProofObligation::assume("lf", "leak_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if leak_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wobble pump: leak detected triggers alarm");
}
