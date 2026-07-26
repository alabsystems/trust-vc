// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_ml_min", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Flow rate in mL/min
    ctx.push_obligation(ProofObligation::assume("fv", "flow_ml_min == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow == 25000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_ml_min >= min_flow && flow_ml_min <= max_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: 500 mL/min flow rate in [1, 25000] range",
    );
}

#[test]
fn rpm() {
    let mut ctx = VerificationContext::new();
    for v in &["rotor_rpm", "min_rpm", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rpm_ok", i32_ty());
    // Rotor speed in RPM
    ctx.push_obligation(ProofObligation::assume("rv", "rotor_rpm == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rpm == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rpm == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rpm_ok == if rotor_rpm >= min_rpm && rotor_rpm <= max_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rpm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: 100 RPM rotor speed in [1, 600] range",
    );
}

#[test]
fn tubing_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_material", i32_ty());
    // Tubing materials: 1=silicone, 2=Norprene, 3=Viton, 4=PharMed, 5=Tygon
    ctx.push_obligation(ProofObligation::assume("mv", "material == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_material == if material == 1 || material == 2 || material == 3 || material == 4 || material == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_material == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: silicone is valid tubing material",
    );
}

#[test]
fn roller_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rollers", u32_ty());
    ctx.declare_var_typed("valid_rollers", i32_ty());
    // Number of rollers: 2, 3, 4, or 8
    ctx.push_obligation(ProofObligation::assume("rv", "rollers == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rollers == if rollers == 2 || rollers == 3 || rollers == 4 || rollers == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_rollers == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Peristaltic pump: 4 is valid roller count");
}

#[test]
fn tubing_bore() {
    let mut ctx = VerificationContext::new();
    for v in &["bore_mm_x10", "min_bore_x10", "max_bore_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bore_ok", i32_ty());
    // Inner diameter in mm x10: 32 = 3.2mm, range 5-250 (0.5-25.0mm)
    ctx.push_obligation(ProofObligation::assume("bv", "bore_mm_x10 == 32"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bore_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bore_x10 == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bore_ok == if bore_mm_x10 >= min_bore_x10 && bore_mm_x10 <= max_bore_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bore_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: 3.2mm tubing bore in [0.5, 25.0]mm range",
    );
}

#[test]
fn max_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar_x10", "max_pressure_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Max discharge pressure in bar x10: 20 = 2.0 bar, max 100 = 10.0 bar
    ctx.push_obligation(ProofObligation::assume("pv", "pressure_bar_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar_x10 <= max_pressure_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: 2.0 bar discharge pressure <= 10.0 bar max",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Flow accuracy x10 (%): 20 = 2.0%, max 50 = 5.0%
    ctx.push_obligation(ProofObligation::assume("av", "accuracy_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Peristaltic pump: 2.0% flow accuracy <= 5.0% max");
}

#[test]
fn direction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dir", u32_ty());
    ctx.declare_var_typed("valid_dir", i32_ty());
    // Pump direction: 1=forward, 2=reverse, 3=bidirectional
    ctx.push_obligation(ProofObligation::assume("dv", "dir == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dir == if dir == 1 || dir == 2 || dir == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dir == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: bidirectional is valid direction",
    );
}

#[test]
fn drive_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", u32_ty());
    ctx.declare_var_typed("valid_drive", i32_ty());
    // Drive type: 1=fixed speed, 2=variable speed (DC), 3=stepper motor
    ctx.push_obligation(ProofObligation::assume("dv", "drive == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_drive == if drive == 1 || drive == 2 || drive == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_drive == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: variable speed DC is valid drive type",
    );
}

#[test]
fn tube_life() {
    let mut ctx = VerificationContext::new();
    for v in &["life_hours", "min_life"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // Tube life in hours, min 500
    ctx.push_obligation(ProofObligation::assume("lv", "life_hours == 2000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_life == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if life_hours >= min_life { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Peristaltic pump: 2000 hr tube life >= 500 hr minimum",
    );
}
