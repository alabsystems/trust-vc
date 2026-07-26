// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_press_force() {
    let mut ctx = VerificationContext::new();
    for v in &["tonnage_kn", "min_tonnage", "max_tonnage"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("force_ok", i32_ty());
    // Press force (tonnage) in kN for forming/stamping
    ctx.push_obligation(ProofObligation::assume("tk", "tonnage_kn == 2000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_tonnage == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_tonnage == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "force_ok == if tonnage_kn >= min_tonnage && tonnage_kn <= max_tonnage { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "force_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Press: 2000 kN tonnage in [50, 50000] -> OK");
}

#[test]
fn test_stroke() {
    let mut ctx = VerificationContext::new();
    for v in &["stroke_mm", "min_stroke", "max_stroke"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stroke_ok", i32_ty());
    // Ram travel (stroke) in mm
    ctx.push_obligation(ProofObligation::assume("sm", "stroke_mm == 300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_stroke == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_stroke == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stroke_ok == if stroke_mm >= min_stroke && stroke_mm <= max_stroke { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stroke_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Press: 300mm stroke in [10, 2000] -> OK");
}

#[test]
fn test_closing_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_mm_s", "min_speed", "max_speed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Approach/closing speed in mm/s
    ctx.push_obligation(ProofObligation::assume("ss", "speed_mm_s == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_speed == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_speed == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "speed_ok == if speed_mm_s >= min_speed && speed_mm_s <= max_speed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Press: 200 mm/s closing speed in [10, 1000] -> OK");
}

#[test]
fn test_press_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Press types: 1=C-frame, 2=H-frame, 3=four-column, 4=knuckle-joint
    ctx.push_obligation(ProofObligation::assume("pt", "press_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if press_type == 1 || press_type == 2 || press_type == 3 || press_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Press: four-column is valid press type (4-way)");
}

#[test]
fn test_control_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Control modes: 1=force, 2=position, 3=velocity
    ctx.push_obligation(ProofObligation::assume("cm", "ctrl_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Press: force is valid control mode (3-way)");
}

#[test]
fn test_hydraulic_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "min_pressure", "max_pressure"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // System hydraulic pressure in bar
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure == 700"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar >= min_pressure && pressure_bar <= max_pressure { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Press: 250 bar hydraulic pressure in [50, 700] -> OK",
    );
}

#[test]
fn test_position_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "min_accuracy", "max_accuracy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Position accuracy in x10 mm (1 = 0.1mm)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x10 == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_accuracy == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 >= min_accuracy && accuracy_x10 <= max_accuracy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Press: 0.1mm position accuracy in [0, 5.0mm] -> OK",
    );
}

#[test]
fn test_cycle_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["strokes_per_min", "min_rate", "max_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Cycle rate in strokes per minute
    ctx.push_obligation(ProofObligation::assume("sp", "strokes_per_min == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if strokes_per_min >= min_rate && strokes_per_min <= max_rate { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Press: 20 strokes/min cycle rate in [1, 120] -> OK",
    );
}

#[test]
fn test_safety_category() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safety_cat", u32_ty());
    ctx.declare_var_typed("valid_cat", i32_ty());
    // Safety categories: 1=PLc, 2=PLd, 3=PLe
    ctx.push_obligation(ProofObligation::assume("sc", "safety_cat == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cat == if safety_cat == 1 || safety_cat == 2 || safety_cat == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cat == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Press: PLd is valid safety category (3-way)");
}

#[test]
fn test_light_curtain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curtain_enabled", i32_ty());
    ctx.declare_var_typed("curtain_active", i32_ty());
    // Light curtain safety device as boolean flag (i32: 1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("ce", "curtain_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "curtain_active == if curtain_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "curtain_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Press: light curtain enabled -> active (boolean flag)",
    );
}
