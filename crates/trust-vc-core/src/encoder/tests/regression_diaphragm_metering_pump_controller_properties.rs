// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_flow_rate_within_operating_range() {
    // Flow rate scaled ×100 (0.01 L/h resolution): 50 = 0.50 L/h, 50000 = 500.00 L/h
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x100", u32_ty());
    ctx.declare_var_typed("min_flow_x100", u32_ty());
    ctx.declare_var_typed("max_flow_x100", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x100 == 2500")); // 25.00 L/h
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow_x100 == 50")); // 0.50 L/h
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow_x100 == 50000")); // 500.00 L/h
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x100 >= min_flow_x100 && flow_rate_x100 <= max_flow_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump flow: 25.00 L/h within 0.50..500.00 L/h");
}

#[test]
fn test_discharge_pressure_limit() {
    // Discharge pressure scaled ×10 (0.1 bar resolution): 250 = 25.0 bar
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", u32_ty());
    ctx.declare_var_typed("max_pressure_x10", u32_ty());
    ctx.declare_var_typed("safe", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "pressure_x10 == 120")); // 12.0 bar
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_x10 == 250")); // 25.0 bar
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "safe == if pressure_x10 <= max_pressure_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure: 12.0 bar <= 25.0 bar max");
}

#[test]
fn test_stroke_rate_bounded() {
    // Stroke rate in strokes/min, bounded 10 to 360
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_rate", u32_ty());
    ctx.declare_var_typed("min_rate", u32_ty());
    ctx.declare_var_typed("max_rate", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "stroke_rate == 180"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate == 360"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if stroke_rate >= min_rate && stroke_rate <= max_rate { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke rate: 180 spm within 10..360");
}

#[test]
fn test_stroke_length_adjustment() {
    // Stroke length scaled ×100 (0.01 mm resolution): 500 = 5.00 mm, 2500 = 25.00 mm
    let mut ctx = VerificationContext::new();
    for v in &["stroke_len_x100", "min_len_x100", "max_len_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sl", "stroke_len_x100 == 1500")); // 15.00 mm
    ctx.push_obligation(ProofObligation::assume("mn", "min_len_x100 == 500")); // 5.00 mm
    ctx.push_obligation(ProofObligation::assume("mx", "max_len_x100 == 2500")); // 25.00 mm
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if stroke_len_x100 >= min_len_x100 && stroke_len_x100 <= max_len_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke length: 15.00 mm within 5.00..25.00 mm");
}

#[test]
fn test_motor_power_within_rating() {
    // Motor power in watts, bounded 10 to 2000
    let mut ctx = VerificationContext::new();
    for v in &["motor_power_w", "min_power_w", "max_power_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mp", "motor_power_w == 750"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_power_w == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_power_w == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if motor_power_w >= min_power_w && motor_power_w <= max_power_w { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "under_max",
        "motor_power_w <= max_power_w",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power: 750W within 10..2000W");
}

#[test]
fn test_diaphragm_material_selection() {
    // Diaphragm material: 1=PTFE, 2=EPDM, 3=stainless steel
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "material == 1")); // PTFE
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if material == 1 || material == 2 || material == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "diaphragm material: PTFE (1) is valid");
}

#[test]
fn test_drive_type_selection() {
    // Drive type: 1=solenoid, 2=motor-driven, 3=hydraulic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "drive_type == 3")); // hydraulic
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if drive_type == 1 || drive_type == 2 || drive_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type: hydraulic (3) is valid");
}

#[test]
fn test_chemical_compatibility_check() {
    // Chemical compatibility: 1=acids, 2=bases, 3=solvents
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chemical_class", u32_ty());
    ctx.declare_var_typed("compatible", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cc", "chemical_class == 2")); // bases
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compatible == if chemical_class == 1 || chemical_class == 2 || chemical_class == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "compatible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chemical compatibility: bases (2) is valid");
}

#[test]
fn test_turndown_ratio_range() {
    // Turndown ratio scaled ×10 (0.1 resolution): 100 = 10.0:1, 10 = 1.0:1
    let mut ctx = VerificationContext::new();
    for v in &["turndown_x10", "min_turndown_x10", "max_turndown_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("td", "turndown_x10 == 100")); // 10.0:1
    ctx.push_obligation(ProofObligation::assume("mn", "min_turndown_x10 == 10")); // 1.0:1
    ctx.push_obligation(ProofObligation::assume("mx", "max_turndown_x10 == 1000")); // 100.0:1
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_spec == if turndown_x10 >= min_turndown_x10 && turndown_x10 <= max_turndown_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turndown ratio: 10.0:1 within 1.0..100.0");
}

#[test]
fn test_leak_detection_flag() {
    // Leak detection: i32 boolean flag (1=leak detected, 0=no leak)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_drop_x10", u32_ty());
    ctx.declare_var_typed("threshold_x10", u32_ty());
    ctx.declare_var_typed("leak_detected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pd", "pressure_drop_x10 == 35")); // 3.5 bar drop
    ctx.push_obligation(ProofObligation::assume("th", "threshold_x10 == 20")); // 2.0 bar threshold
    ctx.push_obligation(ProofObligation::assume(
        "ld_def",
        "leak_detected == if pressure_drop_x10 > threshold_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("alarm", "leak_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leak detection: 3.5 bar drop > 2.0 bar threshold");
}
