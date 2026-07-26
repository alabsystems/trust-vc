// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Flow rate scaled x10 for 0.1 L/min precision.
/// Valid range: 1-5000 (representing 0.1-500.0 L/min).
/// Assumes a specific flow rate of 250 (25.0 L/min) and verifies it
/// stays within the valid operating range.
#[test]
fn test_bellows_pump_flow_rate_within_range() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate_x10", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("min_flow_val", "min_flow == 1"));
    ctx.push_obligation(ProofObligation::assume("max_flow_val", "max_flow == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_rate_x10 >= min_flow && flow_rate_x10 <= max_flow",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_rate_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_bounds",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate 25.0 L/min (x10=250) within valid range 0.1-500.0 L/min",
    );
}

/// Maximum pressure in bar.
/// Valid range: 1-100 bar.
/// Assumes a specific pressure of 65 bar and verifies it does not
/// exceed the maximum rated pressure.
#[test]
fn test_bellows_pump_max_pressure_within_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure", "max_pressure"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 65"));
    ctx.push_obligation(ProofObligation::assume(
        "max_pressure_val",
        "max_pressure == 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_ok",
        "pressure >= 1 && pressure <= max_pressure",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure 65 bar within rated max 100 bar");
}

/// Stroke length scaled x10 for 0.1 mm precision.
/// Valid range: 10-1000 (representing 1.0-100.0 mm).
/// Assumes stroke length of 450 (45.0 mm) and verifies it falls
/// within mechanical limits.
#[test]
fn test_bellows_pump_stroke_length_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["stroke_x10", "min_stroke", "max_stroke"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "min_stroke_val",
        "min_stroke == 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "max_stroke_val",
        "max_stroke == 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "stroke_range",
        "stroke_x10 >= min_stroke && stroke_x10 <= max_stroke",
    ));
    ctx.push_obligation(ProofObligation::assume("stroke_val", "stroke_x10 == 450"));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_in_bounds",
        "stroke_x10 >= 10 && stroke_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stroke length 45.0 mm (x10=450) within mechanical limits 1.0-100.0 mm",
    );
}

/// Cycle rate in cycles per minute.
/// Valid range: 10-300 cycles/min.
/// Assumes a cycle rate of 120 and verifies it is within the
/// operating envelope.
#[test]
fn test_bellows_pump_cycle_rate_in_range() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_rate", "min_rate", "max_rate"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("min_rate_val", "min_rate == 10"));
    ctx.push_obligation(ProofObligation::assume("max_rate_val", "max_rate == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "cycle_rate >= min_rate && cycle_rate <= max_rate",
    ));
    ctx.push_obligation(ProofObligation::assume("rate_val", "cycle_rate == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_in_bounds",
        "cycle_rate >= 10 && cycle_rate <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cycle rate 120 cycles/min within operating range 10-300",
    );
}

/// Bellows material encoded as 3-way disjunction:
/// 1=PTFE, 2=stainless steel, 3=hastelloy.
/// Verifies that a selected material is one of the valid options.
#[test]
fn test_bellows_pump_material_valid_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("material_val", "material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bellows material stainless steel (2) is a valid selection from PTFE/stainless/hastelloy",
    );
}

/// Drive type encoded as 3-way disjunction:
/// 1=pneumatic, 2=hydraulic, 3=mechanical.
/// Verifies that selecting pneumatic drive yields a valid configuration.
#[test]
fn test_bellows_pump_drive_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_valid",
        "drive_type == 1 || drive_type == 2 || drive_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("drive_val", "drive_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid_drive",
        "drive_type == 1 || drive_type == 2 || drive_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type pneumatic (1) is a valid selection from pneumatic/hydraulic/mechanical",
    );
}

/// Seal arrangement encoded as 3-way disjunction:
/// 1=single, 2=double, 3=hermetic.
/// Verifies that selecting hermetic seal yields a valid arrangement.
#[test]
fn test_bellows_pump_seal_arrangement_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid_seal",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal arrangement hermetic (3) is a valid selection from single/double/hermetic",
    );
}

/// Temperature rating using offset +100 to handle negative range.
/// Physical range: -20 to 250 C, encoded as 80 to 350 (offset +100).
/// Assumes a temperature of 180 C (encoded as 280) and verifies it
/// is within the rated operating range.
#[test]
fn test_bellows_pump_temperature_rating_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // -20 C + 100 offset = 80; 250 C + 100 offset = 350
    ctx.push_obligation(ProofObligation::assume(
        "min_temp_val",
        "min_temp_offset == 80",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "max_temp_val",
        "max_temp_offset == 350",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_offset >= min_temp_offset && temp_offset <= max_temp_offset",
    ));
    // 180 C + 100 offset = 280
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 280"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_bounds",
        "temp_offset >= 80 && temp_offset <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature 180 C (offset 280) within rated range -20 to 250 C (offset 80-350)",
    );
}

/// Displacement volume scaled x100 for 0.01 mL precision.
/// Valid range: 10-100000 (representing 0.10-1000.00 mL).
/// Assumes displacement of 5000 (50.00 mL) and verifies it is
/// within the pump's volumetric capacity.
#[test]
fn test_bellows_pump_displacement_volume_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["disp_x100", "min_disp", "max_disp"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("min_disp_val", "min_disp == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "max_disp_val",
        "max_disp == 100000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x100 >= min_disp && disp_x100 <= max_disp",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "disp_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_in_bounds",
        "disp_x100 >= 10 && disp_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement volume 50.00 mL (x100=5000) within capacity 0.10-1000.00 mL",
    );
}

/// Leak detection as a boolean flag using i32 (1=enabled, 0=disabled).
/// Verifies that when leak detection is enabled, the flag value is
/// correctly recognized as active.
#[test]
fn test_bellows_pump_leak_detection_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_detect_flag", i32_ty());
    ctx.declare_var_typed("is_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "leak_detect_flag == 0 || leak_detect_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "leak_detect_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "is_active == if leak_detect_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detection_active",
        "is_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "leak detection flag enabled (1) correctly recognized as active",
    );
}
