// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Magnetic Particle Inspection (MPI) domain properties.
// Encodes physical and procedural constraints for non-destructive testing (NDT).

#[test]
fn magnetizing_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 100 && current <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "current >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "current <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetizing current (A) stays within [100, 10000]");
}

#[test]
fn field_strength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("field", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "field_range",
        "field >= 100 && field <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "field >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "field <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "field strength (A/m) stays within [100, 50000]");
}

#[test]
fn inspection_method_three_way_disjunction() {
    // 1=wet fluorescent, 2=dry visible, 3=wet visible
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_valid",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "method >= 1 && method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inspection method is one of {1,2,3}");
}

#[test]
fn magnetization_type_four_way_disjunction() {
    // 1=AC, 2=DC, 3=HWDC (half-wave DC), 4=FWDC (full-wave DC)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mag_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mag_type_valid",
        "mag_type == 1 || mag_type == 2 || mag_type == 3 || mag_type == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "mag_type >= 1 && mag_type <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetization type is one of {1,2,3,4}");
}

#[test]
fn coil_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_range",
        "diameter >= 50 && diameter <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "diameter >= 50"));
    ctx.push_obligation(ProofObligation::assert("upper", "diameter <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coil diameter (mm) stays within [50, 1000]");
}

#[test]
fn shot_duration_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duration", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "duration_range",
        "duration >= 1 && duration <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "duration >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "duration <= 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shot duration (s) stays within [1, 30]");
}

#[test]
fn uv_intensity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("uv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "uv_range",
        "uv >= 100 && uv <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "uv >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "uv <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV intensity (uW/cm^2) stays within [100, 50000]");
}

#[test]
fn demagnetization_steps_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steps", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "steps_range",
        "steps >= 1 && steps <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "steps >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "steps <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "demagnetization steps stays within [1, 20]");
}

#[test]
fn sensitivity_level_three_way_disjunction() {
    // 1=low, 2=medium, 3=high
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("level", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "level_valid",
        "level == 1 || level == 2 || level == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "level >= 1 && level <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity level is one of {low=1, medium=2, high=3}",
    );
}

#[test]
fn residual_field_check_boolean_flag() {
    // Boolean flag encoded as i32: 0=not checked, 1=checked
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("checked", i32_ty());
    ctx.declare_var_typed("report_valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "checked == 0 || checked == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_set", "checked == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "report_def",
        "report_valid == if checked == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("report_ok", "report_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residual field check flag=1 implies valid report");
}
