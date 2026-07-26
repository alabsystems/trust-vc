// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_supply_pressure_within_range() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_kpa", "min_kpa", "max_kpa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "supply_kpa == 400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_kpa == 140"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_kpa == 700"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if supply_kpa >= min_kpa && supply_kpa <= max_kpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "supply pressure: 400 kPa in [140, 700]");
}

#[test]
fn test_input_signal_within_range() {
    let mut ctx = VerificationContext::new();
    for v in &["signal_ua", "min_ua", "max_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // 4-20 mA control signal represented in microamps
    ctx.push_obligation(ProofObligation::assume("sv", "signal_ua == 12000")); // 12 mA
    ctx.push_obligation(ProofObligation::assume("mn", "min_ua == 4000")); // 4 mA
    ctx.push_obligation(ProofObligation::assume("mx", "max_ua == 20000")); // 20 mA
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if signal_ua >= min_ua && signal_ua <= max_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input signal: 12000 uA (12 mA) in [4000, 20000]");
}

#[test]
fn test_travel_range_within_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["stroke_mm", "min_mm", "max_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "stroke_mm == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mm == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if stroke_mm >= min_mm && stroke_mm <= max_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "travel range: 50 mm in [10, 600]");
}

#[test]
fn test_actuator_type_valid_disjunction() {
    // 1=spring-return, 2=double-acting, 3=rotary
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("actuator_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("at", "actuator_type == 2")); // double-acting
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if actuator_type == 1 || actuator_type == 2 || actuator_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "actuator type: 2 (double-acting) in {1,2,3}");
}

#[test]
fn test_positioning_accuracy_within_spec() {
    // Accuracy as percentage * 100 to avoid fractions: 50 = 0.50%
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "min_x100", "max_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("av", "accuracy_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume("mn", "min_x100 == 10")); // 0.10%
    ctx.push_obligation(ProofObligation::assume("mx", "max_x100 == 200")); // 2.00%
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_spec == if accuracy_x100 >= min_x100 && accuracy_x100 <= max_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "positioning accuracy: 50 (0.50%) in [10, 200]");
}

#[test]
fn test_feedback_type_valid_disjunction() {
    // 1=mechanical, 2=potentiometer, 3=LVDT
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feedback_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ft", "feedback_type == 3")); // LVDT
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if feedback_type == 1 || feedback_type == 2 || feedback_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feedback type: 3 (LVDT) in {1,2,3}");
}

#[test]
fn test_communication_protocol_valid_disjunction() {
    // 1=HART, 2=Foundation Fieldbus, 3=Profibus PA, 4=analog
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_protocol", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "comm_protocol == 1")); // HART
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if comm_protocol == 1 || comm_protocol == 2 || comm_protocol == 3 || comm_protocol == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication: 1 (HART) in {1,2,3,4}");
}

#[test]
fn test_operating_temperature_offset_within_range() {
    // Temperature offset +500: actual = stored - 500
    // value 525 = 25 deg C, min 440 = -60 deg C, max 585 = 85 deg C
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tv", "temp_offset == 525")); // 25 deg C
    ctx.push_obligation(ProofObligation::assume("mn", "min_offset == 440")); // -60 deg C
    ctx.push_obligation(ProofObligation::assume("mx", "max_offset == 585")); // 85 deg C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= min_offset && temp_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp: 525 (25 deg C) in [440, 585] offset +500",
    );
}

#[test]
fn test_ip_rating_valid_non_sequential() {
    // Valid IP ratings: 66, 67, 68 (non-sequential encoding)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_rating", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ipr", "ip_rating == 67")); // IP67
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if ip_rating == 66 || ip_rating == 67 || ip_rating == 68 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IP rating: 67 in {66,67,68}");
}

#[test]
fn test_sil_rated_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil_rated", i32_ty());
    ctx.declare_var_typed("requires_diagnostics", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sil_rated == 1")); // SIL rated
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "requires_diagnostics == if sil_rated == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "requires_diagnostics == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIL rated flag: 1 -> requires diagnostics");
}
