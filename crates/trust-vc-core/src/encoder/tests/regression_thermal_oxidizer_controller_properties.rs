// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Chamber temperature (°C) must be bounded [700, 1100].
#[test]
fn chamber_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_lower", "temp >= 700"));
    ctx.push_obligation(ProofObligation::assume("temp_upper", "temp <= 1100"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= 700 && temp <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber temperature bounded [700, 1100] C");
}

/// Residence time (×10 s) must be bounded [3, 30].
/// E.g., 0.5s → 5, 3.0s → 30.
#[test]
fn residence_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt_lower", "rt >= 3"));
    ctx.push_obligation(ProofObligation::assume("rt_upper", "rt <= 30"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "rt >= 3 && rt <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time bounded [3, 30] (x10 seconds)");
}

/// Oxidizer type is a 3-way disjunction:
/// 1=regenerative (RTO), 2=recuperative, 3=catalytic.
#[test]
fn oxidizer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("otype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "otype_valid",
        "otype == 1 || otype == 2 || otype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "otype_bounded",
        "otype >= 1 && otype <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oxidizer type in {1=RTO, 2=recuperative, 3=catalytic}",
    );
}

/// Air flow (m³/h) must be bounded [100, 100000].
#[test]
fn air_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_lower", "flow >= 100"));
    ctx.push_obligation(ProofObligation::assume("flow_upper", "flow <= 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_range",
        "flow >= 100 && flow <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow bounded [100, 100000] m3/h");
}

/// Destruction efficiency (×100 %) must be bounded [9000, 9999].
/// E.g., 99.50% → 9950.
#[test]
fn destruction_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eff_lower", "eff >= 9000"));
    ctx.push_obligation(ProofObligation::assume("eff_upper", "eff <= 9999"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_in_range",
        "eff >= 9000 && eff <= 9999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "destruction efficiency bounded [9000, 9999] (x100 %)",
    );
}

/// Burner capacity (kW) must be bounded [50, 10000].
#[test]
fn burner_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burner", i32_ty());
    ctx.push_obligation(ProofObligation::assume("burner_lower", "burner >= 50"));
    ctx.push_obligation(ProofObligation::assume("burner_upper", "burner <= 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "burner_in_range",
        "burner >= 50 && burner <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "burner capacity bounded [50, 10000] kW");
}

/// Heat recovery (×10 %) must be bounded [0, 980].
/// E.g., 95.0% → 950.
#[test]
fn heat_recovery_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hr", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hr_lower", "hr >= 0"));
    ctx.push_obligation(ProofObligation::assume("hr_upper", "hr <= 980"));
    ctx.push_obligation(ProofObligation::assert(
        "hr_in_range",
        "hr >= 0 && hr <= 980",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat recovery bounded [0, 980] (x10 %)");
}

/// VOC concentration (ppm) must be bounded [1, 10000].
#[test]
fn voc_concentration_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("voc_lower", "voc >= 1"));
    ctx.push_obligation(ProofObligation::assume("voc_upper", "voc <= 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "voc_in_range",
        "voc >= 1 && voc <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VOC concentration bounded [1, 10000] ppm");
}

/// Media bed type is a 3-way disjunction:
/// 1=ceramic saddle, 2=structured packing, 3=random packing.
#[test]
fn media_bed_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bed_valid",
        "bed == 1 || bed == 2 || bed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bed_bounded",
        "bed >= 1 && bed <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "media bed type in {1=ceramic, 2=structured, 3=random}",
    );
}

/// LEL monitoring is a boolean flag encoded as i32 (0 or 1).
#[test]
fn lel_monitoring_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lel_mon", i32_ty());
    ctx.declare_var_typed("alarm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lel_flag",
        "lel_mon == 0 || lel_mon == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("lel_enabled", "lel_mon == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm == if lel_mon == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("alarm_active", "alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LEL monitoring enabled implies alarm active");
}
