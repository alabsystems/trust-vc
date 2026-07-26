// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Spark source mass spectrometer properties.
// Models key parameters: mass range, mass resolution, detection limit, spark voltage,
// spark repetition rate, electrode geometry, analyzer type, detection method, spark gap,
// vacuum interlock.

#[test]
fn test_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_amu", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass_amu >= 1 && mass_amu <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert("mass_lower", "mass_amu >= 1"));
    ctx.push_obligation(ProofObligation::assert("mass_upper", "mass_amu <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: mass range (amu) bounded [1, 300]",
    );
}

#[test]
fn test_mass_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "resolution >= 500 && resolution <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert("res_lower", "resolution >= 500"));
    ctx.push_obligation(ProofObligation::assert("res_upper", "resolution <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: mass resolution (m/dm) bounded [500, 50000]",
    );
}

#[test]
fn test_detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detect_ppb", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detect_range",
        "detect_ppb >= 1 && detect_ppb <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert("detect_lower", "detect_ppb >= 1"));
    ctx.push_obligation(ProofObligation::assert("detect_upper", "detect_ppb <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: detection limit (ppb) bounded [1, 100]",
    );
}

#[test]
fn test_spark_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_kv >= 5 && voltage_kv <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert("voltage_lower", "voltage_kv >= 5"));
    ctx.push_obligation(ProofObligation::assert("voltage_upper", "voltage_kv <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: spark voltage (kV) bounded [5, 50]",
    );
}

#[test]
fn test_spark_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep_rate_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rep_rate_hz >= 50 && rep_rate_hz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("rate_lower", "rep_rate_hz >= 50"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_upper",
        "rep_rate_hz <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: spark repetition rate (Hz) bounded [50, 10000]",
    );
}

#[test]
fn test_electrode_geometry_three_way_disjunction() {
    // 1=rod-rod, 2=rod-plate, 3=point-plane
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "geometry_valid",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "geometry_in_range",
        "geometry >= 1 && geometry <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: electrode geometry is one of {rod-rod, rod-plate, point-plane}",
    );
}

#[test]
fn test_analyzer_type_three_way_disjunction() {
    // 1=mattauch-herzog, 2=nier-johnson, 3=double-focusing
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analyzer_valid",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_in_range",
        "analyzer >= 1 && analyzer <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: analyzer type is one of {mattauch-herzog, nier-johnson, double-focusing}",
    );
}

#[test]
fn test_detection_method_three_way_disjunction() {
    // 1=photographic-plate, 2=electrical-detection, 3=image-current
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detection", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detection_valid",
        "detection == 1 || detection == 2 || detection == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detection_in_range",
        "detection >= 1 && detection <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spark source MS: detection method is one of {photographic-plate, electrical-detection, image-current}");
}

#[test]
fn test_spark_gap_scaled_bounded() {
    // Spark gap in x100 mm: 1-500 represents 0.01-5.00 mm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gap_range",
        "gap_x100 >= 1 && gap_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("gap_lower", "gap_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("gap_upper", "gap_x100 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: spark gap (x100 mm) bounded [1, 500] (0.01-5.00 mm)",
    );
}

#[test]
fn test_vacuum_interlock_boolean_flag() {
    // Boolean flag encoded as i32: 0=interlock disengaged, 1=interlock engaged
    let mut ctx = VerificationContext::new();
    for v in &["interlock", "spark_allowed"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "interlock_is_flag",
        "interlock == 0 || interlock == 1",
    ));
    // Spark is only allowed when vacuum interlock is engaged (1)
    ctx.push_obligation(ProofObligation::assume(
        "spark_def",
        "spark_allowed == if interlock == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spark_matches_interlock",
        "spark_allowed == interlock",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spark source MS: vacuum interlock boolean flag: spark permission mirrors interlock state",
    );
}
