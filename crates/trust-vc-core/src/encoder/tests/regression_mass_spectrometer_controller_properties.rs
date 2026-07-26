// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_mass_range_min_bounded() {
    // Minimum detectable mass in Daltons: 1 to 10 Da
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_min_da", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mm", "mass_min_da == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if mass_min_da >= 1 && mass_min_da <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range min: 1 Da in [1, 10]");
}

#[test]
fn test_mass_range_max_bounded() {
    // Maximum detectable mass in Daltons: 1000 to 100000 Da
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_max_da", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mx", "mass_max_da == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if mass_max_da >= 1000 && mass_max_da <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range max: 50000 Da in [1000, 100000]");
}

#[test]
fn test_mass_resolution_bounded() {
    // Mass resolution (resolving power): 100 to 1000000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res", "resolution == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if resolution >= 100 && resolution <= 1000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass resolution: 10000 in [100, 1000000]");
}

#[test]
fn test_sensitivity_scaled_femtogram() {
    // Sensitivity at 0.001 fg level, scaled x1000 to avoid fractions
    // 5 fg = 5000 in x1000 units; threshold 10 fg = 10000 in x1000 units
    let mut ctx = VerificationContext::new();
    for v in &["sensitivity_x1000", "threshold_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sens", "sensitivity_x1000 == 5000")); // 5.000 fg
    ctx.push_obligation(ProofObligation::assume(
        "thresh",
        "threshold_x1000 == 10000",
    )); // 10.000 fg
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "meets_spec == if sensitivity_x1000 <= threshold_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity: 5.000 fg <= 10.000 fg threshold");
}

#[test]
fn test_scan_speed_bounded() {
    // Scan speed in Da/s: 100 to 20000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ss", "scan_speed == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if scan_speed >= 100 && scan_speed <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed: 5000 Da/s in [100, 20000]");
}

#[test]
fn test_analyzer_type_disjunction() {
    // Analyzer type: 1=quadrupole, 2=TOF, 3=ion trap
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "analyzer == 2")); // TOF
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if analyzer == 1 || analyzer == 2 || analyzer == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analyzer: TOF (2) in {quadrupole, TOF, ion trap}");
}

#[test]
fn test_ionization_mode_disjunction() {
    // Ionization mode: 1=EI, 2=ESI, 3=MALDI
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionization", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ion", "ionization == 3")); // MALDI
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if ionization == 1 || ionization == 2 || ionization == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionization: MALDI (3) in {EI, ESI, MALDI}");
}

#[test]
fn test_vacuum_level_scaled() {
    // Vacuum pressure at 0.1 Pa resolution, scaled x10
    // 0.5 Pa = 5 in x10 units; max 1.0 Pa = 10 in x10 units
    let mut ctx = VerificationContext::new();
    for v in &["vacuum_x10", "max_vacuum_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("adequate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vac", "vacuum_x10 == 5")); // 0.5 Pa
    ctx.push_obligation(ProofObligation::assume("mv", "max_vacuum_x10 == 10")); // 1.0 Pa
    ctx.push_obligation(ProofObligation::assume(
        "ad_def",
        "adequate == if vacuum_x10 <= max_vacuum_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "adequate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum: 0.5 Pa <= 1.0 Pa max");
}

#[test]
fn test_mass_accuracy_scaled_ppm() {
    // Mass accuracy at 0.1 ppm resolution, scaled x10
    // 2.5 ppm = 25 in x10 units; spec 5.0 ppm = 50 in x10 units
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "spec_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc", "accuracy_x10 == 25")); // 2.5 ppm
    ctx.push_obligation(ProofObligation::assume("sp", "spec_x10 == 50")); // 5.0 ppm
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "meets_spec == if accuracy_x10 <= spec_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass accuracy: 2.5 ppm <= 5.0 ppm spec");
}

#[test]
fn test_tandem_ms_boolean_flag() {
    // Tandem MS (MS/MS) capability: boolean flag as i32
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_msms", i32_ty());
    ctx.declare_var_typed("tandem_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "has_msms == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "tandem_enabled == if has_msms == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "tandem_enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tandem MS: enabled when flag == 1");
}
