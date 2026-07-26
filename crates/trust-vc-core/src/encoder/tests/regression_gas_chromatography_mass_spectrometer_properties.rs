// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Mass range in atomic mass units (amu): valid range 1..=2000.
#[test]
fn test_gcms_mass_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_amu", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mass_lower", "mass_amu >= 1"));
    ctx.push_obligation(ProofObligation::assume("mass_upper", "mass_amu <= 2000"));
    ctx.push_obligation(ProofObligation::assume("mass_val", "mass_amu == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "mass_in_range",
        "mass_amu >= 1 && mass_amu <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass 1000 amu within valid range 1..=2000");
}

/// Scan speed in amu/sec: valid range 100..=50000.
#[test]
fn test_gcms_scan_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_lower", "scan_speed >= 100"));
    ctx.push_obligation(ProofObligation::assume(
        "speed_upper",
        "scan_speed <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "scan_speed == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_in_range",
        "scan_speed >= 100 && scan_speed <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed 10000 amu/sec within valid range");
}

/// Mass resolution (unitless): valid range 100..=100000.
#[test]
fn test_gcms_mass_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_lower", "resolution >= 100"));
    ctx.push_obligation(ProofObligation::assume("res_upper", "resolution <= 100000"));
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "res_in_range",
        "resolution >= 100 && resolution <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 5000 within valid range");
}

/// Sensitivity scaled by 100 (1 = 0.01 pg): valid range 1..=10000.
#[test]
fn test_gcms_sensitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensitivity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sens_lower", "sensitivity >= 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sens_upper",
        "sensitivity <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("sens_val", "sensitivity == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "sens_in_range",
        "sensitivity >= 1 && sensitivity <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity 100 (1.00 pg) within valid range");
}

/// Column length in meters: valid range 5..=100.
#[test]
fn test_gcms_column_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("column_len", i32_ty());
    ctx.push_obligation(ProofObligation::assume("col_lower", "column_len >= 5"));
    ctx.push_obligation(ProofObligation::assume("col_upper", "column_len <= 100"));
    ctx.push_obligation(ProofObligation::assume("col_val", "column_len == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "col_in_range",
        "column_len >= 5 && column_len <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column length 30 m within valid range");
}

/// Oven temperature offset by +100 (300 C = 400): valid range 100..=600.
#[test]
fn test_gcms_oven_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oven_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_lower", "oven_temp >= 100"));
    ctx.push_obligation(ProofObligation::assume("temp_upper", "oven_temp <= 600"));
    ctx.push_obligation(ProofObligation::assume("temp_val", "oven_temp == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "oven_temp >= 100 && oven_temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oven temp 400 (300 C) within valid range");
}

/// Ionization mode: 1=electron-impact, 2=chemical, 3=field.
#[test]
fn test_gcms_ionization_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ion_val", "ion_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "ion_valid",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionization mode 1 (electron-impact) is valid");
}

/// Mass analyzer type: 1=quadrupole, 2=ion-trap, 3=TOF.
#[test]
fn test_gcms_mass_analyzer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("analyzer_val", "analyzer == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_valid",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass analyzer 1 (quadrupole) is valid");
}

/// Injection mode: 1=split, 2=splitless, 3=on-column.
#[test]
fn test_gcms_injection_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("inj_val", "inj_mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "inj_valid",
        "inj_mode == 1 || inj_mode == 2 || inj_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "injection mode 2 (splitless) is valid");
}

/// Automatic tune flag: boolean encoded as i32 (1=enabled, 0=disabled).
#[test]
fn test_gcms_automatic_tune() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_tune", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tune_enabled", "auto_tune == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "tune_active",
        "(if auto_tune == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto_tune flag 1 implies tune is active");
}
