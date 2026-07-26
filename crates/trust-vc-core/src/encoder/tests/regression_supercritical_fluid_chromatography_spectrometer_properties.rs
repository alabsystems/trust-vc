// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Supercritical fluid chromatography (SFC) spectrometer property verification.
// Integer encodings avoid floating-point: values are scaled to fixed-point
// representations (e.g., 300 = 3.00 mL/min, 1500 = 150.0 bar).

#[test]
fn test_sfc_column_length_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "col_len_range",
        "col_len >= 50 && col_len <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("col_len_val", "col_len == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "col_len_valid",
        "col_len >= 50 && col_len <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column length 150 mm within [50, 500]");
}

#[test]
fn test_sfc_back_pressure_bounded() {
    // Back pressure in units of 0.1 bar (1500 = 150.0 bar)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 100 && pressure <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_valid",
        "pressure >= 100 && pressure <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "back pressure 1500 (150.0 bar) within [100, 6000]");
}

#[test]
fn test_sfc_flow_rate_bounded() {
    // Flow rate in units of 0.01 mL/min (300 = 3.00 mL/min)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 10 && flow <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_valid",
        "flow >= 10 && flow <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 300 (3.00 mL/min) within [10, 5000]");
}

#[test]
fn test_sfc_column_temperature_bounded() {
    // Temperature offset: stored as value + 100 (40 C = 140)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 100 && temp <= 400",
    ));
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 140"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_valid",
        "temp >= 100 && temp <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column temperature 140 (40 C) within [100, 400]");
}

#[test]
fn test_sfc_modifier_percentage_bounded() {
    // Modifier percentage in units of 0.1% (200 = 20.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("modifier", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "modifier_range",
        "modifier >= 0 && modifier <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("modifier_val", "modifier == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "modifier_valid",
        "modifier >= 0 && modifier <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modifier percentage 200 (20.0%) within [0, 500]");
}

#[test]
fn test_sfc_injection_volume_bounded() {
    // Injection volume in units of 0.1 uL (50 = 5.0 uL)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inj_vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inj_vol_range",
        "inj_vol >= 1 && inj_vol <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("inj_vol_val", "inj_vol == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "inj_vol_valid",
        "inj_vol >= 1 && inj_vol <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "injection volume 50 (5.0 uL) within [1, 1000]");
}

#[test]
fn test_sfc_mobile_phase_selection() {
    // 1 = pure CO2, 2 = CO2-methanol, 3 = CO2-ethanol
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase", i32_ty());
    ctx.push_obligation(ProofObligation::assume("phase_val", "phase == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "phase_valid",
        "phase == 1 || phase == 2 || phase == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mobile phase CO2-methanol (2) is a valid selection",
    );
}

#[test]
fn test_sfc_detection_method_selection() {
    // 1 = UV-Vis, 2 = ELSD, 3 = mass-spec
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("detector_val", "detector == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection method UV-Vis (1) is a valid selection");
}

#[test]
fn test_sfc_column_chemistry_selection() {
    // 1 = bare-silica, 2 = C18, 3 = chiral
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chemistry", i32_ty());
    ctx.push_obligation(ProofObligation::assume("chemistry_val", "chemistry == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "chemistry_valid",
        "chemistry == 1 || chemistry == 2 || chemistry == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "column chemistry bare-silica (1) is a valid selection",
    );
}

#[test]
fn test_sfc_automatic_back_pressure_regulation() {
    // Boolean flag: 1 = enabled, 0 = disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("abpr_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("abpr_enabled", "abpr_flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "abpr_active",
        "if abpr_flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ABPR flag enabled implies regulation active");
}
