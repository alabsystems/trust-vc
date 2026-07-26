// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ---------- 1. Mass range (amu) ----------
#[test]
fn test_irms_mass_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_amu", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mass_val", "mass_amu == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "mass_in_range",
        "mass_amu >= 1 && mass_amu <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass 300 amu is within valid IRMS range [1, 500]");
}

// ---------- 2. Mass resolution (m/delta_m) ----------
#[test]
fn test_irms_mass_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "resolution == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_in_range",
        "resolution >= 100 && resolution <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resolution 10000 is within valid range [100, 50000]",
    );
}

// ---------- 3. Precision (x10000 per mil) ----------
#[test]
fn test_irms_precision() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("precision_x10000", i32_ty());
    // 50 represents 0.0050 per mil
    ctx.push_obligation(ProofObligation::assume(
        "prec_val",
        "precision_x10000 == 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "precision_in_range",
        "precision_x10000 >= 1 && precision_x10000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision 50 (0.0050 per mil) is within valid range [1, 1000]",
    );
}

// ---------- 4. Number of collectors ----------
#[test]
fn test_irms_num_collectors() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collectors", i32_ty());
    ctx.push_obligation(ProofObligation::assume("coll_val", "collectors == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "collectors_in_range",
        "collectors >= 1 && collectors <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 collectors is within valid range [1, 20]");
}

// ---------- 5. Accelerating voltage (V) ----------
#[test]
fn test_irms_accelerating_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume("volt_val", "voltage == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "voltage >= 1000 && voltage <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accelerating voltage 5000 V is within valid range [1000, 10000]",
    );
}

// ---------- 6. Source pressure (x1000 mbar) ----------
#[test]
fn test_irms_source_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x1000", i32_ty());
    // 5 represents 0.005 mbar
    ctx.push_obligation(ProofObligation::assume("press_val", "pressure_x1000 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_in_range",
        "pressure_x1000 >= 1 && pressure_x1000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source pressure 5 (0.005 mbar) is within valid range [1, 100]",
    );
}

// ---------- 7. Inlet system (disjunction) ----------
#[test]
fn test_irms_inlet_system() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet", i32_ty());
    // 1=dual-inlet, 2=continuous-flow, 3=laser-ablation
    ctx.push_obligation(ProofObligation::assume("inlet_val", "inlet == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_valid",
        "inlet == 1 || inlet == 2 || inlet == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet system continuous-flow (2) is a valid IRMS inlet type",
    );
}

// ---------- 8. Ionization mode (disjunction) ----------
#[test]
fn test_irms_ionization_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionization", i32_ty());
    // 1=electron-impact, 2=thermal, 3=chemical
    ctx.push_obligation(ProofObligation::assume("ion_val", "ionization == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "ionization_valid",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization mode electron-impact (1) is a valid IRMS mode",
    );
}

// ---------- 9. Detector type (disjunction) ----------
#[test]
fn test_irms_detector_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    // 1=faraday, 2=electron-multiplier, 3=multi-collector
    ctx.push_obligation(ProofObligation::assume("det_val", "detector == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type multi-collector (3) is a valid IRMS detector",
    );
}

// ---------- 10. Automatic reference gas injection (boolean flag) ----------
#[test]
fn test_irms_auto_ref_gas_injection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_ref_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_ref_gas == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_ref_active",
        "if auto_ref_gas == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic reference gas injection is active when flag is 1",
    );
}
