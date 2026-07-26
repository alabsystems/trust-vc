// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Test voltage (V) — bounded [100, 100000].
/// From 100 V to 100 kV.
#[test]
fn test_dielectric_strength_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "v_a",
        "voltage >= 100 && voltage <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "v_c",
        "voltage >= 100 && voltage <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage in [100, 100000] V");
}

/// Test 2: Ramp rate (x10 V/s) — bounded [1, 50000].
/// 1 represents 0.1 V/s, 50000 represents 5000.0 V/s.
#[test]
fn test_dielectric_strength_ramp_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ramp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ramp_a",
        "ramp_x10 >= 1 && ramp_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ramp_c",
        "ramp_x10 >= 1 && ramp_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ramp rate x10 in [1, 50000] representing 0.1-5000.0 V/s",
    );
}

/// Test 3: Leakage current threshold (x100 mA) — bounded [1, 10000].
/// 1 represents 0.01 mA, 10000 represents 100.00 mA.
#[test]
fn test_dielectric_strength_leakage_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "leak_a",
        "leak_x100 >= 1 && leak_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "leak_c",
        "leak_x100 >= 1 && leak_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leakage current threshold x100 mA in [1, 10000]");
}

/// Test 4: Dwell time at voltage (x10 seconds) — bounded [1, 36000].
/// 1 represents 0.1 s, 36000 represents 3600.0 s (1 hour).
#[test]
fn test_dielectric_strength_dwell_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dwell_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dwell_a",
        "dwell_x10 >= 1 && dwell_x10 <= 36000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dwell_c",
        "dwell_x10 >= 1 && dwell_x10 <= 36000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dwell time x10 in [1, 36000] representing 0.1-3600.0 s",
    );
}

/// Test 5: Specimen thickness (x100 mm) — bounded [1, 50000].
/// 1 represents 0.01 mm, 50000 represents 500.00 mm.
#[test]
fn test_dielectric_strength_specimen_thickness_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thick_a",
        "thick_x100 >= 1 && thick_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thick_c",
        "thick_x100 >= 1 && thick_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "specimen thickness x100 mm in [1, 50000]");
}

/// Test 6: Breakdown voltage (V) — bounded [50, 100000].
#[test]
fn test_dielectric_strength_breakdown_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("breakdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bd_a",
        "breakdown >= 50 && breakdown <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bd_c",
        "breakdown >= 50 && breakdown <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "breakdown voltage in [50, 100000] V");
}

/// Test 7: Voltage waveform — 3-way disjunction.
/// 1=DC, 2=AC-50Hz, 3=AC-60Hz.
#[test]
fn test_dielectric_strength_waveform_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "waveform >= 1 && waveform <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "waveform 3-way (DC/AC-50Hz/AC-60Hz)");
}

/// Test 8: Electrode configuration — 3-way disjunction.
/// 1=opposed-disc, 2=rod-plane, 3=sphere-sphere.
#[test]
fn test_dielectric_strength_electrode_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elec_a",
        "electrode == 1 || electrode == 2 || electrode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elec_c",
        "electrode >= 1 && electrode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "electrode config 3-way (opposed-disc/rod-plane/sphere-sphere)",
    );
}

/// Test 9: Insulation class — 3-way disjunction.
/// 1=solid, 2=liquid, 3=composite.
#[test]
fn test_dielectric_strength_insulation_class_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("insul", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ins_a",
        "insul == 1 || insul == 2 || insul == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("ins_c", "insul >= 1 && insul <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insulation class 3-way (solid/liquid/composite)");
}

/// Test 10: Auto-discharge flag — boolean.
/// 0=manual, 1=auto.
#[test]
fn test_dielectric_strength_auto_discharge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-discharge flag is boolean (0 or 1)");
}
