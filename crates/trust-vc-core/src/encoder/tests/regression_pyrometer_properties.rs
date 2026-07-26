// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_temp_range_low_offset() {
    // Non-contact IR pyrometer: temperature with +500 offset (°C)
    // -40°C → 460, min -300°C → 200, max 0°C → 500
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_offset == 200"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_offset == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= min_offset && temp_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: -40C (460) in [-300C (200), 0C (500)]");
}

#[test]
fn test_temp_range_high_offset() {
    // High-temperature pyrometer: +500 offset (°C)
    // 3500°C → 4000, min 500°C → 1000, max 4000°C → 4500
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "temp_offset == 4000"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_offset == 1000"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_offset == 4500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= min_offset && temp_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pyrometer: 3500C (4000) in [500C (1000), 4000C (4500)]",
    );
}

#[test]
fn test_spectral_range_nm() {
    // IR detection wavelength range in nanometers
    // value 8000nm (8µm), min 700nm, max 14000nm (14µm)
    let mut ctx = VerificationContext::new();
    for v in &["wavelength_nm", "min_nm", "max_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_band", i32_ty());
    ctx.push_obligation(ProofObligation::assume("w", "wavelength_nm == 8000"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_nm == 700"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_nm == 14000"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_band == if wavelength_nm >= min_nm && wavelength_nm <= max_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_band == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: 8000nm in [700, 14000] spectral range");
}

#[test]
fn test_response_time_bounded() {
    // Response time in milliseconds
    // value 10ms, min 1ms, max 1000ms
    let mut ctx = VerificationContext::new();
    for v in &["response_ms", "min_ms", "max_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "response_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_ms == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if response_ms >= min_ms && response_ms <= max_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: 10ms response in [1, 1000]");
}

#[test]
fn test_emissivity_scaled() {
    // Emissivity scaled ×100: value 95 (0.95), min 10 (0.10), max 100 (1.00)
    let mut ctx = VerificationContext::new();
    for v in &["emissivity_x100", "min_e", "max_e"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("e", "emissivity_x100 == 95"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_e == 10"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_e == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if emissivity_x100 >= min_e && emissivity_x100 <= max_e { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: emissivity 0.95 (95) in [0.10, 1.00]");
}

#[test]
fn test_detector_type_disjunction() {
    // Detector type: 1=thermopile, 2=pyroelectric, 3=photodiode
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "detector_type == 2")); // pyroelectric
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector_type == 1 || detector_type == 2 || detector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: detector type 2 (pyroelectric) valid");
}

#[test]
fn test_optics_type_disjunction() {
    // Optics type: 1=fixed focus, 2=adjustable focus, 3=fiber optic
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "optics_type == 3")); // fiber optic
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if optics_type == 1 || optics_type == 2 || optics_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: optics type 3 (fiber optic) valid");
}

#[test]
fn test_accuracy_scaled() {
    // Accuracy scaled ×10 (%): value 10 (1.0%), min 5 (0.5%), max 50 (5.0%)
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "min_acc", "max_acc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("lo", "min_acc == 5"));
    ctx.push_obligation(ProofObligation::assume("hi", "max_acc == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if accuracy_x10 >= min_acc && accuracy_x10 <= max_acc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: accuracy 1.0% (10) in [0.5%, 5.0%]");
}

#[test]
fn test_output_type_disjunction() {
    // Output type: 1=4-20mA, 2=0-10V, 3=thermocouple, 4=digital
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 1")); // 4-20mA
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pyrometer: output type 1 (4-20mA) valid");
}

#[test]
fn test_laser_sighting_flag() {
    // Laser sighting: boolean flag using i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_sighting", i32_ty());
    ctx.declare_var_typed("aiming_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ls", "laser_sighting == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "aiming_active == if laser_sighting == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aiming_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pyrometer: laser sighting enabled -> aiming active",
    );
}
