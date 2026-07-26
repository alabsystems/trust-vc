// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Electromagnetic (mag) flowmeter: pipe diameter bounded in [3, 3000] mm.
#[test]
fn test_pipe_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diameter_val", "diameter == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_in_range",
        "diameter >= 3 && diameter <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipe diameter 100 mm within [3, 3000]");
}

/// Accuracy scaled by 100: value 50 means 0.50%, bounded in [10, 200].
#[test]
fn test_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy", u32_ty());
    ctx.push_obligation(ProofObligation::assume("accuracy_val", "accuracy == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_in_range",
        "accuracy >= 10 && accuracy <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 0.50% (50/100) within [0.10%, 2.00%]");
}

/// Liner material: 5-way disjunction (1=PTFE, 2=PFA, 3=rubber, 4=ceramic, 5=polyurethane).
#[test]
fn test_liner_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liner", u32_ty());
    ctx.push_obligation(ProofObligation::assume("liner_val", "liner == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "liner_valid",
        "liner == 1 || liner == 2 || liner == 3 || liner == 4 || liner == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liner material PTFE (1) is one of 5 valid choices");
}

/// Electrode material: 4-way disjunction (1=stainless steel, 2=hastelloy, 3=titanium, 4=platinum).
#[test]
fn test_electrode_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("electrode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("electrode_val", "electrode == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "electrode_valid",
        "electrode == 1 || electrode == 2 || electrode == 3 || electrode == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "electrode material titanium (3) is one of 4 valid choices",
    );
}

/// Excitation frequency (Hz): coil drive bounded in [1, 100].
#[test]
fn test_excitation_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "freq_in_range",
        "freq >= 1 && freq <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "excitation frequency 6 Hz within [1, 100]");
}

/// Flow velocity (mm/s): bounded in [100, 15000].
#[test]
fn test_flow_velocity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("velocity_val", "velocity == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "velocity_in_range",
        "velocity >= 100 && velocity <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow velocity 3000 mm/s within [100, 15000]");
}

/// Conductivity minimum (uS/cm): fluid must have conductivity in [1, 50].
#[test]
fn test_conductivity_minimum_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conductivity", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conductivity_val",
        "conductivity == 5",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conductivity_in_range",
        "conductivity >= 1 && conductivity <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conductivity minimum 5 uS/cm within [1, 50]");
}

/// Output type: 4-way disjunction (1=4-20mA, 2=pulse, 3=HART, 4=Profibus PA).
#[test]
fn test_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.push_obligation(ProofObligation::assume("output_val", "output == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "output_valid",
        "output == 1 || output == 2 || output == 3 || output == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type pulse (2) is one of 4 valid choices");
}

/// Process temperature with +500 offset: value 525 means 25 deg C.
/// Range: 460 (-40 deg C) to 680 (180 deg C).
#[test]
fn test_process_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 525"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= 460 && temp <= 680",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "process temp 25 deg C (offset 525) within [-40, 180] deg C",
    );
}

/// Empty pipe detection: boolean flag using i32 (1 = enabled, 0 = disabled).
#[test]
fn test_empty_pipe_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("epd_flag", i32_ty());
    ctx.declare_var_typed("alarm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("epd_enabled", "epd_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm == if epd_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("alarm_active", "alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "empty pipe detection enabled triggers alarm");
}
