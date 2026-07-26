// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Linear Variable Displacement Transducer (LVDT) property verification.
// Fractional values use integer scaling (x100, x1000).
// Negative temperatures use offset encoding (+500).

#[test]
fn test_lvdt_stroke_range_x100() {
    // Stroke length in units of 0.01 mm: 5000 = 50.00 mm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("stroke_val", "stroke_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_lower",
        "stroke_x100 >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_upper",
        "stroke_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke 50.00 mm in [1.00, 1000.00] mm");
}

#[test]
fn test_lvdt_linearity_x100() {
    // Linearity in units of 0.01 %FS: 25 = 0.25 %FS
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("linearity_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lin_val", "linearity_x100 == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "linearity_lower",
        "linearity_x100 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "linearity_upper",
        "linearity_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linearity 0.25 %FS in [0.01, 1.00] %FS");
}

#[test]
fn test_lvdt_excitation_frequency_bounded() {
    // Excitation frequency in Hz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq == 2500"));
    ctx.push_obligation(ProofObligation::assert("freq_lower", "freq >= 50"));
    ctx.push_obligation(ProofObligation::assert("freq_upper", "freq <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "excitation frequency 2500 Hz in [50, 10000] Hz");
}

#[test]
fn test_lvdt_core_material_disjunction() {
    // Core material: 1=nickel-iron, 2=ferrite, 3=permalloy
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("core_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume("core_val", "core_mat == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "core_mat == 1 || core_mat == 2 || core_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "core material ferrite is valid (1|2|3)");
}

#[test]
fn test_lvdt_output_type_disjunction() {
    // Output type: 1=AC, 2=DC voltage, 3=4-20mA, 4=digital
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("out_val", "output_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_output",
        "output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 4-20mA is valid (1|2|3|4)");
}

#[test]
fn test_lvdt_excitation_voltage_bounded() {
    // Excitation voltage in mV: 3000 = 3.000 V
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume("volt_val", "voltage == 3000"));
    ctx.push_obligation(ProofObligation::assert("volt_lower", "voltage >= 500"));
    ctx.push_obligation(ProofObligation::assert("volt_upper", "voltage <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "excitation voltage 3000 mV in [500, 10000] mV");
}

#[test]
fn test_lvdt_body_diameter_bounded() {
    // Body diameter in mm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter == 20"));
    ctx.push_obligation(ProofObligation::assert("dia_lower", "diameter >= 5"));
    ctx.push_obligation(ProofObligation::assert("dia_upper", "diameter <= 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "body diameter 20 mm in [5, 75] mm");
}

#[test]
fn test_lvdt_repeatability_x1000() {
    // Repeatability in units of 0.001 %FS: 10 = 0.010 %FS
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeat_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rep_val", "repeat_x1000 == 10"));
    ctx.push_obligation(ProofObligation::assert("repeat_lower", "repeat_x1000 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "repeat_upper",
        "repeat_x1000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repeatability 0.010 %FS in [0.001, 0.100] %FS");
}

#[test]
fn test_lvdt_operating_temp_offset() {
    // Temperature with +500 offset: 525 = 25 deg C, range 440 (-60 C) to 650 (150 C)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 525"));
    ctx.push_obligation(ProofObligation::assert("temp_lower", "temp >= 440"));
    ctx.push_obligation(ProofObligation::assert("temp_upper", "temp <= 650"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 25 C (offset 525) in [440, 650]");
}

#[test]
fn test_lvdt_spring_return_flag() {
    // Spring return boolean encoded as i32: 1=true, 0=false
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("spring_active", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spring return flag active when flag=1");
}
