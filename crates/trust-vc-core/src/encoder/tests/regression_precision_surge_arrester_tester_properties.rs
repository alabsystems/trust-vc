// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_surge_arrester_tester_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    // Test voltage in kV: range 1-800 kV
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 1 && voltage <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 1 && voltage <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage bounded 1-800 kV");
}

#[test]
fn test_surge_arrester_tester_leakage_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_x100", i32_ty());
    // Leakage current at x100 uA (0.01 mA precision): range 1-50000 representing 0.01-500.00 mA
    ctx.push_obligation(ProofObligation::assume(
        "leak_range",
        "leak_x100 >= 1 && leak_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "leak_bounded",
        "leak_x100 >= 1 && leak_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "leakage current x100 bounded 1-50000 (0.01-500.00 mA)",
    );
}

#[test]
fn test_surge_arrester_tester_reference_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_x10", i32_ty());
    // Reference voltage at x10 kV (0.1 kV precision): range 10-8000 representing 1.0-800.0 kV
    ctx.push_obligation(ProofObligation::assume(
        "ref_range",
        "ref_x10 >= 10 && ref_x10 <= 8000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ref_bounded",
        "ref_x10 >= 10 && ref_x10 <= 8000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference voltage x10 bounded 10-8000 (1.0-800.0 kV)",
    );
}

#[test]
fn test_surge_arrester_tester_power_loss_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("loss_x100", i32_ty());
    // Power loss at x100 W (0.01 W precision): range 1-100000 representing 0.01-1000.00 W
    ctx.push_obligation(ProofObligation::assume(
        "loss_range",
        "loss_x100 >= 1 && loss_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "loss_bounded",
        "loss_x100 >= 1 && loss_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power loss x100 bounded 1-100000 (0.01-1000.00 W)");
}

#[test]
fn test_surge_arrester_tester_third_harmonic_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("harm_x1000", i32_ty());
    // Third harmonic current at x1000 mA (0.001 mA precision): range 1-10000 representing 0.001-10.000 mA
    ctx.push_obligation(ProofObligation::assume(
        "harm_range",
        "harm_x1000 >= 1 && harm_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "harm_bounded",
        "harm_x1000 >= 1 && harm_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "third harmonic x1000 bounded 1-10000 (0.001-10.000 mA)",
    );
}

#[test]
fn test_surge_arrester_tester_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    // Temperature offset +100 degC: range 80-250 representing -20 to 150 degC
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 80 && temp_off <= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 80 && temp_off <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature offset bounded 80-250 (-20 to 150 degC)",
    );
}

#[test]
fn test_surge_arrester_tester_arrester_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arr_type", i32_ty());
    // Arrester type: 1=MOV, 2=gapped, 3=polymer
    ctx.push_obligation(ProofObligation::assume(
        "arr_type_enum",
        "arr_type == 1 || arr_type == 2 || arr_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "arr_type_valid",
        "arr_type == 1 || arr_type == 2 || arr_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "arrester type three-way (MOV/gapped/polymer)");
}

#[test]
fn test_surge_arrester_tester_voltage_class_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v_class", i32_ty());
    // Voltage class: 1=distribution, 2=station, 3=transmission
    ctx.push_obligation(ProofObligation::assume(
        "v_class_enum",
        "v_class == 1 || v_class == 2 || v_class == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "v_class_valid",
        "v_class == 1 || v_class == 2 || v_class == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage class three-way (distribution/station/transmission)",
    );
}

#[test]
fn test_surge_arrester_tester_test_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std_sel", i32_ty());
    // Test standard: 1=IEC60099, 2=IEEE-C62, 3=ANSI
    ctx.push_obligation(ProofObligation::assume(
        "std_enum",
        "std_sel == 1 || std_sel == 2 || std_sel == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "std_valid",
        "std_sel == 1 || std_sel == 2 || std_sel == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test standard three-way (IEC60099/IEEE-C62/ANSI)");
}

#[test]
fn test_surge_arrester_tester_auto_degradation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_degrade", i32_ty());
    // Automatic degradation analysis boolean: 0=disabled, 1=enabled
    ctx.push_obligation(ProofObligation::assume(
        "auto_degrade_flag",
        "auto_degrade == 0 || auto_degrade == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_degrade_valid",
        "auto_degrade == 0 || auto_degrade == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic degradation analysis flag boolean (0 or 1)",
    );
}
