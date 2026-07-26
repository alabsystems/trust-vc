// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_voltage_divider_calibrator_input_voltage_kv_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 1 && voltage <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("voltage_val", "voltage == 400"));
    ctx.push_obligation(ProofObligation::assert("input_voltage", "voltage == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "400 kV input voltage within 1-1000 kV range");
}

#[test]
fn test_voltage_divider_calibrator_division_ratio_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x1000 >= 100 && ratio_x1000 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("ratio_val", "ratio_x1000 == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "division_ratio",
        "ratio_x1000 == 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "10.000 division ratio (10000 scaled x1000) within 0.100-1000.000 range",
    );
}

#[test]
fn test_voltage_divider_calibrator_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc_x10000 == 50"));
    ctx.push_obligation(ProofObligation::assert("accuracy", "acc_x10000 == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "0.0050% accuracy (50 scaled x10000) within 0.0001-0.1000% range",
    );
}

#[test]
fn test_voltage_divider_calibrator_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq_x10 >= 1 && freq_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("frequency", "freq_x10 == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "50.0 Hz frequency (500 scaled x10) within 0.1-1000.0 Hz range",
    );
}

#[test]
fn test_voltage_divider_calibrator_burden_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burden_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "burden_range",
        "burden_x100 >= 1 && burden_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("burden_val", "burden_x100 == 2500"));
    ctx.push_obligation(ProofObligation::assert("burden", "burden_x100 == 2500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "25.00 VA burden (2500 scaled x100) within 0.01-100.00 VA range",
    );
}

#[test]
fn test_voltage_divider_calibrator_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 80 && temp_off <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_off == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "temperature_offset",
        "temp_off == 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "20 C temperature (120 offset +100) within -20 to 100 C range",
    );
}

#[test]
fn test_voltage_divider_calibrator_divider_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dtype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "dtype == 1 || dtype == 2 || dtype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "dtype == 1 || dtype == 2 || dtype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage divider calibrator divider type three-way disjunction",
    );
}

#[test]
fn test_voltage_divider_calibrator_voltage_class_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vclass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_class",
        "vclass == 1 || vclass == 2 || vclass == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "class_bounded",
        "vclass >= 1 && vclass <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage class (1=low-voltage, 2=medium-voltage, 3=high-voltage) implies [1,3]",
    );
}

#[test]
fn test_voltage_divider_calibrator_calibration_standard_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_standard",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "standard_bounded",
        "standard >= 1 && standard <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "calibration standard (1=IEC61869, 2=IEEE-C57, 3=ANSI-C93) implies [1,3]",
    );
}

#[test]
fn test_voltage_divider_calibrator_auto_ratio_correction_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_corr", i32_ty());
    ctx.push_obligation(ProofObligation::assume("auto_corr_set", "auto_corr == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_true",
        "if auto_corr == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto ratio correction flag set to 1 evaluates to true",
    );
}
