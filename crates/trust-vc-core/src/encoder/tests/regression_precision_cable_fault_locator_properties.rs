// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_cable_fault_locator_max_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "length_range",
        "length >= 1 && length <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "length_bounded",
        "length >= 1 && length <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "maximum cable length must be between 1 and 100000 meters",
    );
}

#[test]
fn test_cable_fault_locator_distance_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy", i32_ty());
    // Distance accuracy x100: range 1-10000 representing 0.01-100.00 m
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "accuracy >= 1 && accuracy <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "accuracy >= 1 && accuracy <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "distance accuracy x100 must be between 1 and 10000 (0.01-100.00 m)",
    );
}

#[test]
fn test_cable_fault_locator_pulse_width_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_width", i32_ty());
    // Pulse width x10: range 1-10000 representing 0.1-1000.0 ns
    ctx.push_obligation(ProofObligation::assume(
        "pw_range",
        "pulse_width >= 1 && pulse_width <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_bounded",
        "pulse_width >= 1 && pulse_width <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pulse width x10 must be between 1 and 10000 (0.1-1000.0 ns)",
    );
}

#[test]
fn test_cable_fault_locator_output_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "imp_range",
        "impedance >= 10 && impedance <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "imp_bounded",
        "impedance >= 10 && impedance <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output impedance must be between 10 and 600 ohms");
}

#[test]
fn test_cable_fault_locator_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volt_range",
        "voltage >= 1 && voltage <= 35000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "volt_bounded",
        "voltage >= 1 && voltage <= 35000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage must be between 1 and 35000 V");
}

#[test]
fn test_cable_fault_locator_number_of_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ch_range",
        "channels >= 1 && channels <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ch_bounded",
        "channels >= 1 && channels <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of test channels must be between 1 and 12");
}

#[test]
fn test_cable_fault_locator_measurement_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.declare_var_typed("valid_method", i32_ty());
    // Measurement method: 1=TDR, 2=bridge, 3=impulse
    ctx.push_obligation(ProofObligation::assume("method_val", "method == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "method_def",
        "valid_method == if method == 1 || method == 2 || method == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("method_chk", "valid_method == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement method 1 (TDR) is valid measurement method",
    );
}

#[test]
fn test_cable_fault_locator_cable_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cable_type", i32_ty());
    ctx.declare_var_typed("valid_cable", i32_ty());
    // Cable type: 1=power, 2=communication, 3=coaxial
    ctx.push_obligation(ProofObligation::assume("cable_val", "cable_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cable_def",
        "valid_cable == if cable_type == 1 || cable_type == 2 || cable_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cable_chk", "valid_cable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cable type 2 (communication) is valid cable type");
}

#[test]
fn test_cable_fault_locator_fault_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fault_type", i32_ty());
    ctx.declare_var_typed("valid_fault", i32_ty());
    // Fault type: 1=open, 2=short, 3=high-resistance
    ctx.push_obligation(ProofObligation::assume("fault_val", "fault_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "fault_def",
        "valid_fault == if fault_type == 1 || fault_type == 2 || fault_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fault_chk", "valid_fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fault type 3 (high-resistance) is valid fault type",
    );
}

#[test]
fn test_cable_fault_locator_auto_vop_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_vop", i32_ty());
    ctx.declare_var_typed("valid_flag", i32_ty());
    // Automatic VOP calibration: boolean flag (0=no, 1=yes)
    ctx.push_obligation(ProofObligation::assume("vop_val", "auto_vop == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vop_def",
        "valid_flag == if auto_vop == 0 || auto_vop == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vop_chk", "valid_flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic VOP calibration flag 1 (yes) is valid boolean",
    );
}
