// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_phase_rotation_meter_voltage_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_bounds",
        "voltage >= 50 && voltage <= 750",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_in_range",
        "voltage >= 50 && voltage <= 750",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating voltage must be within 50-750 V");
}

#[test]
fn test_phase_rotation_meter_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frequency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frequency_bounds",
        "frequency >= 25 && frequency <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frequency_in_range",
        "frequency >= 25 && frequency <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating frequency must be within 25-400 Hz");
}

#[test]
fn test_phase_rotation_meter_phase_angle_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_bounds",
        "phase_angle_x10 >= 0 && phase_angle_x10 <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_in_range",
        "phase_angle_x10 >= 0 && phase_angle_x10 <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase angle x10 must be within 0-3600 representing 0.0-360.0 degrees",
    );
}

#[test]
fn test_phase_rotation_meter_sequence_impedance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seq_impedance_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impedance_bounds",
        "seq_impedance_x100 >= 1 && seq_impedance_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impedance_in_range",
        "seq_impedance_x100 >= 1 && seq_impedance_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sequence impedance x100 must be within 1-10000 representing 0.01-100.00 ohms",
    );
}

#[test]
fn test_phase_rotation_meter_unbalance_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("unbalance_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "unbalance_bounds",
        "unbalance_x10 >= 0 && unbalance_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "unbalance_in_range",
        "unbalance_x10 >= 0 && unbalance_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage unbalance x10 must be within 0-500 representing 0.0-50.0 percent",
    );
}

#[test]
fn test_phase_rotation_meter_num_phases_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_phases", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "phases_bounds",
        "num_phases >= 3 && num_phases <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "phases_in_range",
        "num_phases >= 3 && num_phases <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of phases must be within 3-12");
}

#[test]
fn test_phase_rotation_meter_indication_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("indication_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "indication_bounds",
        "indication_type >= 1 && indication_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "indication_in_range",
        "indication_type >= 1 && indication_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "indication type must be 1=LED, 2=LCD-display, or 3=analog-meter",
    );
}

#[test]
fn test_phase_rotation_meter_connection_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connection_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "connection_bounds",
        "connection_method >= 1 && connection_method <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "connection_in_range",
        "connection_method >= 1 && connection_method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connection method must be 1=direct, 2=PT-secondary, or 3=capacitive-divider",
    );
}

#[test]
fn test_phase_rotation_meter_measurement_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("measurement_standard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "standard_bounds",
        "measurement_standard >= 1 && measurement_standard <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "standard_in_range",
        "measurement_standard >= 1 && measurement_standard <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement standard must be 1=IEC, 2=IEEE, or 3=ANSI",
    );
}

#[test]
fn test_phase_rotation_meter_auto_sequence_detect_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_seq_detect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bounds",
        "auto_seq_detect >= 0 && auto_seq_detect <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_in_range",
        "auto_seq_detect >= 0 && auto_seq_detect <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto sequence detect flag must be 0=disabled or 1=enabled",
    );
}
