// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Transformer turns ratio (TTR) must be in [1, 50000].
#[test]
fn ttr_ratio_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio >= 1 && ratio <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_positive",
        "ratio >= 1 && ratio <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turns ratio bounded in [1, 50000]");
}

/// Accuracy class x1000: [1, 500] representing 0.001% to 0.500%.
#[test]
fn ttr_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_range",
        "accuracy_x1000 >= 1 && accuracy_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_bounded",
        "accuracy_x1000 >= 1 && accuracy_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x1000 bounded in [1, 500] representing 0.001-0.500%",
    );
}

/// Test voltage bounded in [1, 200] V.
#[test]
fn ttr_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "test_voltage >= 1 && test_voltage <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "test_voltage >= 1 && test_voltage <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage bounded in [1, 200] V");
}

/// Phase displacement x100: [1, 36000] representing 0.01 to 360.00 degrees.
#[test]
fn ttr_phase_displacement_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "phase_range",
        "phase_x100 >= 1 && phase_x100 <= 36000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "phase_bounded",
        "phase_x100 >= 1 && phase_x100 <= 36000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase displacement x100 bounded in [1, 36000] representing 0.01-360.00 degrees",
    );
}

/// Excitation current x100: [1, 100000] representing 0.01 to 1000.00 mA.
#[test]
fn ttr_excitation_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "excitation_range",
        "excitation_x100 >= 1 && excitation_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "excitation_bounded",
        "excitation_x100 >= 1 && excitation_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation current x100 bounded in [1, 100000] representing 0.01-1000.00 mA",
    );
}

/// Number of tap positions bounded in [1, 40].
#[test]
fn ttr_tap_positions_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tap_positions", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tap_range",
        "tap_positions >= 1 && tap_positions <= 40",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tap_bounded",
        "tap_positions >= 1 && tap_positions <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tap positions bounded in [1, 40]");
}

/// Connection type is a 3-way disjunction: 1=single-phase, 2=three-phase-auto, 3=three-phase-manual.
#[test]
fn ttr_connection_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conn_valid",
        "conn_type == 1 || conn_type == 2 || conn_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conn_in_range",
        "conn_type >= 1 && conn_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connection type disjunction {1,2,3} implies range [1,3]",
    );
}

/// Measurement type is a 3-way disjunction: 1=voltage-ratio, 2=current-ratio, 3=impedance.
#[test]
fn ttr_measurement_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "meas_valid",
        "meas_type == 1 || meas_type == 2 || meas_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "meas_in_range",
        "meas_type >= 1 && meas_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement type disjunction {1,2,3} implies range [1,3]",
    );
}

/// Vector group is a 3-way disjunction: 1=Yy, 2=Yd, 3=Dy.
#[test]
fn ttr_vector_group_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vector_group", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vg_valid",
        "vector_group == 1 || vector_group == 2 || vector_group == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vg_in_range",
        "vector_group >= 1 && vector_group <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vector group disjunction {1=Yy,2=Yd,3=Dy} implies range [1,3]",
    );
}

/// Automatic tap changer sequencing is a boolean flag (0 or 1).
#[test]
fn ttr_auto_tap_changer_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_tap", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_tap_flag",
        "auto_tap == 0 || auto_tap == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_tap_bounded",
        "auto_tap >= 0 && auto_tap <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto tap changer flag is boolean: 0 or 1");
}
