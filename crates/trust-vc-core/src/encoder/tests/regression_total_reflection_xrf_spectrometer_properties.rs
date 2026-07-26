// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_txrf_tube_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 10 && voltage <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 10 && voltage <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube voltage must be between 10 and 60 kV");
}

#[test]
fn test_txrf_tube_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 1 && current <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "current >= 1 && current <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube current must be between 1 and 1000 mA");
}

#[test]
fn test_txrf_incidence_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "angle_x1000 >= 1 && angle_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_bounded",
        "angle_x1000 >= 1 && angle_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "incidence angle x1000 must be between 1 and 500 (0.001-0.500 degrees)",
    );
}

#[test]
fn test_txrf_detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_limit_range",
        "det_limit_x10000 >= 1 && det_limit_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_limit_bounded",
        "det_limit_x10000 >= 1 && det_limit_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x10000 must be between 1 and 10000 (0.0001-1.0000 ppb)",
    );
}

#[test]
fn test_txrf_measurement_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "meas_time_range",
        "meas_time >= 1 && meas_time <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "meas_time_bounded",
        "meas_time >= 1 && meas_time <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement time must be between 1 and 10000 seconds",
    );
}

#[test]
fn test_txrf_detectable_elements_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_elements", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elements_range",
        "num_elements >= 1 && num_elements <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elements_bounded",
        "num_elements >= 1 && num_elements <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detectable elements must be between 1 and 80");
}

#[test]
fn test_txrf_excitation_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "excitation_valid",
        "excitation_src == 1 || excitation_src == 2 || excitation_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "excitation_disjunction",
        "excitation_src == 1 || excitation_src == 2 || excitation_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation source must be Mo-tube (1), W-tube (2), or dual-anode (3)",
    );
}

#[test]
fn test_txrf_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_disjunction",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type must be SDD (1), Si-drift (2), or HPGe (3)",
    );
}

#[test]
fn test_txrf_sample_carrier_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "carrier_valid",
        "carrier == 1 || carrier == 2 || carrier == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "carrier_disjunction",
        "carrier == 1 || carrier == 2 || carrier == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample carrier must be quartz (1), acrylic (2), or silicon-wafer (3)",
    );
}

#[test]
fn test_txrf_auto_alignment_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_align", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_align_bool",
        "auto_align == 0 || auto_align == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_align_flag",
        "auto_align == 0 || auto_align == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic sample alignment flag must be boolean (0 or 1)",
    );
}
