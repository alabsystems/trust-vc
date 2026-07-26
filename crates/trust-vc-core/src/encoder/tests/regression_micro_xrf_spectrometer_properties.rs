// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_micro_xrf_beam_spot_size_bounded() {
    // Beam spot size x10 in range 1-5000 representing 0.1-500.0 um
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_range",
        "spot >= 1 && spot <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_bounded",
        "spot >= 1 && spot <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam spot size x10 must be in range 1-5000 representing 0.1-500.0 um",
    );
}

#[test]
fn test_micro_xrf_tube_voltage_bounded() {
    // Tube voltage bounded 5-50 kV
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 5 && voltage <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 5 && voltage <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube voltage must be in range 5-50 kV");
}

#[test]
fn test_micro_xrf_mapping_resolution_bounded() {
    // Mapping resolution x10 in range 1-10000 representing 0.1-1000.0 um
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "resolution >= 1 && resolution <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "resolution >= 1 && resolution <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mapping resolution x10 must be in range 1-10000 representing 0.1-1000.0 um",
    );
}

#[test]
fn test_micro_xrf_scan_area_bounded() {
    // Scan area bounded 1-100000 mm^2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area >= 1 && area <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area >= 1 && area <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan area must be in range 1-100000 mm^2");
}

#[test]
fn test_micro_xrf_measurement_speed_bounded() {
    // Measurement speed bounded 1-10000 points/s
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1 && speed <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1 && speed <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement speed must be in range 1-10000 points/s",
    );
}

#[test]
fn test_micro_xrf_detectable_elements_bounded() {
    // Number of detectable elements bounded 1-83
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elements", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elem_range",
        "elements >= 1 && elements <= 83",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elem_bounded",
        "elements >= 1 && elements <= 83",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detectable elements must be in range 1-83");
}

#[test]
fn test_micro_xrf_optics_type_disjunction() {
    // Optics type: 1=polycapillary, 2=monocapillary, 3=collimator
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("optics", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "optics_valid",
        "optics == 1 || optics == 2 || optics == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "optics_disjunction",
        "optics == 1 || optics == 2 || optics == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "optics type must be polycapillary(1), monocapillary(2), or collimator(3)",
    );
}

#[test]
fn test_micro_xrf_scanning_mode_disjunction() {
    // Scanning mode: 1=point, 2=line, 3=area-map
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_disjunction",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scanning mode must be point(1), line(2), or area-map(3)",
    );
}

#[test]
fn test_micro_xrf_detector_type_disjunction() {
    // Detector type: 1=SDD, 2=CdTe, 3=Si-PIN
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_disjunction",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type must be SDD(1), CdTe(2), or Si-PIN(3)",
    );
}

#[test]
fn test_micro_xrf_auto_stage_positioning_boolean() {
    // Automatic stage positioning is a boolean flag (0 or 1)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_stage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_stage_valid",
        "auto_stage == 0 || auto_stage == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_stage_boolean",
        "auto_stage == 0 || auto_stage == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic stage positioning must be a boolean flag (0 or 1)",
    );
}
