// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Precision compliance analyzer (EMC/EMI) property tests.

use super::*;

#[test]
fn test_compliance_analyzer_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_bounds",
        "freq_mhz >= 1 && freq_mhz <= 40000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_in_range",
        "freq_mhz > 0 && freq_mhz <= 40000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency range 1-40000 MHz must be valid");
}

#[test]
fn test_compliance_analyzer_sensitivity_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_bounds",
        "sens_off > 200 && sens_off < 400",
    ));
    ctx.push_obligation(ProofObligation::assert("sens_positive", "sens_off > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity offset +200 dBm must be positive");
}

#[test]
fn test_compliance_analyzer_dynamic_range_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_bounds",
        "range_x10 > 0 && range_x10 < 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_positive",
        "range_x10 >= 1 && range_x10 <= 1999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range scaled by 10 dB must be in bounds");
}

#[test]
fn test_compliance_analyzer_resolution_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rbw_hz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rbw_bounds",
        "rbw_hz >= 1 && rbw_hz <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rbw_positive",
        "rbw_hz > 0 && rbw_hz <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution bandwidth 1-10000000 Hz must be valid");
}

#[test]
fn test_compliance_analyzer_measurement_points_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_points", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "points_bounds",
        "num_points >= 100 && num_points <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "points_in_range",
        "num_points >= 100 && num_points <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of measurement points 100-100000 must be valid",
    );
}

#[test]
fn test_compliance_analyzer_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_bounds",
        "scan_speed >= 1 && scan_speed <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_positive",
        "scan_speed > 0 && scan_speed <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scan speed 1-10000 points per second must be valid",
    );
}

#[test]
fn test_compliance_analyzer_test_standard_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "std_valid",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("std_known", "std >= 1 && std <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test standard must be 1=CISPR, 2=FCC, or 3=MIL-STD",
    );
}

#[test]
fn test_compliance_analyzer_measurement_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mtype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mtype_valid",
        "mtype == 1 || mtype == 2 || mtype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mtype_known",
        "mtype >= 1 && mtype <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement type must be 1=conducted, 2=radiated, or 3=immunity",
    );
}

#[test]
fn test_compliance_analyzer_detector_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_valid",
        "det == 1 || det == 2 || det == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("det_known", "det >= 1 && det <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector mode must be 1=peak, 2=quasi-peak, or 3=average",
    );
}

#[test]
fn test_compliance_analyzer_automatic_limit_line_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "auto_limit == 0 || auto_limit == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "auto_limit >= 0 && auto_limit <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic limit line comparison flag must be boolean 0 or 1",
    );
}
