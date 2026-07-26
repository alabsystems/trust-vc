// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Precision nanovoltmeter property verification.
// Models key instrument parameters: voltage range code, resolution digits,
// noise floor (x100 nV scaling), input impedance, reading rate,
// thermoelectric offset (x100 nV scaling), measurement technique,
// input configuration, filter type, and low thermal EMF terminals flag.

#[test]
fn test_voltage_range_code_bounded() {
    // Voltage range encoded as code 1-8 (nV through V ranges)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_code", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_code_bounds",
        "range_code >= 1 && range_code <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_code_positive",
        "range_code >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_code_upper",
        "range_code <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage range code bounded in [1, 8]");
}

#[test]
fn test_resolution_digits_bounded() {
    // Resolution in significant digits (5 to 9 for precision nanovoltmeters)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_bounds",
        "resolution >= 5 && resolution <= 9",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_positive",
        "resolution >= 5",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_upper",
        "resolution <= 9",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution digits bounded in [5, 9]");
}

#[test]
fn test_noise_floor_scaled_bounded() {
    // Noise floor encoded as x100 nV (1 = 0.01 nV, 10000 = 100.00 nV)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_bounds",
        "noise_x100 >= 1 && noise_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("noise_positive", "noise_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "noise_upper",
        "noise_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise floor x100 bounded in [1, 10000] (0.01 to 100.00 nV)",
    );
}

#[test]
fn test_input_impedance_bounded() {
    // Input impedance in gigaohms (1 to 100 GOhm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance_gohm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impedance_bounds",
        "impedance_gohm >= 1 && impedance_gohm <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impedance_positive",
        "impedance_gohm >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impedance_upper",
        "impedance_gohm <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input impedance bounded in [1, 100] GOhm");
}

#[test]
fn test_reading_rate_bounded() {
    // Reading rate in readings per second (1 to 1000)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_bounds",
        "rate >= 1 && rate <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("rate_positive", "rate >= 1"));
    ctx.push_obligation(ProofObligation::assert("rate_upper", "rate <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reading rate bounded in [1, 1000] readings/s");
}

#[test]
fn test_thermoelectric_offset_scaled_bounded() {
    // Thermoelectric offset encoded as x100 nV (1 = 0.01 nV, 5000 = 50.00 nV)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("offset_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "offset_bounds",
        "offset_x100 >= 1 && offset_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "offset_positive",
        "offset_x100 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "offset_upper",
        "offset_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermoelectric offset x100 bounded in [1, 5000] (0.01 to 50.00 nV)",
    );
}

#[test]
fn test_measurement_technique_three_way_disjunction() {
    // Measurement technique: 1=DC, 2=delta-mode, 3=AC-coupled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("technique", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "technique_valid",
        "technique == 1 || technique == 2 || technique == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("technique_lower", "technique >= 1"));
    ctx.push_obligation(ProofObligation::assert("technique_upper", "technique <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement technique is one of DC(1), delta-mode(2), AC-coupled(3)",
    );
}

#[test]
fn test_input_configuration_three_way_disjunction() {
    // Input configuration: 1=differential, 2=single-ended, 3=guarded
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "config_valid",
        "config == 1 || config == 2 || config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("config_lower", "config >= 1"));
    ctx.push_obligation(ProofObligation::assert("config_upper", "config <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "input config is one of differential(1), single-ended(2), guarded(3)",
    );
}

#[test]
fn test_filter_type_three_way_disjunction() {
    // Filter type: 1=analog, 2=digital, 3=median
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "filter_valid",
        "filter == 1 || filter == 2 || filter == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("filter_lower", "filter >= 1"));
    ctx.push_obligation(ProofObligation::assert("filter_upper", "filter <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "filter type is one of analog(1), digital(2), median(3)",
    );
}

#[test]
fn test_low_thermal_emf_terminals_boolean_flag() {
    // Low thermal EMF terminals enable: i32 flag where 1=enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("low_emf", i32_ty());
    ctx.declare_var_typed("active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "low_emf == 0 || low_emf == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("low_emf_on", "low_emf == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "active == if low_emf == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "active_when_enabled",
        "active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "low thermal EMF terminals flag: enabled(1) produces active=1",
    );
}
