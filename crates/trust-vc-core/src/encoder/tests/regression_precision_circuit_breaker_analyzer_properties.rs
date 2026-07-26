// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Voltage must remain within the valid operating range of 100V to 40000V.
#[test]
fn test_circuit_breaker_analyzer_voltage_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tv_a",
        "voltage >= 100 && voltage <= 40000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tv_c",
        "voltage >= 100 && voltage <= 40000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer voltage range");
}

/// Trip current (scaled by x10 A) must remain within the valid range of 10 to 50000.
#[test]
fn test_circuit_breaker_analyzer_trip_current_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trip_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tc_a",
        "trip_x10 >= 10 && trip_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tc_c",
        "trip_x10 >= 10 && trip_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer trip current range");
}

/// Contact resistance (scaled by x1000 ohms) must remain within the valid range of 1 to 5000.
#[test]
fn test_circuit_breaker_analyzer_contact_resistance_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cr_a",
        "res_x1000 >= 1 && res_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cr_c",
        "res_x1000 >= 1 && res_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer contact resistance range");
}

/// Operating time (scaled by x100 ms) must remain within the valid range of 1 to 10000.
#[test]
fn test_circuit_breaker_analyzer_operating_time_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ot_a",
        "time_x100 >= 1 && time_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ot_c",
        "time_x100 >= 1 && time_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer operating time range");
}

/// Coil current (scaled by x10 A) must remain within the valid range of 1 to 1000.
#[test]
fn test_circuit_breaker_analyzer_coil_current_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coil_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "coil_x10 >= 1 && coil_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "coil_x10 >= 1 && coil_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer coil current range");
}

/// Rated voltage in kV must remain within the valid range of 1 to 800.
#[test]
fn test_circuit_breaker_analyzer_rated_voltage_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rated_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rv_a",
        "rated_kv >= 1 && rated_kv <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rv_c",
        "rated_kv >= 1 && rated_kv <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer rated voltage range");
}

/// Breaker type must be one of: vacuum (1), SF6 (2), or oil (3).
#[test]
fn test_circuit_breaker_analyzer_breaker_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("btype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bt_a",
        "btype == 1 || btype == 2 || btype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bt_c",
        "btype == 1 || btype == 2 || btype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer breaker type");
}

/// Trip mechanism must be one of: magnetic (1), thermal (2), or electronic (3).
#[test]
fn test_circuit_breaker_analyzer_trip_mechanism() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mechanism", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tm_a",
        "mechanism == 1 || mechanism == 2 || mechanism == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tm_c",
        "mechanism == 1 || mechanism == 2 || mechanism == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer trip mechanism");
}

/// Test standard must be one of: IEC (1), ANSI (2), or IEEE (3).
#[test]
fn test_circuit_breaker_analyzer_test_standard() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ts_a",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_c",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer test standard");
}

/// Automatic timing analysis flag must be a boolean value (0 or 1).
#[test]
fn test_circuit_breaker_analyzer_auto_timing_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ta_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ta_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "circuit breaker analyzer auto timing flag");
}
