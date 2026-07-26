// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Gas temperature offset +500 (deg C) — bounded [500, 1000].
/// 500 represents 0 C, 750 represents 250 C, 1000 represents 500 C.
#[test]
fn test_dart_ms_gas_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gt_a",
        "gas_temp >= 500 && gas_temp <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gt_c",
        "gas_temp >= 500 && gas_temp <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DART gas temp offset+500 in [500, 1000] representing 0-500 C",
    );
}

/// Test 2: Grid voltage (V) — bounded [50, 600].
#[test]
fn test_dart_ms_grid_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("grid_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gv_a",
        "grid_v >= 50 && grid_v <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gv_c",
        "grid_v >= 50 && grid_v <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DART grid voltage in [50, 600] V");
}

/// Test 3: Gas flow rate (x10 L/min) — bounded [5, 100].
/// 5 represents 0.5 L/min, 100 represents 10.0 L/min.
#[test]
fn test_dart_ms_gas_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_a",
        "flow_x10 >= 5 && flow_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_c",
        "flow_x10 >= 5 && flow_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas flow x10 in [5, 100] representing 0.5-10.0 L/min",
    );
}

/// Test 4: Mass range (m/z) — bounded [50, 2000].
#[test]
fn test_dart_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mz_a", "mz >= 50 && mz <= 2000"));
    ctx.push_obligation(ProofObligation::assert("mz_c", "mz >= 50 && mz <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DART mass range in [50, 2000] m/z");
}

/// Test 5: Discharge needle voltage (V) — bounded [1000, 5000].
#[test]
fn test_dart_ms_discharge_needle_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("needle_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nv_a",
        "needle_v >= 1000 && needle_v <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nv_c",
        "needle_v >= 1000 && needle_v <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge needle voltage in [1000, 5000] V");
}

/// Test 6: Orifice-to-sample distance (x10 mm) — bounded [1, 200].
/// 1 represents 0.1 mm, 200 represents 20.0 mm.
#[test]
fn test_dart_ms_orifice_distance_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dist_a",
        "dist_x10 >= 1 && dist_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dist_c",
        "dist_x10 >= 1 && dist_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orifice distance x10 in [1, 200] representing 0.1-20.0 mm",
    );
}

/// Test 7: Ionization gas — 3-way disjunction.
/// 1=helium, 2=nitrogen, 3=argon.
#[test]
fn test_dart_ms_ionization_gas_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gas_a",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("gas_c", "gas >= 1 && gas <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionization gas 3-way (helium/nitrogen/argon)");
}

/// Test 8: Analysis mode — 3-way disjunction.
/// 1=positive-ion, 2=negative-ion, 3=alternating.
#[test]
fn test_dart_ms_analysis_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "amode_a",
        "amode == 1 || amode == 2 || amode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "amode_c",
        "amode >= 1 && amode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode 3-way (positive-ion/negative-ion/alternating)",
    );
}

/// Test 9: Sample presentation — 3-way disjunction.
/// 1=open-air, 2=transmission, 3=enclosed.
#[test]
fn test_dart_ms_sample_presentation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("present", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pres_a",
        "present == 1 || present == 2 || present == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pres_c",
        "present >= 1 && present <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample presentation 3-way (open-air/transmission/enclosed)",
    );
}

/// Test 10: Standby mode flag — boolean.
/// 0=off, 1=standby.
#[test]
fn test_dart_ms_standby_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "standby mode flag is boolean (0 or 1)");
}
