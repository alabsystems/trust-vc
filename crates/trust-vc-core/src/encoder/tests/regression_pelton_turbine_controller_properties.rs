// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Pelton impulse hydroelectric turbine controller property verification.
// Encodes key parameters of a Pelton wheel hydro generation system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Power output (kW) — generation capacity bounded [10, 200000], value 5000.
#[test]
fn test_power_output_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power_kw == 5000"));
    ctx.push_obligation(ProofObligation::assert("power_min", "power_kw >= 10"));
    ctx.push_obligation(ProofObligation::assert("power_max", "power_kw <= 200000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power output 5000 kW in [10, 200000]");
}

/// Test 2: Head (m) — water head bounded [50, 2000], value 500.
#[test]
fn test_head_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_m", u32_ty());
    ctx.push_obligation(ProofObligation::assume("head_val", "head_m == 500"));
    ctx.push_obligation(ProofObligation::assert("head_min", "head_m >= 50"));
    ctx.push_obligation(ProofObligation::assert("head_max", "head_m <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "water head 500 m in [50, 2000]");
}

/// Test 3: Flow rate (L/s) — water flow bounded [10, 50000], value 1000.
#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_lps", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_lps == 1000"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_lps >= 10"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_lps <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 1000 L/s in [10, 50000]");
}

/// Test 4: Jet count — 3-way non-sequential disjunction (1, 2, 4 nozzles).
/// Value 2.
#[test]
fn test_jet_count_non_sequential_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jet_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("jet_val", "jet_count == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_jet_count",
        "jet_count == 1 || jet_count == 2 || jet_count == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jet count 2 is valid (1, 2, or 4 nozzles)");
}

/// Test 5: Runner speed (RPM) — turbine speed bounded [100, 3000], value 600.
#[test]
fn test_runner_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("runner_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "runner_rpm == 600"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "runner_rpm >= 100"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "runner_rpm <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "runner speed 600 RPM in [100, 3000]");
}

/// Test 6: Efficiency (x10 %) — hydraulic efficiency bounded [800, 960], value 920 (92.0%).
#[test]
fn test_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("eff_val", "efficiency_x10 == 920"));
    ctx.push_obligation(ProofObligation::assert("eff_min", "efficiency_x10 >= 800"));
    ctx.push_obligation(ProofObligation::assert("eff_max", "efficiency_x10 <= 960"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency 920 (92.0%) in [800, 960]");
}

/// Test 7: Nozzle type — 3-way disjunction.
/// 1=needle, 2=deflector, 3=multi-jet. Value 1 (needle).
#[test]
fn test_nozzle_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("nozzle_val", "nozzle_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_nozzle",
        "nozzle_type == 1 || nozzle_type == 2 || nozzle_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle type 1 (needle) is valid 3-way disjunction");
}

/// Test 8: Grid frequency — 2-way disjunction.
/// 1=50Hz, 2=60Hz. Value 1 (50Hz).
#[test]
fn test_grid_frequency_two_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("grid_freq", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "grid_freq == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_freq",
        "grid_freq == 1 || grid_freq == 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "grid frequency 1 (50Hz) is valid 2-way disjunction",
    );
}

/// Test 9: Bearing type — 3-way disjunction.
/// 1=plain, 2=roller, 3=magnetic. Value 2 (roller).
#[test]
fn test_bearing_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bearing_val", "bearing_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_bearing",
        "bearing_type == 1 || bearing_type == 2 || bearing_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type 2 (roller) is valid 3-way disjunction",
    );
}

/// Test 10: Overspeed protection — boolean flag using i32 with if/else pattern.
/// Flag 1 = overspeed protection enabled, which limits runner RPM to 2400.
#[test]
fn test_overspeed_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("overspeed_flag", i32_ty());
    ctx.declare_var_typed("rpm_limit", u32_ty());
    ctx.declare_var_typed("effective_rpm", u32_ty());
    ctx.declare_var_typed("max_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "overspeed_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("max_rpm_val", "max_rpm == 3000"));
    ctx.push_obligation(ProofObligation::assume("limit_val", "rpm_limit == 2400"));
    ctx.push_obligation(ProofObligation::assume(
        "effective_def",
        "effective_rpm == if overspeed_flag == 1 { rpm_limit } else { max_rpm }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "overspeed_rpm_limited",
        "effective_rpm <= 2400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "overspeed protection flag limits RPM to 2400");
}
