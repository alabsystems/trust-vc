// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pulse combustion dryer property verification.
// Encodes key parameters of an industrial pulse combustion dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Pulse frequency (Hz) — bounded [10, 500], value 100.
#[test]
fn test_pulse_combustion_dryer_pulse_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_freq_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "pulse_freq_hz == 100"));
    ctx.push_obligation(ProofObligation::assert("freq_min", "pulse_freq_hz >= 10"));
    ctx.push_obligation(ProofObligation::assert("freq_max", "pulse_freq_hz <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse frequency 100 Hz in [10, 500]");
}

/// Test 2: Combustion temperature offset +100 (deg C) — bounded [300, 1500].
/// 300 represents 200 C, 1500 represents 1400 C. Value 900 (800 C).
#[test]
fn test_pulse_combustion_dryer_combustion_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("combust_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "combust_temp_offset == 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "combust_temp_offset >= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "combust_temp_offset <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "combustion temp 800 C (offset 900) in [300, 1500]");
}

/// Test 3: Evaporation rate (x10 kg/h) — bounded [10, 50000].
/// 10 represents 1.0 kg/h, 50000 represents 5000.0 kg/h. Value 2000 (200.0 kg/h).
#[test]
fn test_pulse_combustion_dryer_evaporation_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap_rate_x10 == 2000"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap_rate_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "evap_max",
        "evap_rate_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "evaporation rate 200.0 kg/h (2000 x10) in [10, 50000]",
    );
}

/// Test 4: Thermal efficiency (x10 %) — bounded [700, 1000].
/// 700 represents 70.0%, 1000 represents 100.0%. Value 950 (95.0%).
#[test]
fn test_pulse_combustion_dryer_thermal_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thermal_eff_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("eff_val", "thermal_eff_x10 == 950"));
    ctx.push_obligation(ProofObligation::assert("eff_min", "thermal_eff_x10 >= 700"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_max",
        "thermal_eff_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal efficiency 95.0% (950 x10) in [700, 1000]");
}

/// Test 5: Tailpipe length (x10 m) — bounded [5, 100].
/// 5 represents 0.5 m, 100 represents 10.0 m. Value 30 (3.0 m).
#[test]
fn test_pulse_combustion_dryer_tailpipe_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tailpipe_len_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "tailpipe_len_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("len_min", "tailpipe_len_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "len_max",
        "tailpipe_len_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tailpipe length 3.0 m (30 x10) in [5, 100]");
}

/// Test 6: Number of combustors — bounded [1, 20], value 4.
#[test]
fn test_pulse_combustion_dryer_combustor_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("combustor_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("count_val", "combustor_count == 4"));
    ctx.push_obligation(ProofObligation::assert("count_min", "combustor_count >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "count_max",
        "combustor_count <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "combustor count 4 in [1, 20]");
}

/// Test 7: Fuel type — 3-way disjunction.
/// 1=natural gas, 2=propane, 3=fuel oil. Value 1 (natural gas).
#[test]
fn test_pulse_combustion_dryer_fuel_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fuel_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fuel_val", "fuel_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fuel",
        "fuel_type == 1 || fuel_type == 2 || fuel_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fuel type 1 (natural gas) is valid 3-way disjunction",
    );
}

/// Test 8: Atomization method — 3-way disjunction.
/// 1=rotary, 2=pressure nozzle, 3=two-fluid. Value 1 (rotary).
#[test]
fn test_pulse_combustion_dryer_atomization_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomization_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atom_val",
        "atomization_method == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_atomization",
        "atomization_method == 1 || atomization_method == 2 || atomization_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomization method 1 (rotary) is valid 3-way disjunction",
    );
}

/// Test 9: Product collection — 3-way disjunction.
/// 1=cyclone, 2=bag filter, 3=wet scrubber. Value 1 (cyclone).
#[test]
fn test_pulse_combustion_dryer_product_collection_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collection_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coll_val",
        "collection_method == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_collection",
        "collection_method == 1 || collection_method == 2 || collection_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product collection 1 (cyclone) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic ignition control — boolean flag using i32 with if/else pattern.
/// Flag 1 = automatic ignition enabled, ignition_active = 1.
#[test]
fn test_pulse_combustion_dryer_auto_ignition_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ignition_flag", i32_ty());
    ctx.declare_var_typed("ignition_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "ignition_flag == 0 || ignition_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "ignition_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ignition_def",
        "ignition_active == if ignition_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ignition_triggered",
        "ignition_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic ignition flag triggers ignition control");
}
