// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial microwave dryer property verification.
// Encodes key parameters of an industrial microwave dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Magnetron power (kW) — bounded [1, 200], value 50.
#[test]
fn test_microwave_dryer_magnetron_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magnetron_power_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_val",
        "magnetron_power_kw == 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_min",
        "magnetron_power_kw >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_max",
        "magnetron_power_kw <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magnetron power 50 kW in [1, 200]");
}

/// Test 2: Frequency (MHz) — bounded [900, 2500], value 2450.
#[test]
fn test_microwave_dryer_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frequency_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "frequency_mhz == 2450"));
    ctx.push_obligation(ProofObligation::assert("freq_min", "frequency_mhz >= 900"));
    ctx.push_obligation(ProofObligation::assert("freq_max", "frequency_mhz <= 2500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency 2450 MHz in [900, 2500]");
}

/// Test 3: Belt speed (x10 m/min) — bounded [1, 200], value 50 (5.0 m/min).
#[test]
fn test_microwave_dryer_belt_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "belt_speed_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "belt_speed_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_max",
        "belt_speed_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt speed 5.0 m/min (50 x10) in [1, 200]");
}

/// Test 4: Chamber temperature offset +100 (deg C) — bounded [100, 500], value 160.
/// 100 represents 0 C, 160 represents 60 C, 500 represents 400 C.
#[test]
fn test_microwave_dryer_chamber_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "chamber_temp_offset == 160",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "chamber_temp_offset >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "chamber_temp_offset <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber temp 60 C (offset 160) in [100, 500]");
}

/// Test 5: Number of magnetrons — bounded [1, 50], value 12.
#[test]
fn test_microwave_dryer_number_of_magnetrons_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_magnetrons", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mag_val", "num_magnetrons == 12"));
    ctx.push_obligation(ProofObligation::assert("mag_min", "num_magnetrons >= 1"));
    ctx.push_obligation(ProofObligation::assert("mag_max", "num_magnetrons <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of magnetrons 12 in [1, 50]");
}

/// Test 6: Cavity length (x10 m) — bounded [5, 200], value 30 (3.0 m).
#[test]
fn test_microwave_dryer_cavity_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cavity_length_x10m", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_val",
        "cavity_length_x10m == 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_min",
        "cavity_length_x10m >= 5",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_max",
        "cavity_length_x10m <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cavity length 3.0 m (30 x10) in [5, 200]");
}

/// Test 7: Waveguide type — 3-way disjunction.
/// 1=rectangular, 2=circular, 3=ridged. Value 1 (rectangular).
#[test]
fn test_microwave_dryer_waveguide_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveguide_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wg_val", "waveguide_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_waveguide_type",
        "waveguide_type == 1 || waveguide_type == 2 || waveguide_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "waveguide type 1 (rectangular) is valid 3-way disjunction",
    );
}

/// Test 8: Power distribution — 3-way disjunction.
/// 1=uniform, 2=variable-zone, 3=pulsed. Value 2 (variable-zone).
#[test]
fn test_microwave_dryer_power_distribution_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_dist", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dist_val", "power_dist == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_power_dist",
        "power_dist == 1 || power_dist == 2 || power_dist == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power distribution 2 (variable-zone) is valid 3-way disjunction",
    );
}

/// Test 9: Moisture sensing — 3-way disjunction.
/// 1=microwave-sensor, 2=infrared, 3=gravimetric. Value 1 (microwave-sensor).
#[test]
fn test_microwave_dryer_moisture_sensing_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_sensing", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sense_val",
        "moisture_sensing == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_moisture_sensing",
        "moisture_sensing == 1 || moisture_sensing == 2 || moisture_sensing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "moisture sensing 1 (microwave-sensor) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic frequency tuning — boolean flag using i32 with if/else pattern.
/// Flag 1 = frequency tuning enabled, tuning_active should be 1.
#[test]
fn test_microwave_dryer_auto_frequency_tuning_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tuning_flag", i32_ty());
    ctx.declare_var_typed("tuning_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "tuning_flag == 0 || tuning_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "tuning_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tuning_def",
        "tuning_active == if tuning_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tuning_enabled",
        "tuning_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency tuning flag triggers tuning active");
}
