// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pulsed fluidized bed dryer property verification.
// Encodes key parameters of a pulsed fluidized bed dryer (pulsed airflow for improved
// drying of cohesive/sticky materials) and verifies bounded, disjunctive, and boolean
// constraints.

/// Test 1: Pulse frequency (Hz) — bounded [1, 100].
#[test]
fn test_pulsed_fluid_bed_dryer_pulse_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_range",
        "freq >= 1 && freq <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_bounded",
        "freq >= 1 && freq <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse frequency must be between 1 and 100 Hz");
}

/// Test 2: Bed height x10 (mm) — bounded [50, 5000] representing 5.0-500.0 mm.
#[test]
fn test_pulsed_fluid_bed_dryer_bed_height_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_height_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "height_range",
        "bed_height_x10 >= 50 && bed_height_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "height_bounded",
        "bed_height_x10 >= 50 && bed_height_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bed height x10 must be in [50, 5000] (5.0-500.0 mm)",
    );
}

/// Test 3: Air velocity x10 (m/s) — bounded [5, 200] representing 0.5-20.0 m/s.
#[test]
fn test_pulsed_fluid_bed_dryer_air_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_range",
        "air_vel_x10 >= 5 && air_vel_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vel_bounded",
        "air_vel_x10 >= 5 && air_vel_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air velocity x10 must be in [5, 200] (0.5-20.0 m/s)",
    );
}

/// Test 4: Inlet air temperature offset+100 (deg C) — bounded [120, 500] representing 20-400°C.
#[test]
fn test_pulsed_fluid_bed_dryer_inlet_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "inlet_temp_off >= 120 && inlet_temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "inlet_temp_off >= 120 && inlet_temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet temperature offset+100 must be in [120, 500] (20-400 deg C)",
    );
}

/// Test 5: Chamber diameter (mm) — bounded [200, 5000].
#[test]
fn test_pulsed_fluid_bed_dryer_chamber_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "chamber_dia >= 200 && chamber_dia <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "chamber_dia >= 200 && chamber_dia <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber diameter must be between 200 and 5000 mm");
}

/// Test 6: Number of pulse zones — bounded [1, 12].
#[test]
fn test_pulsed_fluid_bed_dryer_pulse_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zones_range",
        "pulse_zones >= 1 && pulse_zones <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zones_bounded",
        "pulse_zones >= 1 && pulse_zones <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of pulse zones must be between 1 and 12");
}

/// Test 7: Pulse valve type — 3-way disjunction.
/// 1=butterfly, 2=diaphragm, 3=rotary.
#[test]
fn test_pulsed_fluid_bed_dryer_valve_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valve_range",
        "valve_type == 1 || valve_type == 2 || valve_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valve_valid",
        "valve_type == 1 || valve_type == 2 || valve_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pulse valve type must be butterfly(1), diaphragm(2), or rotary(3)",
    );
}

/// Test 8: Air distributor type — 3-way disjunction.
/// 1=perforated-plate, 2=gill-plate, 3=nozzle-plate.
#[test]
fn test_pulsed_fluid_bed_dryer_air_distributor_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distributor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dist_range",
        "distributor == 1 || distributor == 2 || distributor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dist_valid",
        "distributor == 1 || distributor == 2 || distributor == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air distributor must be perforated-plate(1), gill-plate(2), or nozzle-plate(3)",
    );
}

/// Test 9: Exhaust treatment type — 3-way disjunction.
/// 1=cyclone, 2=bag-filter, 3=scrubber.
#[test]
fn test_pulsed_fluid_bed_dryer_exhaust_treatment_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exhaust", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "exhaust_range",
        "exhaust == 1 || exhaust == 2 || exhaust == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exhaust_valid",
        "exhaust == 1 || exhaust == 2 || exhaust == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "exhaust treatment must be cyclone(1), bag-filter(2), or scrubber(3)",
    );
}

/// Test 10: Automatic moisture control — boolean flag (0 or 1).
#[test]
fn test_pulsed_fluid_bed_dryer_auto_moisture_control_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_moisture", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "moisture_flag",
        "auto_moisture == 0 || auto_moisture == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "moisture_valid",
        "auto_moisture == 0 || auto_moisture == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic moisture control flag must be 0 or 1");
}
