// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial mechanically agitated dryer property verification.
// Encodes key parameters of a horizontal paddle/disc dryer for continuous
// drying of pastes, sludges, and bulk solids, and verifies that they satisfy
// bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Agitator speed bounded (1-60 RPM).
#[test]
fn test_mech_agitated_dryer_agitator_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1 && speed <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1 && speed <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitator speed must be between 1 and 60 RPM");
}

/// Test 2: Heat transfer area x10 bounded (10-2000 representing 1.0-200.0 m2).
#[test]
fn test_mech_agitated_dryer_heat_transfer_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area_x10 >= 10 && area_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area_x10 >= 10 && area_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat transfer area x10 must be between 10 and 2000 (1.0-200.0 m2)",
    );
}

/// Test 3: Throughput x10 bounded (1-50000 representing 0.1-5000.0 kg/h).
#[test]
fn test_mech_agitated_dryer_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "throughput_range",
        "throughput_x10 >= 1 && throughput_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "throughput_bounded",
        "throughput_x10 >= 1 && throughput_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "throughput x10 must be between 1 and 50000 (0.1-5000.0 kg/h)",
    );
}

/// Test 4: Jacket pressure x10 bounded (1-100 representing 0.1-10.0 bar).
#[test]
fn test_mech_agitated_dryer_jacket_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_x10 >= 1 && pressure_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure_x10 >= 1 && pressure_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket pressure x10 must be between 1 and 100 (0.1-10.0 bar)",
    );
}

/// Test 5: Residence time bounded (5-600 min).
#[test]
fn test_mech_agitated_dryer_residence_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_time_range",
        "res_time >= 5 && res_time <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_time_bounded",
        "res_time >= 5 && res_time <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time must be between 5 and 600 minutes");
}

/// Test 6: Number of heating zones bounded (1-6).
#[test]
fn test_mech_agitated_dryer_heating_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zones_range",
        "zones >= 1 && zones <= 6",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zones_bounded",
        "zones >= 1 && zones <= 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of heating zones must be between 1 and 6");
}

/// Test 7: Agitator type 3-way disjunction (1=paddle, 2=disc, 3=coil).
#[test]
fn test_mech_agitated_dryer_agitator_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("agitator_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "agitator_type_range",
        "agitator_type == 1 || agitator_type == 2 || agitator_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "agitator_type_valid",
        "agitator_type == 1 || agitator_type == 2 || agitator_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "agitator type must be paddle (1), disc (2), or coil (3)",
    );
}

/// Test 8: Heating medium 3-way disjunction (1=steam, 2=thermal-oil, 3=hot-water).
#[test]
fn test_mech_agitated_dryer_heating_medium_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_medium", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_medium_range",
        "heat_medium == 1 || heat_medium == 2 || heat_medium == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_medium_valid",
        "heat_medium == 1 || heat_medium == 2 || heat_medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium must be steam (1), thermal-oil (2), or hot-water (3)",
    );
}

/// Test 9: Discharge mechanism 3-way disjunction (1=weir, 2=screw, 3=rotary-valve).
#[test]
fn test_mech_agitated_dryer_discharge_mechanism_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_range",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_valid",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge mechanism must be weir (1), screw (2), or rotary-valve (3)",
    );
}

/// Test 10: Automatic feed rate control boolean flag (== 0 || == 1).
#[test]
fn test_mech_agitated_dryer_auto_feed_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_feed_range",
        "auto_feed == 0 || auto_feed == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_feed_valid",
        "auto_feed == 0 || auto_feed == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic feed rate control flag must be 0 (off) or 1 (on)",
    );
}
