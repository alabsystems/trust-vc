// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial screw conveyor dryer (hollow-flight / jacketed screw conveyor)
// property verification. Encodes key parameters and verifies bounded,
// disjunctive, and boolean-flag constraints.

/// Test 1: Screw speed bounded (1-100 RPM).
#[test]
fn test_screw_conveyor_dryer_screw_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1 && speed <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1 && speed <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw speed must be between 1 and 100 RPM");
}

/// Test 2: Conveyor length bounded (1000-15000 mm).
#[test]
fn test_screw_conveyor_dryer_conveyor_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "length_range",
        "length >= 1000 && length <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "length_bounded",
        "length >= 1000 && length <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveyor length must be between 1000 and 15000 mm");
}

/// Test 3: Throughput x10 bounded (1-50000 representing 0.1-5000.0 kg/h).
#[test]
fn test_screw_conveyor_dryer_throughput_x10_bounded() {
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

/// Test 4: Screw diameter bounded (100-1500 mm).
#[test]
fn test_screw_conveyor_dryer_screw_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_range",
        "diameter >= 100 && diameter <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_bounded",
        "diameter >= 100 && diameter <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw diameter must be between 100 and 1500 mm");
}

/// Test 5: Jacket temperature offset+100 bounded (120-450 representing 20-350 deg C).
#[test]
fn test_screw_conveyor_dryer_jacket_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "jacket_temp_offset >= 120 && jacket_temp_offset <= 450",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "jacket_temp_offset >= 120 && jacket_temp_offset <= 450",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature offset+100 must be between 120 and 450 (20-350 deg C)",
    );
}

/// Test 6: Number of screws bounded (1-4).
#[test]
fn test_screw_conveyor_dryer_num_screws_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_screws", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "screws_range",
        "num_screws >= 1 && num_screws <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "screws_bounded",
        "num_screws >= 1 && num_screws <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of screws must be between 1 and 4");
}

/// Test 7: Flight type 3-way disjunction (1=solid, 2=hollow, 3=ribbon).
#[test]
fn test_screw_conveyor_dryer_flight_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flight_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flight_type_range",
        "flight_type == 1 || flight_type == 2 || flight_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flight_type_valid",
        "flight_type == 1 || flight_type == 2 || flight_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flight type must be solid(1), hollow(2), or ribbon(3)",
    );
}

/// Test 8: Heat transfer medium 3-way disjunction (1=steam, 2=thermal-oil, 3=hot-water).
#[test]
fn test_screw_conveyor_dryer_heat_transfer_medium_disjunction() {
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
        "heat transfer medium must be steam(1), thermal-oil(2), or hot-water(3)",
    );
}

/// Test 9: Discharge type 3-way disjunction (1=overflow, 2=underflow, 3=end-plate).
#[test]
fn test_screw_conveyor_dryer_discharge_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_type_range",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_type_valid",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type must be overflow(1), underflow(2), or end-plate(3)",
    );
}

/// Test 10: Automatic speed regulation boolean flag (== 0 || == 1).
#[test]
fn test_screw_conveyor_dryer_auto_speed_regulation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_speed_reg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_speed_reg_range",
        "auto_speed_reg == 0 || auto_speed_reg == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_speed_reg_valid",
        "auto_speed_reg == 0 || auto_speed_reg == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic speed regulation flag must be 0 or 1");
}
