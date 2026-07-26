// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial rotary kiln controller property verification.
// Encodes key parameters of a rotary kiln system (cement, lime, mineral processing)
// and verifies bounded, disjunctive, scaled, offset, and boolean-flag constraints.

/// Test 1: Shell diameter (mm) — bounded [1000, 6000], value 3500.
#[test]
fn test_shell_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shell_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "shell_dia_mm == 3500"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "shell_dia_mm >= 1000"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "shell_dia_mm <= 6000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shell diameter 3500 mm in [1000, 6000]");
}

/// Test 2: Shell length (mm) — bounded [10000, 100000], value 60000.
#[test]
fn test_shell_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shell_len_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "shell_len_mm == 60000"));
    ctx.push_obligation(ProofObligation::assert("len_min", "shell_len_mm >= 10000"));
    ctx.push_obligation(ProofObligation::assert("len_max", "shell_len_mm <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shell length 60000 mm in [10000, 100000]");
}

/// Test 3: Rotation speed (x10 RPM) — scaled at 0.1 RPM, bounded [5, 50].
/// 5 represents 0.5 RPM, 50 represents 5.0 RPM. Value 15 (1.5 RPM).
#[test]
fn test_rotation_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_x10 == 15"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "speed_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "speed_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 1.5 RPM (15 x10) in [5, 50]");
}

/// Test 4: Zone temperature offset +500 (deg C) — bounded [1300, 2000].
/// 1300 represents 800 C, 2000 represents 1500 C. Value 1850 (1350 C).
#[test]
fn test_zone_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "zone_temp_offset == 1850",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "zone_temp_offset >= 1300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "zone_temp_offset <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zone temp 1350 C (offset 1850) in [1300, 2000]");
}

/// Test 5: Throughput (kg/h) — bounded [500, 50000], value 12000.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tp_val", "throughput_kgh == 12000"));
    ctx.push_obligation(ProofObligation::assert("tp_min", "throughput_kgh >= 500"));
    ctx.push_obligation(ProofObligation::assert("tp_max", "throughput_kgh <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 12000 kg/h in [500, 50000]");
}

/// Test 6: Fuel type — 3-way disjunction.
/// 1=natural gas, 2=coal, 3=oil. Value 1 (natural gas).
#[test]
fn test_fuel_type_three_way_disjunction() {
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

/// Test 7: Refractory type — 3-way disjunction.
/// 1=alumina, 2=magnesia, 3=chrome-mag. Value 2 (magnesia).
#[test]
fn test_refractory_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrac_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("refrac_val", "refrac_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_refrac",
        "refrac_type == 1 || refrac_type == 2 || refrac_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refractory type 2 (magnesia) is valid 3-way disjunction",
    );
}

/// Test 8: Inclination (x100 degrees) — scaled at 0.01 deg, bounded [100, 500].
/// 100 represents 1.00 deg, 500 represents 5.00 deg. Value 300 (3.00 deg).
#[test]
fn test_inclination_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("incline_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "incline_val",
        "incline_x100 == 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "incline_min",
        "incline_x100 >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "incline_max",
        "incline_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclination 3.00 deg (300 x100) in [100, 500]");
}

/// Test 9: Drive power (kW) — bounded [50, 2000], value 750.
#[test]
fn test_drive_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drive_val", "drive_kw == 750"));
    ctx.push_obligation(ProofObligation::assert("drive_min", "drive_kw >= 50"));
    ctx.push_obligation(ProofObligation::assert("drive_max", "drive_kw <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive power 750 kW in [50, 2000]");
}

/// Test 10: Shell cooling — boolean flag using i32 with if/else pattern.
/// Flag 1 = cooling enabled, which limits shell temp to safe threshold.
#[test]
fn test_shell_cooling_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling_flag", i32_ty());
    ctx.declare_var_typed("shell_temp_limit", u32_ty());
    ctx.declare_var_typed("effective_shell_temp", u32_ty());
    ctx.declare_var_typed("max_shell_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "cooling_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_shell_temp == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "limit_val",
        "shell_temp_limit == 250",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "effective_def",
        "effective_shell_temp == if cooling_flag == 1 { shell_temp_limit } else { max_shell_temp }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_limits_temp",
        "effective_shell_temp <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling flag limits shell temp to 250 C");
}
