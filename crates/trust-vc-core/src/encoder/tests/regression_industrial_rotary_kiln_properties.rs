// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial rotary kiln property verification.
// Encodes key parameters of a rotary kiln (cement, lime, ore processing)
// and verifies bounded, disjunctive, scaled, and boolean-flag constraints.

/// Test 1: Kiln diameter (x10 m) — scaled at 0.1 m, bounded [10, 80].
/// 10 represents 1.0 m, 80 represents 8.0 m. Value 45 (4.5 m).
#[test]
fn test_kiln_diameter_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "dia_x10 == 45"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "dia_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "dia_x10 <= 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kiln diameter 4.5 m (45 x10) in [10, 80]");
}

/// Test 2: Kiln length (m) — bounded [10, 200], value 75.
#[test]
fn test_kiln_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kiln_len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "kiln_len == 75"));
    ctx.push_obligation(ProofObligation::assert("len_min", "kiln_len >= 10"));
    ctx.push_obligation(ProofObligation::assert("len_max", "kiln_len <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kiln length 75 m in [10, 200]");
}

/// Test 3: Rotation speed (x10 RPM) — scaled at 0.1 RPM, bounded [1, 50].
/// 1 represents 0.1 RPM, 50 represents 5.0 RPM. Value 15 (1.5 RPM).
#[test]
fn test_rotation_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "rpm_x10 == 15"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "rpm_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "rpm_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 1.5 RPM (15 x10) in [1, 50]");
}

/// Test 4: Max temperature (deg C) — bounded [500, 1800], value 1450.
#[test]
fn test_max_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "max_temp == 1450"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "max_temp >= 500"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "max_temp <= 1800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max temperature 1450 C in [500, 1800]");
}

/// Test 5: Inclination angle (x10 degrees) — scaled at 0.1 deg, bounded [10, 50].
/// 10 represents 1.0 deg, 50 represents 5.0 deg. Value 30 (3.0 deg).
#[test]
fn test_inclination_angle_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("incl_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("incl_val", "incl_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("incl_min", "incl_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("incl_max", "incl_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclination 3.0 deg (30 x10) in [10, 50]");
}

/// Test 6: Firing type — 3-way disjunction.
/// 1=direct, 2=indirect, 3=combined. Value 1 (direct firing).
#[test]
fn test_firing_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("firing_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fire_val", "firing_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_firing",
        "firing_type == 1 || firing_type == 2 || firing_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firing type 1 (direct) is valid 3-way disjunction");
}

/// Test 7: Refractory lining — 3-way disjunction.
/// 1=alumina, 2=magnesia, 3=chrome-mag. Value 2 (magnesia).
#[test]
fn test_refractory_lining_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lining_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lining_val", "lining_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_lining",
        "lining_type == 1 || lining_type == 2 || lining_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refractory lining 2 (magnesia) is valid 3-way disjunction",
    );
}

/// Test 8: Drive system — 3-way disjunction.
/// 1=single-pinion, 2=dual-pinion, 3=friction-drive. Value 2 (dual-pinion).
#[test]
fn test_drive_system_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_sys", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drive_val", "drive_sys == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_drive",
        "drive_sys == 1 || drive_sys == 2 || drive_sys == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive system 2 (dual-pinion) is valid 3-way disjunction",
    );
}

/// Test 9: Throughput (tonnes/h) — bounded [1, 500], value 120.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tp_val", "throughput == 120"));
    ctx.push_obligation(ProofObligation::assert("tp_min", "throughput >= 1"));
    ctx.push_obligation(ProofObligation::assert("tp_max", "throughput <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 120 tonnes/h in [1, 500]");
}

/// Test 10: Kiln shell cooling — boolean flag using i32 with if/else pattern.
/// Flag 1 = shell cooling enabled, which limits shell temperature to safe threshold.
#[test]
fn test_shell_cooling_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling_flag", i32_ty());
    ctx.declare_var_typed("safe_temp", u32_ty());
    ctx.declare_var_typed("effective_temp", u32_ty());
    ctx.declare_var_typed("uncooled_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "cooling_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "uncooled_val",
        "uncooled_temp == 350",
    ));
    ctx.push_obligation(ProofObligation::assume("safe_val", "safe_temp == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "temp_def",
        "effective_temp == if cooling_flag == 1 { safe_temp } else { uncooled_temp }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_limits_temp",
        "effective_temp <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shell cooling flag limits temperature to 200 C");
}
