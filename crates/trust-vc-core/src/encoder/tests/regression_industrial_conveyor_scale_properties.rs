// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial conveyor scale (belt weigher) property verification.
// Encodes key parameters of a continuous weighing system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Max capacity (kg/m) — material load per metre bounded [1, 5000], value 200.
#[test]
fn test_max_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_kg_m", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity_kg_m == 200"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "capacity_kg_m >= 1"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "capacity_kg_m <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capacity 200 kg/m in [1, 5000]");
}

/// Test 2: Belt speed (x100 m/s) — 250 represents 2.50 m/s, bounded [10, 1000].
#[test]
fn test_belt_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_speed_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_val",
        "belt_speed_x100 == 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_min",
        "belt_speed_x100 >= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_max",
        "belt_speed_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt speed 2.50 m/s (250 x100) in [10, 1000]");
}

/// Test 3: Accuracy class — 4-way disjunction.
/// 1=class 0.5, 2=class 1, 3=class 2, 4=class 5. Value 2 (class 1).
#[test]
fn test_accuracy_class_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_class", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc_class == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_acc",
        "acc_class == 1 || acc_class == 2 || acc_class == 3 || acc_class == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy class 2 (class 1) is valid 4-way disjunction",
    );
}

/// Test 4: Belt width (mm) — conveyor belt width bounded [300, 2400], value 800.
#[test]
fn test_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_width_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("width_val", "belt_width_mm == 800"));
    ctx.push_obligation(ProofObligation::assert("width_min", "belt_width_mm >= 300"));
    ctx.push_obligation(ProofObligation::assert(
        "width_max",
        "belt_width_mm <= 2400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt width 800 mm in [300, 2400]");
}

/// Test 5: Weighbridge length (mm) — idler frame length bounded [500, 5000], value 1200.
#[test]
fn test_weighbridge_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bridge_len_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "bridge_len_mm == 1200"));
    ctx.push_obligation(ProofObligation::assert("len_min", "bridge_len_mm >= 500"));
    ctx.push_obligation(ProofObligation::assert("len_max", "bridge_len_mm <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weighbridge length 1200 mm in [500, 5000]");
}

/// Test 6: Load cell count — number of load cells bounded [1, 8], value 4.
#[test]
fn test_load_cell_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cell_val", "cell_count == 4"));
    ctx.push_obligation(ProofObligation::assert("cell_min", "cell_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("cell_max", "cell_count <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load cell count 4 in [1, 8]");
}

/// Test 7: Communication protocol — 4-way disjunction.
/// 1=4-20mA, 2=Profibus, 3=Modbus, 4=Ethernet/IP. Value 3 (Modbus).
#[test]
fn test_communication_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_proto", u32_ty());
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm_proto == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm_proto == 1 || comm_proto == 2 || comm_proto == 3 || comm_proto == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "comm protocol 3 (Modbus) is valid 4-way disjunction",
    );
}

/// Test 8: Totalizer resolution (x100 kg) — 1 represents 0.01 kg, bounded [1, 10000], value 100.
#[test]
fn test_totalizer_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("total_res_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "total_res_x100 == 100"));
    ctx.push_obligation(ProofObligation::assert("res_min", "total_res_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "res_max",
        "total_res_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "totalizer resolution 1.00 kg (100 x100) in [1, 10000]",
    );
}

/// Test 9: Operating temperature with offset +500 — bounded [250, 800].
/// 250 represents -250 C, 500 represents 0 C, 800 represents 300 C.
/// Value 540 represents 40 C ambient.
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 540"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 250"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 40 C (offset 540) in [250, 800]");
}

/// Test 10: Zero tracking — boolean flag using i32 with if/else pattern.
/// Flag 1 = automatic zero tracking enabled, which activates drift compensation.
#[test]
fn test_zero_tracking_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zero_tracking", i32_ty());
    ctx.declare_var_typed("drift_comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "zero_tracking == 0 || zero_tracking == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "zero_tracking == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "comp_def",
        "drift_comp == if zero_tracking == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tracking_enables_comp",
        "drift_comp == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zero tracking flag enables drift compensation");
}
