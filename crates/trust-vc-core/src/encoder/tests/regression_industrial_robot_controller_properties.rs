// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial robot controller property verification.
// Encodes key parameters of an industrial robot controller and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Axis count — bounded [3, 8], value 6.
#[test]
fn test_axis_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axes", u32_ty());
    ctx.push_obligation(ProofObligation::assume("axes_val", "axes == 6"));
    ctx.push_obligation(ProofObligation::assert("axes_min", "axes >= 3"));
    ctx.push_obligation(ProofObligation::assert("axes_max", "axes <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "axis count 6 in [3, 8]");
}

/// Test 2: Payload capacity (kg) — bounded [1, 2000], value 10.
#[test]
fn test_payload_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("payload_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("payload_val", "payload_kg == 10"));
    ctx.push_obligation(ProofObligation::assert("payload_min", "payload_kg >= 1"));
    ctx.push_obligation(ProofObligation::assert("payload_max", "payload_kg <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "payload capacity 10 kg in [1, 2000]");
}

/// Test 3: Repeatability (micrometers) — positioning precision.
/// Value 50 (0.050 mm), bounded [5, 1000].
#[test]
fn test_repeatability_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeatability_um", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rep_val", "repeatability_um == 50"));
    ctx.push_obligation(ProofObligation::assert("rep_min", "repeatability_um >= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "rep_max",
        "repeatability_um <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repeatability 50 um (0.050 mm) in [5, 1000]");
}

/// Test 4: Robot type — 5-way disjunction.
/// 1=articulated, 2=SCARA, 3=delta, 4=cartesian, 5=collaborative.
/// Value 1 (articulated).
#[test]
fn test_robot_type_five_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("robot_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "robot_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "robot_type == 1 || robot_type == 2 || robot_type == 3 || robot_type == 4 || robot_type == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "robot type 1 (articulated) is valid 5-way disjunction",
    );
}

/// Test 5: Max speed (mm/s) — TCP speed bounded [100, 20000], value 2000.
#[test]
fn test_max_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "max_speed == 2000"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "max_speed >= 100"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "max_speed <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max TCP speed 2000 mm/s in [100, 20000]");
}

/// Test 6: Reach (mm) — working envelope bounded [200, 4000], value 1500.
#[test]
fn test_reach_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reach_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("reach_val", "reach_mm == 1500"));
    ctx.push_obligation(ProofObligation::assert("reach_min", "reach_mm >= 200"));
    ctx.push_obligation(ProofObligation::assert("reach_max", "reach_mm <= 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reach 1500 mm in [200, 4000]");
}

/// Test 7: Controller cycle time (microseconds) — servo loop.
/// Value 1000, bounded [125, 4000].
#[test]
fn test_controller_cycle_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_us", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cycle_val", "cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assert("cycle_min", "cycle_us >= 125"));
    ctx.push_obligation(ProofObligation::assert("cycle_max", "cycle_us <= 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "controller cycle time 1000 us in [125, 4000]");
}

/// Test 8: Safety category — 3-way disjunction.
/// 1=PLd, 2=PLe, 3=SIL3. Value 2 (PLe).
#[test]
fn test_safety_category_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safety_cat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("safety_val", "safety_cat == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_safety",
        "safety_cat == 1 || safety_cat == 2 || safety_cat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "safety category 2 (PLe) is valid 3-way disjunction",
    );
}

/// Test 9: IP rating — 3-way non-sequential disjunction.
/// Valid ratings: 40, 54, 67. Value 54.
#[test]
fn test_ip_rating_non_sequential_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_rating", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ip_val", "ip_rating == 54"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ip",
        "ip_rating == 40 || ip_rating == 54 || ip_rating == 67",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IP rating 54 is valid (40, 54, or 67)");
}

/// Test 10: Collaborative mode — boolean flag using i32 with if/else pattern.
/// Flag 1 = collaborative mode enabled, which requires speed <= 1500 mm/s.
#[test]
fn test_collaborative_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collab_flag", i32_ty());
    ctx.declare_var_typed("speed_limit", u32_ty());
    ctx.declare_var_typed("effective_speed", u32_ty());
    ctx.declare_var_typed("max_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "collab_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "max_speed_val",
        "max_speed == 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("limit_val", "speed_limit == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "effective_def",
        "effective_speed == if collab_flag == 1 { speed_limit } else { max_speed }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "collab_speed_limited",
        "effective_speed <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collaborative mode flag limits effective speed to 1500 mm/s",
    );
}
