// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Heading accuracy in tenths of a degree — 5 represents 0.5°, bounded [1, 50].
#[test]
fn test_heading_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heading_acc", u32_ty());
    ctx.push_obligation(ProofObligation::assume("heading_val", "heading_acc == 5"));
    ctx.push_obligation(ProofObligation::assert("heading_lower", "heading_acc >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "heading_upper",
        "heading_acc <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heading accuracy 0.5 deg (5) within [1, 50]");
}

/// Rudder angle maximum in tenths of a degree — 350 represents 35.0°, bounded [200, 450].
#[test]
fn test_rudder_angle_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rudder_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rudder_val", "rudder_max == 350"));
    ctx.push_obligation(ProofObligation::assert("rudder_lower", "rudder_max >= 200"));
    ctx.push_obligation(ProofObligation::assert("rudder_upper", "rudder_max <= 450"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rudder angle max 35.0 deg (350) within [200, 450]");
}

/// Vessel type as 4-way disjunction: 1=sailboat, 2=motorboat, 3=ship, 4=submarine.
#[test]
fn test_vessel_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vessel_type_valid",
        "vessel_type == 1 || vessel_type == 2 || vessel_type == 3 || vessel_type == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vessel_type_lower",
        "vessel_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vessel_type_upper",
        "vessel_type <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vessel type disjunction {1=sailboat, 2=motorboat, 3=ship, 4=submarine} implies [1, 4]",
    );
}

/// Steering mode as 4-way disjunction: 1=compass, 2=wind, 3=track, 4=standby.
#[test]
fn test_steering_mode_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steer_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "steer_mode_valid",
        "steer_mode == 1 || steer_mode == 2 || steer_mode == 3 || steer_mode == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "steer_mode_lower",
        "steer_mode >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "steer_mode_upper",
        "steer_mode <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "steering mode disjunction {1=compass, 2=wind, 3=track, 4=standby} implies [1, 4]",
    );
}

/// Rudder feedback as 3-way disjunction: 1=potentiometer, 2=Hall effect, 3=NMEA.
#[test]
fn test_rudder_feedback_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feedback", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feedback_valid",
        "feedback == 1 || feedback == 2 || feedback == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("feedback_lower", "feedback >= 1"));
    ctx.push_obligation(ProofObligation::assert("feedback_upper", "feedback <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rudder feedback disjunction {1=potentiometer, 2=Hall effect, 3=NMEA} implies [1, 3]",
    );
}

/// Drive type as 3-way disjunction: 1=hydraulic, 2=electric, 3=pneumatic.
#[test]
fn test_drive_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_type_valid",
        "drive_type == 1 || drive_type == 2 || drive_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_type_lower",
        "drive_type >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_type_upper",
        "drive_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type disjunction {1=hydraulic, 2=electric, 3=pneumatic} implies [1, 3]",
    );
}

/// Communication baud rate as 3-way non-sequential disjunction: 4800, 38400, 115200.
#[test]
fn test_communication_baud_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "baud_valid",
        "baud == 4800 || baud == 38400 || baud == 115200",
    ));
    ctx.push_obligation(ProofObligation::assert("baud_lower", "baud >= 4800"));
    ctx.push_obligation(ProofObligation::assert("baud_upper", "baud <= 115200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "baud rate disjunction {4800, 38400, 115200} implies [4800, 115200]",
    );
}

/// Course change rate in tenths of degrees per minute — 30 represents 3.0 deg/min, bounded [5, 100].
#[test]
fn test_course_change_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("change_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_val", "change_rate == 30"));
    ctx.push_obligation(ProofObligation::assert("rate_lower", "change_rate >= 5"));
    ctx.push_obligation(ProofObligation::assert("rate_upper", "change_rate <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "course change rate 3.0 deg/min (30) within [5, 100]",
    );
}

/// Sea state compensation as 3-way disjunction: 1=calm, 2=moderate, 3=rough.
#[test]
fn test_sea_state_compensation_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sea_state", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sea_state_valid",
        "sea_state == 1 || sea_state == 2 || sea_state == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("sea_state_lower", "sea_state >= 1"));
    ctx.push_obligation(ProofObligation::assert("sea_state_upper", "sea_state <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sea state disjunction {1=calm, 2=moderate, 3=rough} implies [1, 3]",
    );
}

/// Man overboard alert as boolean flag — i32 flag where 1=active, 0=inactive.
#[test]
fn test_man_overboard_alert_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mob_alert", i32_ty());
    ctx.declare_var_typed("helm_lock", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mob_flag",
        "mob_alert == 0 || mob_alert == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("mob_active", "mob_alert == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "lock_def",
        "helm_lock == if mob_alert == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "helm_locked_on_mob",
        "helm_lock == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "man overboard alert active engages helm lock");
}
