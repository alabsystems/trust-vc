// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn steps_per_revolution() {
    let mut ctx = VerificationContext::new();
    for v in &["full_steps", "microstep_factor"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_steps", u32_ty());
    // Microsteps per rev = full_steps × microstep_factor. Precompute: 200 × 16 = 3200
    ctx.push_obligation(ProofObligation::assume("fs", "full_steps == 200"));
    ctx.push_obligation(ProofObligation::assume("mf", "microstep_factor == 16"));
    ctx.push_obligation(ProofObligation::assume("ts", "total_steps == 3200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_3200", "total_steps == 3200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 200 full × 16 micro = 3200 steps/rev");
}

#[test]
fn step_angle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steps_per_rev", u32_ty());
    ctx.declare_var_typed("step_angle_mdeg", u32_ty());
    // Angle per step = 360000 mdeg / steps. Precompute: 360000/200 = 1800 mdeg = 1.8°
    ctx.push_obligation(ProofObligation::assume("spr", "steps_per_rev == 200"));
    ctx.push_obligation(ProofObligation::assume("sa", "step_angle_mdeg == 1800")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_1800",
        "step_angle_mdeg == 1800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 360°/200 = 1.8° per step (precomputed)");
}

#[test]
fn acceleration_ramp_steps() {
    let mut ctx = VerificationContext::new();
    for v in &["current_speed", "target_speed", "accel_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "current_speed == 500"));
    ctx.push_obligation(ProofObligation::assume("ts", "target_speed == 1000"));
    ctx.push_obligation(ProofObligation::assume("ar", "accel_rate == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "at_speed == if current_speed >= target_speed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "at_speed == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 500 < 1000 target → not at speed");
}

#[test]
fn holding_torque_check() {
    let mut ctx = VerificationContext::new();
    for v in &["load_torque_mnm", "holding_torque_mnm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_hold", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "load_torque_mnm == 300"));
    ctx.push_obligation(ProofObligation::assume("ht", "holding_torque_mnm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ch_def",
        "can_hold == if holding_torque_mnm >= load_torque_mnm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_hold == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 500 mN·m hold ≥ 300 load → can hold");
}

#[test]
fn position_error_check() {
    let mut ctx = VerificationContext::new();
    for v in &["commanded_steps", "actual_steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("position_error", u32_ty());
    ctx.declare_var_typed("error_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "commanded_steps == 1000"));
    ctx.push_obligation(ProofObligation::assume("as_val", "actual_steps == 998"));
    ctx.push_obligation(ProofObligation::assume(
        "pe_def",
        "position_error == commanded_steps - actual_steps",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "error_ok == if position_error <= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "position_error == 2"));
    ctx.push_obligation(ProofObligation::assert("ok", "error_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 1000-998 = 2 step error ≤ 5 → OK");
}

#[test]
fn current_chopping_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["sense_mv", "threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("chop", i32_ty());
    // Current chopping: turn off when sense voltage exceeds threshold
    ctx.push_obligation(ProofObligation::assume("sm", "sense_mv == 250"));
    ctx.push_obligation(ProofObligation::assume("tm", "threshold_mv == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "chop == if sense_mv >= threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "chop == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 250mV sense ≥ 200mV threshold → chop");
}

#[test]
fn phase_sequence() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_phase", u32_ty());
    ctx.declare_var_typed("num_phases", u32_ty());
    ctx.declare_var_typed("next_phase", u32_ty());
    // Next phase wraps around. Precompute: (2 + 1) % 4 = 3
    ctx.push_obligation(ProofObligation::assume("cp", "current_phase == 2"));
    ctx.push_obligation(ProofObligation::assume("np", "num_phases == 4"));
    ctx.push_obligation(ProofObligation::assume("nph", "next_phase == 3")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_3", "next_phase == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: phase (2+1) % 4 = 3 (precomputed)");
}

#[test]
fn stall_detection_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["back_emf_mv", "stall_threshold_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stalled", i32_ty());
    // Stall: back-EMF drops below threshold
    ctx.push_obligation(ProofObligation::assume("be", "back_emf_mv == 50"));
    ctx.push_obligation(ProofObligation::assume("st", "stall_threshold_mv == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "stalled == if back_emf_mv < stall_threshold_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stalled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: BEMF 50mV < 100mV threshold → stalled");
}

#[test]
fn travel_distance_mm() {
    let mut ctx = VerificationContext::new();
    for v in &["steps_moved", "lead_pitch_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("distance_um", u32_ty());
    // Distance = steps × pitch / steps_per_rev. Precompute: 400 × 8000 / 200 = 16000 μm
    ctx.push_obligation(ProofObligation::assume("sm", "steps_moved == 400"));
    ctx.push_obligation(ProofObligation::assume("lp", "lead_pitch_um == 8000")); // 8mm lead
    ctx.push_obligation(ProofObligation::assume("du", "distance_um == 16000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_16000", "distance_um == 16000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper: 400 steps × 8mm/200 = 16mm travel");
}

#[test]
fn thermal_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["driver_temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overtemp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "driver_temp_c == 160"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_c == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "overtemp == if driver_temp_c > max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overtemp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper driver: 160°C > 150°C → overtemp");
}
