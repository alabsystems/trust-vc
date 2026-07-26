// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn step_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("microsteps", u32_ty());
    // Valid microstep resolutions: 1 (full), 2 (half), 4 (quarter), 8 (eighth), 16 (sixteenth)
    ctx.push_obligation(ProofObligation::assume(
        "valid_resolution",
        "microsteps == 1 || microsteps == 2 || microsteps == 4 || microsteps == 8 || microsteps == 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "microsteps >= 1 && microsteps <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: microstep resolution 1/2/4/8/16 all in [1,16]",
    );
}

#[test]
fn max_pulse_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_rate_khz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pr_val", "pulse_rate_khz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "pr_range",
        "pulse_rate_khz >= 1 && pulse_rate_khz <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "pulse_rate_khz == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: max pulse rate 500 kHz in [1,2000]",
    );
}

#[test]
fn acceleration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accel_k", u32_ty());
    // Acceleration stored as steps/s^2 / 1000. Value 50 means 50000 steps/s^2.
    ctx.push_obligation(ProofObligation::assume("ak_val", "accel_k == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ak_range",
        "accel_k >= 1 && accel_k <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "accel_k == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: acceleration 50 (50000 steps/s^2) in [1,1000]",
    );
}

#[test]
fn motor_current() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_ma", u32_ty());
    ctx.declare_var_typed("current_ok", i32_ty());
    // Phase current in mA, value 2000 (2A), range 100-10000
    ctx.push_obligation(ProofObligation::assume("cm_val", "current_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_ma >= 100 && current_ma <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: 2000 mA phase current in [100,10000]",
    );
}

#[test]
fn holding_torque() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_mnm", u32_ty());
    ctx.declare_var_typed("torque_ok", i32_ty());
    // Holding torque in mN·m, value 500, range 10-5000
    ctx.push_obligation(ProofObligation::assume("tm_val", "torque_mnm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "torque_ok == if torque_mnm >= 10 && torque_mnm <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "torque_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: 500 mN-m holding torque in [10,5000]",
    );
}

#[test]
fn motion_profile() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", u32_ty());
    // 1=trapezoidal, 2=S-curve, 3=parabolic, 4=sinusoidal
    ctx.push_obligation(ProofObligation::assume(
        "valid_profile",
        "profile == 1 || profile == 2 || profile == 3 || profile == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "profile >= 1 && profile <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: motion profile 1-4 (trap/S/parab/sin)",
    );
}

#[test]
fn encoder_feedback() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feedback_mode", u32_ty());
    // 1=open-loop, 2=incremental encoder, 3=absolute encoder
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "feedback_mode == 1 || feedback_mode == 2 || feedback_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "feedback_mode >= 1 && feedback_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: feedback mode 1-3 (open/incremental/absolute)",
    );
}

#[test]
fn idle_current_reduction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idle_pct_x10", u32_ty());
    ctx.declare_var_typed("idle_ok", i32_ty());
    // Idle current as % of run current ×10. Value 500 means 50.0%, range 0-1000 (0-100.0%)
    ctx.push_obligation(ProofObligation::assume("ip_val", "idle_pct_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "idle_ok == if idle_pct_x10 >= 0 && idle_pct_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "idle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: idle current 500 (50.0%) in [0,1000]",
    );
}

#[test]
fn step_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steps", u32_ty());
    ctx.declare_var_typed("steps_ok", i32_ty());
    // Total steps per move, value 10000, max 1000000
    ctx.push_obligation(ProofObligation::assume("s_val", "steps == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "steps_ok == if steps >= 1 && steps <= 1000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "steps_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: 10000 steps per move <= 1000000 max",
    );
}

#[test]
fn direction_setup_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("setup_us", u32_ty());
    ctx.declare_var_typed("setup_ok", i32_ty());
    // Direction signal setup time in microseconds, value 5, range 1-100
    ctx.push_obligation(ProofObligation::assume("su_val", "setup_us == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sok_def",
        "setup_ok == if setup_us >= 1 && setup_us <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "setup_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper indexer: 5 us direction setup time in [1,100]",
    );
}
