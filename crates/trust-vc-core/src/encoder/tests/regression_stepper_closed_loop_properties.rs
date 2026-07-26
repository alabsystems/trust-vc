// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn position_error() {
    let mut ctx = VerificationContext::new();
    for v in &["target_steps", "actual_steps", "max_error_steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tracking_ok", i32_ty());
    // Position error within tolerance (actual > target for positive error)
    ctx.push_obligation(ProofObligation::assume("ts", "target_steps == 1000"));
    ctx.push_obligation(ProofObligation::assume("as_", "actual_steps == 1002"));
    ctx.push_obligation(ProofObligation::assume("me", "max_error_steps == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tracking_ok == if actual_steps - target_steps <= max_error_steps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tracking_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: error 2 ≤ 5 max steps → tracking OK");
}

#[test]
fn stall_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["error_steps", "stall_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stall_detected", i32_ty());
    // Stall: position error exceeds threshold
    ctx.push_obligation(ProofObligation::assume("es", "error_steps == 50"));
    ctx.push_obligation(ProofObligation::assume("st", "stall_threshold == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "stall_detected == if error_steps >= stall_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stall_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper CL: error 50 ≥ 20 threshold → stall detected",
    );
}

#[test]
fn encoder_feedback_ppr() {
    let mut ctx = VerificationContext::new();
    for v in &["encoder_ppr", "min_ppr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("feedback_ok", i32_ty());
    // Encoder PPR for position feedback (1000-10000 typical)
    ctx.push_obligation(ProofObligation::assume("ep", "encoder_ppr == 4000"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_ppr == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "feedback_ok == if encoder_ppr >= min_ppr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "feedback_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 4000 PPR ≥ 1000 min → feedback OK");
}

#[test]
fn current_regulation() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "target_ma", "tolerance_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("regulated", i32_ty());
    // Closed-loop current regulation
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 1510"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_ma == 1500"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_ma == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "regulated == if current_ma >= target_ma - tolerance_ma && current_ma <= target_ma + tolerance_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "regulated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 1.51A in [1.45, 1.55] → regulated");
}

#[test]
fn velocity_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["velocity_sps", "max_velocity_sps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vel_ok", i32_ty());
    // Steps per second within motor capability
    ctx.push_obligation(ProofObligation::assume("vs", "velocity_sps == 50000"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_velocity_sps == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if velocity_sps <= max_velocity_sps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 50K SPS ≤ 100K max → velocity OK");
}

#[test]
fn acceleration_ramp() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_sps2", "max_accel_sps2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accel_ok", i32_ty());
    // Acceleration profile limit (steps/sec²)
    ctx.push_obligation(ProofObligation::assume("as_", "accel_sps2 == 200000"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_accel_sps2 == 500000"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "accel_ok == if accel_sps2 <= max_accel_sps2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "accel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 200K accel ≤ 500K max → ramp OK");
}

#[test]
fn holding_torque() {
    let mut ctx = VerificationContext::new();
    for v in &["load_torque_mnm", "hold_torque_mnm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hold_ok", i32_ty());
    // Holding torque must exceed load (mN·m)
    ctx.push_obligation(ProofObligation::assume("lt", "load_torque_mnm == 300"));
    ctx.push_obligation(ProofObligation::assume("ht", "hold_torque_mnm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hold_ok == if hold_torque_mnm >= load_torque_mnm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hold_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 500mN·m hold ≥ 300mN·m load → OK");
}

#[test]
fn pid_output() {
    let mut ctx = VerificationContext::new();
    for v in &["pid_output", "min_output", "max_output"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_ok", i32_ty());
    // PID controller output clamping
    ctx.push_obligation(ProofObligation::assume("po", "pid_output == 750"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_output == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_output == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "output_ok == if pid_output >= min_output && pid_output <= max_output { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "output_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper CL: PID output 750 in [0, 1000] → clamped OK",
    );
}

#[test]
fn microstep_interpolation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("microsteps", u32_ty());
    ctx.declare_var_typed("valid_ustep", i32_ty());
    // Valid microstep settings: 1, 2, 4, 8, 16, 32, 64, 128, 256
    ctx.push_obligation(ProofObligation::assume("m", "microsteps == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "vu_def",
        "valid_ustep == if microsteps == 1 || microsteps == 2 || microsteps == 4 || microsteps == 8 || microsteps == 16 || microsteps == 32 || microsteps == 64 || microsteps == 128 || microsteps == 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ustep == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 64 microsteps is a valid setting");
}

#[test]
fn thermal_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_x10", "warn_c_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overtemp", i32_ty());
    // Thermal warning when driver exceeds threshold (offset +500)
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_x10 == 1350")); // 85.0°C
    ctx.push_obligation(ProofObligation::assume("wc", "warn_c_x10 == 1200")); // 70.0°C
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "overtemp == if temp_c_x10 >= warn_c_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overtemp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper CL: 85°C ≥ 70°C warning → overtemp");
}
