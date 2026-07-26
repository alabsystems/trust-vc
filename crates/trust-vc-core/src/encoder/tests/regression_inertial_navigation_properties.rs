// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gyro_bias_drift() {
    let mut ctx = VerificationContext::new();
    for v in &["drift_dph", "max_drift_dph"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Gyroscope bias drift (degrees per hour)
    ctx.push_obligation(ProofObligation::assume("dd", "drift_dph == 10"));
    ctx.push_obligation(ProofObligation::assume("md", "max_drift_dph == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if drift_dph <= max_drift_dph { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 10°/h gyro drift ≤ 50°/h max → OK");
}

#[test]
fn accel_bias() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_ug", "max_bias_ug"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // Accelerometer bias stability (μg)
    ctx.push_obligation(ProofObligation::assume("bu", "bias_ug == 100"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_bias_ug == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_ug <= max_bias_ug { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 100μg accel bias ≤ 500μg max → OK");
}

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // IMU update rate: 100-1000Hz for navigation
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 400"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 400Hz update ≥ 100Hz min → rate OK");
}

#[test]
fn axis_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axes", u32_ty());
    ctx.declare_var_typed("is_9dof", i32_ty());
    // Axes: 6 (accel+gyro), 9 (accel+gyro+mag)
    ctx.push_obligation(ProofObligation::assume("a", "axes == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_9dof == if axes == 9 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_9dof == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: axes=9 → 9-DOF (accel+gyro+mag)");
}

#[test]
fn position_error_growth() {
    let mut ctx = VerificationContext::new();
    for v in &["error_m", "max_error_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("nav_ok", i32_ty());
    // Position error after integration period
    ctx.push_obligation(ProofObligation::assume("em", "error_m == 5"));
    ctx.push_obligation(ProofObligation::assume("me", "max_error_m == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "nav_ok == if error_m <= max_error_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "nav_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 5m position error ≤ 10m max → nav OK");
}

#[test]
fn alignment_time() {
    let mut ctx = VerificationContext::new();
    for v in &["align_sec", "max_align_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("align_ok", i32_ty());
    // Initial alignment (leveling + gyrocompassing)
    ctx.push_obligation(ProofObligation::assume("as_", "align_sec == 30"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_align_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "align_ok == if align_sec <= max_align_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "align_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 30s alignment ≤ 120s max → OK");
}

#[test]
fn heading_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["heading_err_x10", "max_err_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("heading_ok", i32_ty());
    // Heading accuracy (×10 for 0.1° resolution)
    ctx.push_obligation(ProofObligation::assume("he", "heading_err_x10 == 5")); // 0.5°
    ctx.push_obligation(ProofObligation::assume("me", "max_err_x10 == 20")); // 2.0°
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "heading_ok == if heading_err_x10 <= max_err_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "heading_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 0.5° heading error ≤ 2.0° max → OK");
}

#[test]
fn vibration_rejection() {
    let mut ctx = VerificationContext::new();
    for v in &["vib_g", "max_vib_g"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vib_ok", i32_ty());
    // Vibration tolerance (g-force)
    ctx.push_obligation(ProofObligation::assume("vg", "vib_g == 10"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vib_g == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vib_ok == if vib_g <= max_vib_g { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vib_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 10g vibration ≤ 20g max → OK");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_x10", "min_comp_x10", "max_comp_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("comp_ok", i32_ty());
    // Temperature compensation range (offset +500)
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_x10 == 750")); // 25.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_comp_x10 == 100")); // -40.0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_comp_x10 == 1350")); // 85.0°C
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "comp_ok == if temp_c_x10 >= min_comp_x10 && temp_c_x10 <= max_comp_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "comp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 25°C in [-40, 85] → temp compensation OK");
}

#[test]
fn kalman_filter_state() {
    let mut ctx = VerificationContext::new();
    for v in &["state_count", "max_states"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("state_ok", i32_ty());
    // Kalman filter state vector size (e.g., 15-state: pos/vel/att/gyro-bias/accel-bias)
    ctx.push_obligation(ProofObligation::assume("sc", "state_count == 15"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_states == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "state_ok == if state_count <= max_states { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "state_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INS: 15 Kalman states ≤ 24 max → OK");
}
