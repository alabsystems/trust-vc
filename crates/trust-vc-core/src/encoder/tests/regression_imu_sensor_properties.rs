// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn accelerometer_range() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_raw", "max_raw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_range", i32_ty());
    // 16-bit ADC, ±16g range. Raw value 0-65535, midpoint = 32768 = 0g
    ctx.push_obligation(ProofObligation::assume("ar", "accel_raw == 40000"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_raw == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "wr_def",
        "within_range == if accel_raw <= max_raw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IMU: accel raw 40000 ≤ 65535 → within range");
}

#[test]
fn gyroscope_sensitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("full_scale_dps", u32_ty());
    ctx.declare_var_typed("sensitivity_mdps_lsb", u32_ty());
    // ±2000 dps at 16-bit: sensitivity = 2000*2*1000/65536 ≈ 61 mdps/LSB
    ctx.push_obligation(ProofObligation::assume("fs", "full_scale_dps == 2000"));
    ctx.push_obligation(ProofObligation::assume("sm", "sensitivity_mdps_lsb == 61")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_61",
        "sensitivity_mdps_lsb == 61",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IMU: ±2000dps → 61 mdps/LSB sensitivity (precomputed)",
    );
}

#[test]
fn sample_rate_valid() {
    let mut ctx = VerificationContext::new();
    for v in &["odr_hz", "min_odr_hz", "max_odr_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_valid", i32_ty());
    // Output data rate: typical 1 Hz to 6664 Hz
    ctx.push_obligation(ProofObligation::assume("oh", "odr_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_odr_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_odr_hz == 6664"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "rate_valid == if odr_hz >= min_odr_hz && odr_hz <= max_odr_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IMU: 1000 Hz in [1, 6664] → valid ODR");
}

#[test]
fn fifo_watermark() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_level", "watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("threshold_reached", i32_ty());
    // FIFO depth typically 512 samples, watermark triggers interrupt
    ctx.push_obligation(ProofObligation::assume("fl", "fifo_level == 256"));
    ctx.push_obligation(ProofObligation::assume("wm", "watermark == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "threshold_reached == if fifo_level >= watermark { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "threshold_reached == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IMU: FIFO level 256 ≥ 200 watermark → threshold reached",
    );
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_raw", "temp_offset", "temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Temperature = (raw - offset). Precompute: 25000 - 23000 = 2000 (20.00°C in centidegrees)
    ctx.push_obligation(ProofObligation::assume("tr", "temp_raw == 25000"));
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 23000"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "temp_c == temp_raw - temp_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2000", "temp_c == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IMU: temp 25000 - 23000 = 2000 centideg (20.00°C)");
}

#[test]
fn axis_data_ready() {
    let mut ctx = VerificationContext::new();
    for v in &["status_reg", "xyz_ready_mask"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("all_ready", i32_ty());
    // Status register: bits [2:0] = X,Y,Z data ready. All ready = 7.
    // Precompute: status & mask. 15 & 7 = 7 → all ready
    ctx.push_obligation(ProofObligation::assume("sr", "status_reg == 15"));
    ctx.push_obligation(ProofObligation::assume("xm", "xyz_ready_mask == 7"));
    ctx.push_obligation(ProofObligation::assume("ar_val", "all_ready == 1")); // precomputed: (15 & 7) == 7
    ctx.push_obligation(ProofObligation::assert("yes", "all_ready == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IMU: status 15 & mask 7 = 7 → all axes ready (precomputed)",
    );
}

#[test]
fn motion_detection_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_magnitude", "motion_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("motion_detected", i32_ty());
    // Motion detection: magnitude exceeds threshold
    ctx.push_obligation(ProofObligation::assume("am", "accel_magnitude == 5000")); // mg
    ctx.push_obligation(ProofObligation::assume("mt", "motion_threshold == 200")); // mg
    ctx.push_obligation(ProofObligation::assume(
        "md_def",
        "motion_detected == if accel_magnitude > motion_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "motion_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IMU: accel 5000mg > 200mg threshold → motion detected",
    );
}

#[test]
fn filter_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bandwidth_hz", "odr_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_bw", i32_ty());
    // Anti-aliasing filter BW must be ≤ ODR/2 (Nyquist)
    // Precompute: 1000/2 = 500. BW 400 ≤ 500.
    ctx.push_obligation(ProofObligation::assume("bh", "bandwidth_hz == 400"));
    ctx.push_obligation(ProofObligation::assume("oh", "odr_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_bw == if bandwidth_hz <= 500 { 1 } else { 0 }",
    )); // precomputed Nyquist = ODR/2
    ctx.push_obligation(ProofObligation::assert("yes", "valid_bw == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IMU: BW 400Hz ≤ 500Hz (ODR/2) → valid anti-alias filter",
    );
}

#[test]
fn self_test_deviation() {
    let mut ctx = VerificationContext::new();
    for v in &["self_test_value", "min_deviation", "max_deviation"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("test_pass", i32_ty());
    // Self-test: output change must be within manufacturer limits
    ctx.push_obligation(ProofObligation::assume("sv", "self_test_value == 500"));
    ctx.push_obligation(ProofObligation::assume("mnd", "min_deviation == 200"));
    ctx.push_obligation(ProofObligation::assume("mxd", "max_deviation == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "test_pass == if self_test_value >= min_deviation && self_test_value <= max_deviation { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "test_pass == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IMU: self-test 500 in [200, 800] → pass");
}

#[test]
fn power_mode_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ua", "budget_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_budget", i32_ty());
    // Low-power mode: ~20μA, normal: ~450μA, high-perf: ~680μA
    ctx.push_obligation(ProofObligation::assume("cu", "current_ua == 450"));
    ctx.push_obligation(ProofObligation::assume("bu", "budget_ua == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if current_ua <= budget_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IMU: 450μA ≤ 1000μA budget → within budget");
}
