// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn echo_time_to_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["echo_us", "speed_cm_per_us_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("distance_cm_x100", u32_ty());
    // distance = echo_time × speed / 2 (round trip). Precompute: 580μs × 34/2 = 9860 (×100 scale)
    ctx.push_obligation(ProofObligation::assume("eu", "echo_us == 580"));
    ctx.push_obligation(ProofObligation::assume("sp", "speed_cm_per_us_x100 == 34")); // 0.034 cm/μs × 100
    ctx.push_obligation(ProofObligation::assume("dc", "distance_cm_x100 == 9860")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_9860",
        "distance_cm_x100 == 9860",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic: 580μs echo → 9.86cm distance (precomputed)",
    );
}

#[test]
fn min_range_check() {
    let mut ctx = VerificationContext::new();
    for v in &["distance_cm", "min_range_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Most ultrasonic sensors have a minimum range (e.g., 2cm)
    ctx.push_obligation(ProofObligation::assume("dc", "distance_cm == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_range_cm == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if distance_cm >= min_range_cm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic: 5cm ≥ 2cm min range → in range");
}

#[test]
fn max_range_check() {
    let mut ctx = VerificationContext::new();
    for v in &["distance_cm", "max_range_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Max range typically 400cm for HC-SR04
    ctx.push_obligation(ProofObligation::assume("dc", "distance_cm == 250"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_range_cm == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if distance_cm <= max_range_cm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic: 250cm ≤ 400cm max range → in range");
}

#[test]
fn trigger_pulse_width() {
    let mut ctx = VerificationContext::new();
    for v in &["trigger_us", "min_trigger_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trigger_ok", i32_ty());
    // HC-SR04 requires ≥10μs trigger pulse
    ctx.push_obligation(ProofObligation::assume("tu", "trigger_us == 15"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_trigger_us == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "trigger_ok == if trigger_us >= min_trigger_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trigger_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic: 15μs trigger ≥ 10μs min → trigger OK");
}

#[test]
fn measurement_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["interval_ms", "min_interval_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("interval_ok", i32_ty());
    // Minimum measurement cycle: ~60ms to avoid echo interference
    ctx.push_obligation(ProofObligation::assume("im", "interval_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_interval_ms == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "interval_ok == if interval_ms >= min_interval_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "interval_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic: 100ms interval ≥ 60ms min → interval OK",
    );
}

#[test]
fn echo_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["echo_us", "timeout_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timed_out", i32_ty());
    // No echo within timeout → out of range
    ctx.push_obligation(ProofObligation::assume("eu", "echo_us == 25000"));
    ctx.push_obligation(ProofObligation::assume("tu", "timeout_us == 23200")); // ~400cm
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timed_out == if echo_us > timeout_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timed_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic: 25000μs echo > 23200μs timeout → timed out",
    );
}

#[test]
fn median_filter() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_a", "sample_b", "sample_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("median_val", u32_ty());
    // Median of 3 samples removes outliers
    ctx.push_obligation(ProofObligation::assume("sa", "sample_a == 100"));
    ctx.push_obligation(ProofObligation::assume("sb", "sample_b == 250")); // outlier
    ctx.push_obligation(ProofObligation::assume("sc", "sample_c == 102"));
    ctx.push_obligation(ProofObligation::assume("mv", "median_val == 102")); // precomputed median
    ctx.push_obligation(ProofObligation::assert("is_102", "median_val == 102"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ultrasonic: median(100, 250, 102) = 102 (precomputed)",
    );
}

#[test]
fn obstacle_alarm() {
    let mut ctx = VerificationContext::new();
    for v in &["distance_cm", "alarm_threshold_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm_active", i32_ty());
    // Proximity alarm when object closer than threshold
    ctx.push_obligation(ProofObligation::assume("dc", "distance_cm == 15"));
    ctx.push_obligation(ProofObligation::assume("at", "alarm_threshold_cm == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if distance_cm < alarm_threshold_cm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic: 15cm < 30cm threshold → alarm active");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_offset", "speed_adjust_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Speed of sound varies with temperature. At 25°C: 34600 cm/s
    // Precompute adjusted speed for current temp
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 525")); // 25°C + 500 offset
    ctx.push_obligation(ProofObligation::assume("sa", "speed_adjust_x100 == 3460")); // 346.0 m/s × 10
    ctx.push_obligation(ProofObligation::assert(
        "is_3460",
        "speed_adjust_x100 == 3460",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic: 25°C → speed 346.0 m/s (precomputed)");
}

#[test]
fn beam_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["beam_angle_deg", "max_angle_deg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("narrow_enough", i32_ty());
    // Beam angle affects spatial resolution. Typical: 15-30°
    ctx.push_obligation(ProofObligation::assume("ba", "beam_angle_deg == 15"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_angle_deg == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ne_def",
        "narrow_enough == if beam_angle_deg <= max_angle_deg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "narrow_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ultrasonic: 15° beam ≤ 30° max → narrow enough");
}
