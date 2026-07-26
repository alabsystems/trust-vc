// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn position_from_counts() {
    let mut ctx = VerificationContext::new();
    for v in &["encoder_counts", "counts_per_rev"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("revolutions", u32_ty());
    // Revolutions = counts / counts_per_rev. Precompute: 8000 / 4000 = 2
    ctx.push_obligation(ProofObligation::assume("ec", "encoder_counts == 8000"));
    ctx.push_obligation(ProofObligation::assume("cpr", "counts_per_rev == 4000"));
    ctx.push_obligation(ProofObligation::assume("rev", "revolutions == 2")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2", "revolutions == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: 8000 counts / 4000 CPR = 2 revolutions");
}

#[test]
fn quadrature_decoding_x4() {
    let mut ctx = VerificationContext::new();
    for v in &["line_count", "decode_mode"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("counts_per_rev", u32_ty());
    // X4 decoding: 4 × lines per revolution. Precompute: 1000 × 4 = 4000
    ctx.push_obligation(ProofObligation::assume("lc", "line_count == 1000"));
    ctx.push_obligation(ProofObligation::assume("dm", "decode_mode == 4")); // X4
    ctx.push_obligation(ProofObligation::assume("cpr", "counts_per_rev == 4000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4000", "counts_per_rev == 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "QE: 1000 lines × X4 = 4000 counts/rev (precomputed)",
    );
}

#[test]
fn direction_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channel_a_leads", u32_ty());
    ctx.declare_var_typed("direction", u32_ty());
    // A leads B → forward (1), B leads A → reverse (0)
    ctx.push_obligation(ProofObligation::assume("cal", "channel_a_leads == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "direction == if channel_a_leads == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("forward", "direction == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: channel A leads → forward direction");
}

#[test]
fn index_pulse_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["position_at_index", "expected_index_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // Index pulse should occur at expected position (once per revolution)
    ctx.push_obligation(ProofObligation::assume("pai", "position_at_index == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "eip",
        "expected_index_position == 0",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "aligned == if position_at_index == expected_index_position { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: index at position 0 = expected → aligned");
}

#[test]
fn speed_from_period() {
    let mut ctx = VerificationContext::new();
    for v in &["timer_counts", "timer_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("period_us", u32_ty());
    // Period = timer_counts / timer_freq_mhz. Precompute: 1000 / 1 = 1000 μs
    ctx.push_obligation(ProofObligation::assume("tc", "timer_counts == 1000"));
    ctx.push_obligation(ProofObligation::assume("tf", "timer_freq_mhz == 1"));
    ctx.push_obligation(ProofObligation::assume("pu", "period_us == 1000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1000", "period_us == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: 1000 counts / 1MHz = 1000μs period");
}

#[test]
fn noise_filter_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["pulse_width_ns", "filter_threshold_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_noise", i32_ty());
    // Pulses shorter than threshold are noise
    ctx.push_obligation(ProofObligation::assume("pw", "pulse_width_ns == 50"));
    ctx.push_obligation(ProofObligation::assume("ft", "filter_threshold_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_noise == if pulse_width_ns < filter_threshold_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_noise == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: 50ns pulse < 100ns filter → noise");
}

#[test]
fn position_wrap_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["current_count", "max_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("near_overflow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cc", "current_count == 65530"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_count == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "near_overflow == if current_count > max_count - 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "near_overflow == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: 65530 > 65525 (65535-10) → near overflow");
}

#[test]
fn multi_turn_position() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "turn_count",
        "counts_per_turn",
        "single_turn_count",
        "total_count",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Total = turns × counts_per_turn + single_turn. Precompute: 3 × 4000 + 500 = 12500
    ctx.push_obligation(ProofObligation::assume("tc", "turn_count == 3"));
    ctx.push_obligation(ProofObligation::assume("cpt", "counts_per_turn == 4000"));
    ctx.push_obligation(ProofObligation::assume("stc", "single_turn_count == 500"));
    ctx.push_obligation(ProofObligation::assume("total", "total_count == 12500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_12500", "total_count == 12500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: 3 turns × 4000 + 500 = 12500 total");
}

#[test]
fn error_count_check() {
    let mut ctx = VerificationContext::new();
    for v in &["error_count", "max_errors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("encoder_healthy", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ec", "error_count == 2"));
    ctx.push_obligation(ProofObligation::assume("me", "max_errors == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "eh_def",
        "encoder_healthy == if error_count < max_errors { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "encoder_healthy == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QE: 2 errors < 10 max → healthy");
}

#[test]
fn commutation_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["electrical_angle", "pole_pairs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mechanical_angle", u32_ty());
    // Mechanical angle = electrical / pole_pairs. Precompute: 720 / 4 = 180
    ctx.push_obligation(ProofObligation::assume("ea", "electrical_angle == 720"));
    ctx.push_obligation(ProofObligation::assume("pp", "pole_pairs == 4"));
    ctx.push_obligation(ProofObligation::assume("ma", "mechanical_angle == 180")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_180", "mechanical_angle == 180"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "QE: 720° electrical / 4 pole pairs = 180° mechanical",
    );
}
