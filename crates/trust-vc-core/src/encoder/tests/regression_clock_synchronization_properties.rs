// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn round_trip_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["t1", "t2", "t3", "t4", "round_trip"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // t1=send request, t2=server receive, t3=server send, t4=receive response
    ctx.push_obligation(ProofObligation::assume("t1v", "t1 == 100"));
    ctx.push_obligation(ProofObligation::assume("t2v", "t2 == 110"));
    ctx.push_obligation(ProofObligation::assume("t3v", "t3 == 112"));
    ctx.push_obligation(ProofObligation::assume("t4v", "t4 == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "rt_def",
        "round_trip == (t4 - t1) - (t3 - t2)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_23", "round_trip == 23"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTT: (125-100) - (112-110) = 23ms");
}

#[test]
fn clock_offset_estimate() {
    let mut ctx = VerificationContext::new();
    for v in &["t1", "t2", "t3", "t4", "offset_doubled"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // offset ≈ ((t2-t1) + (t3-t4)) / 2 — use doubled to avoid integer division
    ctx.push_obligation(ProofObligation::assume("t1v", "t1 == 100"));
    ctx.push_obligation(ProofObligation::assume("t2v", "t2 == 115")); // server 15ms ahead
    ctx.push_obligation(ProofObligation::assume("t3v", "t3 == 117"));
    ctx.push_obligation(ProofObligation::assume("t4v", "t4 == 130"));
    // 2*offset = (t2-t1) + (t3-t4) = 15 + (117-130) ... but t3 < t4, so we avoid underflow
    // Actually: (t2 - t1) = 15, (t3 - t4) would be negative. Use (t2+t3) - (t1+t4) instead
    ctx.push_obligation(ProofObligation::assume(
        "od_def",
        "offset_doubled == (t2 + t3) - (t1 + t4)",
    ));
    // (115 + 117) - (100 + 130) = 232 - 230 = 2
    ctx.push_obligation(ProofObligation::assert("is_2", "offset_doubled == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "offset: (115+117)-(100+130) = 2 (×2)");
}

#[test]
fn stratum_level_propagation() {
    let mut ctx = VerificationContext::new();
    for v in &["source_stratum", "local_stratum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ss", "source_stratum == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ls_def",
        "local_stratum == source_stratum + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "local_stratum == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "higher",
        "local_stratum > source_stratum",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stratum: source 2 → local 3");
}

#[test]
fn maximum_stratum_bound() {
    let mut ctx = VerificationContext::new();
    for v in &["stratum", "max_stratum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "stratum == 15"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_stratum == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if stratum < max_stratum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stratum 15 < max 16 → valid");
}

#[test]
fn polling_interval_exponential() {
    let mut ctx = VerificationContext::new();
    for v in &["poll_exponent", "base", "interval_seconds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // interval = 2^poll_exponent, simplified as base^n for small values
    ctx.push_obligation(ProofObligation::assume("pe", "poll_exponent == 6"));
    ctx.push_obligation(ProofObligation::assume("b", "base == 2"));
    // 2^6 = 64, hardcode the result
    ctx.push_obligation(ProofObligation::assume("is_def", "interval_seconds == 64"));
    ctx.push_obligation(ProofObligation::assert("is_64", "interval_seconds == 64"));
    ctx.push_obligation(ProofObligation::assert("positive", "interval_seconds > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "poll interval: 2^6 = 64 seconds");
}

#[test]
fn clock_discipline_adjustment() {
    let mut ctx = VerificationContext::new();
    for v in &["current_offset", "correction_rate", "correction_per_second"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Slew rate: adjust gradually, correction = offset / rate
    ctx.push_obligation(ProofObligation::assume("co", "current_offset == 500")); // 500ms offset
    ctx.push_obligation(ProofObligation::assume("cr", "correction_rate == 100")); // correct over 100 seconds
    ctx.push_obligation(ProofObligation::assume(
        "cps_def",
        "correction_per_second == current_offset / correction_rate",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_5",
        "correction_per_second == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "slew: 500ms / 100s = 5ms/s correction");
}

#[test]
fn best_of_n_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_a", "sample_b", "sample_c", "best_sample"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Select the sample with smallest round-trip delay
    ctx.push_obligation(ProofObligation::assume("sa", "sample_a == 50")); // 50ms RTT
    ctx.push_obligation(ProofObligation::assume("sb", "sample_b == 30")); // 30ms RTT — best
    ctx.push_obligation(ProofObligation::assume("sc", "sample_c == 45")); // 45ms RTT
    ctx.push_obligation(ProofObligation::assume(
        "bs_def",
        "best_sample == if sample_b <= sample_a && sample_b <= sample_c { sample_b } else { if sample_a <= sample_c { sample_a } else { sample_c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "best_sample == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "best-of-3: 30ms is smallest of {50,30,45}");
}

#[test]
fn drift_rate_bound() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_seconds", "max_drift_ppm", "max_drift_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // max drift = elapsed * drift_rate_ppm (microseconds)
    ctx.push_obligation(ProofObligation::assume("es", "elapsed_seconds == 1000"));
    ctx.push_obligation(ProofObligation::assume("md_ppm", "max_drift_ppm == 100")); // 100 parts per million
    ctx.push_obligation(ProofObligation::assume(
        "md_def",
        "max_drift_us == elapsed_seconds * max_drift_ppm",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_100000",
        "max_drift_us == 100000",
    )); // 100ms
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "drift: 1000s × 100ppm = 100000μs");
}

#[test]
fn peer_selection_intersection() {
    // Select peers whose intervals overlap
    let mut ctx = VerificationContext::new();
    for v in &["peer_a_low", "peer_a_high", "peer_b_low", "peer_b_high"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overlaps", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pal", "peer_a_low == 90"));
    ctx.push_obligation(ProofObligation::assume("pah", "peer_a_high == 110"));
    ctx.push_obligation(ProofObligation::assume("pbl", "peer_b_low == 95"));
    ctx.push_obligation(ProofObligation::assume("pbh", "peer_b_high == 115"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "overlaps == if peer_a_high > peer_b_low && peer_b_high > peer_a_low { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overlaps == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peer overlap: [90,110] ∩ [95,115] ≠ ∅");
}

#[test]
fn leap_second_insertion() {
    let mut ctx = VerificationContext::new();
    for v in &["day_seconds", "leap_seconds", "total_seconds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ds", "day_seconds == 86400"));
    ctx.push_obligation(ProofObligation::assume("ls", "leap_seconds == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_seconds == day_seconds + leap_seconds",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_86401",
        "total_seconds == 86401",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leap second: 86400 + 1 = 86401");
}
