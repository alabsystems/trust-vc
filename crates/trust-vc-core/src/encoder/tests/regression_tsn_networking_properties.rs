// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "min_cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // TSN cycle time: typically 31.25μs to 4ms
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycle_us == 31"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycle_us == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_us >= min_cycle_us && cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 500μs cycle in [31, 4000] → OK");
}

#[test]
fn guard_band() {
    let mut ctx = VerificationContext::new();
    for v in &["guard_ns", "min_guard_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("guard_ok", i32_ty());
    // Guard band between scheduled and best-effort traffic
    ctx.push_obligation(ProofObligation::assume("gn", "guard_ns == 2000"));
    ctx.push_obligation(ProofObligation::assume("mg", "min_guard_ns == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "guard_ok == if guard_ns >= min_guard_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "guard_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 2000ns guard band ≥ 1000ns min → OK");
}

#[test]
fn gcl_entries() {
    let mut ctx = VerificationContext::new();
    for v in &["entries", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gcl_ok", i32_ty());
    // Gate Control List entries per cycle
    ctx.push_obligation(ProofObligation::assume("e", "entries == 8"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gcl_ok == if entries <= max_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gcl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 8 GCL entries ≤ 256 max → OK");
}

#[test]
fn time_aware_shaper() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tas_enabled", u32_ty());
    ctx.declare_var_typed("has_tas", i32_ty());
    // 802.1Qbv Time-Aware Shaper: enabled/disabled
    ctx.push_obligation(ProofObligation::assume("te", "tas_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ht_def",
        "has_tas == if tas_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_tas == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: TAS enabled → time-aware shaping active");
}

#[test]
fn frame_preemption() {
    let mut ctx = VerificationContext::new();
    for v in &["min_frag_bytes", "required_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("preempt_ok", i32_ty());
    // 802.1Qbu frame preemption: min fragment 64 bytes
    ctx.push_obligation(ProofObligation::assume("mf", "min_frag_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume("rm", "required_min == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "preempt_ok == if min_frag_bytes >= required_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "preempt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 64-byte min fragment ≥ 64 required → OK");
}

#[test]
fn ptp_sync_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_ns", "max_accuracy_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ptp_ok", i32_ty());
    // IEEE 1588 PTP synchronization accuracy
    ctx.push_obligation(ProofObligation::assume("an", "accuracy_ns == 100"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_ns == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ptp_ok == if accuracy_ns <= max_accuracy_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ptp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 100ns PTP accuracy ≤ 1000ns max → OK");
}

#[test]
fn stream_reservation() {
    let mut ctx = VerificationContext::new();
    for v in &["streams", "max_streams"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stream_ok", i32_ty());
    // 802.1Qat stream reservations
    ctx.push_obligation(ProofObligation::assume("s", "streams == 50"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_streams == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stream_ok == if streams <= max_streams { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stream_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 50 stream reservations ≤ 1000 max → OK");
}

#[test]
fn vlan_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["priority", "max_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pri_ok", i32_ty());
    // 802.1Q VLAN priority: 0-7 (3 bits)
    ctx.push_obligation(ProofObligation::assume("p", "priority == 6"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_priority == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pri_ok == if priority <= max_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pri_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: VLAN priority 6 ≤ 7 → valid 3-bit");
}

#[test]
fn max_latency() {
    let mut ctx = VerificationContext::new();
    for v in &["latency_us", "max_latency_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lat_ok", i32_ty());
    // End-to-end latency guarantee
    ctx.push_obligation(ProofObligation::assume("lu", "latency_us == 100"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_latency_us == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lat_ok == if latency_us <= max_latency_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 100μs latency ≤ 1000μs max → OK");
}

#[test]
fn best_effort_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["be_pct", "min_be_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("be_ok", i32_ty());
    // Bandwidth remaining for best-effort traffic
    ctx.push_obligation(ProofObligation::assume("bp", "be_pct == 30"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_be_pct == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "be_ok == if be_pct >= min_be_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "be_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TSN: 30% best-effort ≥ 10% min → OK");
}
