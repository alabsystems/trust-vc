// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fifo_ordering() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "submit_order_a",
        "submit_order_b",
        "dispatch_order_a",
        "dispatch_order_b",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("soa", "submit_order_a == 1"));
    ctx.push_obligation(ProofObligation::assume("sob", "submit_order_b == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "doa_def",
        "dispatch_order_a == submit_order_a",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "dob_def",
        "dispatch_order_b == submit_order_b",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fifo",
        "dispatch_order_a < dispatch_order_b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIFO: submitted 1,2 → dispatched 1,2");
}

#[test]
fn elevator_seek_direction() {
    let mut ctx = VerificationContext::new();
    for v in &["current_track", "request_track"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("seek_forward", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "current_track == 50"));
    ctx.push_obligation(ProofObligation::assume("rt", "request_track == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "seek_forward == if request_track > current_track { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("forward", "seek_forward == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "elevator: track 80 > 50 → seek forward");
}

#[test]
fn seek_distance_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["head_position", "target", "distance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hp", "head_position == 50"));
    ctx.push_obligation(ProofObligation::assume("t", "target == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "distance == target - head_position",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "distance == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seek distance: 80 - 50 = 30 tracks");
}

#[test]
fn deadline_io_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["deadline_a", "deadline_b", "selected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("da", "deadline_a == 100"));
    ctx.push_obligation(ProofObligation::assume("db", "deadline_b == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "selected == if deadline_b < deadline_a { deadline_b } else { deadline_a }",
    ));
    ctx.push_obligation(ProofObligation::assert("earliest", "selected == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deadline I/O: 50 < 100 → select 50");
}

#[test]
fn queue_depth_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["submitted", "completed", "in_flight"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "submitted == 32"));
    ctx.push_obligation(ProofObligation::assume("c", "completed == 28"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "in_flight == submitted - completed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "in_flight == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "queue depth: 32 - 28 = 4 in flight");
}

#[test]
fn read_write_priority_separation() {
    let mut ctx = VerificationContext::new();
    for v in &["read_prio", "write_prio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("read_first", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rp", "read_prio == 1")); // reads higher priority
    ctx.push_obligation(ProofObligation::assume("wp", "write_prio == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "rf_def",
        "read_first == if read_prio < write_prio { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("reads_win", "read_first == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "read prio 1 < write prio 2 → reads first");
}

#[test]
fn merge_adjacent_requests() {
    let mut ctx = VerificationContext::new();
    for v in &["req1_start", "req1_size", "req2_start", "merged_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_merge", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r1s", "req1_start == 100"));
    ctx.push_obligation(ProofObligation::assume("r1sz", "req1_size == 8"));
    ctx.push_obligation(ProofObligation::assume("r2s", "req2_start == 108")); // adjacent
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "can_merge == if req2_start == req1_start + req1_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "merged_size == req1_size + 8",
    ));
    ctx.push_obligation(ProofObligation::assert("mergeable", "can_merge == 1"));
    ctx.push_obligation(ProofObligation::assert("is_16", "merged_size == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "merge: [100..108) + [108..116) → [100..116)");
}

#[test]
fn bandwidth_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &["bytes_transferred", "time_elapsed", "bandwidth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bt", "bytes_transferred == 1000"));
    ctx.push_obligation(ProofObligation::assume("te", "time_elapsed == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "bw_def",
        "bandwidth == bytes_transferred / time_elapsed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "bandwidth == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bandwidth: 1000B / 10ms = 100 B/ms");
}

#[test]
fn io_latency_components() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "seek_time",
        "rotational_delay",
        "transfer_time",
        "total_latency",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("st", "seek_time == 5"));
    ctx.push_obligation(ProofObligation::assume("rd", "rotational_delay == 4"));
    ctx.push_obligation(ProofObligation::assume("tt", "transfer_time == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_latency == seek_time + rotational_delay + transfer_time",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total_latency == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "latency: 5 + 4 + 1 = 10ms");
}

#[test]
fn iops_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["operations", "time_sec", "iops"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("o", "operations == 5000"));
    ctx.push_obligation(ProofObligation::assume("t", "time_sec == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "i_def",
        "iops == operations / time_sec",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "iops == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IOPS: 5000 / 10 = 500");
}
