// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn local_event_increments_own_clock() {
    let mut ctx = VerificationContext::new();
    for v in &["clock_before", "clock_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "clock_before == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "clock_after == clock_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "clock_after == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "increases",
        "clock_after > clock_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "local event: clock 5 → 6");
}

#[test]
fn send_increments_before_message() {
    let mut ctx = VerificationContext::new();
    for v in &["sender_clock", "message_clock"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sc", "sender_clock == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "mc_def",
        "message_clock == sender_clock + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "message_clock == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "send: increment 3 → 4, attach to message");
}

#[test]
fn receive_takes_max_plus_one() {
    let mut ctx = VerificationContext::new();
    for v in &["local_clock", "message_clock", "merged_clock"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lc", "local_clock == 3"));
    ctx.push_obligation(ProofObligation::assume("mc", "message_clock == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "mc_def",
        "merged_clock == if message_clock > local_clock { message_clock + 1 } else { local_clock + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "merged_clock == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "receive: max(3,7)+1 = 8");
}

#[test]
fn happens_before_transitivity() {
    // If a→b and b→c then a→c (via clock ordering)
    let mut ctx = VerificationContext::new();
    for v in &["clock_a", "clock_b", "clock_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ca", "clock_a == 1"));
    ctx.push_obligation(ProofObligation::assume("cb", "clock_b == 3"));
    ctx.push_obligation(ProofObligation::assume("cc", "clock_c == 5"));
    ctx.push_obligation(ProofObligation::assert("ab", "clock_a < clock_b"));
    ctx.push_obligation(ProofObligation::assert("bc", "clock_b < clock_c"));
    ctx.push_obligation(ProofObligation::assert("ac", "clock_a < clock_c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "happens-before: 1 < 3 < 5 (transitive)");
}

#[test]
fn concurrent_events_incomparable() {
    // Two events on different nodes with no message between them
    let mut ctx = VerificationContext::new();
    for v in &[
        "node_a_clock_a",
        "node_a_clock_b",
        "node_b_clock_a",
        "node_b_clock_b",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Node A's view: (3, 0), Node B's view: (0, 2) — neither dominates
    ctx.push_obligation(ProofObligation::assume("aa", "node_a_clock_a == 3"));
    ctx.push_obligation(ProofObligation::assume("ab", "node_a_clock_b == 0"));
    ctx.push_obligation(ProofObligation::assume("ba", "node_b_clock_a == 0"));
    ctx.push_obligation(ProofObligation::assume("bb", "node_b_clock_b == 2"));
    // A not <= B (because a_a > b_a) and B not <= A (because b_b > a_b)
    ctx.push_obligation(ProofObligation::assert(
        "a_not_before_b",
        "node_a_clock_a > node_b_clock_a",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "b_not_before_a",
        "node_b_clock_b > node_a_clock_b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concurrent: (3,0) || (0,2) — incomparable");
}

#[test]
fn merge_component_wise_max() {
    let mut ctx = VerificationContext::new();
    for v in &["a1", "a2", "b1", "b2", "merged1", "merged2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a1v", "a1 == 3"));
    ctx.push_obligation(ProofObligation::assume("a2v", "a2 == 5"));
    ctx.push_obligation(ProofObligation::assume("b1v", "b1 == 7"));
    ctx.push_obligation(ProofObligation::assume("b2v", "b2 == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "merged1 == if a1 > b1 { a1 } else { b1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "merged2 == if a2 > b2 { a2 } else { b2 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_7_5",
        "merged1 == 7 && merged2 == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "merge: max(3,7)=7, max(5,2)=5");
}

#[test]
fn clock_size_equals_node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["nodes", "clock_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n", "nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("ce_def", "clock_entries == nodes"));
    ctx.push_obligation(ProofObligation::assert("same", "clock_entries == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vector clock: 5 nodes → 5 entries");
}

#[test]
fn causal_delivery_ordering() {
    let mut ctx = VerificationContext::new();
    for v in &["msg1_clock", "msg2_clock"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("deliver_msg1_first", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m1c", "msg1_clock == 3"));
    ctx.push_obligation(ProofObligation::assume("m2c", "msg2_clock == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "deliver_msg1_first == if msg1_clock < msg2_clock { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ordered",
        "deliver_msg1_first == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "causal delivery: msg1(3) before msg2(5)");
}

#[test]
fn version_vector_conflict_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["replica_a_version", "replica_b_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conflict", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rav", "replica_a_version == 5"));
    ctx.push_obligation(ProofObligation::assume("rbv", "replica_b_version == 3"));
    // Conflict if neither dominates the other (simplified: different versions)
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "conflict == if replica_a_version != replica_b_version { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("has_conflict", "conflict == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "version conflict: replica A(5) != B(3)");
}

#[test]
fn dotted_version_vector_unique_event() {
    let mut ctx = VerificationContext::new();
    for v in &["node_id", "counter", "event_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ni", "node_id == 2"));
    ctx.push_obligation(ProofObligation::assume("c", "counter == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ei_def",
        "event_id == node_id * 1000 + counter",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2010", "event_id == 2010"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "dotted VV: node2 counter10 → event 2010");
}
