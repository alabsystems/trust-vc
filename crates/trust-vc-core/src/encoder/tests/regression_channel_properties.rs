// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn send_receive_fifo_order() {
    let mut ctx = VerificationContext::new();
    for v in &["sent_first", "sent_second", "recv_first", "recv_second"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sf", "sent_first == 10"));
    ctx.push_obligation(ProofObligation::assume("ss", "sent_second == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "rf_def",
        "recv_first == sent_first",
    )); // FIFO
    ctx.push_obligation(ProofObligation::assume(
        "rs_def",
        "recv_second == sent_second",
    ));
    ctx.push_obligation(ProofObligation::assert("order_1", "recv_first == 10"));
    ctx.push_obligation(ProofObligation::assert("order_2", "recv_second == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIFO channel: send 10,20 → recv 10,20");
}

#[test]
fn bounded_channel_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["items", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "items == 5"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if items < capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("room", "can_send == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 items < 10 capacity → can send");
}

#[test]
fn bounded_channel_full() {
    let mut ctx = VerificationContext::new();
    for v in &["items", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "items == 10"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if items < capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("full", "can_send == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 items == 10 capacity → channel full");
}

#[test]
fn unbounded_channel_never_blocks_sender() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("items", u32_ty());
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "items == 1000000"));
    ctx.push_obligation(ProofObligation::assume("cs_def", "can_send == 1")); // always sendable
    ctx.push_obligation(ProofObligation::assert("always", "can_send == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unbounded channel: always can send");
}

#[test]
fn channel_items_after_send() {
    let mut ctx = VerificationContext::new();
    for v in &["items_before", "items_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ib", "items_before == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "items_after == items_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "items_after == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "send: 3 → 4 items");
}

#[test]
fn channel_items_after_recv() {
    let mut ctx = VerificationContext::new();
    for v in &["items_before", "items_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ib", "items_before == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "items_after == items_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "items_after == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "recv: 5 → 4 items");
}

#[test]
fn channel_empty_after_drain() {
    let mut ctx = VerificationContext::new();
    for v in &["items_before", "recv_count", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ib", "items_before == 7"));
    ctx.push_obligation(ProofObligation::assume("rc", "recv_count == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == items_before - recv_count",
    ));
    ctx.push_obligation(ProofObligation::assert("empty", "remaining == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drain 7 of 7: channel empty");
}

#[test]
fn mpsc_total_messages() {
    // Multiple producers, single consumer
    let mut ctx = VerificationContext::new();
    for v in &["from_p1", "from_p2", "from_p3", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fp1", "from_p1 == 10"));
    ctx.push_obligation(ProofObligation::assume("fp2", "from_p2 == 20"));
    ctx.push_obligation(ProofObligation::assume("fp3", "from_p3 == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == from_p1 + from_p2 + from_p3",
    ));
    ctx.push_obligation(ProofObligation::assert("is_60", "total == 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPSC: 10+20+30 = 60 total messages");
}

#[test]
fn rendezvous_channel_zero_buffer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", u32_ty());
    ctx.declare_var_typed("must_sync", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "must_sync == if capacity == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sync", "must_sync == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rendezvous channel: capacity 0 → must sync");
}

#[test]
fn select_chooses_ready() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch1_ready", i32_ty());
    ctx.declare_var_typed("ch2_ready", i32_ty());
    ctx.declare_var_typed("any_ready", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c1r", "ch1_ready == 0")); // not ready
    ctx.push_obligation(ProofObligation::assume("c2r", "ch2_ready == 1")); // ready
    ctx.push_obligation(ProofObligation::assume(
        "ar_def",
        "any_ready == if ch1_ready == 1 || ch2_ready == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ready", "any_ready == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "select: ch2 ready → at least one ready");
}
