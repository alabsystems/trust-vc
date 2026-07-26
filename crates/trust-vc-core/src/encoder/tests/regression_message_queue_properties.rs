// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn enqueue_increases_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "new_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "depth == 10"));
    ctx.push_obligation(ProofObligation::assume("nd_def", "new_depth == depth + 1"));
    ctx.push_obligation(ProofObligation::assert("is_11", "new_depth == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "enqueue: depth 10 → 11");
}

#[test]
fn dequeue_decreases_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "new_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "depth == 10"));
    ctx.push_obligation(ProofObligation::assume("nd_def", "new_depth == depth - 1"));
    ctx.push_obligation(ProofObligation::assert("is_9", "new_depth == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dequeue: depth 10 → 9");
}

#[test]
fn dead_letter_queue_on_failure() {
    let mut ctx = VerificationContext::new();
    for v in &["retry_count", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("to_dlq", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "retry_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "td_def",
        "to_dlq == if retry_count >= max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dlq", "to_dlq == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 retries >= max 3 → dead letter queue");
}

#[test]
fn message_acknowledgment() {
    let mut ctx = VerificationContext::new();
    for v in &["in_flight", "acked", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("if_val", "in_flight == 20"));
    ctx.push_obligation(ProofObligation::assume("a", "acked == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == in_flight - acked",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "remaining == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ack: 20 in-flight - 5 acked = 15 remaining");
}

#[test]
fn partition_assignment() {
    let mut ctx = VerificationContext::new();
    for v in &["num_partitions", "num_consumers", "partitions_per_consumer"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("np", "num_partitions == 12"));
    ctx.push_obligation(ProofObligation::assume("nc", "num_consumers == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ppc_def",
        "partitions_per_consumer == num_partitions / num_consumers",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4",
        "partitions_per_consumer == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "12 partitions / 3 consumers = 4 each");
}

#[test]
fn offset_commit_advances() {
    let mut ctx = VerificationContext::new();
    for v in &["old_offset", "messages_processed", "new_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oo", "old_offset == 1000"));
    ctx.push_obligation(ProofObligation::assume("mp", "messages_processed == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "new_offset == old_offset + messages_processed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1050", "new_offset == 1050"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "offset: 1000 + 50 processed = 1050");
}

#[test]
fn backpressure_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["queue_depth", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("apply_backpressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume("qd", "queue_depth == 10000"));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ab_def",
        "apply_backpressure == if queue_depth > threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure",
        "apply_backpressure == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "depth 10000 > threshold 5000 → backpressure");
}

#[test]
fn message_ttl_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["enqueue_time", "ttl", "current_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("et", "enqueue_time == 100"));
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 60"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if current_time > enqueue_time + ttl { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_expired", "expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time 200 > enqueue 100 + TTL 60 → expired");
}

#[test]
fn consumer_lag() {
    let mut ctx = VerificationContext::new();
    for v in &["latest_offset", "consumer_offset", "lag"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo", "latest_offset == 5000"));
    ctx.push_obligation(ProofObligation::assume("co", "consumer_offset == 4800"));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "lag == latest_offset - consumer_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "lag == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "consumer lag: 5000 - 4800 = 200 messages");
}

#[test]
fn batch_publish_size() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_count", "msg_size", "batch_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mc", "msg_count == 100"));
    ctx.push_obligation(ProofObligation::assume("ms", "msg_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "bb_def",
        "batch_bytes == msg_count * msg_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_25600", "batch_bytes == 25600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "batch: 100 msgs * 256 bytes = 25600");
}
