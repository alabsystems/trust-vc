// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bounded_buffer_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["capacity", "items", "space"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 64"));
    ctx.push_obligation(ProofObligation::assume("i", "items == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "space == capacity - items",
    ));
    ctx.push_obligation(ProofObligation::assert("is_24", "space == 24"));
    ctx.push_obligation(ProofObligation::assert("not_full", "items < capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "buffer: 64-40=24 space remaining");
}

#[test]
fn produce_increments_count() {
    let mut ctx = VerificationContext::new();
    for v in &["old_count", "new_count", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_count == 10"));
    ctx.push_obligation(ProofObligation::assume("cap", "capacity == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == old_count + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_11", "new_count == 11"));
    ctx.push_obligation(ProofObligation::assert(
        "within_cap",
        "new_count <= capacity",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "produce: 10 → 11, within 64");
}

#[test]
fn consume_decrements_count() {
    let mut ctx = VerificationContext::new();
    for v in &["old_count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_count == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == old_count - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_29", "new_count == 29"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "new_count < old_count",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "consume: 30 → 29");
}

#[test]
fn full_buffer_blocks_producer() {
    let mut ctx = VerificationContext::new();
    for v in &["items", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blocked", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "items == 64"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "blocked == if items >= capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blocked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "producer blocked: 64/64 full");
}

#[test]
fn empty_buffer_blocks_consumer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("items", u32_ty());
    ctx.declare_var_typed("blocked", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "items == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "blocked == if items == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blocked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "consumer blocked: buffer empty");
}

#[test]
fn circular_buffer_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["write_pos", "capacity", "next_write"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wp", "write_pos == 63"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "nw_def",
        "next_write == (write_pos + 1) % capacity",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_write == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "circular: pos 63 → 0 (mod 64)");
}

#[test]
fn multi_producer_total() {
    let mut ctx = VerificationContext::new();
    for v in &["producer_a", "producer_b", "total_produced"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pa", "producer_a == 15"));
    ctx.push_obligation(ProofObligation::assume("pb", "producer_b == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_produced == producer_a + producer_b",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "total_produced == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multi-producer: 15+25=40 total");
}

#[test]
fn backpressure_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["items", "capacity", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("backpressure", i32_ty());
    // Backpressure when buffer > 80% full
    ctx.push_obligation(ProofObligation::assume("i", "items == 55"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 64"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 51")); // 64 * 80% ≈ 51
    ctx.push_obligation(ProofObligation::assume(
        "bp_def",
        "backpressure == if items > threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "backpressure == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backpressure: 55 > 51 (80% of 64)");
}

#[test]
fn batch_produce() {
    let mut ctx = VerificationContext::new();
    for v in &["old_count", "batch_size", "new_count", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oc", "old_count == 20"));
    ctx.push_obligation(ProofObligation::assume("bs", "batch_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == old_count + batch_size",
    ));
    ctx.push_obligation(ProofObligation::assume("cap", "capacity == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if new_count <= capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "new_count == 30"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch: 20+10=30, fits in 64");
}

#[test]
fn fairness_round_robin() {
    let mut ctx = VerificationContext::new();
    for v in &["num_consumers", "current_consumer", "next_consumer"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nc", "num_consumers == 4"));
    ctx.push_obligation(ProofObligation::assume("cc", "current_consumer == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_consumer == (current_consumer + 1) % num_consumers",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_consumer == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "round-robin: consumer 3 → 0 (mod 4)");
}
