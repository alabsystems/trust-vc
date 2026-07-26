// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn load_factor_below_threshold() {
    // load_factor = entries / capacity; if entries < 3/4 * capacity → ok
    let mut ctx = VerificationContext::new();
    for v in &["entries", "capacity", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_resize", i32_ty());
    ctx.push_obligation(ProofObligation::assume("e", "entries == 6"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 16"));
    // threshold = capacity * 3 / 4 = 12
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "threshold == capacity * 3 / 4",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nr_def",
        "needs_resize == if entries >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_resize", "needs_resize == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "6/16 < 0.75 → no resize");
}

#[test]
fn resize_doubles_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["old_cap", "new_cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_cap == 16"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_cap == old_cap * 2"));
    ctx.push_obligation(ProofObligation::assert("is_32", "new_cap == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "resize: 16 → 32");
}

#[test]
fn hash_modulo_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["hash", "capacity", "bucket"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hash == 42"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "bucket == hash % capacity",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "bucket < capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "42 % 16 = 10 < 16");
}

#[test]
fn insert_increases_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "count == 5"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_count == count + 1"));
    ctx.push_obligation(ProofObligation::assert("grew", "new_count == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert: count 5 → 6");
}

#[test]
fn remove_decreases_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "count == 5"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_count == count - 1"));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_count == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove: count 5 → 4");
}

#[test]
fn linear_probe_wraps() {
    // probe(hash, i) = (hash + i) % capacity
    let mut ctx = VerificationContext::new();
    for v in &["hash", "step", "capacity", "probe"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hash == 14"));
    ctx.push_obligation(ProofObligation::assume("s", "step == 3"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "probe == (hash + step) % capacity",
    ));
    // (14+3) % 16 = 17 % 16 = 1
    ctx.push_obligation(ProofObligation::assert("is_1", "probe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "probe(14,3,16) = 1");
}

#[test]
fn tombstone_does_not_change_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["capacity_before", "capacity_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "capacity_before == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "capacity_after == capacity_before",
    ));
    ctx.push_obligation(ProofObligation::assert("unchanged", "capacity_after == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tombstone preserves capacity");
}

#[test]
fn robin_hood_displacement() {
    // Robin Hood: new element displaces existing if it has greater probe distance
    let mut ctx = VerificationContext::new();
    for v in &["existing_dist", "new_dist"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_displace", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ed", "existing_dist == 1"));
    ctx.push_obligation(ProofObligation::assume("nd", "new_dist == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "should_displace == if new_dist > existing_dist { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("displace", "should_displace == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Robin Hood: dist 3 > 1 → displace");
}

#[test]
fn power_of_two_capacity() {
    // Capacity must be power of 2 for fast modulo (mask = cap - 1)
    let mut ctx = VerificationContext::new();
    for v in &["capacity", "mask", "hash", "bucket"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 16"));
    ctx.push_obligation(ProofObligation::assume("m_def", "mask == capacity - 1"));
    ctx.push_obligation(ProofObligation::assume("h", "hash == 42"));
    ctx.push_obligation(ProofObligation::assume("b_def", "bucket == hash & mask"));
    // 42 & 15 = 10
    ctx.push_obligation(ProofObligation::assert("is_10", "bucket == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "42 & 15 = 10 (mask-based modulo)");
}

#[test]
fn max_probe_length_bounded() {
    // With load factor < 0.75, expected max probe length is O(log n)
    // For capacity 16 with 8 entries, probe length should be < 16
    let mut ctx = VerificationContext::new();
    for v in &["max_probe", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mp", "max_probe == 4"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 16"));
    ctx.push_obligation(ProofObligation::assert("bounded", "max_probe < capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max probe 4 < capacity 16");
}
