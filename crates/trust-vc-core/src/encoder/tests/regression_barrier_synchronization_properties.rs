// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn all_threads_must_arrive() {
    let mut ctx = VerificationContext::new();
    for v in &["expected_threads", "arrived", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("et", "expected_threads == 8"));
    ctx.push_obligation(ProofObligation::assume("a", "arrived == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == expected_threads - arrived",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "remaining == 3"));
    ctx.push_obligation(ProofObligation::assert("not_done", "remaining > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrier: 8 expected, 5 arrived, 3 remaining");
}

#[test]
fn barrier_releases_when_full() {
    let mut ctx = VerificationContext::new();
    for v in &["expected_threads", "arrived"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("released", i32_ty());
    ctx.push_obligation(ProofObligation::assume("et", "expected_threads == 4"));
    ctx.push_obligation(ProofObligation::assume("a", "arrived == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "rel_def",
        "released == if arrived >= expected_threads { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "released == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrier: 4/4 arrived → released");
}

#[test]
fn generation_increments_on_release() {
    let mut ctx = VerificationContext::new();
    for v in &["old_generation", "new_generation"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("og", "old_generation == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ng_def",
        "new_generation == old_generation + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "new_generation == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "monotonic",
        "new_generation > old_generation",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrier generation: 5 → 6");
}

#[test]
fn reusable_barrier_resets_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count_before_reset", "count_after_reset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cbr", "count_before_reset == 8")); // was full
    ctx.push_obligation(ProofObligation::assume("car", "count_after_reset == 0")); // reset to 0
    ctx.push_obligation(ProofObligation::assert("is_0", "count_after_reset == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "reset",
        "count_after_reset < count_before_reset",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrier reset: 8 → 0");
}

#[test]
fn sense_reversal_barrier() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("old_sense", u32_ty());
    ctx.declare_var_typed("new_sense", u32_ty());
    // Sense flips between 0 and 1
    ctx.push_obligation(ProofObligation::assume("os", "old_sense == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_sense == 1 - old_sense",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "new_sense == 1"));
    ctx.push_obligation(ProofObligation::assert("flipped", "new_sense != old_sense"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sense reversal: 0 → 1");
}

#[test]
fn tree_barrier_fan_in() {
    let mut ctx = VerificationContext::new();
    for v in &["fan_in", "children_arrived", "node_complete"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ready", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fi", "fan_in == 2")); // binary tree
    ctx.push_obligation(ProofObligation::assume("ca", "children_arrived == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "ready == if children_arrived >= fan_in { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ready == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tree barrier: 2/2 children → node ready");
}

#[test]
fn tree_barrier_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["num_threads", "fan_in", "tree_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // depth = ceil(log_fan_in(num_threads))
    // For fan_in=2, num_threads=8: depth=3 (hardcoded)
    ctx.push_obligation(ProofObligation::assume("nt", "num_threads == 8"));
    ctx.push_obligation(ProofObligation::assume("fi", "fan_in == 2"));
    ctx.push_obligation(ProofObligation::assume("td", "tree_depth == 3")); // log2(8) = 3
    ctx.push_obligation(ProofObligation::assert("is_3", "tree_depth == 3"));
    ctx.push_obligation(ProofObligation::assert("small", "tree_depth < num_threads"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tree barrier depth: log2(8) = 3");
}

#[test]
fn dissemination_barrier_rounds() {
    let mut ctx = VerificationContext::new();
    for v in &["num_threads", "rounds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // rounds = ceil(log2(n))
    ctx.push_obligation(ProofObligation::assume("nt", "num_threads == 16"));
    ctx.push_obligation(ProofObligation::assume("r", "rounds == 4")); // log2(16) = 4
    ctx.push_obligation(ProofObligation::assert("is_4", "rounds == 4"));
    ctx.push_obligation(ProofObligation::assert("log_scale", "rounds < num_threads"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dissemination: log2(16) = 4 rounds");
}

#[test]
fn timeout_barrier_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["waited_ms", "timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timed_out", i32_ty());
    ctx.push_obligation(ProofObligation::assume("w", "waited_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume("t", "timeout_ms == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timed_out == if waited_ms >= timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timed_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrier timeout: 5000 >= 3000 → timed out");
}

#[test]
fn phased_barrier_phase_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["current_phase", "total_phases", "next_phase"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cp", "current_phase == 2"));
    ctx.push_obligation(ProofObligation::assume("tp", "total_phases == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "next_phase == (current_phase + 1) % total_phases",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "next_phase == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "phased barrier: phase 2 → 3 (of 5)");
}
