// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fanout_per_round() {
    let mut ctx = VerificationContext::new();
    for v in &["cluster_size", "fanout"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cs", "cluster_size == 100"));
    ctx.push_obligation(ProofObligation::assume("f", "fanout == 3")); // each node tells 3 others
    ctx.push_obligation(ProofObligation::assert("bounded", "fanout < cluster_size"));
    ctx.push_obligation(ProofObligation::assert("positive", "fanout > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gossip fanout: 3 < 100 cluster size");
}

#[test]
fn infected_after_one_round() {
    let mut ctx = VerificationContext::new();
    for v in &["initial_infected", "fanout", "infected_after_round"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Simplified: each infected node infects fanout new nodes (no overlap)
    ctx.push_obligation(ProofObligation::assume("ii", "initial_infected == 1"));
    ctx.push_obligation(ProofObligation::assume("f", "fanout == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "iar_def",
        "infected_after_round == initial_infected + initial_infected * fanout",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "infected_after_round == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gossip: 1 + 1*3 = 4 infected after round 1");
}

#[test]
fn convergence_rounds_log_n() {
    // O(log(n)) rounds to infect all nodes
    // Simplified: for n=1000, log2(1000) ≈ 10
    let mut ctx = VerificationContext::new();
    for v in &["cluster_size", "approx_rounds"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cs", "cluster_size == 1000"));
    ctx.push_obligation(ProofObligation::assume("ar", "approx_rounds == 10")); // ~log2(1000)
    ctx.push_obligation(ProofObligation::assert("is_10", "approx_rounds == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "small",
        "approx_rounds < cluster_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gossip convergence: ~10 rounds for 1000 nodes");
}

#[test]
fn message_count_per_round() {
    let mut ctx = VerificationContext::new();
    for v in &["infected_nodes", "fanout", "messages_sent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("in_val", "infected_nodes == 50"));
    ctx.push_obligation(ProofObligation::assume("f", "fanout == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "messages_sent == infected_nodes * fanout",
    ));
    ctx.push_obligation(ProofObligation::assert("is_150", "messages_sent == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gossip messages: 50 × 3 = 150 per round");
}

#[test]
fn push_vs_pull_gossip() {
    // Push: sender initiates. Pull: receiver requests.
    // Push-pull: both directions.
    let mut ctx = VerificationContext::new();
    for v in &["push_messages", "pull_messages", "push_pull_messages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pm", "push_messages == 100"));
    ctx.push_obligation(ProofObligation::assume("plm", "pull_messages == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ppm_def",
        "push_pull_messages == push_messages + pull_messages",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_200",
        "push_pull_messages == 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "more",
        "push_pull_messages > push_messages",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "push-pull: 100 + 100 = 200 messages (2× push)");
}

#[test]
fn version_vector_update() {
    let mut ctx = VerificationContext::new();
    for v in &["local_version", "received_version", "merged_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Take max of local and received
    ctx.push_obligation(ProofObligation::assume("lv", "local_version == 5"));
    ctx.push_obligation(ProofObligation::assume("rv", "received_version == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "mv_def",
        "merged_version == if local_version > received_version { local_version } else { received_version }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "merged_version == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gossip merge: max(5, 8) = 8");
}

#[test]
fn suspicion_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["missed_heartbeats", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("suspected_failed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mh", "missed_heartbeats == 5"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "suspected_failed == if missed_heartbeats >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "suspected_failed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suspicion: 5 >= 3 threshold → suspected");
}

#[test]
fn bandwidth_per_node() {
    let mut ctx = VerificationContext::new();
    for v in &["fanout", "message_size", "bandwidth_per_round"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "fanout == 3"));
    ctx.push_obligation(ProofObligation::assume("ms", "message_size == 500")); // bytes
    ctx.push_obligation(ProofObligation::assume(
        "bpr_def",
        "bandwidth_per_round == fanout * message_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1500",
        "bandwidth_per_round == 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bandwidth: 3 × 500 = 1500 bytes/round");
}

#[test]
fn crdt_merge_idempotent() {
    // Merging the same state twice yields the same result
    let mut ctx = VerificationContext::new();
    for v in &["state_a", "merged_once", "merged_twice"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // G-Counter: merge = max
    ctx.push_obligation(ProofObligation::assume("sa", "state_a == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "merged_once == if state_a > state_a { state_a } else { state_a }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "merged_twice == if merged_once > state_a { merged_once } else { state_a }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "idempotent",
        "merged_twice == merged_once",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CRDT merge idempotent: max(max(10,10),10) = 10");
}

#[test]
fn protocol_period_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["gossip_interval_ms", "rounds_per_minute"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("gi", "gossip_interval_ms == 1000")); // 1 second
    ctx.push_obligation(ProofObligation::assume(
        "rpm_def",
        "rounds_per_minute == 60000 / gossip_interval_ms",
    ));
    ctx.push_obligation(ProofObligation::assert("is_60", "rounds_per_minute == 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gossip: 60000/1000 = 60 rounds/minute");
}
