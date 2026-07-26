// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn majority_quorum_size() {
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "quorum_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "qs_def",
        "quorum_size == total_nodes / 2 + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "quorum_size == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "majority: 5/2 + 1 = 3");
}

#[test]
fn two_quorums_overlap() {
    // Any two majority quorums must share at least one member
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "quorum_a", "quorum_b", "min_overlap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("qa", "quorum_a == 3"));
    ctx.push_obligation(ProofObligation::assume("qb", "quorum_b == 3"));
    // By pigeonhole: overlap >= qa + qb - total
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "min_overlap == quorum_a + quorum_b - total_nodes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "min_overlap == 1"));
    ctx.push_obligation(ProofObligation::assert("positive", "min_overlap > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "quorum overlap: 3 + 3 - 5 = 1 (at least 1 shared)");
}

#[test]
fn fault_tolerance_from_quorum() {
    // Can tolerate f failures if quorum_size + f <= total_nodes
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "quorum_size", "max_failures"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 7"));
    ctx.push_obligation(ProofObligation::assume("qs", "quorum_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "mf_def",
        "max_failures == total_nodes - quorum_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "max_failures == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fault tolerance: 7 - 4 = 3 failures tolerated");
}

#[test]
fn read_write_quorum_intersection() {
    // R + W > N ensures any read quorum intersects any write quorum
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "read_quorum", "write_quorum", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("intersects", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("rq", "read_quorum == 3"));
    ctx.push_obligation(ProofObligation::assume("wq", "write_quorum == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sum == read_quorum + write_quorum",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "i_def",
        "intersects == if sum > total_nodes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "sum == 6"));
    ctx.push_obligation(ProofObligation::assert("yes", "intersects == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "R+W=6 > N=5 → quorums intersect");
}

#[test]
fn sloppy_quorum_preference_list() {
    let mut ctx = VerificationContext::new();
    for v in &["replication_factor", "preference_list_size", "extra_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rf", "replication_factor == 3"));
    ctx.push_obligation(ProofObligation::assume("pls", "preference_list_size == 5")); // larger for sloppy quorum
    ctx.push_obligation(ProofObligation::assume(
        "en_def",
        "extra_nodes == preference_list_size - replication_factor",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "extra_nodes == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "larger",
        "preference_list_size > replication_factor",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sloppy: pref list 5 > RF 3, 2 extra nodes");
}

#[test]
fn byzantine_fault_tolerance() {
    // BFT requires 3f + 1 nodes to tolerate f Byzantine faults
    let mut ctx = VerificationContext::new();
    for v in &["byzantine_faults", "min_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bf", "byzantine_faults == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mn_def",
        "min_nodes == 3 * byzantine_faults + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "min_nodes == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "BFT: 3*1 + 1 = 4 nodes for 1 Byzantine fault");
}

#[test]
fn weighted_quorum_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "weight_a",
        "weight_b",
        "weight_c",
        "total_weight",
        "threshold",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("met", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wa", "weight_a == 3"));
    ctx.push_obligation(ProofObligation::assume("wb", "weight_b == 2"));
    ctx.push_obligation(ProofObligation::assume("wc", "weight_c == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_weight == weight_a + weight_b + weight_c",
    ));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 4")); // need weight >= 4
                                                                          // Quorum with A + B: weight = 5 >= 4
    ctx.push_obligation(ProofObligation::assume(
        "met_def",
        "met == if weight_a + weight_b >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tw_6", "total_weight == 6"));
    ctx.push_obligation(ProofObligation::assert("ok", "met == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weighted quorum: A(3)+B(2)=5 >= threshold 4");
}

#[test]
fn epoch_number_monotonic() {
    let mut ctx = VerificationContext::new();
    for v in &["old_epoch", "new_epoch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oe", "old_epoch == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ne_def",
        "new_epoch == old_epoch + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_43", "new_epoch == 43"));
    ctx.push_obligation(ProofObligation::assert("greater", "new_epoch > old_epoch"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "epoch: 42 → 43 (monotonically increasing)");
}

#[test]
fn commit_requires_quorum() {
    let mut ctx = VerificationContext::new();
    for v in &["total_nodes", "quorum_size", "acks_received"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("committed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tn", "total_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("qs", "quorum_size == 3"));
    ctx.push_obligation(ProofObligation::assume("ar", "acks_received == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "committed == if acks_received >= quorum_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "committed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "commit: 3 acks >= quorum 3 → committed");
}

#[test]
fn flexible_quorum_tradeoff() {
    // R=1, W=N for fast reads; R=N, W=1 for fast writes
    // Must satisfy R + W > N
    let mut ctx = VerificationContext::new();
    for v in &["n", "r", "w", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nv", "n == 5"));
    ctx.push_obligation(ProofObligation::assume("rv", "r == 1")); // fast reads
    ctx.push_obligation(ProofObligation::assume("wv", "w == 5")); // write to all
    ctx.push_obligation(ProofObligation::assume("s_def", "sum == r + w"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sum > n { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "sum == 6"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flexible: R=1, W=5, R+W=6 > N=5");
}
