// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ring_position_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["hash_value", "ring_size", "position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hv", "hash_value == 12345"));
    ctx.push_obligation(ProofObligation::assume("rs", "ring_size == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "position == hash_value % ring_size",
    ));
    ctx.push_obligation(ProofObligation::assert("bounded", "position < ring_size"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ring position: 12345 % 1000 < 1000");
}

#[test]
fn virtual_nodes_per_physical() {
    let mut ctx = VerificationContext::new();
    for v in &["physical_nodes", "vnodes_per_node", "total_vnodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pn", "physical_nodes == 5"));
    ctx.push_obligation(ProofObligation::assume("vpn", "vnodes_per_node == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "tv_def",
        "total_vnodes == physical_nodes * vnodes_per_node",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "total_vnodes == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "vnodes: 5 × 100 = 500 total");
}

#[test]
fn add_node_redistributes_keys() {
    let mut ctx = VerificationContext::new();
    for v in &["total_keys", "nodes_before", "nodes_after", "keys_moved"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tk", "total_keys == 10000"));
    ctx.push_obligation(ProofObligation::assume("nb", "nodes_before == 4"));
    ctx.push_obligation(ProofObligation::assume("na", "nodes_after == 5"));
    // Ideal: move only 1/nodes_after of keys
    ctx.push_obligation(ProofObligation::assume(
        "km_def",
        "keys_moved == total_keys / nodes_after",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2000", "keys_moved == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "add node: move 10000/5 = 2000 keys");
}

#[test]
fn remove_node_redistributes_keys() {
    let mut ctx = VerificationContext::new();
    for v in &["node_keys", "remaining_nodes", "keys_per_recipient"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nk", "node_keys == 2500"));
    ctx.push_obligation(ProofObligation::assume("rn", "remaining_nodes == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "kpr_def",
        "keys_per_recipient == node_keys / remaining_nodes",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_625",
        "keys_per_recipient == 625",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "remove: 2500 keys / 4 remaining = 625 each");
}

#[test]
fn load_balance_variance() {
    let mut ctx = VerificationContext::new();
    for v in &["node_a_keys", "node_b_keys", "average", "max_deviation"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("balanced", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nak", "node_a_keys == 2100"));
    ctx.push_obligation(ProofObligation::assume("nbk", "node_b_keys == 1900"));
    ctx.push_obligation(ProofObligation::assume("avg", "average == 2000"));
    ctx.push_obligation(ProofObligation::assume("md", "max_deviation == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "balanced == if node_a_keys - average <= max_deviation && average - node_b_keys <= max_deviation { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "balanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "balance: 2100-2000=100, 2000-1900=100 <= 200 max");
}

#[test]
fn replication_factor_copies() {
    let mut ctx = VerificationContext::new();
    for v in &["replication_factor", "nodes", "copies_per_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rf", "replication_factor == 3"));
    ctx.push_obligation(ProofObligation::assume("n", "nodes == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "cpk_def",
        "copies_per_key == replication_factor",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "copies_per_key == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "copies_per_key <= nodes",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "replication: 3 copies <= 5 nodes");
}

#[test]
fn token_range_coverage() {
    let mut ctx = VerificationContext::new();
    for v in &["range_start", "range_end", "range_size", "total_range"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rs", "range_start == 1000"));
    ctx.push_obligation(ProofObligation::assume("re", "range_end == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "rsz_def",
        "range_size == range_end - range_start",
    ));
    ctx.push_obligation(ProofObligation::assume("tr", "total_range == 10000"));
    ctx.push_obligation(ProofObligation::assert("is_1000", "range_size == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "within",
        "range_size <= total_range",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "token range: 2000-1000 = 1000 of 10000 total");
}

#[test]
fn successor_node_lookup() {
    let mut ctx = VerificationContext::new();
    for v in &["key_position", "node_a_pos", "node_b_pos", "successor_pos"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("kp", "key_position == 50"));
    ctx.push_obligation(ProofObligation::assume("nap", "node_a_pos == 30")); // behind key
    ctx.push_obligation(ProofObligation::assume("nbp", "node_b_pos == 70")); // ahead of key
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "successor_pos == if node_b_pos > key_position { node_b_pos } else { node_a_pos }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_70", "successor_pos == 70"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "successor: key at 50, next node at 70");
}

#[test]
fn weight_based_distribution() {
    let mut ctx = VerificationContext::new();
    for v in &["node_weight", "total_weight", "expected_share_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nw", "node_weight == 3"));
    ctx.push_obligation(ProofObligation::assume("tw", "total_weight == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "esp_def",
        "expected_share_pct == node_weight * 100 / total_weight",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "expected_share_pct == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "weight: 3/10 * 100 = 30%");
}

#[test]
fn handoff_on_failure() {
    let mut ctx = VerificationContext::new();
    for v in &["primary_node", "backup_node", "hints_stored"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pn", "primary_node == 3")); // failed
    ctx.push_obligation(ProofObligation::assume("bn", "backup_node == 4")); // next in ring
    ctx.push_obligation(ProofObligation::assume("hs", "hints_stored == 100")); // hinted handoffs
    ctx.push_obligation(ProofObligation::assert(
        "different",
        "primary_node != backup_node",
    ));
    ctx.push_obligation(ProofObligation::assert("has_hints", "hints_stored > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "handoff: node 3→4, 100 hints stored");
}
