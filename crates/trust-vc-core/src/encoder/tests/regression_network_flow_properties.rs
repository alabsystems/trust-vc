// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_conservation() {
    // Flow in == flow out for non-source/sink nodes
    let mut ctx = VerificationContext::new();
    for v in &["flow_in1", "flow_in2", "flow_out1", "flow_out2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fi1", "flow_in1 == 10"));
    ctx.push_obligation(ProofObligation::assume("fi2", "flow_in2 == 5"));
    ctx.push_obligation(ProofObligation::assume("fo1", "flow_out1 == 8"));
    ctx.push_obligation(ProofObligation::assume("fo2", "flow_out2 == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "conserved",
        "flow_in1 + flow_in2 == flow_out1 + flow_out2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow conservation: 10+5 = 8+7 = 15");
}

#[test]
fn capacity_constraint() {
    let mut ctx = VerificationContext::new();
    for v in &["flow", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "flow == 7"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assert("within", "flow <= capacity"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow 7 <= capacity 10");
}

#[test]
fn residual_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["capacity", "flow", "residual"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume("f", "flow == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "residual == capacity - flow",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "residual == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residual: 10 - 7 = 3");
}

#[test]
fn augmenting_path_increases_flow() {
    let mut ctx = VerificationContext::new();
    for v in &["old_flow", "bottleneck", "new_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("of", "old_flow == 15"));
    ctx.push_obligation(ProofObligation::assume("b", "bottleneck == 3")); // min residual on path
    ctx.push_obligation(ProofObligation::assume(
        "nf_def",
        "new_flow == old_flow + bottleneck",
    ));
    ctx.push_obligation(ProofObligation::assert("increases", "new_flow > old_flow"));
    ctx.push_obligation(ProofObligation::assert("is_18", "new_flow == 18"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "augment: 15 + bottleneck 3 = 18");
}

#[test]
fn max_flow_min_cut() {
    // max flow value == min cut capacity
    let mut ctx = VerificationContext::new();
    for v in &["max_flow", "min_cut"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mf", "max_flow == 23"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cut == 23"));
    ctx.push_obligation(ProofObligation::assert("equal", "max_flow == min_cut"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max-flow min-cut: both 23");
}

#[test]
fn source_outflow_equals_total() {
    let mut ctx = VerificationContext::new();
    for v in &["source_out1", "source_out2", "source_out3", "total_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("so1", "source_out1 == 5"));
    ctx.push_obligation(ProofObligation::assume("so2", "source_out2 == 8"));
    ctx.push_obligation(ProofObligation::assume("so3", "source_out3 == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "tf_def",
        "total_flow == source_out1 + source_out2 + source_out3",
    ));
    ctx.push_obligation(ProofObligation::assert("is_23", "total_flow == 23"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source total: 5+8+10 = 23");
}

#[test]
fn sink_inflow_equals_total() {
    let mut ctx = VerificationContext::new();
    for v in &["sink_in1", "sink_in2", "total_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("si1", "sink_in1 == 12"));
    ctx.push_obligation(ProofObligation::assume("si2", "sink_in2 == 11"));
    ctx.push_obligation(ProofObligation::assume(
        "tf_def",
        "total_flow == sink_in1 + sink_in2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_23", "total_flow == 23"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sink total: 12+11 = 23");
}

#[test]
fn multi_commodity_separate_capacities() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_a", "flow_b", "shared_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fa", "flow_a == 4"));
    ctx.push_obligation(ProofObligation::assume("fb", "flow_b == 6"));
    ctx.push_obligation(ProofObligation::assume("sc", "shared_capacity == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "fits",
        "flow_a + flow_b <= shared_capacity",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multi-commodity: 4+6 = 10 <= capacity 10");
}

#[test]
fn edge_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &["flow", "capacity", "utilization_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "flow == 7"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "u_def",
        "utilization_pct == flow * 100 / capacity",
    ));
    ctx.push_obligation(ProofObligation::assert("is_70", "utilization_pct == 70"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "utilization: 7/10 * 100 = 70%");
}

#[test]
fn shortest_augmenting_path_bound() {
    // Edmonds-Karp: at most V*E/2 augmentations
    let mut ctx = VerificationContext::new();
    for v in &[
        "vertices",
        "edges",
        "max_augmentations",
        "actual_augmentations",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "vertices == 6"));
    ctx.push_obligation(ProofObligation::assume("e", "edges == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ma_def",
        "max_augmentations == vertices * edges / 2",
    ));
    ctx.push_obligation(ProofObligation::assume("aa", "actual_augmentations == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "actual_augmentations <= max_augmentations",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Edmonds-Karp: 8 augmentations <= 6*10/2 = 30");
}
