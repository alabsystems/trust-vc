// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pipeline_throughput_one_per_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles", "instructions_completed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "cycles == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "instructions_completed == cycles",
    )); // ideal: 1 IPC
    ctx.push_obligation(ProofObligation::assert(
        "is_100",
        "instructions_completed == 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ideal pipeline: 100 cycles = 100 instructions");
}

#[test]
fn pipeline_stages_latency() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "fetch",
        "decode",
        "execute",
        "memory",
        "writeback",
        "latency",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "fetch == 1"));
    ctx.push_obligation(ProofObligation::assume("d", "decode == 1"));
    ctx.push_obligation(ProofObligation::assume("e", "execute == 1"));
    ctx.push_obligation(ProofObligation::assume("m", "memory == 1"));
    ctx.push_obligation(ProofObligation::assume("w", "writeback == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "latency == fetch + decode + execute + memory + writeback",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "latency == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5-stage pipeline: 1+1+1+1+1 = 5 cycle latency");
}

#[test]
fn data_hazard_stall() {
    let mut ctx = VerificationContext::new();
    for v in &["ideal_cycles", "stall_cycles", "actual_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ic", "ideal_cycles == 100"));
    ctx.push_obligation(ProofObligation::assume("sc", "stall_cycles == 15")); // RAW hazards
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "actual_cycles == ideal_cycles + stall_cycles",
    ));
    ctx.push_obligation(ProofObligation::assert("is_115", "actual_cycles == 115"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data hazard: 100 + 15 stalls = 115 cycles");
}

#[test]
fn branch_misprediction_penalty() {
    let mut ctx = VerificationContext::new();
    for v in &["pipeline_depth", "mispredictions", "total_penalty"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pd", "pipeline_depth == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "mispredictions == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_penalty == pipeline_depth * mispredictions",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "total_penalty == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "branch penalty: 5 × 10 = 50 cycles wasted");
}

#[test]
fn forwarding_eliminates_stall() {
    let mut ctx = VerificationContext::new();
    for v in &["stalls_without_forwarding", "stalls_with_forwarding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "swof",
        "stalls_without_forwarding == 2",
    )); // 2-cycle stall
    ctx.push_obligation(ProofObligation::assume(
        "swf",
        "stalls_with_forwarding == 0",
    )); // forwarding eliminates it
    ctx.push_obligation(ProofObligation::assert(
        "better",
        "stalls_with_forwarding < stalls_without_forwarding",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forwarding: 0 stalls < 2 without");
}

#[test]
fn branch_prediction_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["total_branches", "correct_predictions", "accuracy_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_branches == 1000"));
    ctx.push_obligation(ProofObligation::assume("cp", "correct_predictions == 950"));
    ctx.push_obligation(ProofObligation::assume(
        "ap_def",
        "accuracy_pct == correct_predictions * 100 / total_branches",
    ));
    ctx.push_obligation(ProofObligation::assert("is_95", "accuracy_pct == 95"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "branch prediction: 950/1000 = 95%");
}

#[test]
fn instruction_queue_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["fetched", "dispatched", "in_queue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f", "fetched == 20"));
    ctx.push_obligation(ProofObligation::assume("d", "dispatched == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "iq_def",
        "in_queue == fetched - dispatched",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "in_queue == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "instruction queue: 20-16 = 4 pending");
}

#[test]
fn superscalar_issue_width() {
    let mut ctx = VerificationContext::new();
    for v in &["issue_width", "cycles", "max_instructions"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("iw", "issue_width == 4")); // 4-wide
    ctx.push_obligation(ProofObligation::assume("c", "cycles == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "mi_def",
        "max_instructions == issue_width * cycles",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "max_instructions == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "superscalar: 4-wide × 100 cycles = 400 max");
}

#[test]
fn reorder_buffer_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["rob_entries", "in_flight", "available"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("re", "rob_entries == 128"));
    ctx.push_obligation(ProofObligation::assume("if_val", "in_flight == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "available == rob_entries - in_flight",
    ));
    ctx.push_obligation(ProofObligation::assert("is_28", "available == 28"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ROB: 128 - 100 in flight = 28 available");
}

#[test]
fn cpi_with_stalls() {
    // CPI = base CPI + stall cycles per instruction
    let mut ctx = VerificationContext::new();
    for v in &["base_cpi", "stall_rate_pct", "effective_cpi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Simplified: using integer percentage
    ctx.push_obligation(ProofObligation::assume("bc", "base_cpi == 1"));
    ctx.push_obligation(ProofObligation::assume("sr", "stall_rate_pct == 20")); // 20% stall
    ctx.push_obligation(ProofObligation::assume(
        "ec_def",
        "effective_cpi == base_cpi * 100 + stall_rate_pct",
    ));
    ctx.push_obligation(ProofObligation::assert("is_120", "effective_cpi == 120")); // 1.20 CPI (scaled by 100)
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CPI: 1.00 + 0.20 stalls = 1.20 (scaled)");
}
