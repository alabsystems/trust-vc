// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pipeline_stages_sequential() {
    // Stage 0 → Stage 1 → Stage 2
    let mut ctx = VerificationContext::new();
    for v in &["stage0_out", "stage1_out", "stage2_out"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s0", "stage0_out == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "s1_def",
        "stage1_out == stage0_out + 5",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s2_def",
        "stage2_out == stage1_out + 5",
    ));
    ctx.push_obligation(ProofObligation::assert("final", "stage2_out == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipeline: 10 → 15 → 20");
}

#[test]
fn pipeline_latency() {
    // N stages = N cycle latency
    let mut ctx = VerificationContext::new();
    for v in &["num_stages", "latency"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ns", "num_stages == 5"));
    ctx.push_obligation(ProofObligation::assume("l_def", "latency == num_stages"));
    ctx.push_obligation(ProofObligation::assert("is_5", "latency == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5-stage pipeline = 5 cycle latency");
}

#[test]
fn pipeline_throughput_one_per_cycle() {
    // Steady state: 1 result per cycle regardless of latency
    let mut ctx = VerificationContext::new();
    for v in &["cycles", "results"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "cycles == 100"));
    ctx.push_obligation(ProofObligation::assume("r_def", "results == cycles")); // 1:1
    ctx.push_obligation(ProofObligation::assert("is_100", "results == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 cycles → 100 results in steady state");
}

#[test]
fn pipeline_stall_no_advance() {
    let mut ctx = VerificationContext::new();
    for v in &["stage_val", "next_stage_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stall", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "stage_val == 42"));
    ctx.push_obligation(ProofObligation::assume("st", "stall == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nsv_def",
        "next_stage_val == if stall == 1 { stage_val } else { stage_val + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_change", "next_stage_val == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stall holds stage value");
}

#[test]
fn pipeline_flush_clears() {
    let mut ctx = VerificationContext::new();
    for v in &["stage_val", "flushed_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flush", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "stage_val == 99"));
    ctx.push_obligation(ProofObligation::assume("fl", "flush == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fv_def",
        "flushed_val == if flush == 1 { 0 } else { stage_val }",
    ));
    ctx.push_obligation(ProofObligation::assert("cleared", "flushed_val == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flush clears pipeline stage");
}

#[test]
fn pipeline_forwarding_bypass() {
    // Data forwarding: use result before writeback
    let mut ctx = VerificationContext::new();
    for v in &["alu_result", "forwarded", "reg_file_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("forward_enable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ar", "alu_result == 77"));
    ctx.push_obligation(ProofObligation::assume("rfv", "reg_file_val == 0")); // stale
    ctx.push_obligation(ProofObligation::assume("fe", "forward_enable == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "forwarded == if forward_enable == 1 { alu_result } else { reg_file_val }",
    ));
    ctx.push_obligation(ProofObligation::assert("uses_new", "forwarded == 77"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forwarding bypasses stale register value");
}

#[test]
fn pipeline_bubble_insertion() {
    // Bubble = NOP inserted for hazard resolution
    let mut ctx = VerificationContext::new();
    for v in &["original_count", "bubbles", "total_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "original_count == 50"));
    ctx.push_obligation(ProofObligation::assume("b", "bubbles == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_cycles == original_count + bubbles",
    ));
    ctx.push_obligation(ProofObligation::assert("is_53", "total_cycles == 53"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "50 instructions + 3 bubbles = 53 cycles");
}

#[test]
fn pipeline_branch_penalty() {
    // Mispredicted branch flushes N stages
    let mut ctx = VerificationContext::new();
    for v in &["pipeline_depth", "penalty_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pd", "pipeline_depth == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "penalty_cycles == pipeline_depth - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "penalty_cycles == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5-stage pipeline: branch penalty = 4 cycles");
}

#[test]
fn pipeline_hazard_detection() {
    // RAW hazard: write register matches read register
    let mut ctx = VerificationContext::new();
    for v in &["write_reg", "read_reg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_hazard", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wr", "write_reg == 5"));
    ctx.push_obligation(ProofObligation::assume("rr", "read_reg == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "hh_def",
        "has_hazard == if write_reg == read_reg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("hazard", "has_hazard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RAW hazard: write r5, read r5");
}

#[test]
fn pipeline_superscalar_issue_width() {
    // 2-wide: issue 2 instructions per cycle
    let mut ctx = VerificationContext::new();
    for v in &["instructions", "issue_width", "min_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i", "instructions == 100"));
    ctx.push_obligation(ProofObligation::assume("iw", "issue_width == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "mc_def",
        "min_cycles == instructions / issue_width",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "min_cycles == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100 instr / 2-wide = 50 min cycles");
}
