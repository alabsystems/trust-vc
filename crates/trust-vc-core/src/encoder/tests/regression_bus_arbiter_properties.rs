// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fixed_priority_arbitration() {
    let mut ctx = VerificationContext::new();
    for v in &["master_a_priority", "master_b_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_granted", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ap", "master_a_priority == 0")); // highest
    ctx.push_obligation(ProofObligation::assume("bp", "master_b_priority == 3")); // lower
    ctx.push_obligation(ProofObligation::assume(
        "ag_def",
        "a_granted == if master_a_priority < master_b_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_granted == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bus arbiter: master A(0) < B(3) → A granted");
}

#[test]
fn round_robin_next_master() {
    let mut ctx = VerificationContext::new();
    for v in &["current_master", "num_masters", "next_master"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cm", "current_master == 3"));
    ctx.push_obligation(ProofObligation::assume("nm", "num_masters == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "nxt_def",
        "next_master == (current_master + 1) % num_masters",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_master == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "round-robin: master 3 → 0 (mod 4)");
}

#[test]
fn bus_grant_duration() {
    let mut ctx = VerificationContext::new();
    for v in &["grant_start_cycle", "grant_end_cycle", "duration"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("gs", "grant_start_cycle == 1000"));
    ctx.push_obligation(ProofObligation::assume("ge", "grant_end_cycle == 1016"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "duration == grant_end_cycle - grant_start_cycle",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "duration == 16"));
    ctx.push_obligation(ProofObligation::assert("positive", "duration > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bus grant: 1016-1000=16 cycles");
}

#[test]
fn max_burst_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_count", "max_burst"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("must_release", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bc", "burst_count == 16"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_burst == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "mr_def",
        "must_release == if burst_count >= max_burst { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "must_release == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bus: burst 16 >= max 16 → must release");
}

#[test]
fn starvation_prevention_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["wait_cycles", "starvation_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("promote_priority", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wc", "wait_cycles == 1000"));
    ctx.push_obligation(ProofObligation::assume("st", "starvation_threshold == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "pp_def",
        "promote_priority == if wait_cycles > starvation_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "promote_priority == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anti-starvation: 1000 > 500 → promote");
}

#[test]
fn split_transaction_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["outstanding_txns", "max_outstanding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_issue", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "outstanding_txns == 7"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_outstanding == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ci_def",
        "can_issue == if outstanding_txns < max_outstanding { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_issue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "split txn: 7 < 8 → can issue");
}

#[test]
fn bandwidth_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "total_bandwidth",
        "master_a_share",
        "master_b_share",
        "remaining",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_bandwidth == 100")); // percentage
    ctx.push_obligation(ProofObligation::assume("ma", "master_a_share == 60"));
    ctx.push_obligation(ProofObligation::assume("mb", "master_b_share == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == total_bandwidth - master_a_share - master_b_share",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "remaining == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "fits",
        "master_a_share + master_b_share <= total_bandwidth",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth: 100-60-30=10% remaining");
}

#[test]
fn locked_transfer_exclusion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bus_locked", u32_ty());
    ctx.declare_var_typed("other_request", u32_ty());
    ctx.declare_var_typed("other_granted", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bl", "bus_locked == 1"));
    ctx.push_obligation(ProofObligation::assume("or", "other_request == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "og_def",
        "other_granted == if bus_locked == 0 && other_request == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("blocked", "other_granted == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "locked bus: other request blocked");
}

#[test]
fn multilayer_interconnect_paths() {
    let mut ctx = VerificationContext::new();
    for v in &["num_masters", "num_slaves", "max_concurrent"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    // Multi-layer: min(masters, slaves) concurrent paths
    ctx.push_obligation(ProofObligation::assume("nm", "num_masters == 4"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_slaves == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "mc_def",
        "max_concurrent == if num_masters <= num_slaves { num_masters } else { num_slaves }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "max_concurrent == 4")); // min(4,6)
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multilayer: min(4,6)=4 concurrent paths");
}

#[test]
fn default_slave_response() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "region_start", "region_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("decoded", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "address == 999999"));
    ctx.push_obligation(ProofObligation::assume("rs", "region_start == 0"));
    ctx.push_obligation(ProofObligation::assume("re", "region_end == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "decoded == if address >= region_start && address < region_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_decoded", "decoded == 0")); // out of range
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "default slave: 999999 not in [0,65536)");
}
