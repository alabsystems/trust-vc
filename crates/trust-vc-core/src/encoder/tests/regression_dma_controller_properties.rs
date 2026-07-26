// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn transfer_size_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["block_count", "block_size", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bc", "block_count == 16"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == block_count * block_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8192", "total_bytes == 8192"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DMA: 16×512=8192 bytes");
}

#[test]
fn source_address_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["src_addr", "transfer_size", "next_src"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sa", "src_addr == 65536"));
    ctx.push_obligation(ProofObligation::assume("ts", "transfer_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "next_src == src_addr + transfer_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_69632", "next_src == 69632"));
    ctx.push_obligation(ProofObligation::assert("advanced", "next_src > src_addr"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMA src: 65536+4096=69632");
}

#[test]
fn destination_address_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["dst_addr", "transfer_size", "next_dst"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("da", "dst_addr == 131072"));
    ctx.push_obligation(ProofObligation::assume("ts", "transfer_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "nd_def",
        "next_dst == dst_addr + transfer_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_135168", "next_dst == 135168"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMA dst: 131072+4096=135168");
}

#[test]
fn channel_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["ch0_priority", "ch1_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch0_wins", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp0", "ch0_priority == 3")); // higher = more priority
    ctx.push_obligation(ProofObligation::assume("cp1", "ch1_priority == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cw_def",
        "ch0_wins == if ch0_priority > ch1_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "ch0_wins == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMA priority: ch0(3) > ch1(1)");
}

#[test]
fn burst_transfer_beats() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_length", "beat_size", "burst_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AXI-style burst: 16 beats × 4 bytes = 64 bytes
    ctx.push_obligation(ProofObligation::assume("bl", "burst_length == 16"));
    ctx.push_obligation(ProofObligation::assume("bs", "beat_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "bb_def",
        "burst_bytes == burst_length * beat_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "burst_bytes == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DMA burst: 16×4=64 bytes");
}

#[test]
fn scatter_gather_list_entries() {
    let mut ctx = VerificationContext::new();
    for v in &["total_transfer", "max_per_entry", "min_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tt", "total_transfer == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume("mpe", "max_per_entry == 4096")); // 4KB
    ctx.push_obligation(ProofObligation::assume(
        "me_def",
        "min_entries == total_transfer / max_per_entry",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "min_entries == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "scatter-gather: 65536/4096=16 entries");
}

#[test]
fn transfer_completion_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["transferred", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("complete", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "transferred == 8192"));
    ctx.push_obligation(ProofObligation::assume("tot", "total == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "complete == if transferred >= total { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("done", "complete == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMA: 8192/8192 = complete");
}

#[test]
fn fifo_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_level", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trigger_transfer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fl", "fifo_level == 12"));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 8")); // half-full
    ctx.push_obligation(ProofObligation::assume(
        "tt_def",
        "trigger_transfer == if fifo_level >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trigger_transfer == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMA FIFO: 12 >= 8 threshold → trigger");
}

#[test]
fn address_alignment_check() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "alignment"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "address == 4096"));
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if address % alignment == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DMA alignment: 4096 mod 16 = 0");
}

#[test]
fn remaining_transfer_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_blocks", "completed_blocks", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_blocks == 256"));
    ctx.push_obligation(ProofObligation::assume("cb", "completed_blocks == 192"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == total_blocks - completed_blocks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "remaining == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "progress",
        "remaining < total_blocks",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMA: 256-192=64 blocks remaining");
}
