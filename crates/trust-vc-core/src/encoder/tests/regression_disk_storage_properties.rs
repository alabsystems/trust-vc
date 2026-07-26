// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sector_to_block_mapping() {
    let mut ctx = VerificationContext::new();
    for v in &["sector_number", "sectors_per_block", "block_number"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sn", "sector_number == 24"));
    ctx.push_obligation(ProofObligation::assume("spb", "sectors_per_block == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "bn_def",
        "block_number == sector_number / sectors_per_block",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "block_number == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "sector 24 / 8 sectors/block = block 3");
}

#[test]
fn disk_capacity_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["sectors", "sector_size", "capacity_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "sectors == 1000"));
    ctx.push_obligation(ProofObligation::assume("ss", "sector_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "cb_def",
        "capacity_bytes == sectors * sector_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_512000",
        "capacity_bytes == 512000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "capacity: 1000 * 512 = 512000 bytes");
}

#[test]
fn raid1_mirror_doubles_writes() {
    let mut ctx = VerificationContext::new();
    for v in &["logical_writes", "physical_writes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lw", "logical_writes == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "pw_def",
        "physical_writes == logical_writes * 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "physical_writes == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RAID1: 50 logical → 100 physical writes");
}

#[test]
fn raid5_parity_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["total_disks", "data_disks", "parity_disks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("td", "total_disks == 5"));
    ctx.push_obligation(ProofObligation::assume("pd", "parity_disks == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dd_def",
        "data_disks == total_disks - parity_disks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "data_disks == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RAID5: 5 disks - 1 parity = 4 data");
}

#[test]
fn stripe_size_distribution() {
    let mut ctx = VerificationContext::new();
    for v in &["file_size", "stripe_size", "stripes_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fs", "file_size == 1000"));
    ctx.push_obligation(ProofObligation::assume("ss", "stripe_size == 64"));
    // Ceiling division
    ctx.push_obligation(ProofObligation::assume(
        "sn_def",
        "stripes_needed == (file_size + stripe_size - 1) / stripe_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "stripes_needed == 16")); // ceil(1000/64) = 16
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "stripes: ceil(1000/64) = 16");
}

#[test]
fn write_amplification() {
    let mut ctx = VerificationContext::new();
    for v in &["logical_bytes", "physical_bytes", "amplification"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lb", "logical_bytes == 100"));
    ctx.push_obligation(ProofObligation::assume("pb", "physical_bytes == 400")); // 4x due to journaling + compaction
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "amplification == physical_bytes / logical_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "amplification == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "write amplification: 400/100 = 4x");
}

#[test]
fn block_bitmap_tracks_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["total_blocks", "allocated", "free"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_blocks == 1024"));
    ctx.push_obligation(ProofObligation::assume("a", "allocated == 768"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "free == total_blocks - allocated",
    ));
    ctx.push_obligation(ProofObligation::assert("is_256", "free == 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bitmap: 1024 - 768 = 256 free blocks");
}

#[test]
fn sequential_read_throughput() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "blocks_read",
        "block_size",
        "bytes_read",
        "time_ms",
        "throughput",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("br", "blocks_read == 100"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "byr_def",
        "bytes_read == blocks_read * block_size",
    ));
    ctx.push_obligation(ProofObligation::assume("t", "time_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "throughput == bytes_read / time_ms",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4096", "throughput == 4096"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "throughput: 409600/100 = 4096 bytes/ms");
}

#[test]
fn wear_leveling_count() {
    let mut ctx = VerificationContext::new();
    for v in &["writes_block_a", "writes_block_b", "difference"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("balanced", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wba", "writes_block_a == 1000"));
    ctx.push_obligation(ProofObligation::assume("wbb", "writes_block_b == 998"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "difference == writes_block_a - writes_block_b",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "balanced == if difference <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "balanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wear leveling: |1000-998|=2 <= 10 threshold");
}

#[test]
fn trim_reclaims_blocks() {
    let mut ctx = VerificationContext::new();
    for v in &["used_before", "trimmed", "used_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ub", "used_before == 500"));
    ctx.push_obligation(ProofObligation::assume("t", "trimmed == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ua_def",
        "used_after == used_before - trimmed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "used_after == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TRIM: 500 - 100 = 400 used blocks");
}
