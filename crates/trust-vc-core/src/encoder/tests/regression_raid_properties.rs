// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn raid0_striping_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["disk_count", "disk_capacity", "total_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dc", "disk_count == 4"));
    ctx.push_obligation(ProofObligation::assume("dcap", "disk_capacity == 1000")); // GB
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_capacity == disk_count * disk_capacity",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4000", "total_capacity == 4000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RAID0: 4 × 1000 = 4000 GB");
}

#[test]
fn raid1_mirror_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["disk_count", "disk_capacity", "usable_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dc", "disk_count == 2"));
    ctx.push_obligation(ProofObligation::assume("dcap", "disk_capacity == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "uc_def",
        "usable_capacity == disk_capacity",
    )); // mirror = single disk capacity
    ctx.push_obligation(ProofObligation::assert(
        "is_1000",
        "usable_capacity == 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RAID1: mirror, usable = single disk = 1000 GB");
}

#[test]
fn raid5_parity_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["disk_count", "disk_capacity", "usable_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // RAID5: one disk worth of parity
    ctx.push_obligation(ProofObligation::assume("dc", "disk_count == 5"));
    ctx.push_obligation(ProofObligation::assume("dcap", "disk_capacity == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "uc_def",
        "usable_capacity == (disk_count - 1) * disk_capacity",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4000",
        "usable_capacity == 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RAID5: (5-1) × 1000 = 4000 GB usable");
}

#[test]
fn raid6_double_parity() {
    let mut ctx = VerificationContext::new();
    for v in &["disk_count", "disk_capacity", "usable_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dc", "disk_count == 6"));
    ctx.push_obligation(ProofObligation::assume("dcap", "disk_capacity == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "uc_def",
        "usable_capacity == (disk_count - 2) * disk_capacity",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4000",
        "usable_capacity == 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RAID6: (6-2) × 1000 = 4000 GB usable");
}

#[test]
fn raid10_nested_mirror_stripe() {
    let mut ctx = VerificationContext::new();
    for v in &["disk_count", "disk_capacity", "usable_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // RAID10: mirror pairs, then stripe across pairs → 50% capacity
    ctx.push_obligation(ProofObligation::assume("dc", "disk_count == 4"));
    ctx.push_obligation(ProofObligation::assume("dcap", "disk_capacity == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "uc_def",
        "usable_capacity == disk_count * disk_capacity / 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_2000",
        "usable_capacity == 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RAID10: 4 × 1000 / 2 = 2000 GB");
}

#[test]
fn stripe_unit_distribution() {
    let mut ctx = VerificationContext::new();
    for v in &["block_number", "disk_count", "target_disk", "stripe_number"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bn", "block_number == 17"));
    ctx.push_obligation(ProofObligation::assume("dc", "disk_count == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "td_def",
        "target_disk == block_number % disk_count",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sn_def",
        "stripe_number == block_number / disk_count",
    ));
    ctx.push_obligation(ProofObligation::assert("disk_1", "target_disk == 1")); // 17 % 4 = 1
    ctx.push_obligation(ProofObligation::assert("stripe_4", "stripe_number == 4")); // 17 / 4 = 4
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "stripe: block 17 → disk 1, stripe 4");
}

#[test]
fn rebuild_time_estimate() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "disk_capacity_mb",
        "rebuild_rate_mb_per_sec",
        "rebuild_time_sec",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dcm", "disk_capacity_mb == 100000")); // 100GB
    ctx.push_obligation(ProofObligation::assume(
        "rrm",
        "rebuild_rate_mb_per_sec == 100",
    )); // 100 MB/s
    ctx.push_obligation(ProofObligation::assume(
        "rts_def",
        "rebuild_time_sec == disk_capacity_mb / rebuild_rate_mb_per_sec",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1000",
        "rebuild_time_sec == 1000",
    )); // ~16 minutes
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "rebuild: 100GB / 100MB/s = 1000s");
}

#[test]
fn fault_tolerance_raid5() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_disk_failures", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mdf", "max_disk_failures == 1"));
    ctx.push_obligation(ProofObligation::assert("is_1", "max_disk_failures == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "at_least_one",
        "max_disk_failures >= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RAID5: tolerates 1 disk failure");
}

#[test]
fn fault_tolerance_raid6() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_disk_failures", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mdf", "max_disk_failures == 2"));
    ctx.push_obligation(ProofObligation::assert("is_2", "max_disk_failures == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "better_than_5",
        "max_disk_failures > 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RAID6: tolerates 2 disk failures");
}

#[test]
fn write_amplification_raid5() {
    // RAID5 small write: read old data + old parity, write new data + new parity = 4 I/O
    let mut ctx = VerificationContext::new();
    for v in &["user_writes", "actual_io_ops", "write_amp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("uw", "user_writes == 1"));
    ctx.push_obligation(ProofObligation::assume("aio", "actual_io_ops == 4")); // read-modify-write cycle
    ctx.push_obligation(ProofObligation::assume(
        "wa_def",
        "write_amp == actual_io_ops / user_writes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "write_amp == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RAID5 write amp: 4 I/O per 1 user write");
}
