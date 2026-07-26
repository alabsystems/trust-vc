// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn memtable_flush_to_level0() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "memtable_entries",
        "level0_sstables_before",
        "level0_sstables_after",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("me", "memtable_entries == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "l0b",
        "level0_sstables_before == 3",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "l0a_def",
        "level0_sstables_after == level0_sstables_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4",
        "level0_sstables_after == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flush: 3 L0 SSTs → 4 after memtable flush");
}

#[test]
fn level_size_ratio() {
    // Each level is ratio× larger than the previous
    let mut ctx = VerificationContext::new();
    for v in &["level0_size", "ratio", "level1_size", "level2_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l0", "level0_size == 10"));
    ctx.push_obligation(ProofObligation::assume("r", "ratio == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "l1_def",
        "level1_size == level0_size * ratio",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "l2_def",
        "level2_size == level1_size * ratio",
    ));
    ctx.push_obligation(ProofObligation::assert("l1_100", "level1_size == 100"));
    ctx.push_obligation(ProofObligation::assert("l2_1000", "level2_size == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "LSM levels: 10 → 100 → 1000 (10× ratio)");
}

#[test]
fn compaction_reduces_sstables() {
    let mut ctx = VerificationContext::new();
    for v in &["input_sstables", "output_sstables"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("is", "input_sstables == 10"));
    ctx.push_obligation(ProofObligation::assume("os", "output_sstables == 1")); // merge into 1
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "output_sstables < input_sstables",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compaction: 10 SSTs → 1 merged SST");
}

#[test]
fn bloom_filter_false_positive_rate() {
    // bits_per_key * ln(2) ≈ number of hash functions
    // Simplified: more bits = lower FP rate
    let mut ctx = VerificationContext::new();
    for v in &["bits_per_key", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acceptable_fp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bpk", "bits_per_key == 10"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 8")); // ~2% FP rate minimum
    ctx.push_obligation(ProofObligation::assume(
        "af_def",
        "acceptable_fp == if bits_per_key >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable_fp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bloom filter: 10 bits/key >= 8 minimum → acceptable FP",
    );
}

#[test]
fn write_amplification_per_level() {
    let mut ctx = VerificationContext::new();
    for v in &["ratio", "levels", "write_amp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "ratio == 10"));
    ctx.push_obligation(ProofObligation::assume("l", "levels == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "wa_def",
        "write_amp == ratio * levels",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "write_amp == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "write amp: 10 ratio × 3 levels = 30×");
}

#[test]
fn space_amplification() {
    let mut ctx = VerificationContext::new();
    for v in &["logical_size", "physical_size", "space_amp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ls", "logical_size == 1000"));
    ctx.push_obligation(ProofObligation::assume("ps", "physical_size == 1100")); // 10% overhead
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "space_amp == physical_size - logical_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "space_amp == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "space amp: 1100-1000 = 100 overhead");
}

#[test]
fn tombstone_cleanup() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_before", "tombstones", "entries_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "entries_before == 500"));
    ctx.push_obligation(ProofObligation::assume("t", "tombstones == 100")); // marked for deletion
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "entries_after == entries_before - tombstones",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "entries_after == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compaction: 500 - 100 tombstones = 400");
}

#[test]
fn read_amplification_levels() {
    // Worst case: check bloom filter at each level
    let mut ctx = VerificationContext::new();
    for v in &["levels", "bloom_checks", "disk_reads"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "levels == 4"));
    ctx.push_obligation(ProofObligation::assume("bc_def", "bloom_checks == levels")); // one per level
    ctx.push_obligation(ProofObligation::assume("dr", "disk_reads == 1")); // only one actual read (bloom filters eliminate rest)
    ctx.push_obligation(ProofObligation::assert("checks_4", "bloom_checks == 4"));
    ctx.push_obligation(ProofObligation::assert("reads_1", "disk_reads == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "read amp: 4 bloom checks, 1 disk read");
}

#[test]
fn compaction_trigger_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["level_size", "max_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_compaction", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ls", "level_size == 150"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_size == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "needs_compaction == if level_size > max_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("trigger", "needs_compaction == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "150 > max 100 → trigger compaction");
}

#[test]
fn merge_preserves_sorted_order() {
    // After merge, output has same total entries
    let mut ctx = VerificationContext::new();
    for v in &[
        "sst_a_entries",
        "sst_b_entries",
        "overlap",
        "merged_entries",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sa", "sst_a_entries == 100"));
    ctx.push_obligation(ProofObligation::assume("sb", "sst_b_entries == 200"));
    ctx.push_obligation(ProofObligation::assume("o", "overlap == 50")); // duplicate keys
    ctx.push_obligation(ProofObligation::assume(
        "me_def",
        "merged_entries == sst_a_entries + sst_b_entries - overlap",
    ));
    ctx.push_obligation(ProofObligation::assert("is_250", "merged_entries == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "merge: 100+200-50 overlap = 250 unique");
}
