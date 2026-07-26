// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fifo_evicts_oldest() {
    let mut ctx = VerificationContext::new();
    for v in &["oldest_timestamp", "newest_timestamp", "evict_timestamp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ot", "oldest_timestamp == 100"));
    ctx.push_obligation(ProofObligation::assume("nt", "newest_timestamp == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "et",
        "evict_timestamp == oldest_timestamp",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_oldest",
        "evict_timestamp == 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fifo",
        "evict_timestamp <= newest_timestamp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIFO: evict oldest (100) from [100,500]");
}

#[test]
fn lru_access_updates_timestamp() {
    let mut ctx = VerificationContext::new();
    for v in &["old_timestamp", "access_time", "new_timestamp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ot", "old_timestamp == 200"));
    ctx.push_obligation(ProofObligation::assume("at", "access_time == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_timestamp == access_time",
    ));
    ctx.push_obligation(ProofObligation::assert("updated", "new_timestamp == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "newer",
        "new_timestamp > old_timestamp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LRU: timestamp 200 → 600 on access");
}

#[test]
fn clock_algorithm_reference_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_bit", u32_ty());
    ctx.declare_var_typed("new_ref_bit", u32_ty());
    ctx.declare_var_typed("evict", i32_ty());
    // Clock hand finds ref_bit=0 → evict
    ctx.push_obligation(ProofObligation::assume("rb", "ref_bit == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "evict == if ref_bit == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "evict == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clock: ref_bit=0 → evict");
}

#[test]
fn clock_second_chance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_bit", u32_ty());
    ctx.declare_var_typed("new_ref_bit", u32_ty());
    ctx.declare_var_typed("evict", i32_ty());
    // Clock hand finds ref_bit=1 → clear to 0, skip (second chance)
    ctx.push_obligation(ProofObligation::assume("rb", "ref_bit == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nrb_def",
        "new_ref_bit == if ref_bit == 1 { 0 } else { ref_bit }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "evict == if ref_bit == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cleared", "new_ref_bit == 0"));
    ctx.push_obligation(ProofObligation::assert("spared", "evict == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clock: ref_bit=1 → clear, no evict");
}

#[test]
fn page_fault_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["total_accesses", "page_faults", "hits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ta", "total_accesses == 1000"));
    ctx.push_obligation(ProofObligation::assume("pf", "page_faults == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "h_def",
        "hits == total_accesses - page_faults",
    ));
    ctx.push_obligation(ProofObligation::assert("is_950", "hits == 950"));
    ctx.push_obligation(ProofObligation::assert("mostly_hits", "hits > page_faults"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "page fault: 1000-50=950 hits");
}

#[test]
fn working_set_size() {
    let mut ctx = VerificationContext::new();
    for v in &["allocated_frames", "working_set", "surplus"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("af", "allocated_frames == 32"));
    ctx.push_obligation(ProofObligation::assume("ws", "working_set == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "surplus == allocated_frames - working_set",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "surplus == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "enough",
        "allocated_frames >= working_set",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working set: 32-24=8 surplus frames");
}

#[test]
fn frame_pool_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["free_frames", "requested", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_allocate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ff", "free_frames == 100"));
    ctx.push_obligation(ProofObligation::assume("r", "requested == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_allocate == if free_frames >= requested { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rem_def",
        "remaining == free_frames - requested",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_allocate == 1"));
    ctx.push_obligation(ProofObligation::assert("is_84", "remaining == 84"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frame pool: 100-16=84 remaining");
}

#[test]
fn dirty_page_writeback() {
    let mut ctx = VerificationContext::new();
    for v in &["dirty_pages", "written_back", "remaining_dirty"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dp", "dirty_pages == 20"));
    ctx.push_obligation(ProofObligation::assume("wb", "written_back == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "remaining_dirty == dirty_pages - written_back",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "remaining_dirty == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "remaining_dirty < dirty_pages",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "writeback: 20-8=12 dirty pages");
}

#[test]
fn optimal_beladys_min() {
    // Belady's: evict page used farthest in future
    let mut ctx = VerificationContext::new();
    for v in &["page_a_next_use", "page_b_next_use", "evict_page"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("an", "page_a_next_use == 50"));
    ctx.push_obligation(ProofObligation::assume("bn", "page_b_next_use == 200"));
    // Evict the one used farthest: page_b (200 > 50)
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "evict_page == if page_a_next_use > page_b_next_use { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("evict_b", "evict_page == 1")); // evict page B
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Belady: evict page B (next use 200 > 50)");
}

#[test]
fn thrashing_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["fault_rate", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("thrashing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "fault_rate == 80")); // 80% fault rate
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 50")); // 50% threshold
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "thrashing == if fault_rate > threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thrashing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thrashing: 80% > 50% threshold");
}
