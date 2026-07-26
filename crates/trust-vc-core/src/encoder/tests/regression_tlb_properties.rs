// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn virtual_to_physical_translation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "virtual_addr",
        "page_offset",
        "page_number",
        "frame_number",
        "physical_addr",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("va", "virtual_addr == 8500"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "page_offset == virtual_addr % 4096",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "pn_def",
        "page_number == virtual_addr / 4096",
    ));
    ctx.push_obligation(ProofObligation::assume("fn_val", "frame_number == 10")); // TLB lookup result
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "physical_addr == frame_number * 4096 + page_offset",
    ));
    // 8500 % 4096 = 308, 8500 / 4096 = 2, PA = 10*4096 + 308 = 41268
    ctx.push_obligation(ProofObligation::assert("offset_308", "page_offset == 308"));
    ctx.push_obligation(ProofObligation::assert(
        "pa_41268",
        "physical_addr == 41268",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "TLB: VA 8500 → page 2, offset 308, PA 41268");
}

#[test]
fn tlb_hit_avoids_page_walk() {
    let mut ctx = VerificationContext::new();
    for v in &["tlb_lookup_cycles", "page_walk_cycles", "hit_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tlc", "tlb_lookup_cycles == 1"));
    ctx.push_obligation(ProofObligation::assume("pwc", "page_walk_cycles == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "hc_def",
        "hit_cycles == tlb_lookup_cycles",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "hit_cycles == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "faster",
        "hit_cycles < page_walk_cycles",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TLB hit: 1 cycle vs 100 cycle page walk");
}

#[test]
fn effective_access_time() {
    // EAT = hit_rate * hit_time + (1 - hit_rate) * miss_time
    // Simplified with percentages: EAT_pct = hit_pct * hit_time + miss_pct * miss_time
    let mut ctx = VerificationContext::new();
    for v in &["hit_pct", "miss_pct", "hit_time", "miss_time", "eat_scaled"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hp", "hit_pct == 95"));
    ctx.push_obligation(ProofObligation::assume("mp", "miss_pct == 5"));
    ctx.push_obligation(ProofObligation::assume("ht", "hit_time == 1")); // 1 cycle
    ctx.push_obligation(ProofObligation::assume("mt", "miss_time == 100")); // 100 cycles
    ctx.push_obligation(ProofObligation::assume(
        "eat_def",
        "eat_scaled == hit_pct * hit_time + miss_pct * miss_time",
    ));
    // 95*1 + 5*100 = 95 + 500 = 595 (scaled by 100, so actual = 5.95 cycles)
    ctx.push_obligation(ProofObligation::assert("is_595", "eat_scaled == 595"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "EAT: 95*1 + 5*100 = 595 (÷100 = 5.95 cycles)");
}

#[test]
fn page_size_offset_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["page_size", "offset_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 4KB page = 2^12, so 12 offset bits. Hardcoded.
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("ob", "offset_bits == 12"));
    ctx.push_obligation(ProofObligation::assert("bits_12", "offset_bits == 12"));
    ctx.push_obligation(ProofObligation::assert("size_positive", "page_size > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4KB page: 12 offset bits");
}

#[test]
fn tlb_entry_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ways", "sets", "total_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("w", "ways == 4"));
    ctx.push_obligation(ProofObligation::assume("s", "sets == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "total_entries == ways * sets",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "total_entries == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "TLB: 4 ways × 16 sets = 64 entries");
}

#[test]
fn large_page_reduces_misses() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "memory_range",
        "small_page_size",
        "large_page_size",
        "small_pages",
        "large_pages",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mr", "memory_range == 4194304")); // 4MB
    ctx.push_obligation(ProofObligation::assume("sps", "small_page_size == 4096")); // 4KB
    ctx.push_obligation(ProofObligation::assume("lps", "large_page_size == 2097152")); // 2MB
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "small_pages == memory_range / small_page_size",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "lp_def",
        "large_pages == memory_range / large_page_size",
    ));
    ctx.push_obligation(ProofObligation::assert("sp_1024", "small_pages == 1024"));
    ctx.push_obligation(ProofObligation::assert("lp_2", "large_pages == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "large_pages < small_pages",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "large pages: 4MB / 2MB = 2 vs 4MB / 4KB = 1024");
}

#[test]
fn asid_isolates_processes() {
    let mut ctx = VerificationContext::new();
    for v in &["process_a_asid", "process_b_asid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("isolated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pa", "process_a_asid == 5"));
    ctx.push_obligation(ProofObligation::assume("pb", "process_b_asid == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "i_def",
        "isolated == if process_a_asid != process_b_asid { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "isolated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ASID: 5 ≠ 12 → isolated");
}

#[test]
fn tlb_flush_resets_entries() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_before", "entries_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "entries_before == 64"));
    ctx.push_obligation(ProofObligation::assume("ea", "entries_after == 0")); // full flush
    ctx.push_obligation(ProofObligation::assert("is_0", "entries_after == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "entries_after < entries_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TLB flush: 64 → 0 entries");
}

#[test]
fn multi_level_page_table_depth() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "virtual_bits",
        "offset_bits",
        "remaining_bits",
        "levels",
        "bits_per_level",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("vb", "virtual_bits == 48"));
    ctx.push_obligation(ProofObligation::assume("ob", "offset_bits == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "rb_def",
        "remaining_bits == virtual_bits - offset_bits",
    ));
    ctx.push_obligation(ProofObligation::assume("bpl", "bits_per_level == 9")); // 512-entry page tables
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "levels == remaining_bits / bits_per_level",
    ));
    ctx.push_obligation(ProofObligation::assert("rb_36", "remaining_bits == 36"));
    ctx.push_obligation(ProofObligation::assert("l_4", "levels == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "page table: (48-12)/9 = 4 levels");
}

#[test]
fn page_table_entry_size() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_per_table", "entry_size_bytes", "table_size_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ept", "entries_per_table == 512")); // 2^9
    ctx.push_obligation(ProofObligation::assume("esb", "entry_size_bytes == 8")); // 64-bit PTE
    ctx.push_obligation(ProofObligation::assume(
        "tsb_def",
        "table_size_bytes == entries_per_table * entry_size_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4096",
        "table_size_bytes == 4096",
    )); // fits in one page
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "page table: 512 × 8 = 4096 bytes (one page)");
}
