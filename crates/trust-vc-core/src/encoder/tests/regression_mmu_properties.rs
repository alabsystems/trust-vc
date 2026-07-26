// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn page_table_levels() {
    let mut ctx = VerificationContext::new();
    for v in &["addr_bits", "page_offset_bits", "level_bits", "levels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ab", "addr_bits == 48"));
    ctx.push_obligation(ProofObligation::assume("pob", "page_offset_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("lb", "level_bits == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "levels == (addr_bits - page_offset_bits) / level_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "levels == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "MMU: (48-12)/9 = 4 levels");
}

#[test]
fn permission_bits_check() {
    let mut ctx = VerificationContext::new();
    for v in &["pte_flags", "read_bit", "write_bit", "exec_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("readable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pf", "pte_flags == 5")); // read + exec (bits 0 and 2)
    ctx.push_obligation(ProofObligation::assume("rb", "read_bit == 1"));
    ctx.push_obligation(ProofObligation::assume("wb", "write_bit == 2"));
    ctx.push_obligation(ProofObligation::assume("eb", "exec_bit == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "readable == if (pte_flags & read_bit) != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "readable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PTE: flags=5, read bit set");
}

#[test]
fn page_frame_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["total_frames", "used_frames", "free_frames"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tf", "total_frames == 1048576")); // 4GB / 4KB
    ctx.push_obligation(ProofObligation::assume("uf", "used_frames == 262144")); // 1GB used
    ctx.push_obligation(ProofObligation::assume(
        "ff_def",
        "free_frames == total_frames - used_frames",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_786432",
        "free_frames == 786432",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frames: 1048576 - 262144 = 786432 free");
}

#[test]
fn virtual_address_space_split() {
    let mut ctx = VerificationContext::new();
    for v in &["total_pages", "user_space_pages", "kernel_space_pages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Simplified: total pages split 50/50 user/kernel
    ctx.push_obligation(ProofObligation::assume("tp", "total_pages == 2000000"));
    ctx.push_obligation(ProofObligation::assume(
        "usp_def",
        "user_space_pages == total_pages / 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ksp_def",
        "kernel_space_pages == total_pages / 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "equal",
        "user_space_pages == kernel_space_pages",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1m",
        "user_space_pages == 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "address space: 2M / 2 = 1M pages each");
}

#[test]
fn dirty_bit_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["pte_flags", "dirty_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_dirty", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pf", "pte_flags == 67")); // dirty (bit 6) + present + read
    ctx.push_obligation(ProofObligation::assume("db", "dirty_bit == 64")); // bit 6
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_dirty == if (pte_flags & dirty_bit) != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dirty", "is_dirty == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "PTE dirty: flags=67 has bit 6 set");
}

#[test]
fn page_fault_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_accesses", "tlb_hits", "page_faults"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ta", "total_accesses == 100000"));
    ctx.push_obligation(ProofObligation::assume("th", "tlb_hits == 99500"));
    ctx.push_obligation(ProofObligation::assume(
        "pf_def",
        "page_faults == total_accesses - tlb_hits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "page_faults == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "page faults: 100000 - 99500 = 500");
}

#[test]
fn inverted_page_table_size() {
    // One entry per physical frame, not per virtual page
    let mut ctx = VerificationContext::new();
    for v in &["physical_frames", "entry_size", "table_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pf", "physical_frames == 1024"));
    ctx.push_obligation(ProofObligation::assume("es", "entry_size == 8")); // bytes per entry
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "table_size == physical_frames * entry_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8192", "table_size == 8192"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "inverted PT: 1024 × 8 = 8192 bytes");
}

#[test]
fn memory_protection_key() {
    let mut ctx = VerificationContext::new();
    for v in &["page_key", "access_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("access_allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pk", "page_key == 7"));
    ctx.push_obligation(ProofObligation::assume("ak", "access_key == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "access_allowed == if page_key == access_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "access_allowed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MPK: page key 7 == access key 7 → allowed");
}

#[test]
fn swap_space_usage() {
    let mut ctx = VerificationContext::new();
    for v in &["swapped_out_pages", "swap_total_pages", "swap_free"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sop", "swapped_out_pages == 5000"));
    ctx.push_obligation(ProofObligation::assume("stp", "swap_total_pages == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "swap_free == swap_total_pages - swapped_out_pages",
    ));
    ctx.push_obligation(ProofObligation::assert("is_45000", "swap_free == 45000"));
    ctx.push_obligation(ProofObligation::assert("has_space", "swap_free > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap: 50000 - 5000 = 45000 free");
}

#[test]
fn demand_paging_lazy_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["mapped_pages", "resident_pages", "not_yet_touched"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mp", "mapped_pages == 10000"));
    ctx.push_obligation(ProofObligation::assume("rp", "resident_pages == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "nyt_def",
        "not_yet_touched == mapped_pages - resident_pages",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_8000",
        "not_yet_touched == 8000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lazy",
        "resident_pages < mapped_pages",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "demand paging: 10000 mapped, 2000 resident, 8000 lazy",
    );
}
