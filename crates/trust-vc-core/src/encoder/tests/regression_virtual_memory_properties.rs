// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn virtual_to_physical_mapping() {
    // physical = page_frame * page_size + offset
    let mut ctx = VerificationContext::new();
    for v in &["page_frame", "page_size", "offset", "physical"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pf", "page_frame == 256"));
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("o", "offset == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "physical == page_frame * page_size + offset",
    ));
    // 256 * 4096 + 100 = 1048676
    ctx.push_obligation(ProofObligation::assert("addr", "physical == 1048676"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "VA→PA: frame 256, offset 100 → 1048676");
}

#[test]
fn page_offset_extraction() {
    // offset = virtual_addr % page_size
    let mut ctx = VerificationContext::new();
    for v in &["virtual_addr", "page_size", "offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("va", "virtual_addr == 8292"));
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "offset == virtual_addr % page_size",
    ));
    // 8292 % 4096 = 100
    ctx.push_obligation(ProofObligation::assert("is_100", "offset == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "offset: 8292 % 4096 = 100");
}

#[test]
fn address_space_size() {
    // Use a shift amount below the u32 bit-width; assumptions now enforce
    // shift side conditions instead of accepting `1 << 32` as wraparound.
    let mut ctx = VerificationContext::new();
    for v in &["addr_bits", "addr_space"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ab", "addr_bits == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "addr_space == 1 << addr_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("correct", "addr_space == 1048576"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1 << 20 is 1048576 in u32");
}

#[test]
fn page_table_levels() {
    // 4-level page table: 9+9+9+9+12 = 48 bits
    let mut ctx = VerificationContext::new();
    for v in &["level_bits", "levels", "offset_bits", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lb", "level_bits == 9"));
    ctx.push_obligation(ProofObligation::assume("l", "levels == 4"));
    ctx.push_obligation(ProofObligation::assume("ob", "offset_bits == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bits == level_bits * levels + offset_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_48", "total_bits == 48"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4-level page table: 9*4+12 = 48 bits");
}

#[test]
fn tlb_hit_no_page_walk() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tlb_contains", i32_ty());
    ctx.declare_var_typed("needs_page_walk", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "tlb_contains == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "npw_def",
        "needs_page_walk == if tlb_contains == 1 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_walk", "needs_page_walk == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TLB hit → no page walk needed");
}

#[test]
fn mmap_region_non_overlapping() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "region1_start",
        "region1_size",
        "region1_end",
        "region2_start",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overlaps", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r1s", "region1_start == 1000"));
    ctx.push_obligation(ProofObligation::assume("r1sz", "region1_size == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "r1e_def",
        "region1_end == region1_start + region1_size",
    ));
    ctx.push_obligation(ProofObligation::assume("r2s", "region2_start == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "overlaps == if region2_start < region1_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_overlap", "overlaps == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "regions [1000,1500) and [2000,...) don't overlap");
}

#[test]
fn permission_check_read() {
    // Permission bits: read=4, write=2, exec=1
    let mut ctx = VerificationContext::new();
    for v in &["perms", "read_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_read", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "perms == 5")); // r-x = 4+1
    ctx.push_obligation(ProofObligation::assume("rb_def", "read_bit == perms & 4"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "can_read == if read_bit > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("readable", "can_read == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "perms 5 (r-x): read bit set");
}

#[test]
fn stack_grows_downward() {
    let mut ctx = VerificationContext::new();
    for v in &["stack_top", "alloc_size", "new_sp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("st", "stack_top == 65536"));
    ctx.push_obligation(ProofObligation::assume("as_val", "alloc_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "nsp_def",
        "new_sp == stack_top - alloc_size",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "new_sp < stack_top"));
    ctx.push_obligation(ProofObligation::assert("is_65280", "new_sp == 65280"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stack: 65536 - 256 = 65280 (grows down)");
}

#[test]
fn heap_grows_upward() {
    let mut ctx = VerificationContext::new();
    for v in &["brk", "alloc_size", "new_brk"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b", "brk == 4096"));
    ctx.push_obligation(ProofObligation::assume("as_val", "alloc_size == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "nb_def",
        "new_brk == brk + alloc_size",
    ));
    ctx.push_obligation(ProofObligation::assert("higher", "new_brk > brk"));
    ctx.push_obligation(ProofObligation::assert("is_5120", "new_brk == 5120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heap: 4096 + 1024 = 5120 (grows up)");
}

#[test]
fn guard_page_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["access_addr", "guard_start", "guard_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_guard", i32_ty());
    ctx.push_obligation(ProofObligation::assume("aa", "access_addr == 4000"));
    ctx.push_obligation(ProofObligation::assume("gs", "guard_start == 3000"));
    ctx.push_obligation(ProofObligation::assume("ge", "guard_end == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "ig_def",
        "is_guard == if access_addr >= guard_start && access_addr < guard_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("guard", "is_guard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "addr 4000 in guard page [3000, 4096)");
}
