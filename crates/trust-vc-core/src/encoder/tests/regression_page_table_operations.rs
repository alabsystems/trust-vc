// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn page_offset_extraction() {
    // Page size 4096: offset = addr & 0xFFF
    let mut ctx = VerificationContext::new();
    for v in &["addr", "offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "addr == 8200")); // 0x2008
    ctx.push_obligation(ProofObligation::assume("o_def", "offset == addr & 4095"));
    // 8200 & 4095 = 8200 - 8192 = 8
    ctx.push_obligation(ProofObligation::assert("is_8", "offset == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "page offset of 0x2008 = 8");
}

#[test]
fn page_number_extraction() {
    // page_num = addr >> 12 (for 4KB pages)
    let mut ctx = VerificationContext::new();
    for v in &["addr", "page_num"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "addr == 8200"));
    ctx.push_obligation(ProofObligation::assume("pn_def", "page_num == addr >> 12"));
    // 8200 >> 12 = 2 (page 2)
    ctx.push_obligation(ProofObligation::assert("is_2", "page_num == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "page number of 8200 = 2");
}

#[test]
fn physical_address_reconstruction() {
    // phys_addr = (frame_num << 12) | offset
    let mut ctx = VerificationContext::new();
    for v in &["frame_num", "offset", "phys_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fn_val", "frame_num == 5"));
    ctx.push_obligation(ProofObligation::assume("o", "offset == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "phys_addr == (frame_num << 12) | offset",
    ));
    // 5 * 4096 + 100 = 20480 + 100 = 20580
    ctx.push_obligation(ProofObligation::assert("is_20580", "phys_addr == 20580"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "frame 5, offset 100 → phys 20580");
}

#[test]
fn page_aligned_address() {
    // Page-aligned: offset bits are 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("addr", u32_ty());
    ctx.declare_var_typed("is_aligned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "addr == 8192")); // 0x2000
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_aligned == if (addr & 4095) == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("aligned", "is_aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "8192 is page-aligned");
}

#[test]
fn pages_in_range() {
    // Number of pages to map [start, end): ceil((end - start) / 4096)
    let mut ctx = VerificationContext::new();
    for v in &["start_addr", "end_addr", "size", "pages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "start_addr == 0"));
    ctx.push_obligation(ProofObligation::assume("e", "end_addr == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "sz_def",
        "size == end_addr - start_addr",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "pages == (size + 4095) / 4096",
    ));
    // (10000 + 4095) / 4096 = 14095 / 4096 = 3
    ctx.push_obligation(ProofObligation::assert("is_3", "pages == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "10000 bytes → 3 pages");
}

#[test]
fn permission_bits_read_write() {
    // Permission flags: R=4, W=2, X=1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("perms", u32_ty());
    ctx.declare_var_typed("can_read", i32_ty());
    ctx.declare_var_typed("can_write", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "perms == 6")); // R|W = 4|2 = 6
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "can_read == if (perms & 4) != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cw_def",
        "can_write == if (perms & 2) != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("readable", "can_read == 1"));
    ctx.push_obligation(ProofObligation::assert("writable", "can_write == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "perms=6: readable and writable");
}

#[test]
fn tlb_hit_check() {
    let mut ctx = VerificationContext::new();
    for v in &["cached_page", "requested_page"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tlb_hit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "cached_page == 5"));
    ctx.push_obligation(ProofObligation::assume("rp", "requested_page == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "tlb_hit == if cached_page == requested_page { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("hit", "tlb_hit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TLB hit: cached=requested=5");
}

#[test]
fn multi_level_page_table_indices() {
    // Two-level: L1 index = bits 22-31, L2 index = bits 12-21
    let mut ctx = VerificationContext::new();
    for v in &["addr", "l1_idx", "l2_idx"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "addr == 4198400")); // 0x401000
    ctx.push_obligation(ProofObligation::assume(
        "l1_def",
        "l1_idx == (addr >> 22) & 1023",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "l2_def",
        "l2_idx == (addr >> 12) & 1023",
    ));
    // 0x401000 >> 22 = 0x401000/4194304 = 1
    // 0x401000 >> 12 = 0x401 = 1025; 1025 & 1023 = 1
    ctx.push_obligation(ProofObligation::assert("l1_is_1", "l1_idx == 1"));
    ctx.push_obligation(ProofObligation::assert("l2_is_1", "l2_idx == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "2-level PT: L1=1, L2=1 for 0x401000");
}

#[test]
fn page_fault_on_unmapped() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mapped", u32_ty());
    ctx.declare_var_typed("page_fault", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "mapped == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "pf_def",
        "page_fault == if mapped == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fault", "page_fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unmapped → page fault");
}

#[test]
fn dirty_bit_tracking() {
    // Write to page sets dirty bit
    let mut ctx = VerificationContext::new();
    for v in &["dirty_before", "wrote", "dirty_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("db", "dirty_before == 0"));
    ctx.push_obligation(ProofObligation::assume("w", "wrote == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "da_def",
        "dirty_after == if wrote == 1 { 1 } else { dirty_before }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_dirty", "dirty_after == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write sets dirty bit");
}
