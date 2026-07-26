// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn inode_number_unique() {
    let mut ctx = VerificationContext::new();
    for v in &["inode_a", "inode_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ia", "inode_a == 100"));
    ctx.push_obligation(ProofObligation::assume("ib", "inode_b == 200"));
    ctx.push_obligation(ProofObligation::assert("unique", "inode_a != inode_b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inodes 100 and 200 are distinct");
}

#[test]
fn block_allocation_increases_used() {
    let mut ctx = VerificationContext::new();
    for v in &["used_before", "blocks_alloc", "used_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ub", "used_before == 500"));
    ctx.push_obligation(ProofObligation::assume("ba", "blocks_alloc == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ua_def",
        "used_after == used_before + blocks_alloc",
    ));
    ctx.push_obligation(ProofObligation::assert("is_510", "used_after == 510"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "block alloc: 500 + 10 = 510 used");
}

#[test]
fn directory_entry_count() {
    let mut ctx = VerificationContext::new();
    for v in &["entries", "new_entry", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("e", "entries == 15"));
    ctx.push_obligation(ProofObligation::assume("ne", "new_entry == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == entries + new_entry",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "total == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "15 entries + 1 new = 16 total");
}

#[test]
fn file_size_after_write() {
    let mut ctx = VerificationContext::new();
    for v in &["offset", "write_len", "old_size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("o", "offset == 100"));
    ctx.push_obligation(ProofObligation::assume("wl", "write_len == 50"));
    ctx.push_obligation(ProofObligation::assume("os", "old_size == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_size == if offset + write_len > old_size { offset + write_len } else { old_size }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_150", "new_size == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write at 100, len 50: new size 150");
}

#[test]
fn hard_link_count() {
    let mut ctx = VerificationContext::new();
    for v in &["link_count", "after_link", "after_unlink"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lc", "link_count == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "after_link == link_count + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "au_def",
        "after_unlink == after_link - 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "after_unlink == link_count",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "link + unlink: count restored to 1");
}

#[test]
fn free_blocks_after_delete() {
    let mut ctx = VerificationContext::new();
    for v in &["free_before", "file_blocks", "free_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fb", "free_before == 1000"));
    ctx.push_obligation(ProofObligation::assume("fblk", "file_blocks == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "free_after == free_before + file_blocks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1025", "free_after == 1025"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delete returns 25 blocks: 1000 → 1025 free");
}

#[test]
fn permission_mask_owner_read() {
    // Unix permissions: owner read = 0o400 = 256
    let mut ctx = VerificationContext::new();
    for v in &["perms", "owner_read_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("owner_can_read", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "perms == 420")); // 0o644
    ctx.push_obligation(ProofObligation::assume(
        "orb_def",
        "owner_read_bit == perms & 256",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ocr_def",
        "owner_can_read == if owner_read_bit > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("readable", "owner_can_read == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0o644: owner has read (bit 256 set in 420)");
}

#[test]
fn journal_entry_checksum() {
    // Checksum must match data for valid entry
    let mut ctx = VerificationContext::new();
    for v in &["data_sum", "stored_sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ds", "data_sum == 12345"));
    ctx.push_obligation(ProofObligation::assume("ss", "stored_sum == 12345"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if data_sum == stored_sum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "matching checksums → valid journal entry");
}

#[test]
fn path_depth() {
    // /a/b/c has depth 3
    let mut ctx = VerificationContext::new();
    for v in &["components", "depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "components == 3"));
    ctx.push_obligation(ProofObligation::assume("d_def", "depth == components"));
    ctx.push_obligation(ProofObligation::assert("is_3", "depth == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "/a/b/c: depth 3");
}

#[test]
fn extent_covers_range() {
    // Extent: [start_block, start_block + count)
    let mut ctx = VerificationContext::new();
    for v in &["start_block", "block_count", "query_block"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_extent", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sb", "start_block == 100"));
    ctx.push_obligation(ProofObligation::assume("bc", "block_count == 50"));
    ctx.push_obligation(ProofObligation::assume("qb", "query_block == 130"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "in_extent == if query_block >= start_block && query_block < start_block + block_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("inside", "in_extent == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "block 130 in extent [100, 150)");
}
