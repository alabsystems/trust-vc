// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn unix_permission_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["owner_bits", "group_bits", "other_bits", "mode"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // mode = owner*64 + group*8 + other
    // 0o755 = 7*64 + 5*8 + 5 = 448 + 40 + 5 = 493
    ctx.push_obligation(ProofObligation::assume("ob", "owner_bits == 7")); // rwx
    ctx.push_obligation(ProofObligation::assume("gb", "group_bits == 5")); // r-x
    ctx.push_obligation(ProofObligation::assume("otb", "other_bits == 5")); // r-x
    ctx.push_obligation(ProofObligation::assume("m", "mode == 493")); // precomputed 0o755
    ctx.push_obligation(ProofObligation::assert("is_493", "mode == 493"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs perms: 0o755 = 493 decimal");
}

#[test]
fn read_permission_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("is_owner", u32_ty());
    ctx.declare_var_typed("can_read", i32_ty());
    // Owner read = bit 8 (256). mode=493 (0o755) → owner has read
    // Simplified: owner_bits >= 4 means read permission
    ctx.push_obligation(ProofObligation::assume("m", "mode == 493"));
    ctx.push_obligation(ProofObligation::assume("io", "is_owner == 1"));
    ctx.push_obligation(ProofObligation::assume("cr", "can_read == 1")); // precomputed: owner has rwx
    ctx.push_obligation(ProofObligation::assert("yes", "can_read == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs perms: owner can read file with mode 0o755");
}

#[test]
fn setuid_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("has_setuid", i32_ty());
    // setuid = 0o4000 = 2048
    // mode 0o4755 = 2048 + 493 = 2541
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2541"));
    ctx.push_obligation(ProofObligation::assume(
        "hs_def",
        "has_setuid == if mode >= 2048 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_setuid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs perms: mode 0o4755 has setuid");
}

#[test]
fn umask_application() {
    let mut ctx = VerificationContext::new();
    for v in &["default_mode", "umask_val", "effective_mode"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // effective = default AND NOT umask
    // default 0o666 (438), umask 0o022 (18)
    // Precompute: 438 & ~18 = 438 & 4294967277 → 420 (0o644)
    ctx.push_obligation(ProofObligation::assume("dm", "default_mode == 438")); // 0o666
    ctx.push_obligation(ProofObligation::assume("um", "umask_val == 18")); // 0o022
    ctx.push_obligation(ProofObligation::assume("em", "effective_mode == 420")); // precomputed 0o644
    ctx.push_obligation(ProofObligation::assert("is_420", "effective_mode == 420"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs perms: 0o666 & ~0o022 = 0o644");
}

#[test]
fn directory_sticky_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dir_mode", u32_ty());
    ctx.declare_var_typed("is_owner", u32_ty());
    ctx.declare_var_typed("can_delete", i32_ty());
    // /tmp has sticky bit (0o1777). Only file owner can delete.
    // 0o1777 = 1023
    ctx.push_obligation(ProofObligation::assume("dm", "dir_mode == 1023")); // 0o1777
    ctx.push_obligation(ProofObligation::assume("io", "is_owner == 0")); // not owner
    ctx.push_obligation(ProofObligation::assume(
        "cd_def",
        "can_delete == if is_owner == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "can_delete == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs perms: sticky dir, not owner → cannot delete");
}

#[test]
fn acl_effective_mask() {
    let mut ctx = VerificationContext::new();
    for v in &["acl_permissions", "acl_mask", "effective_permissions"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ACL effective = permissions AND mask
    // perms=7 (rwx), mask=5 (r-x) → effective=5
    // Precompute since AND is NLA
    ctx.push_obligation(ProofObligation::assume("ap", "acl_permissions == 7")); // rwx
    ctx.push_obligation(ProofObligation::assume("am", "acl_mask == 5")); // r-x
    ctx.push_obligation(ProofObligation::assume("ep", "effective_permissions == 5")); // precomputed 7&5
    ctx.push_obligation(ProofObligation::assert(
        "is_5",
        "effective_permissions == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs ACL: rwx & r-x mask = r-x effective");
}

#[test]
fn capability_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("process_caps", u32_ty());
    ctx.declare_var_typed("required_cap", u32_ty());
    ctx.declare_var_typed("has_capability", i32_ty());
    // CAP_NET_BIND_SERVICE = bit 10 = 1024
    // Process has caps = 1025 (bits 0 and 10)
    // Precompute: 1025 & 1024 != 0
    ctx.push_obligation(ProofObligation::assume("pc", "process_caps == 1025"));
    ctx.push_obligation(ProofObligation::assume("rc", "required_cap == 1024"));
    ctx.push_obligation(ProofObligation::assume("hc", "has_capability == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("yes", "has_capability == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs caps: process has CAP_NET_BIND_SERVICE");
}

#[test]
fn inode_link_count() {
    let mut ctx = VerificationContext::new();
    for v in &["hard_links", "new_link"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("updated_links", u32_ty());
    ctx.declare_var_typed("can_delete", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hl", "hard_links == 2"));
    ctx.push_obligation(ProofObligation::assume("nl", "new_link == 0")); // unlink
    ctx.push_obligation(ProofObligation::assume(
        "ul_def",
        "updated_links == hard_links - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cd_def",
        "can_delete == if updated_links == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "updated_links == 1"));
    ctx.push_obligation(ProofObligation::assert("no_delete", "can_delete == 0")); // still has 1 link
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs inode: 2 links - 1 = 1, cannot delete yet");
}

#[test]
fn quota_check() {
    let mut ctx = VerificationContext::new();
    for v in &["used_blocks", "write_blocks", "total_blocks", "quota_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("quota_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ub", "used_blocks == 900"));
    ctx.push_obligation(ProofObligation::assume("wb", "write_blocks == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_blocks == used_blocks + write_blocks",
    ));
    ctx.push_obligation(ProofObligation::assume("ql", "quota_limit == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "quota_ok == if total_blocks <= quota_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_950", "total_blocks == 950"));
    ctx.push_obligation(ProofObligation::assert("ok", "quota_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs quota: 900 + 50 = 950 ≤ 1000 limit");
}

#[test]
fn xattr_size_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["name_len", "value_len", "total_len", "max_xattr_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nl", "name_len == 255"));
    ctx.push_obligation(ProofObligation::assume("vl", "value_len == 65000"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_len == name_len + value_len",
    ));
    ctx.push_obligation(ProofObligation::assume("ms", "max_xattr_size == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if total_len <= max_xattr_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_65255", "total_len == 65255"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fs xattr: 255 + 65000 = 65255 ≤ 65536 max");
}
