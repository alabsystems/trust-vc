// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cdb_opcode_group() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opcode", u32_ty());
    ctx.declare_var_typed("cdb_length", u32_ty());
    ctx.declare_var_typed("is_6byte", i32_ty());
    // SCSI CDB: opcodes 0x00-0x1F are 6-byte commands (group 0)
    ctx.push_obligation(ProofObligation::assume("op", "opcode == 18")); // INQUIRY = 0x12
    ctx.push_obligation(ProofObligation::assume("cl", "cdb_length == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "i6_def",
        "is_6byte == if opcode <= 31 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_6byte == 1"));
    ctx.push_obligation(ProofObligation::assert("len", "cdb_length == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: opcode 0x12 ≤ 0x1F → 6-byte CDB");
}

#[test]
fn sense_key_check_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sense_key", u32_ty());
    ctx.declare_var_typed("is_medium_error", i32_ty());
    // Sense key 3 = MEDIUM ERROR
    ctx.push_obligation(ProofObligation::assume("sk", "sense_key == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ime_def",
        "is_medium_error == if sense_key == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_medium_error == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: sense key 3 = MEDIUM ERROR");
}

#[test]
fn lun_addressing() {
    let mut ctx = VerificationContext::new();
    for v in &["lun_id", "max_luns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_lun", i32_ty());
    // LUN range: 0 to max_luns-1
    ctx.push_obligation(ProofObligation::assume("li", "lun_id == 5"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_luns == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_lun == if lun_id < max_luns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_lun == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: LUN 5 < 256 max → valid");
}

#[test]
fn transfer_length_blocks() {
    let mut ctx = VerificationContext::new();
    for v in &["requested_blocks", "max_transfer_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    // Maximum transfer length check
    ctx.push_obligation(ProofObligation::assume("rb", "requested_blocks == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "mtb",
        "max_transfer_blocks == 65535",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if requested_blocks <= max_transfer_blocks { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: 1024 blocks ≤ 65535 max → within limit");
}

#[test]
fn queue_tag_assignment() {
    let mut ctx = VerificationContext::new();
    for v in &["active_tags", "max_tags"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("next_tag", u32_ty());
    ctx.declare_var_typed("tag_available", i32_ty());
    ctx.push_obligation(ProofObligation::assume("at", "active_tags == 63"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tags == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "next_tag == active_tags + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ta_def",
        "tag_available == if active_tags < max_tags { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "next_tag == 64"));
    ctx.push_obligation(ProofObligation::assert("yes", "tag_available == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: 63 active < 256 max → tag 64 available");
}

#[test]
fn reservation_conflict() {
    let mut ctx = VerificationContext::new();
    for v in &["reservation_holder", "requesting_initiator"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conflict", i32_ty());
    // Persistent reservation: conflict if different initiator
    ctx.push_obligation(ProofObligation::assume("rh", "reservation_holder == 1"));
    ctx.push_obligation(ProofObligation::assume("ri", "requesting_initiator == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "conflict == if reservation_holder != requesting_initiator { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "conflict == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SCSI: initiator 2 ≠ holder 1 → reservation conflict",
    );
}

#[test]
fn vpd_page_length() {
    let mut ctx = VerificationContext::new();
    for v in &["page_header_bytes", "data_bytes", "total_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // VPD page total = header (4 bytes) + data
    ctx.push_obligation(ProofObligation::assume("ph", "page_header_bytes == 4"));
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_length == page_header_bytes + data_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "total_length == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI VPD: 4 header + 60 data = 64 total bytes");
}

#[test]
fn mode_page_select() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("page_code", u32_ty());
    ctx.declare_var_typed("is_caching", i32_ty());
    ctx.declare_var_typed("is_control", i32_ty());
    // Mode page 0x08 = Caching, 0x0A = Control
    ctx.push_obligation(ProofObligation::assume("pc", "page_code == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_caching == if page_code == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ico_def",
        "is_control == if page_code == 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("caching", "is_caching == 1"));
    ctx.push_obligation(ProofObligation::assert("not_control", "is_control == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: page code 0x08 → caching, not control");
}

#[test]
fn task_management_abort() {
    let mut ctx = VerificationContext::new();
    for v in &["task_tag", "abort_tag"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("match_found", i32_ty());
    // ABORT TASK: find matching tag
    ctx.push_obligation(ProofObligation::assume("tt", "task_tag == 42"));
    ctx.push_obligation(ProofObligation::assume("at", "abort_tag == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "mf_def",
        "match_found == if task_tag == abort_tag { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "match_found == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: abort tag 42 matches task tag 42");
}

#[test]
fn inquiry_allocation_length() {
    let mut ctx = VerificationContext::new();
    for v in &["alloc_length", "min_inquiry_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    // Standard INQUIRY needs at least 36 bytes
    ctx.push_obligation(ProofObligation::assume("al", "alloc_length == 96"));
    ctx.push_obligation(ProofObligation::assume("mil", "min_inquiry_length == 36"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if alloc_length >= min_inquiry_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCSI: alloc 96 ≥ 36 min inquiry → sufficient");
}
