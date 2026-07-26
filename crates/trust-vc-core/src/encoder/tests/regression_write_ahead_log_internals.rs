// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lsn_monotonic_after_append() {
    let mut ctx = VerificationContext::new();
    for v in &["old_lsn", "record_size", "new_lsn"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ol", "old_lsn == 1000"));
    ctx.push_obligation(ProofObligation::assume("rs", "record_size == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "nl_def",
        "new_lsn == old_lsn + record_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1128", "new_lsn == 1128"));
    ctx.push_obligation(ProofObligation::assert("monotonic", "new_lsn > old_lsn"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WAL LSN: 1000 + 128 = 1128 (monotonic)");
}

#[test]
fn record_header_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["header_size", "payload_size", "total_record_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 16")); // type + length + checksum + timestamp
    ctx.push_obligation(ProofObligation::assume("ps", "payload_size == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "trs_def",
        "total_record_size == header_size + payload_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_116",
        "total_record_size == 116",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WAL record: 16 header + 100 payload = 116 bytes");
}

#[test]
fn checkpoint_advances_horizon() {
    let mut ctx = VerificationContext::new();
    for v in &["old_checkpoint_lsn", "new_checkpoint_lsn", "reclaimable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ocl", "old_checkpoint_lsn == 5000"));
    ctx.push_obligation(ProofObligation::assume("ncl", "new_checkpoint_lsn == 8000"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "reclaimable == new_checkpoint_lsn - old_checkpoint_lsn",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3000", "reclaimable == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "advanced",
        "new_checkpoint_lsn > old_checkpoint_lsn",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checkpoint: 8000-5000 = 3000 bytes reclaimable");
}

#[test]
fn segment_rotation() {
    let mut ctx = VerificationContext::new();
    for v in &["current_offset", "segment_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_rotation", i32_ty());
    ctx.push_obligation(ProofObligation::assume("co", "current_offset == 65000"));
    ctx.push_obligation(ProofObligation::assume("ss", "segment_size == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume(
        "nr_def",
        "needs_rotation == if current_offset >= segment_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "needs_rotation == 0")); // 65000 < 65536
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "segment: 65000 < 65536 → no rotation needed");
}

#[test]
fn redo_log_apply() {
    let mut ctx = VerificationContext::new();
    for v in &["old_value", "redo_delta", "new_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ov", "old_value == 100"));
    ctx.push_obligation(ProofObligation::assume("rd", "redo_delta == 50")); // add 50
    ctx.push_obligation(ProofObligation::assume(
        "nv_def",
        "new_value == old_value + redo_delta",
    ));
    ctx.push_obligation(ProofObligation::assert("is_150", "new_value == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "redo: 100 + 50 = 150");
}

#[test]
fn undo_log_rollback() {
    let mut ctx = VerificationContext::new();
    for v in &["current_value", "undo_value", "rolled_back"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cv", "current_value == 150"));
    ctx.push_obligation(ProofObligation::assume("uv", "undo_value == 100")); // saved before-image
    ctx.push_obligation(ProofObligation::assume(
        "rb_def",
        "rolled_back == undo_value",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "rolled_back == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "rolled_back != current_value",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "undo: rollback to 100 (was 150)");
}

#[test]
fn group_commit_batching() {
    let mut ctx = VerificationContext::new();
    for v in &["individual_flushes", "batch_size", "batched_flushes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume(
        "if_val",
        "individual_flushes == 100",
    ));
    ctx.push_obligation(ProofObligation::assume("bs", "batch_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "bf_def",
        "batched_flushes == individual_flushes / batch_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "batched_flushes == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "batched_flushes < individual_flushes",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "group commit: 100/10 = 10 batched flushes");
}

#[test]
fn tail_position_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["write_offset", "record_size", "new_tail"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wo", "write_offset == 4000"));
    ctx.push_obligation(ProofObligation::assume("rs", "record_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tail == write_offset + record_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4256", "new_tail == 4256"));
    ctx.push_obligation(ProofObligation::assert(
        "advanced",
        "new_tail > write_offset",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WAL tail: 4000 + 256 = 4256");
}

#[test]
fn truncation_frees_space() {
    let mut ctx = VerificationContext::new();
    for v in &["total_log_size", "checkpoint_lsn", "active_size", "freed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tls", "total_log_size == 100000"));
    ctx.push_obligation(ProofObligation::assume("cl", "checkpoint_lsn == 40000"));
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "active_size == total_log_size - checkpoint_lsn",
    ));
    ctx.push_obligation(ProofObligation::assume("f_def", "freed == checkpoint_lsn"));
    ctx.push_obligation(ProofObligation::assert(
        "active_60000",
        "active_size == 60000",
    ));
    ctx.push_obligation(ProofObligation::assert("freed_40000", "freed == 40000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "truncation: 40000 freed, 60000 active");
}

#[test]
fn checksum_coverage() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "header_bytes",
        "payload_bytes",
        "checksum_bytes",
        "total_checksummed",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 12")); // excluding checksum field
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 200"));
    ctx.push_obligation(ProofObligation::assume("cb", "checksum_bytes == 4")); // CRC32
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_checksummed == header_bytes + payload_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_212",
        "total_checksummed == 212",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checksum: covers 12 + 200 = 212 bytes");
}
