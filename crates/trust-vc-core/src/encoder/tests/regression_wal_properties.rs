// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lsn_monotonically_increases() {
    let mut ctx = VerificationContext::new();
    for v in &["lsn1", "lsn2", "lsn3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l1", "lsn1 == 1000"));
    ctx.push_obligation(ProofObligation::assume("l2_def", "lsn2 == lsn1 + 1"));
    ctx.push_obligation(ProofObligation::assume("l3_def", "lsn3 == lsn2 + 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mono",
        "lsn1 < lsn2 && lsn2 < lsn3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LSN: 1000 < 1001 < 1002");
}

#[test]
fn log_record_size_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["header_size", "data_size", "total_size", "max_record"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 16"));
    ctx.push_obligation(ProofObligation::assume("ds", "data_size == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_size == header_size + data_size",
    ));
    ctx.push_obligation(ProofObligation::assume("mr", "max_record == 4096"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "total_size <= max_record",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "log record: 16 + 100 = 116 <= 4096 max");
}

#[test]
fn checkpoint_advances_log() {
    let mut ctx = VerificationContext::new();
    for v in &["old_checkpoint", "new_checkpoint"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_checkpoint == 500"));
    ctx.push_obligation(ProofObligation::assume("nc", "new_checkpoint == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "advances",
        "new_checkpoint > old_checkpoint",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checkpoint: 500 → 800");
}

#[test]
fn log_segment_rotation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "segment_size",
        "max_segment",
        "segment_number",
        "new_segment",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_rotation", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ss", "segment_size == 1048576")); // 1MB
    ctx.push_obligation(ProofObligation::assume("ms", "max_segment == 1048576"));
    ctx.push_obligation(ProofObligation::assume("sn", "segment_number == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "nr_def",
        "needs_rotation == if segment_size >= max_segment { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_segment == segment_number + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("rotate", "needs_rotation == 1"));
    ctx.push_obligation(ProofObligation::assert("next_seg", "new_segment == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "segment 5 full → rotate to segment 6");
}

#[test]
fn redo_log_after_crash() {
    // Redo applies committed but unflushed changes
    let mut ctx = VerificationContext::new();
    for v in &["committed_lsn", "flushed_lsn", "redo_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cl", "committed_lsn == 100"));
    ctx.push_obligation(ProofObligation::assume("fl", "flushed_lsn == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "redo_count == committed_lsn - flushed_lsn",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "redo_count == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "redo: 100 committed - 90 flushed = 10 to redo");
}

#[test]
fn undo_log_before_modify() {
    let mut ctx = VerificationContext::new();
    for v in &["old_value", "undo_record"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ov", "old_value == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ur_def",
        "undo_record == old_value",
    ));
    ctx.push_obligation(ProofObligation::assert("saved", "undo_record == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "undo log saves old value 42");
}

#[test]
fn log_tail_position() {
    let mut ctx = VerificationContext::new();
    for v in &["log_start", "records_written", "tail_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ls", "log_start == 0"));
    ctx.push_obligation(ProofObligation::assume("rw", "records_written == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "tail_position == log_start + records_written",
    ));
    ctx.push_obligation(ProofObligation::assert("is_250", "tail_position == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "log tail: 0 + 250 = position 250");
}

#[test]
fn truncation_frees_space() {
    let mut ctx = VerificationContext::new();
    for v in &["total_records", "truncated", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tr", "total_records == 1000"));
    ctx.push_obligation(ProofObligation::assume("t", "truncated == 700")); // before checkpoint
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == total_records - truncated",
    ));
    ctx.push_obligation(ProofObligation::assert("is_300", "remaining == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "truncate: 1000 - 700 = 300 remaining");
}

#[test]
fn group_commit_batches() {
    let mut ctx = VerificationContext::new();
    for v in &["pending_commits", "batch_size", "batches"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pc", "pending_commits == 50"));
    ctx.push_obligation(ProofObligation::assume("bs", "batch_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "batches == pending_commits / batch_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "batches == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "group commit: 50 / 10 = 5 batches");
}

#[test]
fn fsync_durability_guarantee() {
    let mut ctx = VerificationContext::new();
    for v in &["written_lsn", "synced_lsn"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("durable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "written_lsn == 100"));
    ctx.push_obligation(ProofObligation::assume("sl", "synced_lsn == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "durable == if synced_lsn >= written_lsn { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_durable", "durable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "synced LSN == written LSN → durable");
}
