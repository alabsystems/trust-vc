// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn transaction_id_monotonic() {
    let mut ctx = VerificationContext::new();
    for v in &["old_txn_id", "new_txn_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ot", "old_txn_id == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_txn_id == old_txn_id + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1001", "new_txn_id == 1001"));
    ctx.push_obligation(ProofObligation::assert(
        "monotonic",
        "new_txn_id > old_txn_id",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "journal: txn_id 1000 → 1001");
}

#[test]
fn journal_space_available() {
    let mut ctx = VerificationContext::new();
    for v in &["journal_size", "used_bytes", "available"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_space", i32_ty());
    ctx.push_obligation(ProofObligation::assume("js", "journal_size == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume("ub", "used_bytes == 40960"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "available == journal_size - used_bytes",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hs_def",
        "has_space == if available > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_24576", "available == 24576"));
    ctx.push_obligation(ProofObligation::assert("ok", "has_space == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "journal: 65536-40960=24576 available");
}

#[test]
fn commit_record_written() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "data_blocks_written",
        "commit_block_written",
        "total_blocks",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("db", "data_blocks_written == 5"));
    ctx.push_obligation(ProofObligation::assume("cb", "commit_block_written == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_blocks == data_blocks_written + commit_block_written",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "total_blocks == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "has_commit",
        "commit_block_written == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "journal: 5 data + 1 commit = 6 blocks");
}

#[test]
fn checkpoint_advances_tail() {
    let mut ctx = VerificationContext::new();
    for v in &["old_tail", "new_tail", "checkpointed_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ot", "old_tail == 8192"));
    ctx.push_obligation(ProofObligation::assume("cb", "checkpointed_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tail == old_tail + checkpointed_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12288", "new_tail == 12288"));
    ctx.push_obligation(ProofObligation::assert("advanced", "new_tail > old_tail"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checkpoint: tail 8192 → 12288");
}

#[test]
fn recovery_replay_count() {
    let mut ctx = VerificationContext::new();
    for v in &["committed_txns", "replayed_txns", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ct", "committed_txns == 50"));
    ctx.push_obligation(ProofObligation::assume("rt", "replayed_txns == 35"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == committed_txns - replayed_txns",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "remaining == 15"));
    ctx.push_obligation(ProofObligation::assert("progress", "replayed_txns > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "recovery: 50-35=15 txns remaining");
}

#[test]
fn journal_wrap_around() {
    let mut ctx = VerificationContext::new();
    for v in &["write_pos", "journal_size", "next_pos"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wp", "write_pos == 65530"));
    ctx.push_obligation(ProofObligation::assume("js", "journal_size == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "next_pos == (write_pos + 10) % journal_size",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_pos == 4")); // 65540 % 65536
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "journal wrap: 65530+10 mod 65536 = 4");
}

#[test]
fn ordered_journal_mode() {
    // Ordered mode: metadata journaled, data written before commit
    let mut ctx = VerificationContext::new();
    for v in &["data_write_seq", "metadata_journal_seq", "commit_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("correct_order", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dw", "data_write_seq == 1"));
    ctx.push_obligation(ProofObligation::assume("mj", "metadata_journal_seq == 2"));
    ctx.push_obligation(ProofObligation::assume("cs", "commit_seq == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "correct_order == if data_write_seq < metadata_journal_seq && metadata_journal_seq < commit_seq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "correct_order == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ordered journal: data(1) < metadata(2) < commit(3)",
    );
}

#[test]
fn revoke_record() {
    let mut ctx = VerificationContext::new();
    for v in &["revoked_blocks", "total_revokes", "new_total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rb", "revoked_blocks == 3"));
    ctx.push_obligation(ProofObligation::assume("tr", "total_revokes == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_total == total_revokes + revoked_blocks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_13", "new_total == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "journal revoke: 10+3=13 total revokes");
}

#[test]
fn descriptor_block_entries() {
    let mut ctx = VerificationContext::new();
    for v in &["block_size", "header_size", "entry_size", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Entries per descriptor block = (block_size - header_size) / entry_size
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 12"));
    ctx.push_obligation(ProofObligation::assume("es", "entry_size == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "me_def",
        "max_entries == (block_size - header_size) / entry_size",
    ));
    // (4096 - 12) / 16 = 4084 / 16 = 255
    ctx.push_obligation(ProofObligation::assert("is_255", "max_entries == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "descriptor: (4096-12)/16=255 entries");
}

#[test]
fn journal_superblock_update() {
    let mut ctx = VerificationContext::new();
    for v in &["old_sequence", "new_sequence", "old_start", "new_start"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("os", "old_sequence == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_sequence == old_sequence + 1",
    ));
    ctx.push_obligation(ProofObligation::assume("ost", "old_start == 1024"));
    ctx.push_obligation(ProofObligation::assume("nst", "new_start == 2048")); // after checkpoint
    ctx.push_obligation(ProofObligation::assert("seq_inc", "new_sequence == 501"));
    ctx.push_obligation(ProofObligation::assert(
        "start_moved",
        "new_start > old_start",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "superblock: seq 500→501, start 1024→2048");
}
