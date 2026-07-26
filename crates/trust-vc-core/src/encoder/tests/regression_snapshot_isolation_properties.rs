// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn snapshot_reads_consistent_version() {
    let mut ctx = VerificationContext::new();
    for v in &["snapshot_version", "read_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sv", "snapshot_version == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "read_version == snapshot_version",
    ));
    ctx.push_obligation(ProofObligation::assert("consistent", "read_version == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "snapshot read: version 42 consistently");
}

#[test]
fn write_creates_new_version() {
    let mut ctx = VerificationContext::new();
    for v in &["current_version", "new_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cv", "current_version == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "nv_def",
        "new_version == current_version + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_43", "new_version == 43"));
    ctx.push_obligation(ProofObligation::assert(
        "newer",
        "new_version > current_version",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write: version 42 → 43");
}

#[test]
fn write_write_conflict_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["txn_a_start", "txn_b_start", "txn_a_write_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conflict", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tas", "txn_a_start == 10"));
    ctx.push_obligation(ProofObligation::assume("tbs", "txn_b_start == 10")); // same snapshot
    ctx.push_obligation(ProofObligation::assume("taw", "txn_a_write_version == 11")); // A committed first
                                                                                      // B tries to commit: conflict if someone wrote after B's snapshot
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "conflict == if txn_a_write_version > txn_b_start { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("has_conflict", "conflict == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WW conflict: A wrote v11 > B's snapshot v10");
}

#[test]
fn read_set_tracks_versions() {
    let mut ctx = VerificationContext::new();
    for v in &["reads_count", "new_read", "total_reads"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rc", "reads_count == 5"));
    ctx.push_obligation(ProofObligation::assume("nr", "new_read == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "total_reads == reads_count + new_read",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "total_reads == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "read set: 5 + 1 = 6 tracked reads");
}

#[test]
fn mvcc_version_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["v1", "v2", "v3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ver1", "v1 == 10"));
    ctx.push_obligation(ProofObligation::assume("ver2", "v2 == 20"));
    ctx.push_obligation(ProofObligation::assume("ver3", "v3 == 30"));
    ctx.push_obligation(ProofObligation::assert("chain", "v1 < v2 && v2 < v3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MVCC chain: v10 < v20 < v30");
}

#[test]
fn garbage_collect_old_versions() {
    let mut ctx = VerificationContext::new();
    for v in &["total_versions", "active_snapshots_min", "reclaimable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tv", "total_versions == 100"));
    ctx.push_obligation(ProofObligation::assume("asm", "active_snapshots_min == 30")); // oldest active snapshot
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "reclaimable == active_snapshots_min",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "reclaimable == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "partial",
        "reclaimable < total_versions",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GC: 30 versions reclaimable < 100 total");
}

#[test]
fn serializable_check() {
    // Transactions are serializable if their dependency graph is acyclic
    // Simplified: no WW + no WR conflict
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ww_conflict", i32_ty());
    ctx.declare_var_typed("wr_conflict", i32_ty());
    ctx.declare_var_typed("serializable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ww", "ww_conflict == 0"));
    ctx.push_obligation(ProofObligation::assume("wr", "wr_conflict == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "serializable == if ww_conflict == 0 && wr_conflict == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_serial", "serializable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "no WW + no WR → serializable");
}

#[test]
fn timestamp_ordering() {
    let mut ctx = VerificationContext::new();
    for v in &["begin_ts", "commit_ts"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_ordering", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bt", "begin_ts == 100"));
    ctx.push_obligation(ProofObligation::assume("ct", "commit_ts == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_ordering == if commit_ts > begin_ts { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_ordering == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "commit 150 > begin 100 → valid ordering");
}

#[test]
fn phantom_read_prevention() {
    // Snapshot isolation prevents phantom reads: count at snapshot is fixed
    let mut ctx = VerificationContext::new();
    for v in &["count_at_snapshot", "count_reread"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cas", "count_at_snapshot == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "count_reread == count_at_snapshot",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "same",
        "count_reread == count_at_snapshot",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "snapshot isolation: re-read count unchanged");
}

#[test]
fn write_set_size_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["writes_before", "new_writes", "total_writes", "max_writes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wb", "writes_before == 45"));
    ctx.push_obligation(ProofObligation::assume("nw", "new_writes == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_writes == writes_before + new_writes",
    ));
    ctx.push_obligation(ProofObligation::assume("mw", "max_writes == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if total_writes <= max_writes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write set: 45+5=50 <= 100 limit");
}
