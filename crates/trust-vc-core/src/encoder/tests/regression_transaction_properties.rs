// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn commit_preserves_balance_sum() {
    // Transfer: source decreases, dest increases, total unchanged
    let mut ctx = VerificationContext::new();
    for v in &[
        "src_before",
        "dst_before",
        "amount",
        "src_after",
        "dst_after",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "src_before == 100"));
    ctx.push_obligation(ProofObligation::assume("db", "dst_before == 50"));
    ctx.push_obligation(ProofObligation::assume("a", "amount == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "src_after == src_before - amount",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "da_def",
        "dst_after == dst_before + amount",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sum_preserved",
        "src_after + dst_after == src_before + dst_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transfer preserves total: 70+80 = 100+50");
}

#[test]
fn rollback_restores_state() {
    let mut ctx = VerificationContext::new();
    for v in &["before", "during", "after_rollback"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b", "before == 42"));
    ctx.push_obligation(ProofObligation::assume("d", "during == 99"));
    ctx.push_obligation(ProofObligation::assume(
        "ar_def",
        "after_rollback == before",
    )); // restore
    ctx.push_obligation(ProofObligation::assert("restored", "after_rollback == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rollback restores original value 42");
}

#[test]
fn isolation_no_dirty_read() {
    // Uncommitted writes invisible to other transactions
    let mut ctx = VerificationContext::new();
    for v in &["committed_val", "uncommitted_val", "read_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cv", "committed_val == 10"));
    ctx.push_obligation(ProofObligation::assume("uv", "uncommitted_val == 99"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "read_val == committed_val",
    )); // reads committed
    ctx.push_obligation(ProofObligation::assert("no_dirty", "read_val == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "isolation: read sees committed 10, not 99");
}

#[test]
fn wal_write_before_data() {
    // WAL: log sequence number advances before data write
    let mut ctx = VerificationContext::new();
    for v in &["log_lsn", "data_lsn"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ll", "log_lsn == 101"));
    ctx.push_obligation(ProofObligation::assume("dl", "data_lsn == 100"));
    ctx.push_obligation(ProofObligation::assert("ahead", "log_lsn > data_lsn"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WAL: log LSN 101 > data LSN 100");
}

#[test]
fn serializable_order() {
    // Transactions produce same result as some serial order
    let mut ctx = VerificationContext::new();
    for v in &["x_init", "x_after_t1", "x_after_t2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("xi", "x_init == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "at1_def",
        "x_after_t1 == x_init + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "at2_def",
        "x_after_t2 == x_after_t1 + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("serial_result", "x_after_t2 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "serial order: T1 then T2 → x = 2");
}

#[test]
fn mvcc_version_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["v1", "v2", "v3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v1_val", "v1 == 10"));
    ctx.push_obligation(ProofObligation::assume("v2_val", "v2 == 20"));
    ctx.push_obligation(ProofObligation::assume("v3_val", "v3 == 30"));
    ctx.push_obligation(ProofObligation::assert("chain", "v1 < v2 && v2 < v3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MVCC version chain: 10 < 20 < 30");
}

#[test]
fn two_phase_commit_all_agree() {
    let mut ctx = VerificationContext::new();
    for v in &["votes_yes", "total_participants"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_commit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vy", "votes_yes == 3"));
    ctx.push_obligation(ProofObligation::assume("tp", "total_participants == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "can_commit == if votes_yes == total_participants { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("commit", "can_commit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2PC: 3/3 vote yes → can commit");
}

#[test]
fn two_phase_commit_one_no() {
    let mut ctx = VerificationContext::new();
    for v in &["votes_yes", "total_participants"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_commit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vy", "votes_yes == 2"));
    ctx.push_obligation(ProofObligation::assume("tp", "total_participants == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "can_commit == if votes_yes == total_participants { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("abort", "can_commit == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2PC: 2/3 vote yes → must abort");
}

#[test]
fn snapshot_isolation_read_timestamp() {
    let mut ctx = VerificationContext::new();
    for v in &["snapshot_ts", "write_ts"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("visible", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "snapshot_ts == 100"));
    ctx.push_obligation(ProofObligation::assume("wt", "write_ts == 90")); // before snapshot
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "visible == if write_ts <= snapshot_ts { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_visible", "visible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write at 90 visible at snapshot 100");
}

#[test]
fn deadlock_detection_cycle() {
    // Cycle: T1 waits for T2, T2 waits for T1
    let mut ctx = VerificationContext::new();
    for v in &["t1_waits_for", "t2_waits_for"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_cycle", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tw1", "t1_waits_for == 2")); // T1→T2
    ctx.push_obligation(ProofObligation::assume("tw2", "t2_waits_for == 1")); // T2→T1
    ctx.push_obligation(ProofObligation::assume(
        "hc_def",
        "has_cycle == if t1_waits_for == 2 && t2_waits_for == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cycle", "has_cycle == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deadlock: T1→T2→T1 cycle detected");
}
