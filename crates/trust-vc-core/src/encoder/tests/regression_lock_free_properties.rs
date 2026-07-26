// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cas_success_updates_value() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "expected", "desired", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "current == 10"));
    ctx.push_obligation(ProofObligation::assume("e", "expected == 10"));
    ctx.push_obligation(ProofObligation::assume("d", "desired == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if current == expected { desired } else { current }",
    ));
    ctx.push_obligation(ProofObligation::assert("updated", "result == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAS: current==expected → write desired");
}

#[test]
fn cas_failure_preserves_value() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "expected", "desired", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "current == 10"));
    ctx.push_obligation(ProofObligation::assume("e", "expected == 5")); // mismatch
    ctx.push_obligation(ProofObligation::assume("d", "desired == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if current == expected { desired } else { current }",
    ));
    ctx.push_obligation(ProofObligation::assert("unchanged", "result == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAS: current!=expected → keep current");
}

#[test]
fn fetch_add_returns_old() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "add_amount", "old_val", "new_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 100"));
    ctx.push_obligation(ProofObligation::assume("aa", "add_amount == 5"));
    ctx.push_obligation(ProofObligation::assume("ov_def", "old_val == val"));
    ctx.push_obligation(ProofObligation::assume(
        "nv_def",
        "new_val == val + add_amount",
    ));
    ctx.push_obligation(ProofObligation::assert("old_is_100", "old_val == 100"));
    ctx.push_obligation(ProofObligation::assert("new_is_105", "new_val == 105"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fetch_add: returns 100, stores 105");
}

#[test]
fn atomic_increment_linearizable() {
    // Two increments: final = initial + 2
    let mut ctx = VerificationContext::new();
    for v in &["initial", "after_inc1", "after_inc2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i", "initial == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ai1_def",
        "after_inc1 == initial + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ai2_def",
        "after_inc2 == after_inc1 + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "after_inc2 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two atomic increments: 0 → 1 → 2");
}

#[test]
fn spin_lock_acquire_release() {
    let mut ctx = VerificationContext::new();
    for v in &["lock_state", "after_acquire", "after_release"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ls", "lock_state == 0")); // free
    ctx.push_obligation(ProofObligation::assume("aa_def", "after_acquire == 1")); // locked
    ctx.push_obligation(ProofObligation::assume("ar_def", "after_release == 0")); // free
    ctx.push_obligation(ProofObligation::assert(
        "cycle",
        "after_release == lock_state",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lock: free → acquired → free");
}

#[test]
fn ticket_lock_ordering() {
    // ticket lock: next_ticket > current_ticket means queue not empty
    let mut ctx = VerificationContext::new();
    for v in &["current_ticket", "next_ticket", "waiting"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ct", "current_ticket == 5"));
    ctx.push_obligation(ProofObligation::assume("nt", "next_ticket == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "w_def",
        "waiting == next_ticket - current_ticket",
    ));
    ctx.push_obligation(ProofObligation::assert("has_waiters", "waiting == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ticket lock: 3 waiters (8 - 5)");
}

#[test]
fn sequence_number_monotonic() {
    let mut ctx = VerificationContext::new();
    for v in &["seq1", "seq2", "seq3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1", "seq1 == 100"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "seq2 == seq1 + 1"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "seq3 == seq2 + 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mono",
        "seq1 < seq2 && seq2 < seq3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sequence numbers: 100 < 101 < 102");
}

#[test]
fn epoch_based_reclamation_guard() {
    // Can only free when all threads past epoch
    let mut ctx = VerificationContext::new();
    for v in &["global_epoch", "thread_epoch", "retire_epoch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("safe_to_free", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ge", "global_epoch == 5"));
    ctx.push_obligation(ProofObligation::assume("te", "thread_epoch == 5")); // caught up
    ctx.push_obligation(ProofObligation::assume("re", "retire_epoch == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "stf_def",
        "safe_to_free == if thread_epoch > retire_epoch { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("safe", "safe_to_free == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thread epoch 5 > retire epoch 3 → safe to free");
}

#[test]
fn hazard_pointer_protection() {
    // Object protected if any hazard pointer points to it
    let mut ctx = VerificationContext::new();
    for v in &["obj_addr", "hp1", "hp2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("protected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oa", "obj_addr == 1000"));
    ctx.push_obligation(ProofObligation::assume("h1", "hp1 == 1000")); // points to obj
    ctx.push_obligation(ProofObligation::assume("h2", "hp2 == 2000")); // points elsewhere
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "protected == if hp1 == obj_addr || hp2 == obj_addr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_protected", "protected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hazard pointer protects object at 1000");
}

#[test]
fn backoff_exponential() {
    // Exponential backoff: delay doubles each retry
    let mut ctx = VerificationContext::new();
    for v in &["base_delay", "retry", "delay"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bd", "base_delay == 1"));
    ctx.push_obligation(ProofObligation::assume("r", "retry == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "delay == base_delay << retry",
    ));
    // 1 << 3 = 8
    ctx.push_obligation(ProofObligation::assert("is_8", "delay == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "exponential backoff: retry 3 → delay 8");
}
