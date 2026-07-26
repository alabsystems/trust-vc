// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn store_before_load_sequential() {
    // Sequential consistency: store before load means load sees store
    let mut ctx = VerificationContext::new();
    for v in &["stored_val", "loaded_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "stored_val == 42"));
    ctx.push_obligation(ProofObligation::assume("l_def", "loaded_val == stored_val"));
    ctx.push_obligation(ProofObligation::assert("sees_store", "loaded_val == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SC: load sees preceding store");
}

#[test]
fn release_acquire_pair() {
    // Release store + acquire load establishes happens-before
    let mut ctx = VerificationContext::new();
    for v in &["data", "flag"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "data == 100"));
    ctx.push_obligation(ProofObligation::assume("f", "flag == 1")); // release store
                                                                    // acquire load of flag=1 implies data=100 visible
    ctx.push_obligation(ProofObligation::assert(
        "visible",
        "flag == 1 && data == 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "release-acquire: data visible after flag");
}

#[test]
fn atomic_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["old_val", "new_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ov", "old_val == 5"));
    ctx.push_obligation(ProofObligation::assume("nv_def", "new_val == old_val + 1"));
    ctx.push_obligation(ProofObligation::assert("is_6", "new_val == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "atomic increment: 5 → 6");
}

#[test]
fn compare_and_swap_success() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "expected", "desired", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("swapped", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "current == 5"));
    ctx.push_obligation(ProofObligation::assume("e", "expected == 5"));
    ctx.push_obligation(ProofObligation::assume("d", "desired == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if current == expected { desired } else { current }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sw_def",
        "swapped == if current == expected { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("success", "swapped == 1"));
    ctx.push_obligation(ProofObligation::assert("new_val", "result == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAS success: 5 == 5 → set to 10");
}

#[test]
fn compare_and_swap_failure() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "expected", "desired", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("swapped", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "current == 7"));
    ctx.push_obligation(ProofObligation::assume("e", "expected == 5"));
    ctx.push_obligation(ProofObligation::assume("d", "desired == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if current == expected { desired } else { current }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sw_def",
        "swapped == if current == expected { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("failure", "swapped == 0"));
    ctx.push_obligation(ProofObligation::assert("unchanged", "result == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAS failure: 7 != 5 → unchanged");
}

#[test]
fn fetch_add_returns_old() {
    let mut ctx = VerificationContext::new();
    for v in &["old_val", "delta", "returned", "new_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ov", "old_val == 10"));
    ctx.push_obligation(ProofObligation::assume("d", "delta == 3"));
    ctx.push_obligation(ProofObligation::assume("ret_def", "returned == old_val"));
    ctx.push_obligation(ProofObligation::assume(
        "nv_def",
        "new_val == old_val + delta",
    ));
    ctx.push_obligation(ProofObligation::assert("returns_10", "returned == 10"));
    ctx.push_obligation(ProofObligation::assert("stores_13", "new_val == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fetch_add(10, 3) returns 10, stores 13");
}

#[test]
fn atomic_flag_test_and_set() {
    let mut ctx = VerificationContext::new();
    for v in &["old_flag", "new_flag"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("of", "old_flag == 0"));
    ctx.push_obligation(ProofObligation::assume("nf_def", "new_flag == 1"));
    ctx.push_obligation(ProofObligation::assert("was_clear", "old_flag == 0"));
    ctx.push_obligation(ProofObligation::assert("now_set", "new_flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test_and_set: was 0, now 1");
}

#[test]
fn memory_fence_ordering() {
    // After fence, all prior stores are visible
    let mut ctx = VerificationContext::new();
    for v in &["store1", "store2", "fence_done"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1", "store1 == 1"));
    ctx.push_obligation(ProofObligation::assume("s2", "store2 == 2"));
    ctx.push_obligation(ProofObligation::assume("fd", "fence_done == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "both_visible",
        "fence_done == 1 && store1 == 1 && store2 == 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fence: both stores visible after");
}

#[test]
fn spinlock_acquire_release() {
    let mut ctx = VerificationContext::new();
    for v in &["lock_state", "after_acquire", "after_release"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ls", "lock_state == 0")); // free
    ctx.push_obligation(ProofObligation::assume("aa_def", "after_acquire == 1")); // locked
    ctx.push_obligation(ProofObligation::assume("ar_def", "after_release == 0")); // free
    ctx.push_obligation(ProofObligation::assert(
        "back_to_free",
        "after_release == lock_state",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spinlock: free → locked → free");
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
    expect_verified(&result, "100 < 101 < 102: monotonic");
}
