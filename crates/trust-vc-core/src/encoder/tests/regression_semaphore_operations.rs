// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn acquire_decrements_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "count == 3"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_count == count - 1"));
    ctx.push_obligation(ProofObligation::assert("is_2", "new_count == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "semaphore acquire: 3 → 2");
}

#[test]
fn release_increments_count() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "count == 2"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_count == count + 1"));
    ctx.push_obligation(ProofObligation::assert("is_3", "new_count == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "semaphore release: 2 → 3");
}

#[test]
fn binary_semaphore_max_one() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "max_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "count == 1"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_count == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if count <= max_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "binary semaphore: count <= 1");
}

#[test]
fn counting_semaphore_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "max_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_acquire", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "count == 0"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_count == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_acquire == if count > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("blocked", "can_acquire == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "count=0 → cannot acquire");
}

#[test]
fn mutex_lock_unlock_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["initial", "after_lock", "after_unlock"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("init", "initial == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "after_lock == initial - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "au_def",
        "after_unlock == after_lock + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "after_unlock == initial",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mutex lock-unlock restores state");
}

#[test]
fn reader_count_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["readers", "new_readers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "readers == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "nr_def",
        "new_readers == readers + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "new_readers == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rwlock: readers 3 → 4");
}

#[test]
fn writer_excludes_readers() {
    let mut ctx = VerificationContext::new();
    for v in &["readers", "writers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("w", "writers == 1"));
    ctx.push_obligation(ProofObligation::assume("r", "readers == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if writers > 0 && readers == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("exclusive", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "writer active → 0 readers");
}

#[test]
fn semaphore_count_non_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "count == 0"));
    ctx.push_obligation(ProofObligation::assert("non_neg", "count >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "semaphore count >= 0 (u32)");
}

#[test]
fn barrier_wait_count() {
    // Barrier releases when wait_count == parties
    let mut ctx = VerificationContext::new();
    for v in &["parties", "wait_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("release", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "parties == 4"));
    ctx.push_obligation(ProofObligation::assume("wc", "wait_count == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "rel_def",
        "release == if wait_count == parties { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("released", "release == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrier: 4/4 → release");
}

#[test]
fn condition_variable_spurious_wakeup() {
    // After wakeup, must re-check condition (predicate may be false)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("predicate_holds", i32_ty());
    ctx.declare_var_typed("woke_up", i32_ty());
    ctx.push_obligation(ProofObligation::assume("w", "woke_up == 1"));
    ctx.push_obligation(ProofObligation::assume("p", "predicate_holds == 0"));
    // Wakeup does NOT imply predicate
    ctx.push_obligation(ProofObligation::assert(
        "spurious",
        "woke_up == 1 && predicate_holds == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spurious wakeup: woke but predicate false");
}
