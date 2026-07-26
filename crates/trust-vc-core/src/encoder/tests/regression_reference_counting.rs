// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn clone_increments_refcount() {
    let mut ctx = VerificationContext::new();
    for v in &["refcount", "new_refcount"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nrc_def",
        "new_refcount == refcount + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "new_refcount == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clone: refcount 1 → 2");
}

#[test]
fn drop_decrements_refcount() {
    let mut ctx = VerificationContext::new();
    for v in &["refcount", "new_refcount"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "nrc_def",
        "new_refcount == refcount - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "new_refcount == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drop: refcount 3 → 2");
}

#[test]
fn free_at_zero_refcount() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refcount", u32_ty());
    ctx.declare_var_typed("should_free", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "should_free == if refcount == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("free", "should_free == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refcount 0 → should free");
}

#[test]
fn no_free_while_references_exist() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refcount", u32_ty());
    ctx.declare_var_typed("should_free", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "should_free == if refcount == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_free", "should_free == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refcount 2 → don't free");
}

#[test]
fn initial_refcount_is_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("initial_refcount", u32_ty());
    ctx.push_obligation(ProofObligation::assume("irc", "initial_refcount == 1"));
    ctx.push_obligation(ProofObligation::assert("is_one", "initial_refcount == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "initial refcount = 1");
}

#[test]
fn clone_then_drop_restores() {
    let mut ctx = VerificationContext::new();
    for v in &["rc_init", "rc_after_clone", "rc_after_drop"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ri", "rc_init == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rac_def",
        "rc_after_clone == rc_init + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rad_def",
        "rc_after_drop == rc_after_clone - 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "restored",
        "rc_after_drop == rc_init",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clone+drop: refcount restored to 1");
}

#[test]
fn weak_reference_no_increment() {
    // Weak refs don't increment strong count
    let mut ctx = VerificationContext::new();
    for v in &["strong_count", "weak_count", "strong_after_weak"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sc", "strong_count == 2"));
    ctx.push_obligation(ProofObligation::assume("wc", "weak_count == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "saw_def",
        "strong_after_weak == strong_count",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "unchanged",
        "strong_after_weak == 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weak ref doesn't change strong count");
}

#[test]
fn refcount_non_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refcount", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 0"));
    ctx.push_obligation(ProofObligation::assert("non_neg", "refcount >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refcount >= 0 (u32)");
}

#[test]
fn multiple_clones() {
    let mut ctx = VerificationContext::new();
    for v in &["rc", "after_3_clones"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "rc == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "a3c_def",
        "after_3_clones == rc + 3",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "after_3_clones == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 + 3 clones = refcount 4");
}

#[test]
fn exclusive_access_at_refcount_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refcount", u32_ty());
    ctx.declare_var_typed("can_get_mut", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refcount == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cgm_def",
        "can_get_mut == if refcount == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("exclusive", "can_get_mut == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refcount 1 → exclusive access (get_mut)");
}
