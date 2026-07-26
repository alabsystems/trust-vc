//! Overflow checking coordination, soundness guards, and double-parse
//! regression tests for assertion.rs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from verification_orchestration/mod.rs (#2145).

use super::*;
use crate::encoder::verification::test_hooks::FORCE_OVERFLOW_PRECHECK_DEMOTION;

// ============================================================
// assertion.rs: Overflow checking coordination
// ============================================================

/// Assertion with overflow checks present: verify that arithmetic overflow
/// is detected when check_overflow is enabled.
///
/// Tests the overflow checking coordination in verify_single_assertion_inner
/// (assertion.rs:101-163): resolve_condition_with_overflow discovers overflow
/// predicates, each is verified with a fresh encoder, and overflow failure
/// produces a Counterexample.
#[test]
fn test_assertion_overflow_check_detects_overflow() {
    let ctx = VerificationContext::new().with_overflow_checks();
    let mut ctx = ctx;
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Assume x is at i32::MAX, then assert x + 1 > x.
    // With overflow checking enabled, x + 1 overflows i32 and should be caught.
    ctx.push_obligation(ProofObligation::assume("at_max", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("overflow_sum", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Overflow check should catch i32::MAX + 1 overflow");
    // If it's a counterexample, verify the obligation name mentions overflow
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert!(
            obligation_name.contains("overflow") || obligation_name.contains("overflow_sum"),
            "Obligation name should reference overflow, got: {}",
            obligation_name
        );
    }
}

/// Assertion with overflow checks enabled but no actual overflow: normal
/// verification should succeed after overflow checks pass.
///
/// Tests the happy path through assertion.rs:133-163 where overflow_checks
/// is non-empty but all checks pass, then verify_assertion_with_timeout
/// is called for the main assertion.
#[test]
fn test_assertion_overflow_check_passes_then_assertion_verified() {
    let ctx = VerificationContext::new().with_overflow_checks();
    let mut ctx = ctx;
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("small_x", "x == 5"));
    // x + 1 does not overflow when x == 5, so the overflow check passes,
    // and then the main assertion x + 1 == 6 should be verified.
    ctx.push_obligation(ProofObligation::assert("safe_add", "x + 1 == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x + 1 == 6 with x == 5 should verify after overflow check passes",
    );
}

/// Assertion without overflow checks: the overflow checking phase is skipped
/// entirely (overflow_checks is empty), and only verify_assertion_with_timeout
/// runs.
///
/// Control test for the above two — verifies the no-overflow-checks path
/// in assertion.rs where overflow_checks.is_empty() == true.
#[test]
fn test_assertion_no_overflow_check_mode() {
    // check_overflow = false (default)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("at_max", "x == 2147483647"));
    // Without overflow checking, x + 1 wraps to i32::MIN per BV semantics.
    // x + 1 > x is false because -2147483648 < 2147483647 (signed).
    ctx.push_obligation(ProofObligation::assert("wrapping", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Without overflow checks, x + 1 wraps and x + 1 > x is false",
    );
}

/// Assertions that cannot emit overflow side-channel checks should skip the
/// dedicated auxiliary precheck encoder even when overflow checking is enabled.
///
/// Regression test for #1786: `x == x` used to build an extra fresh encoder
/// before the main solve. The forced demotion hook only fires if that
/// auxiliary pass actually runs.
#[test]
fn test_trivial_assertion_skips_auxiliary_overflow_precheck() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "trivial_overflow_precheck",
        "x == x",
    ));

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_OVERFLOW_PRECHECK_DEMOTION);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "trivial assertion should skip the auxiliary overflow precheck and stay verified",
    );
}

// ============================================================
// mod.rs: Soundness guards
// ============================================================

/// Assumptions-only context (no assertions) must return Error, not Verified.
///
/// Tests the soundness guard at mod.rs:102-108 — a context with only
/// assumptions and no assertions to verify is a configuration error,
/// not a vacuously true proof.
#[test]
fn test_assumptions_only_context_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("some_fact", "x > 0"));
    // No assertions — only assumptions

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Context with only assumptions and no assertions should be an error",
    );
    if let VerifyResult::Error { message } = &result {
        assert!(
            message.contains("no assertions") || message.contains("nothing to prove"),
            "Error should mention missing assertions, got: {}",
            message
        );
    }
}

/// Empty context (no obligations at all) must return Error.
///
/// Tests the empty context guard at mod.rs:92-96.
#[test]
fn test_empty_context_returns_error() {
    let ctx = VerificationContext::new();
    // No variables, no obligations

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "Empty context should return Error");
}

// ============================================================
// assertion.rs: Double-parse collection_lengths regression (#1914)
// ============================================================

/// REGRESSION: overflow checking + Seq push must not corrupt length tracking.
///
/// The overflow check path parses the assertion expression (first parse) to
/// discover overflow predicates. This parse mutates `collection_lengths` as
/// a side-effect (push creates new_len = old_len + 1). The main assertion
/// parse (second parse) must see the ORIGINAL collection_lengths.
///
/// Fix: `check_overflow_predicates` saves/restores `collection_lengths`
/// around `resolve_condition_with_overflow_typed` (assertion.rs). The
/// two-encoder architecture (separate overflow encoder, discarded after use)
/// provides structural redundancy — the save/restore is defense-in-depth.
///
/// Regression test for #1914. Part of #1931.
#[test]
fn test_double_parse_collection_lengths_no_corruption() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("len_2", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    // push mutates collection_lengths (new_len = old_len + 1).
    // With overflow checks, the expression is parsed TWICE:
    //   1. Overflow parse: discovers push overflow predicates
    //   2. Main parse: verifies the assertion
    // If collection_lengths isn't saved/restored in a single-encoder
    // architecture, the main parse sees corrupted lengths.
    ctx.push_obligation(ProofObligation::assert("push_len", "s.push(x).len() == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.push(x).len() == 3 with s.len() == 2 should verify (overflow checks on)",
    );
}

/// CONTROL: wrong push length must NOT verify even with overflow checks.
///
/// Discriminating control — if length tracking were broken (returning
/// Verified for any length), this would pass too, exposing false positives.
/// Part of #1931.
#[test]
fn test_double_parse_collection_lengths_wrong_length_rejected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("len_2", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "push_len_wrong",
        "s.push(x).len() == 4",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "s.push(x).len() == 4 with s.len() == 2");
}
