//! Frame-state unit tests — dedicated coverage for `frame_state.rs`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests the three frame-state functions through the verification pipeline:
//! - `declare_pre_state_variables`: pre-state shadow declaration
//! - `add_unmodified_frame_conditions`: scalar equality for unmodified vars
//! - `alias_map_domain_to_pre_state`: keeps framed Map-domain reads on one term
//!
//! Each test targets a specific function's behavior via observable verification
//! outcomes (Verified vs Unknown/Counterexample), not internal state.

use crate::encoder::tests::expect_verified;
use crate::encoder::types::VerifyResult;
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::vc::{ProofObligation, VerificationContext};

// ========================================================================
// Scalar frame conditions — add_unmodified_frame_conditions path
// ========================================================================

/// POSITIVE: Unmodified scalar variable retains its value across a loop.
///
/// `limit` is declared but NOT in modified_vars for the invariant.
/// Frame condition: `limit == limit__trust_vc_pre`.
/// Since `limit` starts at 10 and is unmodified, the ensures `limit == 10`
/// should verify.
///
/// Exercises `add_unmodified_frame_conditions` for scalar variables.
#[test]
fn test_frame_unmodified_scalar_retains_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("count", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("limit", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_count", "count == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 10"));

    ctx.obligations
        .push(ProofObligation::loop_invariant("limit_inv", "limit == 10"));
    ctx.set_loop_modified_vars("limit_inv", vec!["count".to_string()]);

    ctx.obligations.push(ProofObligation::loop_ensures(
        "limit_still_10",
        "limit == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "unmodified scalar should retain value via frame condition",
    );
}

/// NEGATIVE (discriminating pair): Modified scalar variable is havoced.
///
/// Same setup as above, but `limit` is now in modified_vars.
/// Without the frame condition, `limit` is unconstrained after the loop,
/// so `limit == 10` should NOT verify.
///
/// Discriminating pair with `test_frame_unmodified_scalar_retains_value`.
#[test]
fn test_frame_modified_scalar_is_havoced() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("count", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("limit", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_count", "count == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 10"));

    ctx.obligations
        .push(ProofObligation::loop_invariant("limit_inv", "limit == 10"));
    // Both count AND limit are modified — limit loses its frame condition.
    ctx.set_loop_modified_vars("limit_inv", vec!["count".to_string(), "limit".to_string()]);

    ctx.obligations.push(ProofObligation::loop_ensures(
        "limit_still_10",
        "limit == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "modified scalar should be havoced — limit==10 must NOT verify: {:?}",
        result
    );
}

/// POSITIVE: Multiple unmodified variables all get frame conditions.
///
/// Both `a` and `b` are unmodified while `x` is modified.
/// The ensures checks `a + b == 15` which requires both frame conditions.
#[test]
fn test_frame_multiple_unmodified_vars() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("a", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("b", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_a", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("init_b", "b == 10"));

    ctx.obligations
        .push(ProofObligation::loop_invariant("ab_inv", "a + b == 15"));
    ctx.set_loop_modified_vars("ab_inv", vec!["x".to_string()]);

    ctx.obligations.push(ProofObligation::loop_ensures(
        "sum_preserved",
        "a + b == 15",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "multiple unmodified vars should all get frame conditions",
    );
}

/// NEGATIVE: Partial modification — only one of two variables is unmodified.
///
/// `a` is unmodified (retains value), `b` is modified (havoced).
/// The ensures `a + b == 15` should NOT verify because `b` is unconstrained.
///
/// Discriminating pair with `test_frame_multiple_unmodified_vars`.
#[test]
fn test_frame_partial_modification_breaks_property() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("a", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("b", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_a", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("init_b", "b == 10"));

    ctx.obligations
        .push(ProofObligation::loop_invariant("ab_inv", "a + b == 15"));
    // Both x and b are modified — b loses its frame condition.
    ctx.set_loop_modified_vars("ab_inv", vec!["x".to_string(), "b".to_string()]);

    ctx.obligations.push(ProofObligation::loop_ensures(
        "sum_preserved",
        "a + b == 15",
    ));

    let result = AYEncoder::verify(&ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "partially modified vars — a+b==15 should NOT verify with b havoced: {:?}",
        result
    );
}

// ========================================================================
// Collection frame conditions — collection_lengths equality path
// ========================================================================

/// POSITIVE: Unmodified Seq retains its length across a loop.
///
/// `s` is a Seq<i32> that is NOT modified. The frame condition should preserve
/// both the scalar equality (s == s__trust_vc_pre) and the collection length
/// equality (len(s) == len(s__trust_vc_pre)).
///
/// Exercises the `var.ty.is_collection()` branch in `add_unmodified_frame_conditions`.
#[test]
fn test_frame_unmodified_seq_retains_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "s",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    ctx.declare_var_typed("i", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations.push(ProofObligation::loop_invariant(
        "seq_stable",
        "s.len() == 3",
    ));
    ctx.set_loop_modified_vars("seq_stable", vec!["i".to_string()]);

    ctx.obligations.push(ProofObligation::loop_ensures(
        "seq_len_preserved",
        "s.len() == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "unmodified Seq should retain length via frame condition",
    );
}

/// NEGATIVE: Modified Seq does NOT retain its length.
///
/// Same setup, but `s` is in modified_vars. Length is unconstrained.
///
/// Discriminating pair with `test_frame_unmodified_seq_retains_length`.
#[test]
fn test_frame_modified_seq_loses_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "s",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    ctx.declare_var_typed("i", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations.push(ProofObligation::loop_invariant(
        "seq_stable",
        "s.len() == 3",
    ));
    // s is now modified — it loses both scalar and length frame conditions.
    ctx.set_loop_modified_vars("seq_stable", vec!["i".to_string(), "s".to_string()]);

    ctx.obligations.push(ProofObligation::loop_ensures(
        "seq_len_preserved",
        "s.len() == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "modified Seq should NOT retain length — havoced: {:?}",
        result
    );
}

// ========================================================================
// Pre-state variable declaration — declare_pre_state_variables path
// ========================================================================

/// POSITIVE: Pre-state variables allow reasoning about loop body effects.
///
/// In a loop invariant inductive step, the pre-state and post-state are
/// distinct. This test verifies that pre-state variables are correctly
/// declared and accessible for frame condition reasoning.
///
/// Exercises `declare_pre_state_variables` through the invariant verification path.
#[test]
fn test_frame_prestate_declaration_enables_inductive_reasoning() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("bound", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_n", "n == 0"));
    ctx.push_obligation(ProofObligation::assume("init_bound", "bound == 100"));

    // Invariant: bound is always 100 (unmodified).
    ctx.obligations.push(ProofObligation::loop_invariant(
        "bound_stable",
        "bound == 100",
    ));
    ctx.set_loop_modified_vars("bound_stable", vec!["n".to_string()]);

    // Guard: n < bound (so after loop: n >= bound = 100).
    ctx.obligations
        .push(ProofObligation::loop_guard("guard", "n < bound"));

    // Ensures: n >= 100 (requires both frame condition on bound and guard negation).
    ctx.obligations.push(ProofObligation::loop_ensures(
        "n_at_least_bound",
        "n >= 100",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pre-state declaration should enable frame+guard reasoning",
    );
}
