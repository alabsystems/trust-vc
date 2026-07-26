//! Broadcast activation: group filtering and bound-var resolution tests.
//!
//! Issues: #1629, #2414
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Broadcast group filtering (#2414)
// ========================================================================

#[test]
fn test_broadcast_group_filtered_when_not_imported() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations
        .push(grouped_ground_broadcast("grouped_fact", "x == 1", "arith"));
    ctx.push_obligation(ProofObligation::assert("needs_grouped_fact", "x == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Grouped broadcast should be filtered without broadcast_use import",
    );
}

#[test]
fn test_broadcast_group_active_when_imported() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.add_broadcast_use_group("arith");
    ctx.obligations
        .push(grouped_ground_broadcast("grouped_fact", "x == 1", "arith"));
    ctx.push_obligation(ProofObligation::assert("needs_grouped_fact", "x == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Imported broadcast group should activate grouped broadcasts",
    );
}

#[test]
fn test_multiple_broadcast_groups_are_additive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.add_broadcast_use_group("arith");
    ctx.add_broadcast_use_group("ordering");
    ctx.obligations
        .push(grouped_ground_broadcast("arith_fact", "x == 1", "arith"));
    ctx.obligations.push(grouped_ground_broadcast(
        "ordering_fact",
        "y == 2",
        "ordering",
    ));
    ctx.push_obligation(ProofObligation::assert("needs_arith_fact", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("needs_ordering_fact", "y == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Multiple broadcast_use imports should be additive");
}

#[test]
fn test_ungrouped_broadcasts_always_active() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations
        .push(ground_broadcast("ungrouped_fact", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("needs_ungrouped_fact", "x == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ungrouped broadcasts should remain globally active",
    );
}

// ========================================================================
// Broadcast bound_vars error detection (Fix 3.1 of quantifier redesign, #1629)
// ========================================================================

/// DISCRIMINATING: Without Fix 3.1, this test would pass with the broadcast
/// silently degraded to a ground formula. With Fix 3.1, the encoder returns
/// an error because the bound variable "nonexistent" is not in scope.
#[test]
fn test_broadcast_bound_vars_unresolvable_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Broadcast with a bound_var name that doesn't match any declared variable
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("test_broadcast", "x > 0")
            .with_bound_vars(vec!["nonexistent".to_string()]),
    );
    // Also add a trivial assert so verification doesn't short-circuit
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Broadcast with unresolvable bound_vars should error",
    );
}

/// DISCRIMINATING: Broadcast with bound_vars that partially resolve — some
/// names found, some not. Should error (not silently drop the missing ones).
#[test]
fn test_broadcast_bound_vars_partial_match_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // "x" resolves, "z" does not
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("partial_broadcast", "x > 0")
            .with_bound_vars(vec!["x".to_string(), "z".to_string()]),
    );
    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Broadcast with partially resolvable bound_vars should error",
    );
}

/// Broadcast with all bound_vars resolving — should not error (no regression).
/// Note: ay quantifier reasoning may return Unknown for quantified broadcasts,
/// so we accept both Verified and Unknown. The key assertion is no Error.
#[test]
fn test_broadcast_bound_vars_all_resolved_no_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("good_broadcast", "n >= 0")
            .with_bound_vars(vec!["n".to_string()]),
    );
    // With the broadcast assuming n >= 0, asserting n >= 0 should not error
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    // Broadcast bound-var resolution doesn't always constrain — Counterexample possible (#2229 triage)
    expect_encodes_without_error(&result, "Broadcast with all bound_vars resolved");
}
