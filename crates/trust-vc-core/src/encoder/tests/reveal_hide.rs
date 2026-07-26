// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for opaque/reveal spec function support (#1901).
//!
//! Validates that:
//! - Opaque body axioms are hidden from the solver (returns Unknown)
//! - `reveal!(fn_name)` makes opaque body axioms available (returns Verified)
//! - Non-opaque functions are unaffected by the opaque filter
//! - Reveal for non-opaque functions is harmless

use super::*;
use crate::vc::{FunctionContext, ProofObligation};

/// Helper: set up a context with a non-recursive spec function and body axiom.
fn setup_spec_fn_context(
    fn_name: &str,
    body_condition: &str,
    is_opaque: bool,
) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(FunctionContext {
        name: fn_name.to_string(),
        params: vec![("x".to_string(), u64_ty())],
        return_type: u64_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let axiom_name = format!("__body_axiom_{}", fn_name);
    let call_expr = format!("{}(x)", fn_name);
    let condition = format!("{} == {}", call_expr, body_condition);
    ctx.obligations.push(
        ProofObligation::broadcast_assume(axiom_name, condition)
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec![call_expr]])
            .with_opaque(is_opaque),
    );
    ctx
}

/// Helper: set up a context with a recursive spec function and body axiom.
/// Uses the factorial pattern: fact(n) == if n == 0 { 1 } else { n * fact(n - 1) }
fn setup_recursive_spec_fn_context(fn_name: &str, is_opaque: bool) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: fn_name.to_string(),
        params: vec![("n".to_string(), i32_ty())],
        return_type: i32_ty(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let axiom_name = format!("__body_axiom_{}", fn_name);
    let body = format!(
        "{}(n) == {{ if n == 0 {{ 1 }} else {{ n * {}(n - 1) }} }}",
        fn_name, fn_name
    );
    ctx.obligations.push(
        ProofObligation::broadcast_assume(axiom_name, body)
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec![format!("{}(n)", fn_name)]])
            .with_opaque(is_opaque),
    );
    ctx
}

#[test]
fn test_opaque_function_hidden_without_reveal() {
    // Opaque spec fn secret(x: u64) -> u64 = x * x
    // Without reveal, body axiom is hidden → assertion cannot be proven.
    let mut ctx = setup_spec_fn_context("secret", "x * x", true);
    ctx.push_obligation(ProofObligation::assert("check", "secret(3) == 9"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "opaque function without reveal should NOT verify");
}

#[test]
fn test_opaque_function_verified_with_reveal() {
    // Opaque spec fn secret(x: u64) -> u64 = x * x
    // With reveal, body axiom is available → assertion verifies.
    let mut ctx = setup_spec_fn_context("secret", "x * x", true);
    ctx.obligations.push(ProofObligation::reveal("secret"));
    ctx.push_obligation(ProofObligation::assert("check", "secret(3) == 9"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "opaque function with reveal should verify");
}

#[test]
fn test_non_opaque_function_always_visible() {
    // Non-opaque spec fn double(x: u64) -> u64 = x + x
    // Body axiom is always visible → existing behavior preserved.
    let mut ctx = setup_spec_fn_context("double", "x + x", false);
    ctx.push_obligation(ProofObligation::assert("check", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "non-opaque function should always verify");
}

#[test]
fn test_reveal_does_not_affect_non_opaque() {
    // Reveal on a non-opaque function should be harmless.
    let mut ctx = setup_spec_fn_context("double", "x + x", false);
    ctx.obligations.push(ProofObligation::reveal("double"));
    ctx.push_obligation(ProofObligation::assert("check", "double(3) == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reveal on non-opaque should still verify");
}

// --- Prefix leak regression test (P1 audit, #1901) ---

/// Regression: `reveal!(foo)` when only `foo_bar` exists must produce an error
/// (#2473). Before #2473, the reveal silently did nothing (or worse, with the
/// old prefix heuristic, it leaked to `foo_bar`'s body axiom).
#[test]
fn test_reveal_nonexistent_function_errors() {
    // foo_bar is the primary spec fn. Its body axiom is opaque.
    // reveal!(foo) should error because "foo" is not a known function.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(FunctionContext {
        name: "foo_bar".to_string(),
        params: vec![("x".to_string(), u64_ty())],
        return_type: u64_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom for foo_bar: foo_bar(x) == x + 2 (opaque)
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_foo_bar",
            "foo_bar(x) == x + 2".to_string(),
        )
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["foo_bar(x)".to_string()]])
        .with_opaque(true),
    );

    // Reveal only "foo", NOT "foo_bar"
    ctx.obligations.push(ProofObligation::reveal("foo"));

    ctx.push_obligation(ProofObligation::assert("foo_bar_check", "foo_bar(3) == 5"));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("reveal!(foo)"),
                "error should mention the misspelled name, got: {message}"
            );
            assert!(
                message.contains("foo_bar"),
                "error should list available functions, got: {message}"
            );
        }
        other => panic!(
            "reveal!(foo) for nonexistent function should produce Error, got: {:?}",
            other
        ),
    }
}

// --- Recursive opaque function tests (opaque + fuel encoding path) ---

/// Recursive opaque spec fn without reveal: the opaque filter skips the body
/// axiom before the fuel encoding path runs, so the solver cannot unfold
/// the recursion and the assertion is unprovable.
#[test]
fn test_recursive_opaque_hidden_without_reveal() {
    let mut ctx = setup_recursive_spec_fn_context("rfact", true);
    ctx.push_obligation(ProofObligation::assert("rfact_2_is_2", "rfact(2) == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "recursive opaque function without reveal should NOT verify",
    );
}

/// Recursive opaque spec fn with reveal: the opaque filter passes the body
/// axiom through, and the fuel encoding path creates the direct defining
/// axiom. E-matching unfolds rfact(2) → rfact(1) → rfact(0) → 1, proving
/// the assertion.
#[test]
fn test_recursive_opaque_verified_with_reveal() {
    let mut ctx = setup_recursive_spec_fn_context("rfact", true);
    ctx.obligations.push(ProofObligation::reveal("rfact"));
    ctx.push_obligation(ProofObligation::assert("rfact_2_is_2", "rfact(2) == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "recursive opaque function with reveal should verify via fuel encoding",
    );
}

/// Non-opaque recursive spec fn verifies without any reveal — existing fuel
/// encoding behavior is preserved when opaque is not set.
#[test]
fn test_recursive_non_opaque_always_visible() {
    let mut ctx = setup_recursive_spec_fn_context("rfact", false);
    ctx.push_obligation(ProofObligation::assert("rfact_2_is_2", "rfact(2) == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "non-opaque recursive function should verify without reveal",
    );
}

// --- reveal_group tests (#2415) ---

/// reveal_group: revealing multiple opaque functions at once makes both
/// body axioms available.
#[test]
fn test_reveal_group_makes_multiple_opaque_fns_visible() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(FunctionContext {
        name: "alpha".to_string(),
        params: vec![("x".to_string(), u64_ty())],
        return_type: u64_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Register beta with full typed signature so the encoder can declare it in ay
    ctx.declare_helper_function_typed("beta", u64_ty(), vec![("x".to_string(), u64_ty())]);

    // Two opaque body axioms
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_alpha", "alpha(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["alpha(x)".to_string()]])
            .with_opaque(true),
    );
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_beta", "beta(x) == x + 2")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["beta(x)".to_string()]])
            .with_opaque(true),
    );

    // Reveal both via individual reveal obligations (what reveal_group! emits)
    ctx.obligations.push(ProofObligation::reveal("alpha"));
    ctx.obligations.push(ProofObligation::reveal("beta"));

    // Both should be provable
    ctx.push_obligation(ProofObligation::assert("alpha_check", "alpha(3) == 4"));
    ctx.push_obligation(ProofObligation::assert("beta_check", "beta(3) == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reveal_group revealing alpha + beta should verify both",
    );
}

/// Without reveal_group, both opaque fns remain hidden.
#[test]
fn test_without_reveal_group_both_opaque_hidden() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(FunctionContext {
        name: "alpha".to_string(),
        params: vec![("x".to_string(), u64_ty())],
        return_type: u64_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_alpha", "alpha(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["alpha(x)".to_string()]])
            .with_opaque(true),
    );

    // No reveals — alpha is hidden
    ctx.push_obligation(ProofObligation::assert("alpha_check", "alpha(3) == 4"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "opaque alpha without reveal should not verify");
}

/// Partial reveal: revealing only one of two opaque fns.
#[test]
fn test_partial_reveal_only_reveals_named_fn() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_function_context(FunctionContext {
        name: "alpha".to_string(),
        params: vec![("x".to_string(), u64_ty())],
        return_type: u64_ty(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Register beta with full typed signature so the encoder can declare it in ay
    ctx.declare_helper_function_typed("beta", u64_ty(), vec![("x".to_string(), u64_ty())]);

    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_alpha", "alpha(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["alpha(x)".to_string()]])
            .with_opaque(true),
    );
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_beta", "beta(x) == x + 2")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["beta(x)".to_string()]])
            .with_opaque(true),
    );

    // Reveal only alpha
    ctx.obligations.push(ProofObligation::reveal("alpha"));

    // Alpha is provable, but beta is not — assert only alpha
    ctx.push_obligation(ProofObligation::assert("alpha_check", "alpha(3) == 4"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "partial reveal of alpha should make alpha verifiable",
    );
}
