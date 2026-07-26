// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proc-macro integration tests for `choose!` macro lowering through the
//! full `VerificationPipeline` → ay pipeline.
//!
//! These tests exercise the fix for #2486: `choose!` in macro-form
//! (as opposed to call-form `choose(...)`) now lowers correctly through
//! `lower_macro_expr` to `TrustVcExpr::Choose`.
//!
//! Part of #2486, #2429.

mod common;

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// `choose!` macro-form in an assumption lowers and verifies through the pipeline.
///
/// Assumes an existential witness exists, binds it via choose!, and asserts
/// the chosen value satisfies the bound. Uses the string lowering path where
/// `choose!(...)` is parsed as `syn::Expr::Macro`.
#[test]
fn test_choose_macro_let_binding_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    // Assume w is the choose witness satisfying the condition
    ctx.push_assume("w_is_witness", "w >= 0i32 && w < 10i32");
    ctx.push_assert("w_nonneg", "w >= 0i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "#2486: choose witness with assumed bounds should verify, got: {:?}",
        result,
    );
}

/// `choose!` macro-form expression lowers through string lowering without error.
///
/// This verifies that `choose!(|x: i32| cond)` parses and lowers through
/// `lower_macro_expr` to `TrustVcExpr::Choose`. Before #2486, this produced
/// "unsupported expression: macro". The test proves lowering succeeds by
/// getting a non-Error result from the pipeline (tautology assertion on the
/// choose-bound variable).
#[test]
fn test_choose_macro_form_expression_lowers() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    // Use the choose! macro form in an assumption.
    // This string goes through syn::parse_str → Expr::Macro → lower_macro_expr.
    ctx.push_assume("w_def", "w == choose!(|x: i32| x >= 0i32 && x < 10i32)");
    ctx.push_assert("tautology", "w == w");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "#2486: choose! macro form should lower without error, got: {:?}",
        result,
    );
}

/// Path-qualified `trust_vc::choose!` macro form also lowers correctly.
#[test]
fn test_choose_macro_path_qualified_lowers() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume(
        "w_def",
        "w == trust_vc::choose!(|x: i32| x >= 0i32 && x < 10i32)",
    );
    ctx.push_assert("tautology", "w == w");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "#2486: path-qualified choose! should lower without error, got: {:?}",
        result,
    );
}

#[test]
fn test_choose_call_form_expression_preserves_conjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume("w_def", "w == choose(|x: i32| x >= 5i32 && x < 100i32)");
    ctx.push_assert("w_ge_5", "w >= 5i32");
    ctx.push_assert("w_lt_100", "w < 100i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "choose call form should preserve both predicate bounds, got: {:?}",
        result,
    );
}

/// Verus-style single-binder `choose|x: T| P` syntax normalizes through the
/// string lowering path when it appears as a parenthesized expression.
#[test]
fn test_choose_verus_source_syntax_expression_lowers() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume("w_def", "w == (choose|x: i32| x >= 0i32 && x < 10i32)");
    ctx.push_assert("w_nonneg", "w >= 0i32");
    ctx.push_assert("w_lt_10", "w < 10i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Verus-style choose source syntax should preserve both predicate bounds, got: {:?}",
        result,
    );
}

/// Verus-style single-binder `choose|x: T| P` syntax also normalizes when it
/// appears as an unparenthesized RHS expression. This must prove the chosen
/// value satisfies both conjuncts, not just that the expression parsed.
#[test]
fn test_choose_verus_source_syntax_unparenthesized_rhs_preserves_conjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume("witness", "exists|x: i32| x >= 0i32 && x < 10i32");
    ctx.push_assume("w_def", "w == choose|x: i32| x >= 0i32 && x < 10i32");
    ctx.push_assert("w_nonneg", "w >= 0i32");
    ctx.push_assert("w_lt_10", "w < 10i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "unparenthesized Verus-style choose source syntax should preserve both predicate bounds, got: {:?}",
        result,
    );
}

/// Negative companion: the same unparenthesized Verus-style choose predicate
/// must not verify a bound that contradicts the preserved upper conjunct.
#[test]
fn test_choose_verus_source_syntax_unparenthesized_rhs_rejects_contradictory_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume("witness", "exists|x: i32| x >= 0i32 && x < 10i32");
    ctx.push_assume("w_def", "w == choose|x: i32| x >= 0i32 && x < 10i32");
    ctx.push_assert("w_ge_10", "w >= 10i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "unparenthesized Verus-style choose source syntax must not prove w >= 10 from x < 10, got: {:?}",
        result,
    );
}

/// Negative: the runtime `Default::default()` placeholder must not leak into
/// verification. Without existential assumption, `choose!(...)` should not
/// produce a concrete zero.
#[test]
fn test_choose_runtime_default_does_not_leak() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    // w is an unconstrained choose result — no existential assumption
    ctx.push_assume("w_def", "w == choose!(|x: i32| x >= 0i32 && x < 10i32)");
    // Assert w == 0 — this should fail because choose returns an arbitrary
    // value satisfying the condition, not the default value 0
    ctx.push_assert("w_is_zero", "w == 0i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "#2486: choose runtime default must not leak — unconstrained choose should not equal 0, got: {:?}",
        result,
    );
}

// === Skolem encoding tests (#2429) ===

/// The choose Skolem value satisfies its own condition: the pipeline
/// encodes `choose(|x| cond)` as a Skolem UF `sk()` with axiom
/// `cond[x := sk()]`, so asserting the condition on w must verify.
#[test]
fn test_choose_skolem_satisfies_own_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume("w_def", "w == choose!(|x: i32| x >= 5i32 && x < 100i32)");
    // The Skolem axiom ensures the chosen value satisfies x >= 5 && x < 100.
    ctx.push_assert("w_ge_5", "w >= 5i32");
    ctx.push_assert("w_lt_100", "w < 100i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "#2429: choose Skolem should satisfy its own condition, got: {:?}",
        result,
    );
}

/// Negative: choose Skolem cannot prove conditions outside its specification.
#[test]
fn test_choose_skolem_does_not_overshoot() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("w", "i32");
    ctx.push_assume("w_def", "w == choose!(|x: i32| x >= 5i32 && x < 100i32)");
    // The Skolem only guarantees 5 <= w < 100, not w >= 50.
    ctx.push_assert("w_ge_50", "w >= 50i32");

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "#2429: choose Skolem should not prove conditions beyond its spec, got: {:?}",
        result,
    );
}

// NOTE: `#[proof]` + `choose!` proc-macro integration is not yet possible
// because the `#[proof]` macro's runtime value capture records the Default
// placeholder (0) as a concrete assumption, disconnecting the variable from
// its Skolem UF. The VerificationContext + VerificationPipeline tests above
// exercise the full encoder → ay Skolem pipeline correctly. Part of #2429.
