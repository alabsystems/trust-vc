//! Parser rejection, unary operator recursion, and variable shadowing tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Trailing token detection tests (Issue #55)
// ========================================================================

#[test]
fn test_trailing_garbage_rejected() {
    // "x + 1 garbage" should NOT silently parse as "x + 1"
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("garbage", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("invalid", "x + 1 garbage"));

    let result = AYEncoder::verify(&ctx);
    // Parser rejects with "unexpected token" — verify it errors, not silently succeeds
    match result {
        VerifyResult::Error { message } => {
            let lower = message.to_lowercase();
            assert!(
                lower.contains("trailing") || lower.contains("unexpected"),
                "Error should mention trailing/unexpected tokens: {}",
                message
            );
        }
        _ => panic!("Expected Error for trailing garbage, got: {:?}", result),
    }
}

// ========================================================================
// Chained comparison tests (Issue #2493)
// ========================================================================

#[test]
fn test_chained_comparison_verifies() {
    // "1 < x < 10" normalizes to "(1 < x) && (x < 10)" and verifies with x == 5.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("chained", "1 < x < 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Chained comparison 1 < x < 10 with x==5 should verify",
    );
}

#[test]
fn test_chained_comparison_counterexample() {
    // Without constraining x, "1 < x < 10" can be violated.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("chained", "1 < x < 10"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Unconstrained chained comparison should produce counterexample",
    );
}

#[test]
fn test_mixed_chained_comparison_rejected() {
    // "1 < x > 5" mixes ascending and descending — should error.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("mixed", "1 < x > 5"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("monotone"),
                "Error should mention monotonicity: {}",
                message
            );
        }
        _ => panic!(
            "Expected Error for mixed chained comparison, got: {:?}",
            result
        ),
    }
}

#[test]
fn test_index_bound_chain_verifies() {
    // "0 <= i < n" normalizes to "(0 <= i) && (i < n)".
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 3"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 10"));
    ctx.push_obligation(ProofObligation::assert("bound", "0 <= i < n"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Index bound chain 0 <= i < n should verify");
}

#[test]
fn test_descending_chain_verifies() {
    // "hi >= mid > lo" normalizes to "(hi >= mid) && (mid > lo)".
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hi", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("mid", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("lo", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("mid_val", "mid == 5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 1"));
    ctx.push_obligation(ProofObligation::assert("desc", "hi >= mid > lo"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Descending chain hi >= mid > lo should verify");
}

// ========================================================================
// Unary operator recursion tests (Issue #56)
// ========================================================================

#[test]
fn test_double_negation_parses() {
    // "-(-x)" should parse as "neg(neg(x))" not fail with "Unexpected token"
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    // -(-5) == 5 is always true (double negation cancels)
    ctx.push_obligation(ProofObligation::assert("double_neg", "-(-x) == x"));

    let result = AYEncoder::verify(&ctx);
    // -(-x) == x should verify as it's a tautology
    expect_verified(&result, "Double negation identity should verify");
}

#[test]
fn test_negation_of_negation_parses() {
    // !(!b) should parse as "not(not(b))"
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert("double_not", "!!b == b"));

    let result = AYEncoder::verify(&ctx);
    // !!b == b should verify as it's a tautology
    expect_verified(&result, "Double logical not identity should verify");
}

#[test]
fn test_mixed_unary_operators() {
    // !(-x < 0) should parse correctly
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
    // If x > 0, then -x < 0 is true, so !(-x < 0) is false
    ctx.push_obligation(ProofObligation::assert(
        "negated_condition",
        "!(-x < 0) == false",
    ));

    let result = AYEncoder::verify(&ctx);
    // If x > 0, then -x < 0, so !(-x < 0) == false should verify
    expect_verified(&result, "Mixed unary operators assertion should verify");
}

// ========================================================================
// Variable shadowing detection tests (Issue #58)
// ========================================================================

#[test]
fn test_duplicate_variable_rejected() {
    // Declaring the same variable twice should error, not silently overwrite
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("bool")); // Second declaration with different type
    ctx.push_obligation(ProofObligation::assert("dummy", "true")); // Need an obligation to pass empty-context check

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("already declared"),
                "Error should mention duplicate declaration: {}",
                message
            );
        }
        _ => panic!("Expected Error for duplicate variable, got: {:?}", result),
    }
}

#[test]
fn test_duplicate_variable_same_type_rejected() {
    // Even same type should error - no silent overwrite
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32")); // Same type but still duplicate
    ctx.push_obligation(ProofObligation::assert("dummy", "true")); // Need an obligation to pass empty-context check

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("already declared"),
                "Error should mention duplicate declaration: {}",
                message
            );
        }
        _ => panic!("Expected Error for duplicate variable, got: {:?}", result),
    }
}
