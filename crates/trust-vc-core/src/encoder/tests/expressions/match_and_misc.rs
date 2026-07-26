//! Match expression, return, reference, dereference soundness, and
//! assignment rejection tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from expressions.rs (#2145).

use super::*;

// ========================================================================
// Tier 2 expression type tests (Issue #1552)
// ========================================================================

#[test]
fn test_match_literal_patterns() {
    // match x { 1 => 10, 2 => 20, _ => 0 } == 10 when x == 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_1", "x == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "match_arm1",
        "match x { 1 => 10, 2 => 20, _ => 0 } == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "match x {{ 1 => 10, ... }} should yield 10 when x == 1",
    );
}

#[test]
fn test_match_literal_second_arm() {
    // match x { 1 => 10, 2 => 20, _ => 0 } == 20 when x == 2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_2", "x == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "match_arm2",
        "match x { 1 => 10, 2 => 20, _ => 0 } == 20",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "match x {{ ..., 2 => 20, ... }} should yield 20 when x == 2",
    );
}

#[test]
fn test_match_wildcard_arm() {
    // match x { 1 => 10, 2 => 20, _ => 0 } == 0 when x == 99
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_99", "x == 99"));
    ctx.push_obligation(ProofObligation::assert(
        "match_default",
        "match x { 1 => 10, 2 => 20, _ => 0 } == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "match x {{ ..., _ => 0 }} should yield 0 when x == 99",
    );
}

#[test]
fn test_match_with_binding() {
    // match x { y => y + 1 } == x + 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "match_binding",
        "match x { y => y + 1 } == 6",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "match x {{ y => y + 1 }} should yield 6 when x == 5",
    );
}

#[test]
fn test_match_counterexample() {
    // match x { 1 => 10, _ => 0 } == 10 is NOT always true
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "match_not_always",
        "match x { 1 => 10, _ => 0 } == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "match x { 1 => 10, _ => 0 } == 10 should NOT verify for all x",
    );
}

#[test]
fn test_match_no_arms_rejected() {
    // Empty match should be rejected (this requires crafting the AST, but
    // we test through the string parser which will produce a parse error)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // "match x {}" is valid Rust syntax but has no arms
    ctx.push_obligation(ProofObligation::assert("empty_match", "match x {}"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "match with no arms should produce error");
}

#[test]
fn test_return_expression() {
    // return x is just x in verification context
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("return_val", "return x == 42"));

    // Note: "return x == 42" parses as "return (x == 42)" in Rust,
    // so this tests that return of a boolean expression works.
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "return x == 42 should verify when x == 42");
}

#[test]
fn test_reference_expression() {
    // &x is just x in verification context
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert("ref_val", "&x == 10"));

    // Note: "&x == 10" parses as "(&x) == 10" in Rust
    // Since & is identity in verification, this should verify
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "&x == 10 should verify when x == 10");
}

#[test]
fn test_deref_expression() {
    // *x is rejected in verification context to avoid silent identity rewrites.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("deref_val", "*x == 7"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains(
                    "dereference expressions are only supported for erased immutable reference variables"
                ),
                "Error should mention unsupported dereference syntax: {}",
                message
            );
        }
        _ => panic!("Expected Error for dereference syntax, got: {:?}", result),
    }
}

// ========================================================================
// SOUNDNESS: #1856 — dereference (*x) now fails closed
// ========================================================================

/// #1856: verification-time dereference syntax is rejected instead of being
/// silently rewritten to the inner expression. The lowering layer cannot tell
/// `&T` apart from pointer-like types, so dereference must fail closed.
#[test]
fn test_deref_is_rejected_1856() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));

    // #1856: `*x != x` must be rejected before encoding instead of silently
    // becoming `x != x`.
    ctx.push_obligation(ProofObligation::assert("deref_differs", "*x != x"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains(
                    "dereference expressions are only supported for erased immutable reference variables"
                ),
                "Error should mention unsupported dereference syntax: {}",
                message
            );
        }
        _ => panic!("Expected Error for dereference syntax, got: {:?}", result),
    }
}

#[test]
fn test_assign_rejected() {
    // x = 5 should produce an error (verification is functional)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("assign_val", "x = 5"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "Assignment should produce error in verification");
}

#[test]
fn test_match_nested_in_if() {
    // if x > 0 { match x { 1 => 10, _ => 20 } } else { 0 }
    // When x == 1, result should be 10
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_1", "x == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "nested_match",
        "if x > 0 { match x { 1 => 10, _ => 20 } } else { 0 } == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Nested match in if should yield 10 when x == 1");
}
