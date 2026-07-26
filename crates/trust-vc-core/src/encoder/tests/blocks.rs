//! Block expression encoding tests — semicolon handling, scoping, unit values.
//!
//! Split from expressions.rs for file size compliance.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Block trailing-semicolon tests (Issue #1784)
// ========================================================================

#[test]
fn test_block_trailing_semicolon_is_unit() {
    // In Rust, `{ expr; }` evaluates to `()`, not to `expr`.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("semi_block", "{ x; } == ()"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "{{ x; }} == () should verify");
}

#[test]
fn test_block_no_trailing_semicolon_returns_value() {
    // In Rust, `{ expr }` (no semicolon) evaluates to `expr`.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("no_semi_block", "{ x } == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "{{ x }} == 5 should verify when x == 5");
}

#[test]
fn test_block_let_then_semicolon_is_unit() {
    // `{ let y = x + 1; y; }` — trailing semicolon means block is unit
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "let_semi",
        "{ let y = x + 1; y; } == ()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "{{ let y = x + 1; y; }} == () should verify");
}

#[test]
fn test_block_trailing_let_statement_is_unit() {
    // `{ let y = x + 1; }` is unit-valued in Rust and must not be lowered
    // as if it returned the initializer value.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "trailing_let",
        "{ let y = x + 1; } == 11",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "{{ let y = x + 1; }} should error (unit-valued block)",
    );
}

#[test]
fn test_block_trailing_let_statement_after_prefix_let_is_unit() {
    // This path exercises lower_stmts() after an initial let in the outer block.
    // Final `let` statement still means the block value is unit.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "nested_trailing_let",
        "{ let a = 1; let b = a + 1; } == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "{{ let a = 1; let b = a + 1; }} should error (unit-valued block)",
    );
}
