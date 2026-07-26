//! ITE (if-else), block, let-binding, cast, and const-eval tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from expressions.rs (#2145).

use super::*;

// ========================================================================
// Tier 1 expression type tests (Issue #1552)
// ========================================================================

#[test]
fn test_if_else_expression_true_branch() {
    // if x > 0 { 1 } else { 0 } == 1 when x > 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert(
        "if_result",
        "if x > 0 { 1 } else { 0 } == 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "if x > 0 {{ 1 }} else {{ 0 }} == 1 should verify when x > 0",
    );
}

#[test]
fn test_if_else_expression_false_branch() {
    // if x > 0 { 1 } else { 0 } == 0 when x <= 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_nonpositive", "x <= 0"));
    ctx.push_obligation(ProofObligation::assert(
        "if_result",
        "if x > 0 { 1 } else { 0 } == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "if x > 0 {{ 1 }} else {{ 0 }} == 0 should verify when x <= 0",
    );
}

#[test]
fn test_if_else_nested() {
    // Nested if-else: if x > 0 { if x > 10 { 2 } else { 1 } } else { 0 }
    // When x == 5: result should be 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_is_5", "x == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "nested_if",
        "if x > 0 { if x > 10 { 2 } else { 1 } } else { 0 } == 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Nested if-else with x == 5 should yield 1");
}

#[test]
fn test_if_else_without_else_rejected() {
    // if x > 0 { 1 } (no else) should produce an error
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("no_else", "if x > 0 { 1 }"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "if without else should produce error");
}

#[test]
fn test_block_expression_simple() {
    // { 42 } == 42
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("block_val", "{ x } == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "{{ x }} == 42 should verify when x == 42");
}

#[test]
fn test_block_with_let_binding() {
    // { let y = x + 1; y } == x + 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "let_binding",
        "{ let y = x + 1; y } == 11",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "{{ let y = x + 1; y }} == 11 should verify when x == 10",
    );
}

#[test]
fn test_block_let_scoping() {
    // Let bindings in blocks are scoped — y from inner block should not leak
    // This test verifies that a variable bound in a block doesn't shadow
    // an outer variable after the block ends.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 100"));
    // Inner block binds y = x + 1 = 6, but outer y should remain 100
    // Test: { let y = x + 1; y } == 6 AND y == 100
    ctx.push_obligation(ProofObligation::assert(
        "inner_y",
        "{ let y = x + 1; y } == 6",
    ));
    ctx.push_obligation(ProofObligation::assert("outer_y", "y == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Block let binding should not leak: inner y == 6, outer y == 100",
    );
}

#[test]
fn test_cast_widening_i32_to_i64() {
    // (x as i64) should preserve value for positive x
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 42"));
    ctx.push_obligation(ProofObligation::assert("cast_preserves", "(x as i64) == y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42_i32 as i64 == 42_i64 should verify");
}

#[test]
fn test_cast_narrowing_i64_to_i32() {
    // (x as i32) truncates to low 32 bits
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 42"));
    ctx.push_obligation(ProofObligation::assert("cast_truncates", "(x as i32) == y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "42_i64 as i32 == 42_i32 should verify (small value)",
    );
}

#[test]
fn test_cast_unsigned_to_wider() {
    // u8 to u32 should zero-extend
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 200"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 200"));
    ctx.push_obligation(ProofObligation::assert("zext_cast", "(x as u32) == y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "200_u8 as u32 == 200_u32 should verify (zero-extend)",
    );
}

// ========================================================================
// Mixed float compare boundary (#2715)
// ========================================================================

#[test]
fn test_mixed_float_non_float_compare_errors() {
    // Float casts are supported now, but mixing a float cast with a non-float
    // compare operand must fail in the encoder instead of falling through to
    // fp.eq(FP, BV) and becoming Unknown.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("bad_cast", "(x as f64) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "floating-point comparison requires both operands to be float of the same width",
        "mixed float/non-float equality should fail during encoding",
    );
    expect_error_containing(
        &result,
        "got f64 and i32",
        "mixed float/non-float equality should report the effective compare types",
    );
}

#[test]
fn test_mixed_float_non_float_ordered_compare_errors() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("bad_cast_lt", "(x as f64) < x"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "floating-point comparison requires both operands to be float of the same width",
        "mixed float/non-float ordered comparison should fail during encoding",
    );
    expect_error_containing(
        &result,
        "got f64 and i32",
        "mixed float/non-float ordered comparison should report the effective compare types",
    );
}

#[test]
fn test_mixed_float_width_equal_compare_errors() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("f32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("f64"));
    ctx.push_obligation(ProofObligation::assert(
        "mixed_width_float_compare",
        "x == y",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "floating-point comparison requires both operands to be float of the same width",
        "mixed float-width equality should fail during encoding",
    );
    expect_error_containing(
        &result,
        "got f32 and f64",
        "mixed float-width equality should report the effective compare types",
    );
}

#[test]
fn test_mixed_float_width_not_equal_compare_errors() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("f32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("f64"));
    ctx.push_obligation(ProofObligation::assert(
        "mixed_width_float_ne_compare",
        "x != y",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "floating-point comparison requires both operands to be float of the same width",
        "mixed float-width inequality should fail during encoding",
    );
    expect_error_containing(
        &result,
        "got f32 and f64",
        "mixed float-width inequality should report the effective compare types",
    );
}

#[test]
fn test_if_else_with_variables() {
    // if x > y { x } else { y } gives the maximum
    // When x > y, the result should equal x
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_bigger", "x > y"));
    ctx.push_obligation(ProofObligation::assert(
        "max_is_x",
        "if x > y { x } else { y } == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(x, y) == x when x > y should verify");
}

#[test]
fn test_if_else_counterexample() {
    // if x > 0 { x } else { 0 - x } == x is NOT always true (fails for x < 0)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "abs_is_x",
        "if x > 0 { x } else { 0 - x } == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "abs(x) == x should NOT verify for all x (x could be negative)",
    );
}

#[test]
fn test_block_nested_scoping() {
    // Regression test: nested blocks that rebind the same variable name
    // must restore the outer binding when the inner block ends.
    // { let y = 1; { let y = 2; y }; y } should be:
    //   inner block returns 2, then outer y (== 1) is used
    // But we can't express this directly in a single string assertion
    // because the string parser doesn't see intermediate semicolons well.
    // Instead, test that a block binding doesn't corrupt quantifier-bound vars.
    //
    // Test: x == 5, { let x = 10; x } == 10, AND x == 5 still holds after block
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "block_shadows",
        "{ let x = 10; x } == 10",
    ));
    ctx.push_obligation(ProofObligation::assert("outer_restored", "x == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Block let should shadow x (10) then restore outer x (5)",
    );
}

#[test]
fn test_const_eval_respects_bv_width() {
    // Regression for #1553 + casts-bitvec literal-width soundness (round-3).
    //
    // The original #1553 guard asserted that `128 > 127` in an i8 context should
    // fail closed because `128` "wraps to -128" in signed BV(8). That wrap was
    // itself the casts-bitvec soundness hole: a positive literal that does not
    // fit the SIGNED width must NOT be silently aliased to a different (negative)
    // value. `128` is now encoded value-preservingly (widened so it stays `128`),
    // so the bare comparison of two default-int literals `128 > 127` is the true
    // tautology it mathematically is — verifying it is SOUND (no variable, no
    // reachable-state claim).
    //
    // `try_const_eval_typed` STILL refuses to fold this (its `value_fits_in_type`
    // check returns `false` for `128i8`); the verdict now comes from the solver
    // on the value-preserved literal. The function-level guards in
    // `const_eval_typed.rs` continue to pin that the const-eval shortcut never
    // folds an out-of-width comparison to `Some(true)`.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("overflow_compare", "128 > 127"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "128 > 127 is a true comparison once 128 is encoded at its real value \
         (not aliased to -128); verifying it is sound",
    );
}

/// DUAL soundness guard (the property the wrap-based predecessor was really
/// protecting): an out-of-signed-range literal must NOT manufacture a false
/// `Verified` for a genuinely-false goal. Under the old wrap, `128` aliased
/// `-128`, so `x >= 128` became `x >= -128` — vacuously true for every i8 and a
/// catastrophic false `Verified` at `x == 0`. With the value-preserving fix,
/// `x >= 128` is correctly false for all i8 (witness `x = 0`).
#[test]
fn test_out_of_signed_range_literal_no_false_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("ge_128", "x >= 128"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "x >= 128 (x == 0) must NOT verify — 128 must not alias -128 and weaken \
         the goal",
    );
}

#[test]
fn test_const_eval_small_literals_still_fold() {
    // Verify that small literals that fit in any BV width are still folded.
    // 5 > 3 should const-fold to true regardless of BV width.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("small_compare", "5 > 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "5 > 3 should still const-fold to true in any BV width",
    );
}
