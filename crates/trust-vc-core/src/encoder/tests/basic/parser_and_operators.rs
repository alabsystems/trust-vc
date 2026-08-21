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

#[test]
fn test_map_dom_name_collision_reverse_order_is_error() {
    // The Map is declared FIRST. Its `{name}_dom` companion is minted lazily by
    // the encoder, so it is NOT in `variable_index` when `x_dom` is declared —
    // the plain duplicate check cannot see it. The companion-collision check
    // must therefore inspect the BASE name's type, in this order too.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "x",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.declare_var_typed("x_dom", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert("dummy", "true"));

    match AYEncoder::verify(&ctx) {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("map domain") && message.contains("already declared"),
                "Error should surface the map-domain collision: {}",
                message
            );
        }
        other => panic!("Expected Error for reverse-order map-dom collision, got: {other:?}"),
    }
}

#[test]
fn test_map_dom_name_collision_same_sort_is_error() {
    // The case the SOLVER cannot catch: `x_dom: Map<i32, bool>` lowers to
    // exactly the domain sort `Array(BitVec32, Bool)` that `x: Map<i32, i32>`
    // mints. ay's `try_declare_const` treats an identical-sort redeclaration as
    // idempotent and returns Ok, so relying on the solver would silently rebind
    // the user's `x_dom` to `x`'s domain array. Must fail closed on the NAME.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "x_dom",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.declare_var_typed(
        "x",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("dummy", "true"));

    match AYEncoder::verify(&ctx) {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("map domain") && message.contains("already declared"),
                "Error should surface the same-sort map-domain collision: {}",
                message
            );
        }
        other => panic!("Expected Error for same-sort map-dom collision, got: {other:?}"),
    }
}

#[test]
fn test_encoder_level_map_dom_collision_fails_closed() {
    // Pins the DEFENSE-IN-DEPTH arm inside `declare_variable` on its own. The
    // context-level gate makes this unreachable through the normal
    // `VerificationContext` route, but `declare_variable` is also called
    // directly by frame-state, ground-seeding and extra-variable setup, so the
    // guard has to hold without the context gate in front of it.
    //
    // The sorts here COINCIDE deliberately: `x_dom: Map<i32, bool>` lowers to
    // exactly the `Array(BitVec32, Bool)` domain sort minted for `x`, so ay's
    // `try_declare_const` accepts it as an IDEMPOTENT redeclaration and returns
    // Ok. Delegating to the solver therefore cannot catch this case — only the
    // NAME check can.
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x_dom".to_string(),
            ty: crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
        })
        .expect("first declaration should succeed");
    let err = encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
        })
        .expect_err("map domain companion collision must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("map domain") && message.contains("already declared"),
        "encoder guard should surface the collision: {message}"
    );
}

#[test]
fn test_dom_suffix_without_map_base_is_not_rejected() {
    // NARROWNESS PIN for the companion-collision gate. Only a `Map` base mints a
    // `{name}_dom` companion, so a `_dom`-suffixed variable sitting beside a
    // NON-Map base is perfectly legal and must still verify. Without this pin
    // the gate could be widened to reject every `_dom` name and nothing would
    // notice.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x_dom", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.push_obligation(ProofObligation::assert("dummy", "true"));

    match AYEncoder::verify(&ctx) {
        VerifyResult::Verified => {}
        other => panic!("`x_dom` beside a non-Map `x` must stay legal, got: {other:?}"),
    }
}

#[test]
fn test_map_dom_name_collision_is_error_not_panic() {
    // A user variable occupying a Map's internal `{name}_dom` companion name
    // bypasses the `self.variables` duplicate check when the Map is declared
    // AFTER it: `declare_variable` then minted the domain array through the
    // PANICKING `Solver::declare_const`, unwinding out of the encoder (in
    // trustc, a compiler ICE). The collision is an embedder mistake and must
    // surface as `VerifyResult::Error`. The reverse declaration order is
    // already caught by the duplicate check above (#58).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x_dom", crate::ir::TrustVcType::parse_or_opaque("bool"));
    ctx.declare_var_typed(
        "x",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("dummy", "true"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("map domain") && message.contains("already declared"),
                "Error should surface the declare_const collision: {}",
                message
            );
        }
        _ => panic!(
            "Expected Error for map-dom name collision, got: {:?}",
            result
        ),
    }
}
