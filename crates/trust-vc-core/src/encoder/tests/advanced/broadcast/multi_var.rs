//! Multi-variable broadcast encoding tests (bound_vars.len() > 1).
//!
//! Issues: #2113
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Multi-variable broadcast encoding (#2113)
// ========================================================================

/// DISCRIMINATING: A broadcast with two bound variables and a trigger pattern.
/// The broadcast axiom `g(x, y) == x + y` with trigger `g(x, y)` is the only
/// source of information about `g`. The assertion `g(3, 4) == 7` can only be
/// proved via the broadcast.
///
/// This exercises the multi-variable code path in `add_typed_broadcast` where
/// `bound_vars` has length > 1, which was previously untested (#2113).
#[test]
fn test_broadcast_multi_variable_two_bound_vars_with_trigger() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "g".to_string(),
        params: vec![
            (
                "x".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "y".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0 && x <= 50"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y >= 0 && y <= 50"));

    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("__body_axiom_g", "g(x, y) == x + y")
            .with_bound_vars(vec!["x".to_string(), "y".to_string()])
            .with_trigger_patterns(vec![vec!["g(x, y)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assert("g_property", "g(3, 4) == 7"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DISCRIMINATING: Multi-variable broadcast g(x,y)==x+y must prove g(3,4)==7.",
    );
}

/// Negative counterpart: broadcast says g(x,y)==x+y but assertion claims
/// g(3,4)==8. Must NOT verify.
#[test]
fn test_broadcast_multi_variable_negative_wrong_result() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "g".to_string(),
        params: vec![
            (
                "x".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
            (
                "y".to_string(),
                crate::ir::TrustVcType::from_str("i32").unwrap(),
            ),
        ],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0 && x <= 50"));
    ctx.push_obligation(ProofObligation::assume("y_bound", "y >= 0 && y <= 50"));

    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("__body_axiom_g", "g(x, y) == x + y")
            .with_bound_vars(vec!["x".to_string(), "y".to_string()])
            .with_trigger_patterns(vec![vec!["g(x, y)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assert("g_wrong", "g(3, 4) == 8"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "g(3,4)==8 when broadcast says g(x,y)==x+y");
}

/// DISCRIMINATING: Multi-variable broadcast over the cap. With 35 two-variable
/// broadcasts, the first 30 are quantified and the rest are ground. Verification
/// must still succeed.
#[test]
fn test_broadcast_multi_variable_over_cap_still_succeeds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));

    for i in 0..35 {
        ctx.obligations.push(
            crate::vc::ProofObligation::broadcast_assume(
                format!("broadcast_{}", i),
                "a + b == b + a",
            )
            .with_bound_vars(vec!["a".to_string(), "b".to_string()]),
        );
    }
    ctx.push_obligation(ProofObligation::assert("commutative", "a + b == b + a"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed();

    expect_verified(
        &result,
        "35 multi-variable broadcasts (over cap) should still verify",
    );
    assert!(
        elapsed.as_secs() < 10,
        "Multi-variable broadcast cap should prevent explosion: {:?}",
        elapsed,
    );
}
