//! Broadcast requires-guard encoding tests.
//!
//! Issues: #2575
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Broadcast requires-guard encoding (#2575)
// ========================================================================

/// DISCRIMINATING: Broadcast with `requires!(x > 0)` and `ensures!(f(x) > 0)`
/// must prove `f(a) > 0` when `a > 0`. The guard is folded into the axiom as
/// `x > 0 ==> f(x) > 0`, so the postcondition applies only within the
/// precondition domain.
#[test]
fn test_broadcast_guard_positive_proves_within_domain() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Broadcast: requires x > 0, ensures f(x) > 0
    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("broadcast_guarded", "f(x) > 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]);
    obligation.broadcast_guard = Some(vec![crate::vc::BroadcastGuardClause {
        condition: "x > 0".to_string(),
    }]);
    ctx.obligations.push(obligation);

    // Assume a > 0 (within domain), then assert f(a) > 0
    ctx.push_obligation(ProofObligation::assume("a_positive", "a > 0"));
    ctx.push_obligation(ProofObligation::assert("f_a_positive", "f(a) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DISCRIMINATING: Guarded broadcast (x>0 ==> f(x)>0) must prove f(a)>0 when a>0",
    );
}

/// DISCRIMINATING: The same guarded broadcast must NOT prove `f(a) > 0` when
/// `a == 0`. The guard `x > 0` blocks the axiom at `x == 0`, so the solver
/// has no information about `f(0)`.
#[test]
fn test_broadcast_guard_negative_outside_domain() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Same broadcast: requires x > 0, ensures f(x) > 0
    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("broadcast_guarded", "f(x) > 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]);
    obligation.broadcast_guard = Some(vec![crate::vc::BroadcastGuardClause {
        condition: "x > 0".to_string(),
    }]);
    ctx.obligations.push(obligation);

    // a == 0 (outside domain), then assert f(a) > 0 — should FAIL
    ctx.push_obligation(ProofObligation::assume("a_zero", "a == 0"));
    ctx.push_obligation(ProofObligation::assert("f_a_positive", "f(a) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Guarded broadcast must NOT prove f(a)>0 when a==0 (outside requires domain)",
    );
}

/// Broadcast WITHOUT a guard behaves exactly as before — no regression.
/// This confirms that the guard-handling code path does not alter the
/// behavior of guardless broadcasts.
#[test]
fn test_broadcast_without_guard_unchanged_behavior() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Broadcast WITHOUT guard: ensures f(x) > 0 for ALL x
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_unguarded", "f(x) > 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
    );

    // Even at a == 0, the unguarded broadcast proves f(a) > 0
    ctx.push_obligation(ProofObligation::assume("a_zero", "a == 0"));
    ctx.push_obligation(ProofObligation::assert("f_a_positive", "f(a) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Unguarded broadcast f(x)>0 must still prove f(a)>0 for any a (no regression)",
    );
}

/// DISCRIMINATING: Broadcast with multiple requires clauses. Both guards
/// must be conjoined: `x > 0 && x < 100 ==> f(x) > 0`. The assertion
/// `f(50) > 0` should verify (50 is within [1, 99]).
#[test]
fn test_broadcast_guard_multiple_clauses_positive() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Two guard clauses: requires x > 0, requires x < 100
    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("broadcast_multi_guard", "f(x) > 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]);
    obligation.broadcast_guard = Some(vec![
        crate::vc::BroadcastGuardClause {
            condition: "x > 0".to_string(),
        },
        crate::vc::BroadcastGuardClause {
            condition: "x < 100".to_string(),
        },
    ]);
    ctx.obligations.push(obligation);

    ctx.push_obligation(ProofObligation::assume("a_in_range", "a == 50"));
    ctx.push_obligation(ProofObligation::assert("f_a_positive", "f(a) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multi-guard broadcast (x>0 && x<100 ==> f(x)>0) should prove f(50)>0",
    );
}

/// DISCRIMINATING: Multi-guard broadcast must NOT prove f(a) > 0 when a
/// satisfies only one of the two requires clauses (a == 200 satisfies
/// x > 0 but NOT x < 100).
#[test]
fn test_broadcast_guard_multiple_clauses_partial_fail() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("broadcast_multi_guard", "f(x) > 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]);
    obligation.broadcast_guard = Some(vec![
        crate::vc::BroadcastGuardClause {
            condition: "x > 0".to_string(),
        },
        crate::vc::BroadcastGuardClause {
            condition: "x < 100".to_string(),
        },
    ]);
    ctx.obligations.push(obligation);

    // a == 200: satisfies x > 0 but NOT x < 100
    ctx.push_obligation(ProofObligation::assume("a_out_of_range", "a == 200"));
    ctx.push_obligation(ProofObligation::assert("f_a_positive", "f(a) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Multi-guard broadcast must NOT prove f(200)>0 (only one guard satisfied)",
    );
}

/// Broadcast obligation with conservative (default) trigger inference mode
/// returns only the best single trigger group. Part of #2461 Slice 3.
#[test]
fn test_broadcast_conservative_trigger_mode() {
    use crate::trigger_inference::TriggerInferenceMode;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "f",
        crate::ir::TrustVcType::Int { width: 32 },
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        crate::ir::TrustVcType::Int { width: 32 },
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );

    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("conservative_bc", "f(x) > 0 && g(x) > 0")
            .with_bound_vars(vec!["x".to_string()]);
    obligation.trigger_inference_mode = Some(TriggerInferenceMode::Conservative);
    ctx.obligations.push(obligation);

    ctx.push_obligation(ProofObligation::assert("check", "f(x) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(
        &result,
        "Broadcast with conservative trigger inference mode",
    );
}
