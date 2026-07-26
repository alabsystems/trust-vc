// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Basic invariant open/close protocol tests.

use super::*;

/// Invariant open: assume `inner >= 0 && inner <= 100`.
/// Body: no modification (inner stays the same).
/// Invariant close: assert `inner >= 0 && inner <= 100`.
/// Should verify: predicate trivially preserved.
#[test]
fn test_invariant_open_close_no_modification_verifies() {
    let predicate = bounded_predicate("inner", 100);
    let ctx = build_invariant_context(
        vec![VariableDecl {
            bounded_len: false,
            name: "inner".to_string(),
            ty: i32_type(),
        }],
        vec![
            PreparedObligation {
                name: "invariant_open_inner".to_string(),
                kind: ObligationKind::InvariantOpen,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: Some(0),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate.clone(),
            },
            PreparedObligation {
                name: "invariant_close_inv".to_string(),
                kind: ObligationKind::InvariantClose,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: None,

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate,
            },
        ],
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_verified(
        &result,
        "invariant open+close with no body modification should verify",
    );
}

/// Invariant open: assume `inner >= 0 && inner <= 100`.
/// Body: assume `inner == inner + 1000` (assigns inner to a value > 100).
/// Invariant close: assert `inner >= 0 && inner <= 100`.
/// Should produce counterexample: body violates the predicate.
#[test]
fn test_invariant_close_fails_when_body_violates_predicate() {
    let predicate = bounded_predicate("inner", 100);
    let ctx = build_invariant_context(
        vec![
            VariableDecl {
                bounded_len: false,
                name: "inner".to_string(),
                ty: i32_type(),
            },
            VariableDecl {
                bounded_len: false,
                name: "inner_post".to_string(),
                ty: i32_type(),
            },
        ],
        vec![
            // Open: assume inner in [0, 100]
            PreparedObligation {
                name: "invariant_open_inner".to_string(),
                kind: ObligationKind::InvariantOpen,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: Some(0),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate.clone(),
            },
            // Body effect: inner_post == inner + 1000 (violates bound)
            PreparedObligation {
                name: "body_effect".to_string(),
                kind: ObligationKind::Assume,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: None,

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner_post == inner + 1000".to_string(),
                expr: TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left: Box::new(TrustVcExpr::Var {
                        name: "inner_post".to_string(),
                        ty: i32_type(),
                    }),
                    right: Box::new(TrustVcExpr::Arith {
                        op: ArithOp::Add,
                        left: Box::new(TrustVcExpr::Var {
                            name: "inner".to_string(),
                            ty: i32_type(),
                        }),
                        right: Box::new(TrustVcExpr::IntLit {
                            value: 1000,
                            ty: i32_type(),
                        }),
                        ty: i32_type(),
                    }),
                },
            },
            // Close: assert inner_post in [0, 100] — should FAIL
            PreparedObligation {
                name: "invariant_close_inv".to_string(),
                kind: ObligationKind::InvariantClose,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: None,

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner_post >= 0 && inner_post <= 100".to_string(),
                expr: bounded_predicate("inner_post", 100),
            },
        ],
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_counterexample(
        &result,
        "invariant close should fail when body violates predicate",
    );
}

/// Invariant open: assume `inner >= 0 && inner <= 100`.
/// Body: assume `inner_post == inner + 1` (increment by 1).
/// Invariant close: assert `inner_post >= 0 && inner_post <= 100`.
/// Should verify: inner was in [0, 100], inner_post = inner+1 ∈ [1, 101].
/// But 101 > 100, so this should NOT verify for all values.
///
/// This test verifies soundness: the encoder correctly detects that
/// incrementing an inner variable at the boundary can violate the predicate.
#[test]
fn test_invariant_close_soundness_boundary_violation() {
    let predicate = bounded_predicate("inner", 100);
    let ctx = build_invariant_context(
        vec![
            VariableDecl {
                bounded_len: false,
                name: "inner".to_string(),
                ty: i32_type(),
            },
            VariableDecl {
                bounded_len: false,
                name: "inner_post".to_string(),
                ty: i32_type(),
            },
        ],
        vec![
            PreparedObligation {
                name: "invariant_open_inner".to_string(),
                kind: ObligationKind::InvariantOpen,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: Some(0),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate,
            },
            PreparedObligation {
                name: "body_effect".to_string(),
                kind: ObligationKind::Assume,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: None,

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner_post == inner + 1".to_string(),
                expr: TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left: Box::new(TrustVcExpr::Var {
                        name: "inner_post".to_string(),
                        ty: i32_type(),
                    }),
                    right: Box::new(TrustVcExpr::Arith {
                        op: ArithOp::Add,
                        left: Box::new(TrustVcExpr::Var {
                            name: "inner".to_string(),
                            ty: i32_type(),
                        }),
                        right: Box::new(TrustVcExpr::IntLit {
                            value: 1,
                            ty: i32_type(),
                        }),
                        ty: i32_type(),
                    }),
                },
            },
            PreparedObligation {
                name: "invariant_close_inv".to_string(),
                kind: ObligationKind::InvariantClose,
                location: None,
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                invariant_namespace: None,

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner_post >= 0 && inner_post <= 100".to_string(),
                expr: bounded_predicate("inner_post", 100),
            },
        ],
    );

    let result = AYEncoder::verify_prepared(&ctx);
    // inner=100 → inner_post=101 > 100, so close assertion fails.
    expect_counterexample(&result, "boundary increment should produce counterexample");
}
