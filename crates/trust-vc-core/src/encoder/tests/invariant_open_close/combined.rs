// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Combined invariant tests: guarded body + mixed obligations.

use super::*;

/// Invariant open: assume `inner >= 0 && inner <= 100`.
/// Body: guard + modify: assume `inner < 100`, inner_post = inner + 1.
/// Invariant close: assert `inner_post >= 0 && inner_post <= 100`.
/// Should verify: guarded increment stays in bounds.
#[test]
fn test_invariant_close_succeeds_with_guarded_body() {
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
            // Guard: inner < 100 (so inner+1 <= 100)
            PreparedObligation {
                name: "body_guard".to_string(),
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
                condition: "inner < 100".to_string(),
                expr: TrustVcExpr::Compare {
                    op: CompareOp::Lt,
                    left: Box::new(TrustVcExpr::Var {
                        name: "inner".to_string(),
                        ty: i32_type(),
                    }),
                    right: Box::new(TrustVcExpr::IntLit {
                        value: 100,
                        ty: i32_type(),
                    }),
                },
            },
            // Body: inner_post = inner + 1
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
    expect_verified(&result, "guarded increment should verify");
}

/// Mixed context: regular requires + invariant open/close + regular assert.
/// Verifies that invariant obligations work alongside standard obligations.
#[test]
fn test_invariant_mixed_with_regular_obligations() {
    let predicate = bounded_predicate("inner", 50);
    let ctx = build_invariant_context(
        vec![
            VariableDecl {
                bounded_len: false,
                name: "x".to_string(),
                ty: i32_type(),
            },
            VariableDecl {
                bounded_len: false,
                name: "inner".to_string(),
                ty: i32_type(),
            },
        ],
        vec![
            // Regular assumption: x > 0
            PreparedObligation {
                name: "pre_x_positive".to_string(),
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
                condition: "x > 0".to_string(),
                expr: TrustVcExpr::Compare {
                    op: CompareOp::Gt,
                    left: Box::new(TrustVcExpr::Var {
                        name: "x".to_string(),
                        ty: i32_type(),
                    }),
                    right: Box::new(TrustVcExpr::IntLit {
                        value: 0,
                        ty: i32_type(),
                    }),
                },
            },
            // Invariant open: inner in [0, 50]
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
                condition: "inner >= 0 && inner <= 50".to_string(),
                expr: predicate.clone(),
            },
            // Invariant close: inner still in [0, 50] (no modification)
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
                condition: "inner >= 0 && inner <= 50".to_string(),
                expr: predicate,
            },
            // Regular assertion: x > 0 (from pre-assumption)
            PreparedObligation {
                name: "post_x_positive".to_string(),
                kind: ObligationKind::Assert,
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
                condition: "x > 0".to_string(),
                expr: TrustVcExpr::Compare {
                    op: CompareOp::Gt,
                    left: Box::new(TrustVcExpr::Var {
                        name: "x".to_string(),
                        ty: i32_type(),
                    }),
                    right: Box::new(TrustVcExpr::IntLit {
                        value: 0,
                        ty: i32_type(),
                    }),
                },
            },
        ],
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_verified(
        &result,
        "mixed context with invariant + regular obligations should verify",
    );
}
