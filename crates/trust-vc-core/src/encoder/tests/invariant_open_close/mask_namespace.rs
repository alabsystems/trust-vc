// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mask namespace tests: double-open, different namespaces, fail-closed.

use super::*;

/// Two InvariantOpen with the same namespace (re-entrancy violation).
/// Should return Error: double open detected.
#[test]
fn test_mask_rejects_double_open_same_namespace() {
    let predicate = bounded_predicate("inner", 100);
    let predicate2 = bounded_predicate("inner2", 100);
    let ctx = build_masked_context(
        vec![
            VariableDecl {
                bounded_len: false,
                name: "inner".to_string(),
                ty: i32_type(),
            },
            VariableDecl {
                bounded_len: false,
                name: "inner2".to_string(),
                ty: i32_type(),
            },
        ],
        vec![
            PreparedObligation {
                name: "invariant_open_first".to_string(),
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
                invariant_namespace: Some(42),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate,
            },
            PreparedObligation {
                name: "invariant_open_second".to_string(),
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
                invariant_namespace: Some(42),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner2 >= 0 && inner2 <= 100".to_string(),
                expr: predicate2.clone(),
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
                invariant_namespace: Some(42),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner2 >= 0 && inner2 <= 100".to_string(),
                expr: predicate2,
            },
        ],
        InvariantMask::Any,
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_error(&result, "double open of namespace 42 should be rejected");
    if let VerifyResult::Error { message } = &result {
        assert!(
            message.contains("opened twice"),
            "error should mention re-entrancy: {}",
            message
        );
    }
}

/// Two InvariantOpen with different namespaces — both allowed.
/// Should verify normally: no re-entrancy conflict.
#[test]
fn test_mask_allows_different_namespaces() {
    let predicate1 = bounded_predicate("inner1", 100);
    let predicate2 = bounded_predicate("inner2", 200);
    let ctx = build_masked_context(
        vec![
            VariableDecl {
                bounded_len: false,
                name: "inner1".to_string(),
                ty: i32_type(),
            },
            VariableDecl {
                bounded_len: false,
                name: "inner2".to_string(),
                ty: i32_type(),
            },
        ],
        vec![
            PreparedObligation {
                name: "invariant_open_ns10".to_string(),
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
                invariant_namespace: Some(10),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner1 >= 0 && inner1 <= 100".to_string(),
                expr: predicate1.clone(),
            },
            PreparedObligation {
                name: "invariant_close_ns10".to_string(),
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
                invariant_namespace: Some(10),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner1 >= 0 && inner1 <= 100".to_string(),
                expr: predicate1,
            },
            PreparedObligation {
                name: "invariant_open_ns20".to_string(),
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
                invariant_namespace: Some(20),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner2 >= 0 && inner2 <= 200".to_string(),
                expr: predicate2.clone(),
            },
            PreparedObligation {
                name: "invariant_close_ns20".to_string(),
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
                invariant_namespace: Some(20),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner2 >= 0 && inner2 <= 200".to_string(),
                expr: predicate2,
            },
        ],
        InvariantMask::Namespaces(vec![10, 20]),
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_verified(&result, "two different namespaces should both be allowed");
}

/// InvariantOpen without a namespace (invariant_namespace: None) is rejected
/// as a fail-closed error. The proc-macro always provides a namespace, so
/// namespace-less InvariantOpen can only arise from direct API misuse. (#2474)
#[test]
fn test_no_namespace_rejected_fail_closed() {
    let predicate = bounded_predicate("inner", 100);
    let ctx = build_masked_context(
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
                invariant_namespace: None,

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
        InvariantMask::None,
    );

    let result = AYEncoder::verify_prepared(&ctx);
    match &result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("no namespace"),
                "error should mention missing namespace, got: {message}"
            );
        }
        other => panic!(
            "namespace-less InvariantOpen should be rejected, got: {:?}",
            other
        ),
    }
}
