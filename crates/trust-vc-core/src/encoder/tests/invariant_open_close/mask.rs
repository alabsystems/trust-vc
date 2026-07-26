// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mask enforcement tests: basic namespace allow/reject (Part of #2427 Slice 4).

use super::*;

/// InvariantOpen with namespace 42, mask allows namespace 42.
/// Should verify normally (mask allows the open).
#[test]
fn test_mask_allows_namespace_verifies() {
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
                invariant_namespace: Some(42),

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
                invariant_namespace: Some(42),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate,
            },
        ],
        InvariantMask::Namespaces(vec![42]),
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_verified(
        &result,
        "mask allowing namespace 42 should let invariant open succeed",
    );
}

/// InvariantOpen with namespace 42, mask is `None` (no invariants allowed).
/// Should return Error: namespace not allowed.
#[test]
fn test_mask_none_rejects_open() {
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
                invariant_namespace: Some(42),

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
                invariant_namespace: Some(42),

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
    expect_error(&result, "mask None should reject invariant open");
    if let VerifyResult::Error { message } = &result {
        assert!(
            message.contains("not allowed"),
            "error should mention namespace not allowed: {}",
            message
        );
    }
}

/// InvariantOpen with namespace 42, mask only allows namespace 99.
/// Should return Error: namespace not in allowed set.
#[test]
fn test_mask_wrong_namespace_rejects_open() {
    let predicate = bounded_predicate("inner", 50);
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
                invariant_namespace: Some(42),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 50".to_string(),
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
                invariant_namespace: Some(42),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 50".to_string(),
                expr: predicate,
            },
        ],
        InvariantMask::Namespaces(vec![99]),
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_error(&result, "mask [99] should reject namespace 42 open");
}

/// InvariantOpen with `Any` mask always succeeds regardless of namespace.
#[test]
fn test_mask_any_allows_all_namespaces() {
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
                invariant_namespace: Some(999),

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
                invariant_namespace: Some(999),

                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
                condition: "inner >= 0 && inner <= 100".to_string(),
                expr: predicate,
            },
        ],
        InvariantMask::Any,
    );

    let result = AYEncoder::verify_prepared(&ctx);
    expect_verified(&result, "mask Any should allow any namespace");
}
