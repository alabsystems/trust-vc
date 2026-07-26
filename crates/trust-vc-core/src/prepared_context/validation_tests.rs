// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the validation boundary.
//!
//! Split from `validation.rs` for the 500-line limit (#2621).

use super::*;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::prepared_context::PreparedVerificationContext;
use crate::vc::{ConditionOrigin, ObligationKind, VariableDecl, VerificationMode};

fn var_decl(name: &str, ty: TrustVcType) -> VariableDecl {
    VariableDecl {
        bounded_len: false,
        name: name.to_string(),
        ty,
    }
}

fn simple_obligation(
    name: &str,
    kind: ObligationKind,
    origin: ConditionOrigin,
) -> PreparedObligation {
    PreparedObligation {
        name: name.to_string(),
        kind,
        location: None,
        condition_origin: origin,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        condition: "true".to_string(),
        expr: TrustVcExpr::BoolLit(true),
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

fn simple_ctx_with(obligations: Vec<PreparedObligation>) -> PreparedVerificationContext {
    PreparedVerificationContext {
        obligations,
        variables: vec![var_decl("x", TrustVcType::Int { width: 32 })],
        ..Default::default()
    }
}

#[test]
fn test_simple_assertion_validates() {
    let ctx = simple_ctx_with(vec![simple_obligation(
        "test_assert",
        ObligationKind::Assert,
        ConditionOrigin::LoweredFromCondition,
    )]);
    let validated = validate_prepared_context(&ctx);
    assert!(validated.is_ok(), "simple assertion should validate");
    let plan = &validated.unwrap().plan;
    assert_eq!(plan.assertions.len(), 1);
    assert!(plan.assumptions.is_empty());
}

#[test]
fn test_empty_context_rejected() {
    let ctx = simple_ctx_with(vec![]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::EmptyContext),
        "empty context should be rejected"
    );
}

#[test]
fn test_only_assumptions_rejected() {
    let ctx = simple_ctx_with(vec![simple_obligation(
        "assume_only",
        ObligationKind::Assume,
        ConditionOrigin::LoweredFromCondition,
    )]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::OnlyAssumptions),
        "assumptions-only context should be rejected"
    );
}

#[test]
fn test_opaque_variable_rejected() {
    let ctx = PreparedVerificationContext {
        obligations: vec![simple_obligation(
            "a",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        )],
        variables: vec![var_decl("x", TrustVcType::Opaque("MyStruct".to_string()))],
        ..Default::default()
    };
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(matches!(err, ValidationError::OpaqueVariable { .. }));
}

#[test]
fn test_float_variable_allowed() {
    let ctx = PreparedVerificationContext {
        obligations: vec![simple_obligation(
            "a",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        )],
        variables: vec![var_decl("x", TrustVcType::Float { width: 64 })],
        ..Default::default()
    };
    validate_prepared_context(&ctx).expect("float variables should validate");
}

#[test]
fn test_malformed_trigger_rejected() {
    let mut obligation = simple_obligation(
        "trigger_test",
        ObligationKind::Assert,
        ConditionOrigin::LoweredFromCondition,
    );
    // Declare 2 trigger groups but prepared_triggers is None (all lost).
    obligation.trigger_patterns = Some(vec![vec!["f(x)".to_string()], vec!["g(x)".to_string()]]);
    // prepared_triggers left as None — lossy lowering.

    let ctx = simple_ctx_with(vec![obligation]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(
            err,
            ValidationError::MalformedTrigger {
                expected_groups: 2,
                lowered_groups: 0,
                ..
            }
        ),
        "malformed triggers should be rejected"
    );
}

#[test]
fn test_legacy_translated_with_triggers_rejected() {
    let mut obligation = simple_obligation(
        "legacy_trigger",
        ObligationKind::Assert,
        ConditionOrigin::LegacyTranslatedString,
    );
    obligation.trigger_patterns = Some(vec![vec!["f(x)".to_string()]]);

    let ctx = simple_ctx_with(vec![obligation]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::LegacyStructuredObligation { .. }),
        "legacy-translated obligation with triggers should be rejected"
    );
}

#[test]
fn test_legacy_translated_broadcast_with_bound_vars_rejected() {
    let mut obligation = simple_obligation(
        "legacy_broadcast",
        ObligationKind::BroadcastAssume,
        ConditionOrigin::LegacyTranslatedString,
    );
    obligation.bound_vars = Some(vec!["x".to_string()]);

    let ctx = simple_ctx_with(vec![
        simple_obligation(
            "assertion",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        ),
        obligation,
    ]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::LegacyStructuredObligation { .. }),
        "legacy-translated broadcast with bound vars should be rejected"
    );
}

#[test]
fn test_legacy_translated_measure_rejected() {
    let obligation = simple_obligation(
        "legacy_measure",
        ObligationKind::MeasureDecreases,
        ConditionOrigin::LegacyTranslatedString,
    );
    let ctx = simple_ctx_with(vec![obligation]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::LegacyStructuredObligation { .. }),
        "legacy-translated measure obligation should be rejected"
    );
}

#[test]
fn test_lane_classification_body_level() {
    let ctx = PreparedVerificationContext {
        obligations: vec![
            simple_obligation(
                "req",
                ObligationKind::Requires,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "ens",
                ObligationKind::Ensures,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "bc",
                ObligationKind::BroadcastAssume,
                ConditionOrigin::PreBuiltExprCache,
            ),
            simple_obligation(
                "rec",
                ObligationKind::Recommends,
                ConditionOrigin::LoweredFromCondition,
            ),
        ],
        variables: vec![var_decl("x", TrustVcType::Int { width: 32 })],
        verification_mode: VerificationMode::BodyLevel,
        ..Default::default()
    };
    let validated = validate_prepared_context(&ctx).unwrap();
    let plan = &validated.plan;
    // At body level: Requires → assumption; Recommends is ADVISORY (soft-warning
    // check), NEVER assumed — assuming it in the body was a false-verify (a
    // function's own recommends let a false ensures verify). Recommends → the
    // `recommends` lane at every mode.
    assert_eq!(plan.assumptions.len(), 1, "only Requires at body level");
    assert_eq!(plan.assertions.len(), 1, "Ensures → assertion");
    assert_eq!(plan.broadcast_assumptions.len(), 1);
    assert_eq!(
        plan.recommends.len(),
        1,
        "Recommends is a soft-warning check, not a body assumption"
    );
}

#[test]
fn test_lane_classification_call_site() {
    let ctx = PreparedVerificationContext {
        obligations: vec![
            simple_obligation(
                "req",
                ObligationKind::Requires,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "ens",
                ObligationKind::Ensures,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "rec",
                ObligationKind::Recommends,
                ConditionOrigin::LoweredFromCondition,
            ),
        ],
        variables: vec![var_decl("x", TrustVcType::Int { width: 32 })],
        verification_mode: VerificationMode::CallSite,
        ..Default::default()
    };
    let validated = validate_prepared_context(&ctx).unwrap();
    let plan = &validated.plan;
    // At call site: Requires → assertion, Recommends → recommends
    assert_eq!(plan.assertions.len(), 2, "Requires + Ensures → assertions");
    assert_eq!(plan.recommends.len(), 1, "Recommends checked at call site");
    assert!(plan.assumptions.is_empty());
}

#[test]
fn test_reveal_obligation_is_metadata_only() {
    let ctx = simple_ctx_with(vec![
        simple_obligation(
            "reveal_fn",
            ObligationKind::Reveal,
            ConditionOrigin::LoweredFromCondition,
        ),
        simple_obligation(
            "assertion",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        ),
    ]);
    let validated = validate_prepared_context(&ctx).unwrap();
    let plan = &validated.plan;
    assert_eq!(plan.assertions.len(), 1);
    assert!(
        plan.assumptions.is_empty(),
        "Reveal is metadata, not an assumption"
    );
}

#[test]
fn test_prebuilt_cache_origin_validates() {
    let ctx = simple_ctx_with(vec![simple_obligation(
        "cached_assert",
        ObligationKind::Assert,
        ConditionOrigin::PreBuiltExprCache,
    )]);
    assert!(
        validate_prepared_context(&ctx).is_ok(),
        "PreBuiltExprCache origin should validate"
    );
}

#[test]
fn test_partial_trigger_loss_rejected() {
    use super::super::obligation::PreparedTrigger;

    let mut obligation = simple_obligation(
        "partial_trigger",
        ObligationKind::Assert,
        ConditionOrigin::LoweredFromCondition,
    );
    // Declare 2 trigger groups
    obligation.trigger_patterns = Some(vec![vec!["f(x)".to_string()], vec!["g(x)".to_string()]]);
    // Only 1 group survived lowering
    obligation.prepared_triggers = Some(vec![vec![PreparedTrigger {
        source: "f(x)".to_string(),
        expr: TrustVcExpr::BoolLit(true),
        head_symbol: Some("f".to_string()),
    }]]);

    let ctx = simple_ctx_with(vec![obligation]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(
            err,
            ValidationError::MalformedTrigger {
                expected_groups: 2,
                lowered_groups: 1,
                ..
            }
        ),
        "partial trigger loss should be rejected"
    );
}

#[test]
fn test_partial_trigger_term_loss_rejected() {
    use super::super::obligation::PreparedTrigger;

    let mut obligation = simple_obligation(
        "partial_trigger_terms",
        ObligationKind::Assert,
        ConditionOrigin::LoweredFromCondition,
    );
    obligation.trigger_patterns = Some(vec![vec!["f(x)".to_string(), "g(x)".to_string()]]);
    obligation.prepared_triggers = Some(vec![vec![PreparedTrigger {
        source: "f(x)".to_string(),
        expr: TrustVcExpr::BoolLit(true),
        head_symbol: Some("f".to_string()),
    }]]);

    let ctx = simple_ctx_with(vec![obligation]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(
            err,
            ValidationError::MalformedTrigger {
                expected_groups: 2,
                lowered_groups: 1,
                ..
            }
        ),
        "partial trigger term loss should be rejected"
    );
}

#[test]
fn test_dropped_broadcast_guard_rejected() {
    let mut obligation = simple_obligation(
        "broadcast_guard_lost",
        ObligationKind::BroadcastAssume,
        ConditionOrigin::LoweredFromCondition,
    );
    obligation.raw_broadcast_guard_count = 1;

    let ctx = simple_ctx_with(vec![obligation]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::DroppedBroadcastGuard { .. }),
        "broadcast guard loss should be rejected"
    );
}

#[test]
fn test_invariant_open_without_namespace_rejected() {
    let mut obligation = simple_obligation(
        "inv_open_no_ns",
        ObligationKind::InvariantOpen,
        ConditionOrigin::LoweredFromCondition,
    );
    obligation.invariant_namespace = None;

    // Need at least one assertion to pass emptiness checks.
    let ctx = simple_ctx_with(vec![
        obligation,
        simple_obligation(
            "a",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        ),
    ]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(err, ValidationError::InvariantMissingNamespace { .. }),
        "InvariantOpen without namespace should be rejected"
    );
}

#[test]
fn test_invariant_mask_violation_rejected() {
    use crate::vc::InvariantMask;

    let mut obligation = simple_obligation(
        "inv_open_blocked",
        ObligationKind::InvariantOpen,
        ConditionOrigin::LoweredFromCondition,
    );
    obligation.invariant_namespace = Some(42);

    let ctx = PreparedVerificationContext {
        obligations: vec![
            obligation,
            simple_obligation(
                "a",
                ObligationKind::Assert,
                ConditionOrigin::LoweredFromCondition,
            ),
        ],
        variables: vec![var_decl("x", TrustVcType::Int { width: 32 })],
        invariant_mask: InvariantMask::None,
        ..Default::default()
    };
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(
            err,
            ValidationError::InvariantMaskViolation { namespace: 42, .. }
        ),
        "InvariantOpen for blocked namespace should be rejected"
    );
}

#[test]
fn test_invariant_reentry_rejected() {
    let mut open1 = simple_obligation(
        "inv_open_1",
        ObligationKind::InvariantOpen,
        ConditionOrigin::LoweredFromCondition,
    );
    open1.invariant_namespace = Some(7);

    let mut open2 = simple_obligation(
        "inv_open_2",
        ObligationKind::InvariantOpen,
        ConditionOrigin::LoweredFromCondition,
    );
    open2.invariant_namespace = Some(7); // same namespace = re-entrancy

    let ctx = simple_ctx_with(vec![
        open1,
        open2,
        simple_obligation(
            "a",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        ),
    ]);
    let err = validate_prepared_context(&ctx).unwrap_err();
    assert!(
        matches!(
            err,
            ValidationError::InvariantReentrancy { namespace: 7, .. }
        ),
        "same namespace opened twice should be rejected"
    );
}

#[test]
fn test_lane_classification_loop_and_measure_obligations() {
    let ctx = PreparedVerificationContext {
        obligations: vec![
            simple_obligation(
                "li",
                ObligationKind::LoopInvariant,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "ieb",
                ObligationKind::InvariantExceptBreak,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "lg",
                ObligationKind::LoopGuard,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "le",
                ObligationKind::LoopEnsures,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "pla",
                ObligationKind::PostLoopAssume,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "ab",
                ObligationKind::AssertBy,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "mnn",
                ObligationKind::MeasureNonNegative,
                ConditionOrigin::LoweredFromCondition,
            ),
            simple_obligation(
                "md",
                ObligationKind::MeasureDecreases,
                ConditionOrigin::LoweredFromCondition,
            ),
        ],
        variables: vec![var_decl("x", TrustVcType::Int { width: 32 })],
        ..Default::default()
    };
    let validated = validate_prepared_context(&ctx).unwrap();
    let plan = &validated.plan;
    assert_eq!(
        plan.loop_invariants.len(),
        2,
        "LoopInvariant + InvariantExceptBreak"
    );
    assert_eq!(plan.loop_guards.len(), 1, "LoopGuard");
    assert_eq!(plan.loop_ensures.len(), 1, "LoopEnsures");
    assert_eq!(plan.assumptions.len(), 1, "PostLoopAssume → assumptions");
    assert_eq!(plan.assert_by.len(), 1, "AssertBy");
    assert_eq!(
        plan.assertions.len(),
        2,
        "MeasureNonNegative + MeasureDecreases → assertions"
    );
}

#[test]
fn test_invariant_open_close_classification() {
    let mut open = simple_obligation(
        "inv_open",
        ObligationKind::InvariantOpen,
        ConditionOrigin::LoweredFromCondition,
    );
    open.invariant_namespace = Some(1);

    let ctx = PreparedVerificationContext {
        obligations: vec![
            open,
            simple_obligation(
                "inv_close",
                ObligationKind::InvariantClose,
                ConditionOrigin::LoweredFromCondition,
            ),
        ],
        variables: vec![var_decl("x", TrustVcType::Int { width: 32 })],
        // InvariantMask defaults to Any — allows all namespaces
        ..Default::default()
    };
    let validated = validate_prepared_context(&ctx).unwrap();
    let plan = &validated.plan;
    assert_eq!(plan.assumptions.len(), 1, "InvariantOpen → assumption");
    assert_eq!(plan.assertions.len(), 1, "InvariantClose → assertion");
}

#[test]
fn test_multiple_opaque_variables_all_reported() {
    let ctx = PreparedVerificationContext {
        obligations: vec![simple_obligation(
            "a",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        )],
        variables: vec![
            var_decl("x", TrustVcType::Opaque("Vec<i32>".to_string())),
            var_decl("y", TrustVcType::Opaque("Widget".to_string())),
        ],
        ..Default::default()
    };
    let err = validate_prepared_context(&ctx).unwrap_err();
    match err {
        ValidationError::OpaqueVariable { variables } => {
            assert_eq!(
                variables.len(),
                2,
                "both opaque variables should be collected"
            );
            let names: Vec<&str> = variables.iter().map(|(n, _)| n.as_str()).collect();
            assert!(names.contains(&"x"), "x should be reported");
            assert!(names.contains(&"y"), "y should be reported");
        }
        other => panic!("expected OpaqueVariable, got: {other:?}"),
    }
}

#[test]
fn test_multiple_float_variables_validate() {
    let ctx = PreparedVerificationContext {
        obligations: vec![simple_obligation(
            "a",
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        )],
        variables: vec![
            var_decl("f1", TrustVcType::Float { width: 32 }),
            var_decl("f2", TrustVcType::Float { width: 64 }),
        ],
        ..Default::default()
    };
    validate_prepared_context(&ctx).expect("multiple float variables should validate");
}

// --- #2778 bit_vector diagnostic-parity wiring -------------------------------
//
// These exercise the full `validate_prepared_context` →
// `validate_obligation_integrity` → `detect_bit_vector_parity_error` path for a
// `by(bit_vector)` proof, covering the upstream Verus cases
// `not_supported_int_in_by_bit_vector`,
// `not_supported_datatype_in_by_bit_vector`, and the finite-width-operand
// acceptance that backs `usize_in_by_bit_vector` /
// `bit_vector_usize_as_32bit` / `bit_vector_usize_as_64bit`. The byte-exact
// message text is unit-tested in `ir_lowering::diagnostic_parity`; here we pin
// that the *validation boundary* routes a real bit-vector obligation to those
// messages (or accepts it), in both the should-fail and should-verify
// directions. Every error is fail-closed: the parity message is only produced
// after a provably-unmodellable operand is detected, never to fabricate a pass.

/// Builds a `by(bit_vector)` assertion obligation over `expr`.
fn bit_vector_assert(name: &str, expr: TrustVcExpr) -> PreparedObligation {
    PreparedObligation {
        solver_mode: Some(crate::vc::SolverMode::BitVector),
        condition: "<bit_vector>".to_string(),
        expr,
        ..simple_obligation(
            name,
            ObligationKind::Assert,
            ConditionOrigin::LoweredFromCondition,
        )
    }
}

fn ctx_with_obligation(obligation: PreparedObligation) -> PreparedVerificationContext {
    PreparedVerificationContext {
        obligations: vec![obligation],
        variables: vec![var_decl("x", TrustVcType::Uint { width: 32 })],
        ..Default::default()
    }
}

#[test]
fn test_bit_vector_int_operand_rejected_with_finite_width_message() {
    // Upstream: not_supported_int_in_by_bit_vector
    //   `assert(x == y) by (bit_vector)` with `x: int, y: int`
    //   => Err: "expected finite-width integer".
    let int_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::MathInt,
    };
    let ctx = ctx_with_obligation(bit_vector_assert("not_supported_int", int_var));
    let err = validate_prepared_context(&ctx)
        .expect_err("a by(bit_vector) proof over an `int` operand must fail closed");
    match err {
        ValidationError::BitVectorParity { message, .. } => {
            // Byte-exact upstream `bitvector_to_air.rs` text; the asserted
            // upstream substring is `expected finite-width integer`.
            assert_eq!(
                message,
                "IntRange error: expected finite-width integer for bit-vector, got Int(Int)"
            );
            assert!(message.contains("expected finite-width integer"));
        }
        other => panic!("expected BitVectorParity, got: {other:?}"),
    }
}

#[test]
fn test_bit_vector_nat_operand_rejected_with_finite_width_message() {
    // `nat` is likewise non-finite-width and must fail closed with the same
    // upstream substring (`got Int(Nat)` trailing token).
    let nat_var = TrustVcExpr::Var {
        name: "n".to_string(),
        ty: TrustVcType::Nat,
    };
    let ctx = ctx_with_obligation(bit_vector_assert("not_supported_nat", nat_var));
    let err = validate_prepared_context(&ctx)
        .expect_err("a by(bit_vector) proof over a `nat` operand must fail closed");
    match err {
        ValidationError::BitVectorParity { message, .. } => {
            assert_eq!(
                message,
                "IntRange error: expected finite-width integer for bit-vector, got Int(Nat)"
            );
            assert!(message.contains("expected finite-width integer"));
        }
        other => panic!("expected BitVectorParity, got: {other:?}"),
    }
}

#[test]
fn test_bit_vector_datatype_operand_rejected_with_cannot_handle_message() {
    // Upstream: not_supported_datatype_in_by_bit_vector
    //   `struct X {}` then `assert(x == y) by (bit_vector)` with `x: X, y: X`
    //   => Err: "bit_vector prover cannot handle type `...X`".
    let datatype = TrustVcType::Datatype {
        name: "X".to_string(),
        variants: vec![crate::ir::DatatypeVariant::new("X", vec![])],
    };
    let datatype_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: datatype,
    };
    let ctx = ctx_with_obligation(bit_vector_assert("not_supported_datatype", datatype_var));
    let err = validate_prepared_context(&ctx)
        .expect_err("a by(bit_vector) proof over a datatype operand must fail closed");
    match err {
        ValidationError::BitVectorParity { message, .. } => {
            assert_eq!(message, "error: bit_vector prover cannot handle type `X`");
            // Asserted upstream substring (modulo crate prefix; see the
            // detector's SOUND-but-not-byte-exact note).
            assert!(message.contains("bit_vector prover cannot handle type `X`"));
        }
        other => panic!("expected BitVectorParity, got: {other:?}"),
    }
}

#[test]
fn test_bit_vector_finite_width_usize_operand_accepted() {
    // Upstream should-verify direction: `usize_in_by_bit_vector` and the
    // finite-width operands inside `bit_vector_usize_as_32bit` /
    // `bit_vector_usize_as_64bit` (`assert(x & x == x) by(bit_vector)` with
    // `x: usize`). A finite-width unsigned operand is modellable, so the parity
    // detector must NOT fire and the obligation must validate as an assertion.
    let usize_var = TrustVcExpr::Var {
        name: "x".to_string(),
        // `usize` lowers to `Uint { width: pointer_width() }`; any finite width
        // is fine — the detector keys on finite-width-ness, not the exact width.
        ty: TrustVcType::Uint { width: 64 },
    };
    let ctx = ctx_with_obligation(bit_vector_assert("usize_in_by_bit_vector", usize_var));
    let validated = validate_prepared_context(&ctx)
        .expect("a by(bit_vector) proof over a finite-width `usize` operand must validate");
    assert_eq!(validated.plan.assertions.len(), 1);
}

#[test]
fn test_bit_vector_finite_width_u32_operand_accepted() {
    // Companion should-verify direction for a fixed-width operand (mirrors the
    // `test_and` / `test_xor` finite-width bitwise asserts): a `u32` variable is
    // modellable and must validate without a parity error.
    let u32_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Uint { width: 32 },
    };
    let ctx = ctx_with_obligation(bit_vector_assert("finite_width_u32", u32_var));
    validate_prepared_context(&ctx)
        .expect("a by(bit_vector) proof over a finite-width `u32` operand must validate");
}

#[test]
fn test_non_bit_vector_int_operand_not_flagged() {
    // Soundness guard: the parity detector is gated on `SolverMode::BitVector`.
    // An `int`-typed operand in a *normal* (non-bit-vector) obligation must be
    // left to the solver, NOT rejected with the bit-vector parity message —
    // upstream `int` is perfectly fine outside `by(bit_vector)`.
    let int_var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::MathInt,
    };
    let mut obligation = bit_vector_assert("normal_int", int_var);
    obligation.solver_mode = None;
    let ctx = ctx_with_obligation(obligation);
    validate_prepared_context(&ctx)
        .expect("an `int` operand outside by(bit_vector) must not be flagged as a parity error");
}

// Builds `eq(left, right)` — the lowered shape of `left == right`, the operand
// container in every `assert(x == y) by(bit_vector)` upstream case.
fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir_expr::CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn datatype_x() -> TrustVcType {
    TrustVcType::Datatype {
        name: "X".to_string(),
        variants: vec![crate::ir::DatatypeVariant::new("X", vec![])],
    }
}

#[test]
fn test_bit_vector_datatype_operands_in_equality_rejected() {
    // Upstream `not_supported_datatype_in_by_bit_vector`: the operand lives
    // inside an equality (`assert(x == y) by(bit_vector)` with `x: X, y: X`).
    // The parity message must surface from the actual struct-typed operand even
    // when it is nested under `==`, not from a downstream encoder surrogate.
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: datatype_x(),
    };
    let y = TrustVcExpr::Var {
        name: "y".to_string(),
        ty: datatype_x(),
    };
    let ctx = ctx_with_obligation(bit_vector_assert("datatype_eq", eq(x, y)));
    let err = validate_prepared_context(&ctx)
        .expect_err("a by(bit_vector) proof over datatype operands of `==` must fail closed");
    match err {
        ValidationError::BitVectorParity { message, .. } => {
            assert_eq!(message, "error: bit_vector prover cannot handle type `X`");
            assert!(message.contains("bit_vector prover cannot handle type `X`"));
        }
        other => panic!("expected BitVectorParity, got: {other:?}"),
    }
}

#[test]
fn test_bit_vector_datatype_from_fncall_operand_rejected() {
    // Reusability: the struct-typed operand is NOT a bare `Var` but the result
    // of a spec-function call (`assert(x == make_x()) by(bit_vector)`). Routing
    // through the inferred operand type still surfaces the byte-exact
    // `bit_vector prover cannot handle type` message from the real operand,
    // rather than the encoder's sort-metadata surrogate.
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: datatype_x(),
    };
    let make_x = TrustVcExpr::FnCall {
        name: "make_x".to_string(),
        args: vec![],
        return_ty: datatype_x(),
    };
    let ctx = ctx_with_obligation(bit_vector_assert("datatype_fncall", eq(x, make_x)));
    let err = validate_prepared_context(&ctx).expect_err(
        "a by(bit_vector) proof over a datatype-returning call operand must fail closed",
    );
    match err {
        ValidationError::BitVectorParity { message, .. } => {
            assert_eq!(message, "error: bit_vector prover cannot handle type `X`");
            assert!(message.contains("bit_vector prover cannot handle type `X`"));
        }
        other => panic!("expected BitVectorParity, got: {other:?}"),
    }
}

#[test]
fn test_bit_vector_widening_int_cast_operand_accepted() {
    // Should-verify guard for the promoted int-widening family (verified
    // upstream cases such as `signed_cast_to_math_int_div_neg_one_i8`:
    // `(x as int) / (-1 as int) == -(x as int)`). A *finite-width* value cast to
    // `int` carries a known source width and is modellable — it must NOT be
    // flagged as `expected finite-width integer`, even though its inferred type
    // is `int`. Only a variable *declared* `int`/`nat` (no source width) is.
    let widened = TrustVcExpr::Cast {
        expr: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 8 },
        }),
        from_ty: TrustVcType::Int { width: 8 },
        to_ty: TrustVcType::MathInt,
    };
    let ctx = ctx_with_obligation(bit_vector_assert(
        "widen_cast",
        eq(widened.clone(), widened),
    ));
    validate_prepared_context(&ctx).expect(
        "an `as int` widening of a finite-width operand must validate under by(bit_vector)",
    );
}

#[test]
fn test_bit_vector_const_int_cast_operand_accepted() {
    // Upstream `const_int_in_by_bit_vector` (`(0 as int) == (0 as int)` is
    // `Ok`): a folded `int` constant carries no symbolic non-finite-width
    // operand and must validate. The detector flags non-finite-width *variables*
    // (and literals are never `Var`), so this is accepted.
    let zero_int = TrustVcExpr::Cast {
        expr: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
        from_ty: TrustVcType::Int { width: 32 },
        to_ty: TrustVcType::MathInt,
    };
    let ctx = ctx_with_obligation(bit_vector_assert(
        "const_int",
        eq(zero_int.clone(), zero_int),
    ));
    validate_prepared_context(&ctx)
        .expect("a folded `int` constant operand must validate under by(bit_vector)");
}
