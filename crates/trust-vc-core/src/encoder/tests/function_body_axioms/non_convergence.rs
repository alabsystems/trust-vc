//! Tests for ground pool fixpoint non-convergence diagnostic (#2324 Slice 1).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::tests::i32_ty;
use crate::ir::{ArithOp, CompareOp, TrustVcExpr};
use crate::prepared_context::PreparedObligation;
use crate::vc::{FunctionContext, ObligationKind, VariableDecl};

fn x_var() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "x".to_string(),
        ty: i32_ty(),
    }
}

fn fn_call(name: &str) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args: vec![x_var()],
        return_ty: i32_ty(),
    }
}

/// Body axiom: `name(x) == next(x) + 1` with trigger `name(x)`.
fn chain_axiom(name: &str, next: &str) -> PreparedObligation {
    PreparedObligation {
        name: format!("__body_axiom_{name}"),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: Some(vec!["x".to_string()]),
        trigger_patterns: Some(vec![vec![format!("{name}(x)")]]),
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
        condition: format!("{name}(x)"),
        expr: TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(fn_call(name)),
            right: Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(fn_call(next)),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: i32_ty(),
                }),
                ty: i32_ty(),
            }),
        },
    }
}

/// Terminal axiom: `name(x) == x`.
fn terminal_axiom(name: &str) -> PreparedObligation {
    PreparedObligation {
        name: format!("__body_axiom_{name}"),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: Some(vec!["x".to_string()]),
        trigger_patterns: Some(vec![vec![format!("{name}(x)")]]),
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
        condition: format!("{name}(x)"),
        expr: TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(fn_call(name)),
            right: Box::new(x_var()),
        },
    }
}

/// Build a chain of `n` functions where each calls the next.
/// Exceeds `GROUND_FIXPOINT_ROUNDS` (1) when n > 1.
fn build_chain_encoder(n: usize) -> AYEncoder {
    assert!(n >= 2);
    let names: Vec<String> = (0..n).map(|i| format!("fn{i}")).collect();
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: i32_ty(),
        })
        .expect("variable declaration should succeed");
    for name in &names {
        encoder
            .register_function_context(&FunctionContext {
                name: name.clone(),
                params: vec![("x".to_string(), i32_ty())],
                return_type: i32_ty(),
                is_recursive: false,
                mode: crate::mode::FunctionMode::Spec,
                trait_bounds: vec![],
            })
            .expect("function declaration should succeed");
    }
    let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();
    for pair in names.windows(2) {
        encoder
            .add_typed_broadcast(&chain_axiom(&pair[0], &pair[1]), &all_var_terms)
            .expect("body axiom should encode");
    }
    encoder
        .add_typed_broadcast(&terminal_axiom(names.last().unwrap()), &all_var_terms)
        .expect("terminal body axiom should encode");
    encoder
}

/// A 6-deep chain exceeds the 1-round fixpoint limit. The loop should not
/// converge, and `needs_flush()` should remain true.
#[test]
fn test_deep_chain_non_convergence() {
    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        let mut encoder = build_chain_encoder(6);
        let ground_term = encoder
            .solver
            .try_bv_const(3, 32)
            .expect("ground constant should encode");
        encoder.state.ground_pool.register("fn0", vec![ground_term]);

        let total = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("flush should not error");
        assert!(total > 0, "some axioms should have been instantiated");
        assert!(
            encoder.state.ground_pool.needs_flush(),
            "6-deep chain should NOT converge in 1 round"
        );
    });
}

/// A 3-deep chain does NOT converge in 1 round (requires 3 rounds).
/// ay's 8-round E-matching handles the remaining chain at check_sat time.
#[test]
fn test_shallow_chain_does_not_converge_in_single_round() {
    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        let mut encoder = build_chain_encoder(3);
        let ground_term = encoder
            .solver
            .try_bv_const(3, 32)
            .expect("ground constant should encode");
        encoder.state.ground_pool.register("fn0", vec![ground_term]);

        let total = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("flush should not error");
        assert!(
            total > 0,
            "seed round should instantiate at least one axiom"
        );
        assert!(
            encoder.state.ground_pool.needs_flush(),
            "3-deep chain should NOT converge in 1 round"
        );
    });
}
