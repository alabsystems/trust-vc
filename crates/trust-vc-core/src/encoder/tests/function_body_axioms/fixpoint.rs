//! Fixpoint regressions for chained body axioms (#2277).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::tests::i32_ty;
use crate::ir::{ArithOp, CompareOp, TrustVcExpr};
use crate::prepared_context::PreparedObligation;
use crate::vc::{FunctionContext, ObligationKind, VariableDecl};

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

fn build_chained_body_axiom_encoder(include_g_axiom: bool) -> AYEncoder {
    fn spec_fn(name: &str) -> FunctionContext {
        FunctionContext {
            name: name.to_string(),
            params: vec![("x".to_string(), i32_ty())],
            return_type: i32_ty(),
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        }
    }

    fn fn_call(name: &str, arg: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::FnCall {
            name: name.to_string(),
            args: vec![arg],
            return_ty: i32_ty(),
        }
    }

    fn body_axiom(name: &str, expr: TrustVcExpr, trigger: &str) -> PreparedObligation {
        PreparedObligation {
            name: format!("__body_axiom_{name}"),
            kind: ObligationKind::BroadcastAssume,
            location: None,
            condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
            bound_vars: Some(vec!["x".to_string()]),
            trigger_patterns: Some(vec![vec![trigger.to_string()]]),
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
            condition: trigger.to_string(),
            expr,
        }
    }

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: i32_ty(),
        })
        .expect("bound variable declaration should succeed");
    for name in ["f", "g"] {
        encoder
            .register_function_context(&spec_fn(name))
            .expect("function declaration should succeed");
    }

    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: i32_ty(),
    };
    let all_var_terms: Vec<_> = encoder.variables.values().copied().collect();
    encoder
        .add_typed_broadcast(
            &body_axiom(
                "f",
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left: Box::new(fn_call("f", x.clone())),
                    right: Box::new(TrustVcExpr::Arith {
                        op: ArithOp::Add,
                        left: Box::new(fn_call("g", x.clone())),
                        right: Box::new(TrustVcExpr::IntLit {
                            value: 1,
                            ty: i32_ty(),
                        }),
                        ty: i32_ty(),
                    }),
                },
                "f(x)",
            ),
            &all_var_terms,
        )
        .expect("f body axiom should encode");
    if include_g_axiom {
        encoder
            .add_typed_broadcast(
                &body_axiom(
                    "g",
                    TrustVcExpr::Compare {
                        op: CompareOp::Eq,
                        left: Box::new(fn_call("g", x.clone())),
                        right: Box::new(TrustVcExpr::Arith {
                            op: ArithOp::Add,
                            left: Box::new(x.clone()),
                            right: Box::new(x),
                            ty: i32_ty(),
                        }),
                    },
                    "g(x)",
                ),
                &all_var_terms,
            )
            .expect("g body axiom should encode");
    }
    encoder
}

fn chained_assertion() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::FnCall {
            name: "f".to_string(),
            args: vec![TrustVcExpr::IntLit {
                value: 3,
                ty: i32_ty(),
            }],
            return_ty: i32_ty(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 7,
            ty: i32_ty(),
        }),
    }
}

#[test]
fn test_chained_body_axioms_seed_round_plus_ay_ematching() {
    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        let mut encoder = build_chained_body_axiom_encoder(true);
        let condition = encoder
            .resolve_condition_typed(&chained_assertion())
            .expect("assertion should encode");
        encoder.solver.try_push().expect("push should succeed");
        let negated = encoder
            .solver
            .try_not(condition)
            .expect("negation should encode");
        encoder
            .solver
            .try_assert_term(negated)
            .expect("negated assertion should assert");
        let first_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("first flush should succeed");
        let result = encoder.solver.check_sat_with_details();
        encoder.solver.try_pop().expect("pop should succeed");

        assert!(
            first_flush > 0,
            "seed round should instantiate at least one ground axiom"
        );
        // With GROUND_FIXPOINT_ROUNDS=1, the pool seeds f(3) in round 1 but
        // does not chain to g(3). ay's 8-round E-matching handles the remaining
        // chain at check_sat time.
        assert!(
            result.result.result().is_unsat(),
            "ay multi-round E-matching should complete the chain and prove f(3) == 7, got: {:?}",
            result.result.result()
        );
    });
}

#[test]
fn test_chained_body_axioms_without_second_axiom_remain_unproved() {
    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        let mut encoder = build_chained_body_axiom_encoder(false);
        let condition = encoder
            .resolve_condition_typed(&chained_assertion())
            .expect("assertion should encode");
        encoder.solver.try_push().expect("push should succeed");
        let negated = encoder
            .solver
            .try_not(condition)
            .expect("negation should encode");
        encoder
            .solver
            .try_assert_term(negated)
            .expect("negated assertion should assert");
        encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("flush should succeed");
        let result = encoder.solver.check_sat_with_details();
        encoder.solver.try_pop().expect("pop should succeed");

        assert!(
            !result.result.result().is_unsat(),
            "without g(x) == x + x, f(3) == 7 should remain unproved, got: {:?}",
            result.result.result()
        );
    });
}

#[test]
fn test_ground_axiom_incremental_flush_processes_only_new_entry() {
    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        let existing_entries = 4;
        let mut encoder = build_incremental_reflush_encoder(existing_entries);

        let first_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("initial flush should succeed");
        assert_eq!(
            first_flush, existing_entries,
            "initial flush should instantiate each pre-registered ground term exactly once"
        );

        register_new_ground_term(&mut encoder, 10_000);
        let incremental_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("incremental flush should succeed");
        let converged_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("converged flush should succeed");

        assert_eq!(
            incremental_flush, 1,
            "incremental flush should instantiate only the newly added ground term"
        );
        assert_eq!(
            converged_flush, 0,
            "pool should reconverge after the delta flush"
        );
    });
}

/// `flush_ground_axioms_to_fixpoint()` re-encodes each matched body axiom via
/// `resolve_condition_typed_with_bindings()`, which seeds `local_vars` and
/// `local_var_types` from the binding slice before encoding the body. With a
/// fixed body and N bindings, that setup should stay O(N), not regress to
/// O(N^2).
#[test]
fn test_ground_axiom_binding_reencode_scaling_linear() {
    let small = 25;
    let large = 100;
    let iterations = 400;

    let t_small = measure_median(
        || time_resolve_condition_with_bindings(small, iterations),
        3,
    );
    let t_large = measure_median(
        || time_resolve_condition_with_bindings(large, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "ground-axiom binding re-encode appears quadratic: \
         T(B={})={}μs, T(B={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         resolve_condition_typed_with_bindings() should stay O(B) in bound vars.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// After a pool has converged once, adding one fresh ground term should force
/// only a linear re-scan over the already-instantiated entries for that
/// symbol. The incremental flush must not regress to O(E^2) in the historical
/// pool size.
#[test]
fn test_ground_axiom_incremental_reflush_scaling_linear() {
    let small = 50;
    let large = 200;
    let iterations = 200;

    let t_small = measure_median(|| time_incremental_ground_axiom_flush(small, iterations), 3);
    let t_large = measure_median(|| time_incremental_ground_axiom_flush(large, iterations), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "incremental ground-axiom re-flush appears quadratic: \
         T(E={})={}μs, T(E={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         after one new ground term, the follow-up flush should stay O(E) in \
         prior instantiated entries.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_resolve_condition_with_bindings(n_bindings: usize, iterations: usize) -> u128 {
    let (mut encoder, expr, binding_names, binding_terms) = build_binding_reencode_case(n_bindings);
    let bindings: Vec<(&str, ay_dpll::api::Term)> = binding_names
        .iter()
        .zip(binding_terms.iter().copied())
        .map(|(name, term)| (name.as_str(), term))
        .collect();

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let term = encoder
            .resolve_condition_typed_with_bindings(&expr, &bindings)
            .expect("bound-variable re-encode should succeed");
        std::hint::black_box(term);
    }
    start.elapsed().as_micros()
}

fn time_incremental_ground_axiom_flush(existing_entries: usize, iterations: usize) -> u128 {
    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut encoder = build_incremental_reflush_encoder(existing_entries);
        let first_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("initial flush should succeed");
        assert_eq!(
            first_flush, existing_entries,
            "initial flush should instantiate each historical entry before convergence"
        );

        register_new_ground_term(&mut encoder, 10_000);
        let start = std::time::Instant::now();
        let incremental_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("incremental flush should succeed");
        total_elapsed += start.elapsed().as_micros();

        assert_eq!(
            incremental_flush, 1,
            "incremental flush should instantiate only the new entry"
        );
        let converged_flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("converged flush should succeed");
        assert_eq!(
            converged_flush, 0,
            "pool should reconverge after the delta flush"
        );
    }

    total_elapsed
}

fn build_binding_reencode_case(
    n_bindings: usize,
) -> (AYEncoder, TrustVcExpr, Vec<String>, Vec<ay_dpll::api::Term>) {
    let mut encoder = AYEncoder::new();
    let binding_names: Vec<String> = (0..n_bindings).map(|i| format!("x{i}")).collect();

    for name in &binding_names {
        encoder
            .declare_variable(&VariableDecl {
                bounded_len: false,
                name: name.clone(),
                ty: i32_ty(),
            })
            .expect("bound variable declaration should succeed");
    }

    let binding_terms: Vec<_> = (0..n_bindings)
        .map(|i| {
            encoder
                .solver
                .try_bv_const(i as i64, 32)
                .expect("ground binding term should encode")
        })
        .collect();

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(TrustVcExpr::Var {
            name: binding_names[0].clone(),
            ty: i32_ty(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: i32_ty(),
        }),
    };

    (encoder, expr, binding_names, binding_terms)
}

fn build_incremental_reflush_encoder(existing_entries: usize) -> AYEncoder {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: i32_ty(),
        })
        .expect("bound variable declaration should succeed");
    encoder
        .state
        .ground_pool
        .register_axiom(crate::encoder::ground_pool::GroundAxiom {
            name: "axiom_f".to_string(),
            seed_symbols: vec!["f".to_string()],
            seed_triggers: Vec::new(),
            bound_vars: vec!["x".to_string()],
            expr: TrustVcExpr::Compare {
                op: CompareOp::Ge,
                left: Box::new(TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: i32_ty(),
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 0,
                    ty: i32_ty(),
                }),
            },
        });

    for i in 0..existing_entries {
        register_new_ground_term(&mut encoder, i as i64);
    }

    encoder
}

fn register_new_ground_term(encoder: &mut AYEncoder, value: i64) {
    let term = encoder
        .solver
        .try_bv_const(value, 32)
        .expect("ground term should encode");
    assert!(
        encoder.state.ground_pool.register("f", vec![term]),
        "new ground term should bump the pool revision"
    );
}
