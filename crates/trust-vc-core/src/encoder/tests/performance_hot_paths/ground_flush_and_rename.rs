//! Ground axiom flush scaling, convergence, and rename_vars deep Let chain tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from performance_hot_paths/mod.rs (#2145).

use super::*;

/// A one-axiom ground-pool flush should only instantiate matching symbol+arity
/// pairs, and `mark_flushed()` plus `instantiated_pairs` should make the second
/// flush a no-op.
#[test]
fn test_ground_axiom_flush_filters_irrelevant_pairs_and_then_converges() {
    let mut encoder = build_pending_scan_encoder(2, true);

    let first = encoder
        .flush_ground_axioms_to_fixpoint()
        .expect("first flush should succeed");
    let second = encoder
        .flush_ground_axioms_to_fixpoint()
        .expect("second flush should succeed");

    assert_eq!(
        first, 2,
        "flush should instantiate only matching one-argument entries for the registered axiom"
    );
    assert_eq!(second, 0, "converged flush should be a no-op");
}

/// `flush_ground_axioms_to_fixpoint()` starts by scanning pending
/// instantiations for each registered axiom. With one trivial axiom and N
/// matching ground entries, that pre-solver pass should stay O(N), not
/// regress to O(N²).
#[test]
fn test_ground_axiom_pending_scan_scaling_linear() {
    let small = 50;
    let large = 200;
    let iterations = 200;

    let t_small = measure_median(|| time_ground_axiom_flush(small, iterations), 3);
    let t_large = measure_median(|| time_ground_axiom_flush(large, iterations), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "ground-pool pending scan appears quadratic: \
         T(E={})={}μs, T(E={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         one-axiom fixpoint setup should stay O(E) in matching ground entries.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// The same pending-instantiation helper also walks the registered axiom list.
/// With one matching ground entry per axiom, flush setup should stay O(A), not
/// regress to O(A²) as the number of trivial body axioms grows.
#[test]
fn test_ground_axiom_pending_scan_axiom_scaling_linear() {
    let small = 25;
    let large = 100;
    let iterations = 200;

    let t_small = measure_median(|| time_ground_axiom_flush_by_axioms(small, iterations), 3);
    let t_large = measure_median(|| time_ground_axiom_flush_by_axioms(large, iterations), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "ground-pool axiom scan appears quadratic: \
         T(A={})={}μs, T(A={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         pending_instantiations() should stay O(A) in registered axioms \
         when per-axiom matches stay constant.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

/// Once the first flush converges, `mark_flushed()` should let
/// `needs_flush()` reject later calls before rescanning any entries. With one
/// registered axiom and a converged pool, repeated no-op flushes should stay
/// O(1) in ground-entry count, not fall back to another O(E) pending scan.
#[test]
fn test_ground_axiom_converged_flush_short_circuits() {
    let small = 50;
    let large = 200;
    let iterations = 10_000;

    let t_small = measure_median(|| time_converged_ground_axiom_flush(small, iterations), 3);
    let t_large = measure_median(|| time_converged_ground_axiom_flush(large, iterations), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;

    assert!(
        ratio < 3.0,
        "converged ground-pool flush still scales with entry count: \
         T(E={})={}μs, T(E={})={}μs, ratio={:.1}x. \
         needs_flush()/mark_flushed() should short-circuit no-op flushes \
         instead of rescanning the full pool.",
        small,
        t_small,
        large,
        t_large,
        ratio,
    );
}

fn build_pending_scan_encoder(n_entries: usize, include_irrelevant_entries: bool) -> AYEncoder {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&crate::vc::VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: crate::ir::TrustVcType::Int { width: 32 },
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
            expr: crate::ir::TrustVcExpr::BoolLit(true),
        });

    for i in 0..n_entries {
        let term = encoder
            .solver
            .try_bv_const(i as i64, 32)
            .expect("ground term should encode");
        assert!(encoder.state.ground_pool.register("f", vec![term]));
    }

    if include_irrelevant_entries {
        let x = encoder
            .solver
            .try_bv_const(10_000, 32)
            .expect("noise term x should encode");
        let y = encoder
            .solver
            .try_bv_const(10_001, 32)
            .expect("noise term y should encode");
        assert!(encoder.state.ground_pool.register("f", vec![x, y]));
        assert!(encoder.state.ground_pool.register("g", vec![x]));
    }

    encoder
}

fn build_axiom_scan_encoder(n_axioms: usize) -> AYEncoder {
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&crate::vc::VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: crate::ir::TrustVcType::Int { width: 32 },
        })
        .expect("bound variable declaration should succeed");

    for i in 0..n_axioms {
        let symbol = format!("f_{i}");
        encoder
            .state
            .ground_pool
            .register_axiom(crate::encoder::ground_pool::GroundAxiom {
                name: format!("axiom_{i}"),
                seed_symbols: vec![symbol.clone()],
                seed_triggers: Vec::new(),
                bound_vars: vec!["x".to_string()],
                expr: crate::ir::TrustVcExpr::BoolLit(true),
            });
        let term = encoder
            .solver
            .try_bv_const(i as i64, 32)
            .expect("ground term should encode");
        assert!(encoder.state.ground_pool.register(&symbol, vec![term]));
    }

    encoder
}

fn time_ground_axiom_flush(n_entries: usize, iterations: usize) -> u128 {
    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut encoder = build_pending_scan_encoder(n_entries, false);
        let start = std::time::Instant::now();
        let first = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("flush should succeed");
        total_elapsed += start.elapsed().as_micros();
        assert_eq!(
            first, n_entries,
            "all matching entries should instantiate during the first flush"
        );
        let second = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("second flush should succeed");
        assert_eq!(second, 0, "second flush should be a no-op");
    }

    total_elapsed
}

fn time_ground_axiom_flush_by_axioms(n_axioms: usize, iterations: usize) -> u128 {
    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut encoder = build_axiom_scan_encoder(n_axioms);
        let start = std::time::Instant::now();
        let first = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("flush should succeed");
        total_elapsed += start.elapsed().as_micros();
        assert_eq!(
            first, n_axioms,
            "each registered axiom should instantiate exactly one matching entry"
        );
        let second = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("second flush should succeed");
        assert_eq!(second, 0, "second flush should be a no-op");
    }

    total_elapsed
}

fn time_converged_ground_axiom_flush(n_entries: usize, iterations: usize) -> u128 {
    let mut encoder = build_pending_scan_encoder(n_entries, false);
    let first = encoder
        .flush_ground_axioms_to_fixpoint()
        .expect("first flush should succeed");
    assert_eq!(
        first, n_entries,
        "first flush should instantiate all matching entries before convergence"
    );

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let flush = encoder
            .flush_ground_axioms_to_fixpoint()
            .expect("converged flush should succeed");
        assert_eq!(flush, 0, "converged flush should be a no-op");
    }

    start.elapsed().as_micros()
}

/// `rename_vars` clones `shadowed` at each Let scope: O(D²) inherent. Reject cubic.
#[test]
fn test_rename_vars_deep_let_chain_not_cubic() {
    use crate::encoder::verification::rewrite::replace_vars_with_pre_typed;
    use crate::ir::{TrustVcExpr, TrustVcType};
    let ty = TrustVcType::Int { width: 32 };
    let vars = vec![crate::vc::VariableDecl {
        bounded_len: false,
        name: "x".into(),
        ty: ty.clone(),
    }];
    let build = |d: usize| -> TrustVcExpr {
        (0..d).fold(
            TrustVcExpr::Var {
                name: "x".into(),
                ty: ty.clone(),
            },
            |body, i| TrustVcExpr::Let {
                name: format!("t{i}"),
                ty: ty.clone(),
                value: Box::new(TrustVcExpr::IntLit {
                    value: i as i128,
                    ty: ty.clone(),
                }),
                body: Box::new(body),
            },
        )
    };
    // Scope-aware folder (#2641) uses 2 stack frames per recursion level
    // (trait method + fold_expr_scoped_children), halving the safe depth.
    // Use 12/48 (4x ratio) to preserve O(D²)-vs-O(D³) detection.
    let (sm, lg, iters) = (12, 48, 5_000);
    let (se, le) = (build(sm), build(lg));
    let time_it = |expr: &TrustVcExpr| {
        measure_median(
            || {
                let s = std::time::Instant::now();
                for _ in 0..iters {
                    let _ = replace_vars_with_pre_typed(expr, &vars);
                }
                s.elapsed().as_micros()
            },
            3,
        )
    };
    let (ts, tl) = (time_it(&se), time_it(&le));
    if ts < MIN_MEASURABLE_US {
        return;
    }
    let ratio = tl as f64 / ts as f64;
    assert!(
        ratio < 64.0,
        "rename_vars deep Let exceeds cubic: T(D={sm})={ts}μs, T(D={lg})={tl}μs, \
         ratio={ratio:.1}x (expected ≤16x for O(D²))."
    );
}
