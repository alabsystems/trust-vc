//! Cross-product scaling tests for ground pool and expression fold.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Coverage gaps addressed
//!
//! `ground_flush_and_rename.rs` tests entry-scaling (fixed A=1, varying E)
//! and axiom-scaling (varying A, fixed E=1 per symbol). This module tests
//! the cross-product case: M axioms sharing one seed symbol with N entries.
//!
//! `pending_instantiations()` inner loop is O(A × S × E_s) where A = axiom
//! count, S = seed symbols per axiom, E_s = entries per symbol. When all
//! axioms share one symbol, this becomes O(A × E). Each pending item clones
//! a `GroundAxiom` (contains `TrustVcExpr`) and a `Vec<Term>`.
//!
//! Also covers `fold_expr_children` scaling with wide trees (many FnCall
//! args), which was not tested by the depth-only chain tests.
//!
//! Re: performance_proofs phase audit, P1-971.

use super::*;

// ============================================================
// Test 1: Ground pool pending_instantiations cross-product (A × E)
// ============================================================

/// When M axioms all share the same seed symbol "f" and there are N ground
/// entries for "f", `pending_instantiations()` produces M × N pending items.
/// Each item clones a GroundAxiom (with a TrustVcExpr) and a Vec<Term>.
///
/// With both M and N scaling by 2x (total work scales 4x), the ratio should
/// be ~4x. Accept up to 8x for clone and allocation overhead. Reject > 20x
/// which would indicate a regression to worse-than-linear per dimension.
#[test]
fn test_ground_pool_cross_product_scaling_bounded() {
    let small_a = 10;
    let small_e = 10;
    let large_a = 20;
    let large_e = 20;
    let iterations = 500;

    let t_small = measure_median(
        || time_pending_instantiations_cross_product(small_a, small_e, iterations),
        3,
    );
    let t_large = measure_median(
        || time_pending_instantiations_cross_product(large_a, large_e, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Both dimensions doubled → expect 4x (2² = 4). Accept up to 20x for
    // clone overhead (GroundAxiom contains TrustVcExpr which is heap-allocated).
    // >20x indicates a regression beyond O(A × E).
    assert!(
        ratio < 20.0,
        "Ground pool cross-product scaling worse than expected: \
         T(A={},E={})={}μs, T(A={},E={})={}μs, ratio={:.1}x. \
         Expected ~4x for 2x-per-dimension scaling. \
         pending_instantiations() clone overhead may have regressed.",
        small_a,
        small_e,
        t_small,
        large_a,
        large_e,
        t_large,
        ratio,
    );
}

fn time_pending_instantiations_cross_product(
    n_axioms: usize,
    n_entries: usize,
    iterations: usize,
) -> u128 {
    use crate::encoder::ground_pool::{GroundAxiom, GroundTermPool};
    use ay_dpll::api::{Logic, Solver};

    let mut solver = Solver::try_new(Logic::All).expect("solver");

    // Pre-create ground terms
    let terms: Vec<_> = (0..n_entries)
        .map(|i| solver.try_bv_const(i as i64, 32).expect("bv const"))
        .collect();

    let mut total_elapsed = 0u128;

    for _ in 0..iterations {
        let mut pool = GroundTermPool::new();

        // Register M axioms, ALL sharing seed symbol "f"
        for i in 0..n_axioms {
            pool.register_axiom(GroundAxiom {
                name: format!("axiom_{i}"),
                seed_symbols: vec!["f".to_string()],
                seed_triggers: Vec::new(),
                bound_vars: vec!["x".to_string()],
                expr: crate::ir::TrustVcExpr::BoolLit(true),
            });
        }

        // Register N entries for "f"
        for term in &terms {
            pool.register("f", vec![*term]);
        }

        let start = std::time::Instant::now();
        let count = pool.pending_instantiation_count_for_tests();
        total_elapsed += start.elapsed().as_micros();

        assert_eq!(
            count,
            n_axioms * n_entries,
            "cross-product should produce A×E pending items"
        );
    }

    total_elapsed
}

// ============================================================
// Test 2: fold_expr_children scaling with wide FnCall args
// ============================================================

/// `fold_expr_children` for `FnCall` collects folded args via
/// `fold_expr_vec` which does `into_iter().map().collect()`. With W args,
/// cost should be O(W) per fold — linear in width. This test verifies
/// no quadratic regression from e.g., Vec reallocation in the collect.
///
/// The existing depth-chain test (`test_trust_vc_expr_tree_walk_linear`)
/// tests depth scaling. This tests width scaling.
#[test]
fn test_fold_expr_wide_fncall_linear_in_args() {
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::ir_expr_traversal::{fold_expr_children, TrustVcExprFolder};

    struct IdentityFolder;
    impl TrustVcExprFolder for IdentityFolder {}

    let small_w = 100;
    let large_w = 400;

    let build_wide = |width: usize| -> TrustVcExpr {
        let ty = TrustVcType::Int { width: 32 };
        let args: Vec<TrustVcExpr> = (0..width)
            .map(|i| TrustVcExpr::Var {
                name: format!("a{i}"),
                ty: ty.clone(),
            })
            .collect();
        TrustVcExpr::FnCall {
            name: "wide_fn".to_string(),
            args,
            return_ty: ty,
        }
    };

    let small_expr = build_wide(small_w);
    let large_expr = build_wide(large_w);

    let t_small = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..5_000 {
                let _ = fold_expr_children(&mut IdentityFolder, small_expr.clone());
            }
            start.elapsed().as_micros()
        },
        3,
    );

    let t_large = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..5_000 {
                let _ = fold_expr_children(&mut IdentityFolder, large_expr.clone());
            }
            start.elapsed().as_micros()
        },
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_w as f64 / small_w as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "fold_expr_children wide FnCall scaling appears quadratic: \
         T(W={})={}μs, T(W={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         fold_expr_vec collect() may have regressed.",
        small_w,
        t_small,
        large_w,
        t_large,
        ratio,
        normalized,
    );
}

// ============================================================
// Test 3: walk_expr scaling with wide Match arms
// ============================================================

/// `walk_expr` for `Match` visits each arm's body. With A arms,
/// cost should be O(A). This ensures no accidental quadratic pattern
/// from e.g., scanning arms for each arm.
#[test]
fn test_walk_expr_wide_match_linear_in_arms() {
    use crate::ir::{MatchArm, MatchPattern, TrustVcExpr, TrustVcType};
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

    struct CountVisitor(usize);
    impl TrustVcExprVisitor for CountVisitor {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            self.0 += 1;
            walk_expr(self, expr);
        }
    }

    let small_a = 100;
    let large_a = 400;

    let build_match = |n_arms: usize| -> TrustVcExpr {
        let ty = TrustVcType::Int { width: 32 };
        let scrutinee = Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: ty.clone(),
        });
        let arms: Vec<MatchArm> = (0..n_arms)
            .map(|i| MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: i as i128,
                    ty: ty.clone(),
                }),
                body: TrustVcExpr::IntLit {
                    value: i as i128,
                    ty: ty.clone(),
                },
                guard: None,
            })
            .collect();
        TrustVcExpr::Match {
            scrutinee,
            arms,
            ty,
        }
    };

    let small_expr = build_match(small_a);
    let large_expr = build_match(large_a);

    let t_small = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..5_000 {
                let mut visitor = CountVisitor(0);
                visitor.visit_expr(&small_expr);
            }
            start.elapsed().as_micros()
        },
        3,
    );

    let t_large = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..5_000 {
                let mut visitor = CountVisitor(0);
                visitor.visit_expr(&large_expr);
            }
            start.elapsed().as_micros()
        },
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_a as f64 / small_a as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "walk_expr wide Match scaling appears quadratic: \
         T(A={})={}μs, T(A={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         Match arm visitor loop may have regressed.",
        small_a,
        t_small,
        large_a,
        t_large,
        ratio,
        normalized,
    );
}
