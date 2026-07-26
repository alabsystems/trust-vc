//! Performance scaling tests for arithmetic normalization and equality
//! back-propagation paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Coverage gaps addressed
//!
//! `performance_proof_audit.rs` covers expression depth, ground pool, and
//! encoder multiplier. This module covers normalization and equality paths:
//!
//! 1. `normalize_int_expr` recursive flatten — O(N²) for right-leaning trees
//!    of depth N (each level re-flattens the normalized subtree). KNOWN
//!    quadratic, acceptable: real inputs are left-associative with ≤20 operands.
//!
//! 2. Distribution sort via `expr_sort_key` Compound variant — `format!("{:?}")`
//!    allocation for non-leaf operands. O(n × S) for n operands of subtree size S.
//!
//! 3. `try_cancel_common_addends` — Vec::remove in a while loop. O(n²) in
//!    addend count, but n is bounded by expression structure (~5 in practice).
//!
//! 4. Equality back-propagation in `add_typed_assumption` — each new binding
//!    substitutes into all existing bindings. O(m²) in equality count, but m
//!    is bounded by assumption count per verification context (~10 in practice).
//!
//! Re: performance_proofs phase audit, P1-578.

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

// ============================================================
// Test 1: Normalization scaling with many flat operands
// ============================================================

/// `normalize_int_expr` recurses into children, normalizes them, then
/// re-flattens the already-normalized result. For right-leaning trees of
/// depth N, this causes O(N²) total work: each level re-flattens the
/// entire normalized subtree below it (sum(1..N) = O(N²)).
///
/// This is a KNOWN quadratic pattern, acceptable because:
///   1. Rust source parsers produce left-associative trees (not right-leaning)
///   2. Real expressions have ≤20 operands per associative group
///   3. At N=20, wall time is <1ms per normalization call
///
/// This test guards that scaling stays within bounded quadratic (not worse —
/// e.g., exponential from recursive re-distribution).
/// Threshold: (4x input)² = 16x, allow up to 24x for overhead.
#[test]
fn test_normalize_flat_operand_scaling_bounded_quadratic() {
    let small_n = 20;
    let large_n = 80;

    let t_small = measure_median(|| time_normalize_flat(small_n), 3);
    let t_large = measure_median(|| time_normalize_flat(large_n), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Known quadratic: expect ~16x for 4x input. Allow 24x for overhead.
    assert!(
        ratio < 24.0,
        "Normalization flat operand scaling worse than bounded quadratic: \
         T(N={})={}μs, T(N={})={}μs, ratio={:.1}x. \
         Expected ≤24x (known O(N²) from recursive flatten). \
         Possible regression to worse-than-quadratic.",
        small_n,
        t_small,
        large_n,
        t_large,
        ratio,
    );
}

fn time_normalize_flat(n_operands: usize) -> u128 {
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::ir_expr::ArithOp;

    let ty = TrustVcType::MathInt;

    // Build a right-leaning chain: v0 + (v1 + (v2 + ... (v_{n-2} + v_{n-1})))
    // with distinct variable names so sorting must compare all keys.
    let vars: Vec<TrustVcExpr> = (0..n_operands)
        .map(|i| TrustVcExpr::Var {
            name: format!("v{}", i),
            ty: ty.clone(),
        })
        .collect();

    let mut expr = vars[n_operands - 1].clone();
    for i in (0..n_operands - 1).rev() {
        expr = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(vars[i].clone()),
            right: Box::new(expr),
            ty: ty.clone(),
        };
    }

    let start = std::time::Instant::now();
    for _ in 0..100 {
        let _ = crate::encoder::ir_encoder::normalize::normalize_int_expr(&expr);
    }
    start.elapsed().as_micros()
}

// ============================================================
// Test 2: Additive cancellation scaling
// ============================================================

/// `try_cancel_common_addends` uses Vec::remove() in a while loop to cancel
/// common terms between LHS and RHS of an equality. Each `remove()` is O(n)
/// and `position()` is O(n), called up to n times → O(n²).
///
/// This is acceptable because n (number of addends per side) is bounded by
/// expression structure — typically 2-5 in practice. This test verifies the
/// pattern doesn't regress at larger scales that could emerge from deeply
/// distributed expressions.
#[test]
fn test_additive_cancellation_scaling_bounded() {
    let small_n = 20;
    let large_n = 80;

    let t_small = measure_median(|| time_additive_cancellation(small_n), 3);
    let t_large = measure_median(|| time_additive_cancellation(large_n), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Expected: O(n²) → ratio ≈ 16x for 4x input increase.
    // We accept up to 20x (quadratic with overhead). If it exceeds 20x,
    // Vec::remove has regressed to worse than quadratic.
    assert!(
        ratio < 20.0,
        "Additive cancellation scaling worse than expected quadratic: \
         T(N={})={}μs, T(N={})={}μs, ratio={:.1}x. \
         Vec::remove pattern may have regressed beyond O(n²).",
        small_n,
        t_small,
        large_n,
        t_large,
        ratio,
    );
}

fn time_additive_cancellation(n_common: usize) -> u128 {
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::ir_expr::{ArithOp, CompareOp};

    let ty = TrustVcType::MathInt;

    // Build LHS: common_0 + common_1 + ... + common_{n-1} + unique_lhs
    // Build RHS: common_0 + common_1 + ... + common_{n-1} + unique_rhs
    // Cancellation should remove all n common terms.
    let common: Vec<TrustVcExpr> = (0..n_common)
        .map(|i| TrustVcExpr::Var {
            name: format!("c{}", i),
            ty: ty.clone(),
        })
        .collect();

    let unique_lhs = TrustVcExpr::Var {
        name: "lhs_unique".to_string(),
        ty: ty.clone(),
    };
    let unique_rhs = TrustVcExpr::Var {
        name: "rhs_unique".to_string(),
        ty: ty.clone(),
    };

    fn build_sum(terms: &[TrustVcExpr], ty: &TrustVcType) -> TrustVcExpr {
        let mut acc = terms[0].clone();
        for t in &terms[1..] {
            acc = TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(acc),
                right: Box::new(t.clone()),
                ty: ty.clone(),
            };
        }
        acc
    }

    let mut lhs_terms = common.clone();
    lhs_terms.push(unique_lhs);
    let mut rhs_terms = common;
    rhs_terms.push(unique_rhs);

    let lhs = build_sum(&lhs_terms, &ty);
    let rhs = build_sum(&rhs_terms, &ty);

    // Wrap in Compare::Eq for normalization to trigger cancellation
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(lhs),
        right: Box::new(rhs),
    };

    let start = std::time::Instant::now();
    for _ in 0..100 {
        let _ = crate::encoder::ir_encoder::normalize::normalize_int_expr(&expr);
    }
    start.elapsed().as_micros()
}

// ============================================================
// Test 3: Equality back-propagation scaling
// ============================================================

/// `add_typed_assumption` back-propagates each new equality binding into
/// all existing bindings: O(m²) total for m equality assumptions.
///
/// Scaling: m equality assumptions → sum(i=1..m, i) = O(m²) substitutions,
/// each O(tree_size). This test verifies the pattern at realistic scale
/// (10 vs 40 equalities) and accepts quadratic behavior as bounded.
///
/// A regression beyond quadratic (e.g., exponential from recursive
/// substitution loops) would show as T(40)/T(10) >> 16x.
#[test]
fn test_equality_backpropagation_scaling_bounded() {
    let small_m = 10;
    let large_m = 40;

    let t_small = measure_median(|| time_equality_backpropagation(small_m), 3);
    let t_large = measure_median(|| time_equality_backpropagation(large_m), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Expected quadratic: (40/10)² = 16x. Allow up to 24x for overhead.
    assert!(
        ratio < 24.0,
        "Equality back-propagation scaling worse than quadratic: \
         T(M={})={}μs, T(M={})={}μs, ratio={:.1}x. \
         Back-propagation loop may have regressed beyond O(m²).",
        small_m,
        t_small,
        large_m,
        t_large,
        ratio,
    );
}

fn time_equality_backpropagation(n_equalities: usize) -> u128 {
    use crate::encoder::verification::test_gate::with_verify_test_gate;

    with_verify_test_gate(|| {
        let mut ctx = VerificationContext::new();

        // Declare variables v0..v_{n-1} and a target
        for i in 0..n_equalities {
            ctx.declare_var_typed(
                &format!("v{}", i),
                crate::ir::TrustVcType::parse_or_opaque("i32"),
            );
        }
        ctx.declare_var_typed("target", crate::ir::TrustVcType::parse_or_opaque("i32"));

        // Add n equality assumptions: v0 == 1, v1 == v0 + 1, v2 == v1 + 1, ...
        // Each triggers back-propagation into all prior bindings.
        ctx.push_obligation(crate::vc::ProofObligation::assume("eq_0", "v0 == 1"));
        for i in 1..n_equalities {
            ctx.push_obligation(crate::vc::ProofObligation::assume(
                format!("eq_{}", i),
                format!("v{} == v{} + 1", i, i - 1),
            ));
        }

        // Simple assertion that exercises the binding map
        ctx.push_obligation(crate::vc::ProofObligation::assert(
            "check",
            format!("v{} >= 0", n_equalities - 1),
        ));

        let start = std::time::Instant::now();
        let result = AYEncoder::verify(&ctx);
        let elapsed = start.elapsed().as_micros();

        expect_verified(&result, "Back-propagation scaling test failed at M={}");

        elapsed
    })
}

// ============================================================
// Test 4: Normalization with compound sort keys (distribution path)
// ============================================================

/// After distribution, `d * (a + b + c + ...)` produces compound product
/// terms that sort via `format!("{:?}", expr)` in the Compound variant of
/// `expr_sort_key`. This test verifies that sorting distributed terms
/// scales acceptably with the number of sum terms.
#[test]
fn test_distribution_sort_scaling_linear() {
    let small_n = 20;
    let large_n = 80;

    let t_small = measure_median(|| time_distribution_sort(small_n), 3);
    let t_large = measure_median(|| time_distribution_sort(large_n), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_n as f64 / small_n as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Distribution sort scaling appears quadratic: \
         T(N={})={}μs, T(N={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         Compound sort key allocation may have regressed.",
        small_n,
        t_small,
        large_n,
        t_large,
        ratio,
        normalized,
    );
}

fn time_distribution_sort(n_sum_terms: usize) -> u128 {
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::ir_expr::ArithOp;

    let ty = TrustVcType::MathInt;

    // Build: d * (a0 + a1 + a2 + ... + a_{n-1})
    // Distribution produces n products: d*a0, d*a1, ..., d*a_{n-1}
    // Each product is a Compound sort key → triggers format!("{:?}")
    let d = TrustVcExpr::Var {
        name: "d".to_string(),
        ty: ty.clone(),
    };

    let mut sum = TrustVcExpr::Var {
        name: "a0".to_string(),
        ty: ty.clone(),
    };
    for i in 1..n_sum_terms {
        sum = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(sum),
            right: Box::new(TrustVcExpr::Var {
                name: format!("a{}", i),
                ty: ty.clone(),
            }),
            ty: ty.clone(),
        };
    }

    let expr = TrustVcExpr::Arith {
        op: ArithOp::Mul,
        left: Box::new(d),
        right: Box::new(sum),
        ty: ty.clone(),
    };

    let start = std::time::Instant::now();
    for _ in 0..100 {
        let _ = crate::encoder::ir_encoder::normalize::normalize_int_expr(&expr);
    }
    start.elapsed().as_micros()
}
