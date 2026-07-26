//! Performance proof audit — targeted scaling tests for uncovered encoder paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Coverage gaps addressed
//!
//! `performance_scaling.rs` covers:
//!   - Assertion count (linear)
//!   - Variable count (linear)
//!   - Assumption count (linear)
//!   - replace_vars_with_pre (linear in V for fixed condition length)
//!   - Broadcast cap (bounded)
//!   - Combined A×V (quadratic in cross-product, bounded)
//!   - infer_int_width (linear in type count)
//!   - Invariant cascade (quadratic by design, bounded at cubic)
//!   - Literal count (linear)
//!
//! This module covers paths NOT tested above:
//!
//! 1. Invariant cascade with scaled V at fixed I — catches O(V²) in
//!    `replace_vars_with_pre_typed` HashSet construction.
//!
//! 2. Deep expression encoding — catches O(E²) in `encode_trust_vc_expr`
//!    recursive tree walk.
//!
//! 3. Per-assertion encoder multiplier — verifies the 2x overhead from
//!    overflow+main encoders stays bounded (not 3x or 4x regression).
//!
//! 4. Ground pool registration — catches O(N) regression in HashSet-based
//!    `GroundTermPool::register()`. P1-467.
//!
//! 5. Ground pool convergence — verifies fixpoint flush converges and
//!    produces correct results with body axioms + ground terms. P1-467.
//!
//! Re: performance_proofs phase audit, P1-449.

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

// ============================================================
// Test 1: Invariant cascade variable scaling (fixed I, scaled V)
// ============================================================

/// The invariant cascade calls `replace_vars_with_pre_typed` O(I²) times.
/// Each call constructs a `HashSet<&str>` from `variables` (O(V)). Total
/// HashSet construction cost: O(I² * V). This test holds I=3 fixed and
/// scales V from 10 to 40 to verify V-scaling is linear, not quadratic.
///
/// A regression to O(V²) per HashSet construction (e.g., from scanning
/// variables twice) would show as T(40)/T(10) ≈ 16x instead of ≈ 4x.
#[test]
fn test_invariant_cascade_variable_scaling_linear() {
    let invariant_count = 3; // Fixed I — small enough to keep O(I²) constant
    let small_v = 10;
    let large_v = 40;

    let t_small = measure_median(
        || time_invariant_cascade_with_vars(invariant_count, small_v),
        3,
    );
    let t_large = measure_median(
        || time_invariant_cascade_with_vars(invariant_count, large_v),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_v as f64 / small_v as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Invariant cascade V-scaling appears quadratic (fixed I={}): \
         T(V={})={}μs, T(V={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         replace_vars_with_pre_typed HashSet construction may have \
         regressed from O(V) to O(V²).",
        invariant_count,
        small_v,
        t_small,
        large_v,
        t_large,
        ratio,
        normalized,
    );
}

fn time_invariant_cascade_with_vars(n_invariants: usize, n_vars: usize) -> u128 {
    let mut ctx = VerificationContext::new();

    // Declare V u32 variables (so invariants are tautological: u32 >= 0)
    for i in 0..n_vars {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("u32"),
        );
    }
    ctx.push_obligation(crate::vc::ProofObligation::assume("init", "v0 == 0"));

    // I invariants on the first I variables
    for i in 0..n_invariants {
        let var_idx = i.min(n_vars - 1);
        ctx.obligations
            .push(crate::vc::ProofObligation::loop_invariant(
                format!("inv_{}", i),
                format!("v{} >= 0", var_idx),
            ));
    }

    ctx.push_obligation(crate::vc::ProofObligation::assert("check", "v0 >= 0"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(
        &result,
        &format!("Invariant cascade V-scaling test setup failed at I={n_invariants}, V={n_vars}"),
    );

    elapsed
}

// ============================================================
// Test 2: Deep expression encoding (expression depth scaling)
// ============================================================

/// The typed encoder (`encode_trust_vc_expr`) recurses into child nodes.
/// Tree walk helpers (`references_collection`, `has_non_skolemized_quantifier`)
/// also walk the full AST per assertion. With expression depth D and A=1
/// assertion, encoding cost should be O(D), not O(D²).
///
/// Builds a chain: v0 + v0 + v0 + ... (D additions, flattened left).
/// Total AST nodes: ~2D (D Arith + D Var leaves).
#[test]
fn test_deep_expression_encoding_linear() {
    let small_d = 10;
    let large_d = 40;

    let t_small = measure_median(|| time_deep_expression(small_d), 3);
    let t_large = measure_median(|| time_deep_expression(large_d), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_d as f64 / small_d as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Deep expression encoding appears quadratic: \
         T(D={})={}μs, T(D={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         encode_trust_vc_expr or tree walk helpers may have O(D²) behavior.",
        small_d,
        t_small,
        large_d,
        t_large,
        ratio,
        normalized,
    );
}

fn time_deep_expression(depth: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("v0", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("bound", "v0 == 1"));

    // Build: v0 + v0 + v0 + ... == v0 * D
    // Parsed as left-associative: ((v0 + v0) + v0) + ...
    let mut additions = "v0".to_string();
    for _ in 1..depth {
        additions = format!("{} + v0", additions);
    }
    let assertion = format!("{} == v0 * {}", additions, depth);
    ctx.push_obligation(crate::vc::ProofObligation::assert("deep_check", &assertion));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(
        &result,
        &format!("Deep expression test failed at depth {depth}"),
    );

    elapsed
}

// ============================================================
// Test 3: TrustVcExpr tree walk scaling (IR-level)
// ============================================================

/// Directly measures `references_collection()` and
/// `has_non_skolemized_quantifier()` on synthetic TrustVcExpr trees
/// of varying depth. Both should be O(D) — one traversal per call.
///
/// This catches regressions where a tree walk accidentally
/// traverses subtrees multiple times (e.g., evaluating both
/// left and right branches before short-circuiting).
#[test]
fn test_trust_vc_expr_tree_walk_linear() {
    let small_d = 200;
    let large_d = 800;

    let small_tree = build_chain_expr(small_d);
    let large_tree = build_chain_expr(large_d);

    let t_small = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..10_000 {
                let _ = small_tree.references_collection();
                let _ = small_tree.has_non_skolemized_quantifier();
            }
            start.elapsed().as_micros()
        },
        3,
    );

    let t_large = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..10_000 {
                let _ = large_tree.references_collection();
                let _ = large_tree.has_non_skolemized_quantifier();
            }
            start.elapsed().as_micros()
        },
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_d as f64 / small_d as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "TrustVcExpr tree walk appears quadratic: \
         T(D={})={}μs, T(D={})={}μs, ratio={:.1}x, normalized={:.1}x.",
        small_d,
        t_small,
        large_d,
        t_large,
        ratio,
        normalized,
    );
}

/// Build a left-leaning chain: ((v + v) + v) + ... with D additions.
fn build_chain_expr(depth: usize) -> crate::ir::TrustVcExpr {
    use crate::ir::{TrustVcExpr, TrustVcType};
    use crate::ir_expr::ArithOp;

    let ty = TrustVcType::Uint { width: 32 };
    let leaf = TrustVcExpr::Var {
        name: "v".to_string(),
        ty: ty.clone(),
    };

    let mut acc = leaf.clone();
    for _ in 1..depth {
        acc = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(acc),
            right: Box::new(leaf.clone()),
            ty: ty.clone(),
        };
    }
    acc
}

// ============================================================
// Test 4: Encoder multiplier constant factor
// ============================================================

/// Both paths create 2 encoder setups per assertion (overflow + main).
/// When `check_overflow=true`, the overflow encoder additionally runs
/// per-predicate solver calls for each arithmetic operation. This test
/// verifies that overhead stays bounded — specifically, that enabling
/// overflow checks doesn't exceed 4x the cost of the base verification.
///
/// A regression beyond 4x would indicate an expensive new step in the
/// overflow checking path (e.g., an extra encoder setup or solver call
/// leaking into the per-assertion hot path).
#[test]
fn test_encoder_multiplier_bounded() {
    let n_assertions = 10;

    let t_overflow = measure_median(|| time_verify_with_overflow(n_assertions, true), 3);
    let t_no_overflow = measure_median(|| time_verify_with_overflow(n_assertions, false), 3);

    if t_no_overflow < MIN_MEASURABLE_US {
        return;
    }

    let multiplier = t_overflow as f64 / t_no_overflow as f64;

    // Both paths create 2 encoder setups. Overflow=true adds per-predicate
    // solver calls. For simple expressions (x+0==x), the overhead should be
    // modest. 4x threshold catches regressions from unexpected extra work.
    assert!(
        multiplier < 4.0,
        "Overflow check overhead exceeds 4x: \
         T(overflow)={}μs, T(no_overflow)={}μs, ratio={:.1}x. \
         Check verify_single_assertion_typed_inner for extra encoder setups.",
        t_overflow,
        t_no_overflow,
        multiplier,
    );
}

fn time_verify_with_overflow(n_assertions: usize, check_overflow: bool) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("bound", "x > 0"));
    if check_overflow {
        ctx.enable_overflow_checks();
    }

    for i in 0..n_assertions {
        ctx.push_obligation(crate::vc::ProofObligation::assert(
            format!("id_{}", i),
            "x + 0 == x",
        ));
    }

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(
        &result,
        &format!("Encoder multiplier test failed (overflow={check_overflow})"),
    );

    elapsed
}

// ============================================================
// Test 5: Ground pool registration scales linearly
// ============================================================

/// The ground pool's `register()` is called per ground function call during
/// encoding. Internally it hashes a `GroundKey` (String + Vec<Term>) and
/// inserts into a HashSet for deduplication — O(1) amortized per call.
///
/// End-to-end verification time scales super-linearly with ground term count
/// (observed ~46x for 4x input increase at E=5→20) but that cost is ay-dpll
/// solver overhead from more ground assertions, not our encoding code.
///
/// This test isolates the data structure from solver overhead by measuring
/// only registration time (no check_sat, no flush). A regression from O(1)
/// to O(N) per registration (e.g., linear scan replacing HashSet lookup)
/// would show as T(200)/T(50) ≈ 16x instead of ≈ 4x.
#[test]
fn test_ground_pool_registration_scales_linearly() {
    let small = 50;
    let large = 200;

    let t_small = measure_median(|| time_pool_registration(small), 5);
    let t_large = measure_median(|| time_pool_registration(large), 5);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Ground pool registration scaling appears quadratic: \
         T(E={})={}μs, T(E={})={}μs, ratio={:.1}x, normalized={:.1}x. \
         register() may have regressed from O(1) to O(N) per call.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_pool_registration(n_entries: usize) -> u128 {
    use crate::encoder::ground_pool::GroundTermPool;
    use ay_dpll::api::{Logic, Solver};

    let mut solver = Solver::try_new(Logic::All).expect("solver");

    // Create N distinct BV32 constants as ground terms
    let terms: Vec<_> = (0..n_entries)
        .map(|i| solver.try_bv_const(i as i64, 32).expect("bv const"))
        .collect();

    let mut pool = GroundTermPool::new();

    let start = std::time::Instant::now();

    // Register N ground entries for symbol "f"
    for term in &terms {
        assert!(pool.register("f", vec![*term]));
    }

    let elapsed = start.elapsed().as_micros();

    assert_eq!(pool.ground_term_count(), n_entries);
    elapsed
}

// ============================================================
// Test 6: Ground pool convergence — early termination
// ============================================================

/// The fixpoint loop uses `GROUND_FIXPOINT_ROUNDS = 1` as the hard
/// bound. When no chaining occurs (single-hop axioms), the loop
/// should converge in round 1 (all pending pairs instantiated, no
/// new ground terms discovered). This test verifies that adding
/// ground terms to the pool doesn't prevent convergence.
///
/// With a single round, convergence means all pending (axiom, term)
/// pairs are instantiated and no new ground terms are discovered.
/// ay's 8-round E-matching handles any further chaining internally.
#[test]
fn test_ground_pool_convergence_bounded_rounds() {
    use crate::vc::FunctionContext;

    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.set_function_context(FunctionContext {
            name: "f".to_string(),
            params: vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
            return_type: crate::ir::TrustVcType::Int { width: 32 },
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        });

        // Body axiom: f(x) == x + 1
        ctx.obligations.push(
            ProofObligation::broadcast_assume("__body_axiom_f", "f(x) == x + 1")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
        );

        // 10 ground terms — all instantiated in round 1
        for i in 1..=10 {
            ctx.push_obligation(crate::vc::ProofObligation::assume(
                format!("ground_{}", i),
                format!("f({}) >= 0", i),
            ));
        }
        ctx.push_obligation(crate::vc::ProofObligation::assert("check", "f(1) == 2"));

        let result = AYEncoder::verify(&ctx);
        expect_verified(&result, "Ground pool convergence test should verify");
    });
}
