//! Performance scaling proofs for overflow checking and typed path allocation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Design
//!
//! Complements `performance_scaling.rs` which covers the default (no overflow)
//! path. These tests target the typed verification pipeline's overflow handling
//! (`verify_single_assertion_typed_inner` in assertion.rs) where each assertion
//! with overflow checks creates a fresh encoder and re-encodes conditions.
//!
//! # Findings covered
//!
//! 1. Overflow assertion scaling: each assertion creates a fresh encoder and
//!    re-encodes all assumptions. With A assertions total cost is O(A * (V+K)).
//!    Test ensures this stays proportional.
//!
//! 2. Per-assertion overflow predicate count: each overflow predicate creates
//!    a fresh encoder + full re-parse. For P predicates per assertion, cost
//!    is O(P * (V + K + B)). Test ensures linear scaling.
//!
//! 3. Expression chain encoding: `encode_trust_vc_expr` recurses into
//!    TrustVcExpr trees. A left-leaning chain of N operations should take
//!    O(N) time, not O(N²) from intermediate allocations.
//!
//! 4. Trigger encoding var_types clone: `encode_trigger_typed` clones
//!    `var_types` per trigger expression. With V variables and T triggers,
//!    cost should be O(T * V), not worse.
//!
//! 5. Wide conjunction typed encoding: flat N-way && chains should scale
//!    linearly through `encode_trust_vc_expr` (direct benchmark, not full
//!    `verify()` pipeline).

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. 12x threshold detects quadratic.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

// ============================================================
// Test 1: Overflow checking assertion count scaling
// ============================================================

/// When `check_overflow = true`, each assertion with arithmetic triggers
/// overflow checking in the typed path. Each assertion creates a fresh
/// encoder and re-encodes all assumptions.
///
/// With A assertions, verification time should be O(A * (V + K)).
/// This test confirms scaling is not worse than quadratic.
#[test]
fn test_overflow_assertion_scaling_not_cubic() {
    let small = 3;
    let large = 12;

    let t_small = measure_median(|| time_overflow_n_assertions(small), 3);
    let t_large = measure_median(|| time_overflow_n_assertions(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Expected O(A²): ratio should be ~16x for 4x scale.
    // Cubic would be ~64x. Threshold at 50x catches cubic.
    assert!(
        ratio < 50.0,
        "Overflow assertion scaling appears cubic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ≤16x for O(A²), \
         got {:.1}x). The overflow typed path may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        ratio,
    );
}

fn time_overflow_n_assertions(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound_x", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("bound_y", "y > 0"));
    ctx.enable_overflow_checks();

    // Each assertion has `x + y` which produces an overflow check
    for i in 0..n {
        ctx.push_obligation(ProofObligation::assert(format!("arith_{}", i), "x + y > 0"));
    }

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    // Overflow checking may find a counterexample (x + y can overflow i32).
    // We're measuring timing, not correctness — accept any result.
    expect_encodes_without_error(&result, "overflow scaling test");

    elapsed
}

// ============================================================
// Test 2: Overflow predicate count per assertion
// ============================================================

/// A single assertion with N arithmetic operations produces ~N overflow
/// predicates. Each predicate creates a fresh encoder (`setup_from_context`).
/// Total cost should be O(N * (V + K)) — linear in predicate count.
#[test]
fn test_overflow_predicate_count_linear() {
    let small = 2;
    let large = 8;

    let t_small = measure_median(|| time_n_overflow_predicates(small), 3);
    let t_large = measure_median(|| time_n_overflow_predicates(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64; // 4x
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Overflow predicate scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ~{:.0}x for linear, \
         normalized={:.1}x). Fresh-encoder-per-overflow may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_n_overflow_predicates(depth: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));
    ctx.enable_overflow_checks();

    // Build a condition with `depth` additions: x + x + x + ... > 0
    // Each `+` produces an overflow check, so depth additions = depth predicates.
    let mut expr = "x".to_string();
    for _ in 0..depth {
        expr = format!("{} + x", expr);
    }
    expr = format!("{} > 0", expr);

    ctx.push_obligation(ProofObligation::assert("deep_arith", &expr));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_encodes_without_error(&result, "overflow predicate scaling test");

    elapsed
}

// ============================================================
// Test 3: Deep expression tree encoding
// ============================================================

/// `encode_trust_vc_expr` recurses into TrustVcExpr trees. A left-leaning chain
/// of N additions: ((((x + x) + x) + x) + x) has depth N and N nodes.
/// Encoding should take O(N) time — linear in chain length.
///
/// This catches quadratic patterns from repeated width coercion (each
/// `coerce_bv_widths` call on the accumulator) or term_widths HashMap growth.
#[test]
fn test_expression_chain_scales_linearly() {
    // Keep this benchmark within the supported expression-depth budget.
    // Deeper left-leaning chains now fail closed via `validate_expr_depth`
    // before recursive IR encoding can exhaust the default test-thread stack.
    let small = 6;
    let large = 24;

    let t_small = measure_median(|| time_expression_chain(small), 3);
    let t_large = measure_median(|| time_expression_chain(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64; // 4x
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Expression chain encoding appears quadratic: \
         T(len={})={}μs, T(len={})={}μs, ratio={:.1}x (expected ~{:.0}x \
         for linear, normalized={:.1}x). encode_trust_vc_expr may have O(N²) \
         intermediate allocation.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_expression_chain(chain_len: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));

    // Build a left-leaning chain: ((((x + x) + x) + x) ... ) > 0
    // Chain length = chain_len additions, depth = chain_len.
    let mut expr = "x".to_string();
    for _ in 0..chain_len {
        expr = format!("({} + x)", expr);
    }
    expr = format!("{} > 0", expr);

    ctx.push_obligation(ProofObligation::assert("chain", &expr));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_encodes_without_error(&result, "Expression chain test");

    elapsed
}

// ============================================================
// Test 4: Broadcast trigger encoding with many variables
// ============================================================

/// `encode_trigger_typed` (eval.rs:55) clones `self.var_types` per trigger.
/// With V variables and T triggers, cost should be O(T * V) — not worse.
/// This test scales V for fixed T and verifies linear growth.
#[test]
fn test_trigger_encoding_scales_linearly_with_variables() {
    let small_v = 5;
    let large_v = 20;

    let t_small = measure_median(|| time_trigger_encoding_n_vars(small_v), 3);
    let t_large = measure_median(|| time_trigger_encoding_n_vars(large_v), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_v as f64 / small_v as f64; // 4x
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Trigger encoding scaling appears quadratic in variables: \
         T({} vars)={}μs, T({} vars)={}μs, ratio={:.1}x (expected ~{:.0}x \
         for linear, normalized={:.1}x). var_types clone in \
         encode_trigger_typed may have regressed.",
        small_v,
        t_small,
        large_v,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_trigger_encoding_n_vars(n_vars: usize) -> u128 {
    let mut ctx = VerificationContext::new();

    for i in 0..n_vars {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("i32"),
        );
    }
    ctx.push_obligation(ProofObligation::assume("bound", "v0 > 0"));

    // Add a broadcast with a trigger pattern referencing v0.
    // The trigger encoding path clones var_types once per trigger expression.
    // Body must be satisfiable as a universal — "v0 == v0" is always true,
    // avoiding vacuous truth from contradictory "forall v0: v0 > 0" (#2258).
    let mut broadcast = ProofObligation::broadcast_assume("bc_0", "v0 == v0");
    broadcast = broadcast.with_bound_vars(vec!["v0".to_string()]);
    broadcast = broadcast.with_trigger_patterns(vec![vec!["v0".to_string()]]);
    ctx.obligations.push(broadcast);

    ctx.push_obligation(ProofObligation::assert("check", "v0 >= 0"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Trigger scaling test failed");

    elapsed
}

// ============================================================
// Test 5: Wide conjunction typed encoding (direct benchmark)
// ============================================================

/// Build a flat N-way conjunction TrustVcExpr: (a0 >= 0) && (a1 >= 0) && ...
///
/// The tree is left-leaning: `((a0 >= 0) && (a1 >= 0)) && (a2 >= 0) ...`
fn build_wide_conjunction_expr(n: usize) -> crate::ir_expr::TrustVcExpr {
    use crate::ir::TrustVcType;
    use crate::ir_expr::{CompareOp, LogicOp, TrustVcExpr};

    let conjunct = |i: usize| -> TrustVcExpr {
        TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Var {
                name: format!("a{}", i),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }
    };

    assert!(n > 0, "need at least 1 conjunct");
    let mut expr = conjunct(0);
    for i in 1..n {
        expr = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(expr),
            right: Box::new(conjunct(i)),
        };
    }
    expr
}

/// Time direct `encode_trust_vc_expr` on a wide N-way conjunction.
///
/// Isolates the encoding path (parser construction + recursive LogicOp::And
/// encoding + per-node metadata) from solver work and assertion orchestration.
fn time_wide_conjunction_encoding(n: usize) -> u128 {
    use crate::ir::TrustVcType;

    let expr = build_wide_conjunction_expr(n);

    let mut solver = Solver::try_new(ay_dpll::api::Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    for i in 0..n {
        let name = format!("a{}", i);
        let term = solver.declare_const(&name, Sort::bitvec(32));
        variables.insert(name.clone(), term);
        var_types.insert(name, TrustVcType::Int { width: 32 });
    }
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let start = std::time::Instant::now();
    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let result = parser.encode_trust_vc_expr(&expr);
    let elapsed = start.elapsed().as_micros();

    std::hint::black_box(&result);
    assert!(
        result.is_ok(),
        "Wide conjunction encoding failed: {:?}",
        result.err()
    );

    elapsed
}

fn measure_wide_conjunction_best_pair(small: usize, large: usize, trials: usize) -> (u128, u128) {
    let _timing_guard = TIMING_SERIALIZE_MUTEX
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    assert!(trials > 0);

    let _ = std::panic::catch_unwind(|| time_wide_conjunction_encoding(small));
    let _ = std::panic::catch_unwind(|| time_wide_conjunction_encoding(large));

    let mut small_best = None;
    let mut large_best = None;
    for _ in 0..trials {
        if let Ok(t) = std::panic::catch_unwind(|| time_wide_conjunction_encoding(small)) {
            small_best = Some(small_best.map_or(t, |best: u128| best.min(t)));
        }
        if let Ok(t) = std::panic::catch_unwind(|| time_wide_conjunction_encoding(large)) {
            large_best = Some(large_best.map_or(t, |best: u128| best.min(t)));
        }
    }

    (
        small_best.expect("all small wide-conjunction timing trials panicked"),
        large_best.expect("all large wide-conjunction timing trials panicked"),
    )
}

/// Flat N-way && chains should scale linearly through `encode_trust_vc_expr`.
///
/// This test benchmarks the typed encoding path directly — not the full
/// `AYEncoder::verify()` pipeline. That removes context preparation, solver
/// check_sat, and assertion orchestration noise that caused false positives
/// when this benchmark was run inside the full lib suite (#2383).
#[test]
fn test_wide_conjunction_scales_linearly() {
    let small = 15;
    let large = 60;

    // Use interleaved best-of samples for this microbenchmark. In the full
    // lib suite, ordinary non-timing tests still run concurrently and can
    // stretch one median sample enough to look quadratic (#2786).
    let (t_small, t_large) = measure_wide_conjunction_best_pair(small, large, 9);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64; // 4x
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Wide conjunction encoding scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ~{:.0}x for linear, \
         normalized={:.1}x).",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

// ============================================================
// Test 5b: Wide conjunction end-to-end correctness (non-timing)
// ============================================================

/// Separate correctness check: a wide conjunction still verifies through the
/// full `AYEncoder::verify()` pipeline.
///
/// This does NOT perform ratio checks or timing claims — it only asserts that
/// the end-to-end path produces a correct result. Complements the narrower
/// timing test above.
#[test]
fn test_wide_conjunction_verifies_end_to_end() {
    let n = 20;
    let mut ctx = VerificationContext::new();

    for i in 0..n {
        ctx.declare_var_typed(
            &format!("a{}", i),
            crate::ir::TrustVcType::parse_or_opaque("i32"),
        );
        ctx.push_obligation(ProofObligation::assume(
            format!("pos_{}", i),
            format!("a{} > 0", i),
        ));
    }

    let conjuncts: Vec<String> = (0..n).map(|i| format!("a{} >= 0", i)).collect();
    let condition = conjuncts.join(" && ");
    ctx.push_obligation(ProofObligation::assert("wide_check", &condition));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wide conjunction end-to-end test failed");
}
