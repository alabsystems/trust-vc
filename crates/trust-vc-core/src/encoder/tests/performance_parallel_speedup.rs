// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance proof: parallel batch verification achieves linear speedup.
//!
//! Demonstrates acceptance criterion 2 of #2647: "Linear speedup demonstrated
//! (≥1.5x conservative gate; typically 3-6x on 8+ core machines)."
//!
//! Creates N independent verification contexts using MathInt variables (LIA
//! theory — fast per assertion), each with enough variables and assertions to
//! require measurable encoder + solver time. Compares sequential wall-clock
//! time against parallel (via `verify_batch_parallel`).
//!
//! MathInt is used instead of i32/u32 to avoid BV SAT decomposition overhead
//! (~2s per BV assertion). LIA comparisons resolve in milliseconds, letting
//! us measure dispatch/parallelism overhead rather than solver-bound time.
//!
//! Feature-gated behind `expensive-tests`.

use super::*;
use crate::prepared_context::prepare_context;
use std::time::Instant;

/// Number of independent function contexts to verify.
const BATCH_SIZE: usize = 8;

/// Variables per context — enough to require meaningful encoder setup.
const VARS_PER_CTX: usize = 40;

/// Assumptions per context — chain of ordering constraints.
const ASSUMPTIONS_PER_CTX: usize = 30;

/// Assertions per context — transitivity proofs over the ordering chain.
const ASSERTIONS_PER_CTX: usize = 15;

/// Build a verification context with enough solver work to take measurable time.
///
/// Uses MathInt variables (Sort::Int, LIA theory) for fast-but-non-trivial
/// verification. Each context has `VARS_PER_CTX` variables,
/// `ASSUMPTIONS_PER_CTX` chained ordering assumptions (v0 < v1 < v2 < ...),
/// and `ASSERTIONS_PER_CTX` transitivity assertions (v_i < v_{i+gap}).
fn make_solver_context(id: usize) -> PreparedVerificationContext {
    let mut ctx = VerificationContext::new();

    for j in 0..VARS_PER_CTX {
        ctx.declare_var_typed(&format!("v{id}_{j}"), crate::ir::TrustVcType::MathInt);
    }

    // Ordering chain: v0 < v1 < v2 < ... < v_{n-1}
    for j in 0..ASSUMPTIONS_PER_CTX {
        ctx.push_obligation(ProofObligation::assume(
            &format!("order_{id}_{j}"),
            format!("v{id}_{j} < v{id}_{}", j + 1),
        ));
    }

    // Transitivity assertions: v_i < v_{i+gap} where gap > 1
    for j in 0..ASSERTIONS_PER_CTX {
        let lo = j;
        let hi = lo + 3; // gap of 3 — requires 3-step transitivity
        assert!(
            hi <= ASSUMPTIONS_PER_CTX,
            "assertion index out of bounds: hi={hi}, max={}",
            ASSUMPTIONS_PER_CTX,
        );
        ctx.push_obligation(ProofObligation::assert(
            &format!("trans_{id}_{j}"),
            format!("v{id}_{lo} < v{id}_{hi}"),
        ));
    }

    prepare_context(&ctx).expect("MathInt context should prepare")
}

/// Proves parallel batch verification is faster than sequential.
///
/// Creates `BATCH_SIZE` independent contexts, times sequential execution
/// (one-at-a-time via `verify_prepared_inner`) against parallel execution
/// (via `verify_batch_parallel`), and asserts meaningful speedup.
///
/// The threshold is conservative: at least 1.5x on any machine with 2+ cores.
/// The test prints actual speedup and timing for closure evidence (#2647).
#[test]
fn test_parallel_batch_speedup_over_sequential() {
    let contexts: Vec<_> = (0..BATCH_SIZE).map(make_solver_context).collect();

    // Sequential: verify each context one at a time
    let seq_us = measure_median(
        || {
            let start = Instant::now();
            for (i, ctx) in contexts.iter().enumerate() {
                let result = AYEncoder::verify_prepared_inner(ctx);
                expect_verified(&result, &format!("sequential context {i}"));
            }
            start.elapsed().as_micros()
        },
        3,
    );

    // Parallel: verify all contexts concurrently
    let par_us = measure_median(
        || {
            let batch = contexts.clone();
            let start = Instant::now();
            let results = AYEncoder::verify_batch_parallel(batch);
            let elapsed = start.elapsed().as_micros();
            for r in &results {
                expect_verified(r.result(), &format!("parallel context {}", r.index()));
            }
            elapsed
        },
        3,
    );

    let cores = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(2);
    let max_threads = crate::encoder::verification::timeout::max_solver_threads();
    let speedup = if par_us > 0 {
        seq_us as f64 / par_us as f64
    } else {
        f64::INFINITY
    };

    // Print evidence for closure verification (#2647).
    eprintln!(
        "[parallel_speedup] {speedup:.2}x speedup \
         (seq={seq_us}µs, par={par_us}µs, cores={cores}, \
         max_threads={max_threads}, batch={BATCH_SIZE})"
    );

    // Conservative threshold: at least 1.5x speedup with 8 contexts.
    assert!(
        speedup >= 1.5,
        "Parallel speedup {speedup:.2}x is below 1.5x threshold \
         (seq={seq_us}µs, par={par_us}µs, cores={cores}, \
         max_threads={max_threads}, batch={BATCH_SIZE}). \
         verify_batch_parallel should provide linear scaling (#2647).",
    );
}

/// Proves result ordering is preserved even under heavy parallel load.
///
/// Verifies that `BatchVerifyResult::index` values match the input order,
/// regardless of which thread finishes first.
#[test]
fn test_parallel_result_ordering_under_load() {
    let contexts: Vec<_> = (0..BATCH_SIZE).map(make_solver_context).collect();

    let results = AYEncoder::verify_batch_parallel(contexts);

    assert_eq!(
        results.len(),
        BATCH_SIZE,
        "result count should match input count"
    );
    for (position, r) in results.iter().enumerate() {
        assert_eq!(
            r.index(),
            position,
            "result at position {position} has wrong index {}",
            r.index()
        );
        expect_verified(r.result(), &format!("heavy batch context {position}"));
    }
}
