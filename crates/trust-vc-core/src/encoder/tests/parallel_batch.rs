// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `AYEncoder::verify_batch_parallel` — the parallel function
//! verification API introduced in v2 (#2647).
//!
//! Key properties tested:
//! 1. Correct results from parallel dispatch (all-Verified, mixed outcomes)
//! 2. Result ordering matches input ordering
//! 3. Single-context fallback (sequential fast-path)
//! 4. Empty batch produces empty results

use super::*;
use crate::prepared_context::prepare_context;

/// Build a trivially-verified context: `x > 0 ⊢ x >= 0`.
fn make_verified_context(label: &str) -> PreparedVerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume(format!("{label}_assume"), "x > 0"));
    ctx.push_obligation(ProofObligation::assert(format!("{label}_assert"), "x >= 0"));
    prepare_context(&ctx).expect("prepare should succeed for trivial context")
}

/// Build a context that produces a counterexample: `⊢ x > 0` (no assumptions).
fn make_counterexample_context(label: &str) -> PreparedVerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assert(format!("{label}_assert"), "x > 0"));
    prepare_context(&ctx).expect("prepare should succeed for counterexample context")
}

#[test]
fn test_batch_parallel_all_verified() {
    let contexts: Vec<_> = (0..4)
        .map(|i| make_verified_context(&format!("fn{i}")))
        .collect();

    let results = AYEncoder::verify_batch_parallel(contexts);

    assert_eq!(results.len(), 4, "should return one result per context");
    for (i, batch_result) in results.iter().enumerate() {
        assert_eq!(
            batch_result.index(),
            i,
            "result index should match input order"
        );
        expect_verified(batch_result.result(), &format!("batch fn{i}"));
        assert!(
            batch_result.elapsed().as_nanos() > 0,
            "elapsed time should be non-zero"
        );
    }
}

#[test]
fn test_batch_parallel_mixed_outcomes() {
    let contexts = vec![
        make_verified_context("fn0"),
        make_counterexample_context("fn1"),
        make_verified_context("fn2"),
        make_counterexample_context("fn3"),
    ];

    let results = AYEncoder::verify_batch_parallel(contexts);

    assert_eq!(results.len(), 4);
    expect_verified(results[0].result(), "fn0 should verify");
    expect_counterexample(results[1].result(), "fn1 should produce counterexample");
    expect_verified(results[2].result(), "fn2 should verify");
    expect_counterexample(results[3].result(), "fn3 should produce counterexample");
}

#[test]
fn test_batch_parallel_single_context_sequential() {
    let contexts = vec![make_verified_context("solo")];

    let results = AYEncoder::verify_batch_parallel(contexts);

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].index(), 0);
    expect_verified(results[0].result(), "solo function");
}

#[test]
fn test_batch_parallel_empty_batch() {
    let results = AYEncoder::verify_batch_parallel(vec![]);
    assert!(
        results.is_empty(),
        "empty batch should produce empty results"
    );
}

#[test]
fn test_batch_parallel_preserves_index_ordering() {
    let contexts: Vec<_> = (0..8)
        .map(|i| make_verified_context(&format!("fn{i}")))
        .collect();

    let results = AYEncoder::verify_batch_parallel(contexts);

    assert_eq!(results.len(), 8);
    for (i, batch_result) in results.iter().enumerate() {
        assert_eq!(
            batch_result.index(),
            i,
            "result at position {i} should have index {i}, got {}",
            batch_result.index()
        );
    }
}
