// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;
use super::super::{MIN_MEASURABLE_US, QUADRATIC_THRESHOLD};

// ============================================================
// Test 4: Collection-heavy stress (Seq push chains) — #949
// ============================================================

/// Build a Seq push chain: `s.push(0).push(1)...push(n-1)`.
fn build_push_chain(base: &str, n: usize) -> String {
    let mut expr = base.to_string();
    for i in 0..n {
        expr = format!("{}.push({})", expr, i);
    }
    expr
}

/// Build a nested universally quantified formula that mentions every bound
/// variable in the final body.
fn build_nested_forall_reflexive_formula(depth: usize) -> String {
    assert!(depth > 0);

    let vars: Vec<String> = (0..depth).map(|i| format!("q{i}")).collect();
    let mut body = vars
        .iter()
        .map(|var| format!("{var} == {var}"))
        .collect::<Vec<_>>()
        .join(" && ");

    for var in vars.iter().rev() {
        body = format!("forall(|{var}: i32| !({var} >= 0 && {var} < 2) || ({body}))");
    }

    body
}

/// Stress regression for #949: ghost collection operations with a chain of
/// N push calls. Each push creates a nested array store term; the solver must
/// reason through the entire chain to verify length and element properties.
///
/// N=10 exercises the full encoder collection metadata pipeline (length
/// tracking, element axioms, BV coercion) at a depth that goes well beyond
/// typical unit tests (N=1-2) without entering the HEAVY tier.
#[test]
fn test_seq_push_chain_stress_verifies() {
    const CHAIN_LEN: usize = 10;
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::requires("empty", "s.len() == 0"));

    let chain = build_push_chain("s", CHAIN_LEN);

    // Verify the chain length equals the number of pushes.
    ctx.push_obligation(ProofObligation::assert(
        "chain_len",
        format!("{}.len() == {}", chain, CHAIN_LEN),
    ));

    // Verify the last pushed element is accessible and correct.
    ctx.push_obligation(ProofObligation::assert(
        "last_elem",
        format!("{}.index({}) == {}", chain, CHAIN_LEN - 1, CHAIN_LEN - 1),
    ));

    // Verify the first pushed element survives through all subsequent pushes.
    // This reads through N nested store operations in array theory.
    ctx.push_obligation(ProofObligation::assert(
        "first_elem",
        format!("{}.index(0) == 0", chain),
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "10-push Seq chain should verify length and element access without timeout",
    );
}

/// Larger deterministic stress regression for #949: a materially deeper Seq
/// push chain should still verify key length and element facts without falling
/// into timeout, Unknown, or fail-closed behavior.
///
/// This does not close the separate "huge collection benchmark" residual from
/// `#949`, but it raises the regular in-tree stress depth from 10 to 32 pushes
/// so collection regressions have a larger deterministic gate in CI.
#[test]
fn test_seq_push_chain_large_stress_verifies() {
    const CHAIN_LEN: usize = 32;
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::requires("empty", "s.len() == 0"));

    let chain = build_push_chain("s", CHAIN_LEN);
    let mid = CHAIN_LEN / 2;

    ctx.push_obligation(ProofObligation::assert(
        "large_chain_len",
        format!("{}.len() == {}", chain, CHAIN_LEN),
    ));
    ctx.push_obligation(ProofObligation::assert(
        "large_chain_first_elem",
        format!("{}.index(0) == 0", chain),
    ));
    ctx.push_obligation(ProofObligation::assert(
        "large_chain_mid_elem",
        format!("{}.index({}) == {}", chain, mid, mid),
    ));
    ctx.push_obligation(ProofObligation::assert(
        "large_chain_last_elem",
        format!("{}.index({}) == {}", chain, CHAIN_LEN - 1, CHAIN_LEN - 1),
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "32-push Seq chain should verify length and indexed reads without timeout",
    );
}

/// Deterministic quantifier-depth stress regression for #949: the verification
/// pipeline should still prove a 10-deep nested universal formula without
/// degrading to Unknown or fail-closed behavior.
///
/// The guarded reflexive body keeps the theorem solver-stable while still
/// forcing the parser, IR lowering, quantifier encoder, and solver bridge to
/// handle a materially deeper nested-quantifier shape than the regular suite.
#[test]
fn test_nested_quantifier_reflexive_stress_verifies() {
    const DEPTH: usize = 10;
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "nested_quantifier_reflexive",
        build_nested_forall_reflexive_formula(DEPTH),
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "10-deep nested forall reflexive body should verify without timeout",
    );
}

/// Scaling test for #949: compare Seq push chain verification time at
/// small (N=3) and large (N=8) depths. The encoder creates a fresh
/// array store per push, so time should scale roughly linearly in chain
/// depth (each push adds one store + one length axiom). Quadratic
/// blowup would indicate an axiom-count explosion or metadata tracking
/// regression.
#[test]
fn test_seq_push_chain_scaling_not_quadratic() {
    let small = 3;
    let large = 8;

    let t_small = measure_median(|| time_seq_push_chain(small), 3);
    let t_large = measure_median(|| time_seq_push_chain(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Seq push chain scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ~{:.1}x for linear, \
         got {:.1}x normalized). Collection metadata or axiom encoding may \
         have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_seq_push_chain(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::requires("empty", "s.len() == 0"));

    let chain = build_push_chain("s", n);
    ctx.push_obligation(ProofObligation::assert(
        "chain_len",
        format!("{}.len() == {}", chain, n),
    ));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Seq push chain should verify");
    elapsed
}
