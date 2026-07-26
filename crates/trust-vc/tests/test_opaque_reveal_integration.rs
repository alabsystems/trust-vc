// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proc-macro integration tests for opaque/reveal through the full pipeline.
//!
//! These tests exercise the full `#[trust_vc::proof]` → `VerificationPipeline` → ay
//! pipeline for opaque/reveal features that previously only had encoder-level
//! coverage (#2429).
//!
//! Part of #2429.

mod common;

use trust_vc::{proof, spec};

// === Opaque / Reveal integration tests ===

// opaque must appear AFTER spec so spec expansion can detect it
#[spec]
#[trust_vc::opaque]
fn secret_square(x: u64) -> u64 {
    x * x
}

#[proof]
fn proof_opaque_with_reveal() {
    let _ = secret_square(0u64);
    trust_vc::reveal!(secret_square);
    trust_vc::assert!(secret_square(3u64) == 9u64);
}

/// Opaque spec function WITH reveal should verify.
#[test]
fn test_opaque_spec_with_reveal_verifies() {
    let _ = common::verify_should_pass(proof_opaque_with_reveal);
}

#[proof]
fn proof_opaque_without_reveal() {
    let _ = secret_square(0u64);
    // No reveal — body axiom is hidden, assertion unprovable
    trust_vc::assert!(secret_square(3u64) == 9u64);
}

/// Opaque spec function WITHOUT reveal should fail (body hidden).
#[test]
fn test_opaque_spec_without_reveal_fails() {
    let _ = common::verify_should_fail(proof_opaque_without_reveal);
}

// === Non-opaque spec function (baseline) ===

#[spec]
fn visible_double(x: u64) -> u64 {
    x + x
}

#[proof]
fn proof_non_opaque_always_visible() {
    let _ = visible_double(0u64);
    trust_vc::assert!(visible_double(3u64) == 6u64);
}

/// Non-opaque spec function should verify without reveal.
#[test]
fn test_non_opaque_spec_verifies_without_reveal() {
    let _ = common::verify_should_pass(proof_non_opaque_always_visible);
}

// === reveal_group integration test ===

#[spec]
#[trust_vc::opaque]
fn opaque_alpha(x: u64) -> u64 {
    x + 1
}

#[spec]
#[trust_vc::opaque]
fn opaque_beta(x: u64) -> u64 {
    x + 2
}

#[proof]
fn proof_reveal_group_both() {
    let _ = opaque_alpha(0u64);
    let _ = opaque_beta(0u64);
    trust_vc::reveal_group!(opaque_alpha, opaque_beta);
    trust_vc::assert!(opaque_alpha(3u64) == 4u64);
    trust_vc::assert!(opaque_beta(3u64) == 5u64);
}

/// reveal_group! reveals multiple opaque functions at once.
#[test]
fn test_reveal_group_verifies_both() {
    let _ = common::verify_should_pass(proof_reveal_group_both);
}

/// Partial reveal: revealing alpha but NOT beta.
#[proof]
fn proof_partial_reveal_alpha_only() {
    let _ = opaque_alpha(0u64);
    let _ = opaque_beta(0u64);
    trust_vc::reveal!(opaque_alpha);
    // Only alpha is provable; assert only about alpha
    trust_vc::assert!(opaque_alpha(3u64) == 4u64);
}

#[test]
fn test_partial_reveal_alpha_only_verifies() {
    let _ = common::verify_should_pass(proof_partial_reveal_alpha_only);
}

// === Named reveal group tests (#2415) ===

// Define a named group containing both opaque functions.
trust_vc::reveal_group!(group_opaque_pair {
    opaque_alpha,
    opaque_beta
});

/// reveal!(group_name) expands to individual reveals for all members.
#[proof]
fn proof_reveal_named_group() {
    let _ = opaque_alpha(0u64);
    let _ = opaque_beta(0u64);
    trust_vc::reveal!(group_opaque_pair);
    trust_vc::assert!(opaque_alpha(3u64) == 4u64);
    trust_vc::assert!(opaque_beta(3u64) == 5u64);
}

#[test]
fn test_reveal_named_group_verifies_both() {
    let _ = common::verify_should_pass(proof_reveal_named_group);
}

/// reveal!(name) for an unregistered name falls through to single-function path.
#[proof]
fn proof_reveal_unknown_name_fallthrough() {
    let _ = opaque_alpha(0u64);
    trust_vc::reveal!(opaque_alpha);
    trust_vc::assert!(opaque_alpha(3u64) == 4u64);
}

#[test]
fn test_reveal_unknown_name_fallthrough() {
    let _ = common::verify_should_pass(proof_reveal_unknown_name_fallthrough);
}

/// Inline reveal_group syntax still works (backward compat).
#[proof]
fn proof_inline_reveal_group_still_works() {
    let _ = opaque_alpha(0u64);
    let _ = opaque_beta(0u64);
    trust_vc::reveal_group!(opaque_alpha, opaque_beta);
    trust_vc::assert!(opaque_alpha(3u64) == 4u64);
    trust_vc::assert!(opaque_beta(3u64) == 5u64);
}

#[test]
fn test_inline_reveal_group_backward_compat() {
    let _ = common::verify_should_pass(proof_inline_reveal_group_still_works);
}
