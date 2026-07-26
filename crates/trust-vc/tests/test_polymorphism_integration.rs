// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proc-macro integration tests for generic spec functions through the
//! full `#[trust_vc::proof]` → `VerificationPipeline` → ay pipeline.
//!
//! These tests exercise Box/Unbox polymorphism encoding when a generic
//! `#[trust_vc::spec]` function is called with concrete types from a proof.
//!
//! Part of #2429.

mod common;

use trust_vc::{proof, spec};
use trust_vc_core::VerifyResult;

// === Generic spec function: identity<T>(x: T) -> T ===

#[spec]
fn spec_identity<T>(x: T) -> T {
    x
}

#[proof]
fn proof_identity_u64_verifies() {
    let _ = spec_identity(0u64);
    trust_vc::assert!(spec_identity(5u64) == 5u64);
}

/// Generic spec function called with u64 should verify through Box/Unbox.
#[test]
fn test_generic_spec_identity_u64_verifies() {
    let _ = common::verify_should_pass(proof_identity_u64_verifies);
}

#[proof]
fn proof_identity_u64_wrong_value_fails() {
    let _ = spec_identity(0u64);
    trust_vc::assert!(spec_identity(5u64) == 6u64);
}

/// Generic spec function with wrong expected value should be rejected.
#[test]
fn test_generic_spec_identity_u64_wrong_value_fails() {
    let result = common::verify_should_fail(proof_identity_u64_wrong_value_fails);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "generic spec identity wrong-value should produce Counterexample, got: {:?}",
        result
    );
}
