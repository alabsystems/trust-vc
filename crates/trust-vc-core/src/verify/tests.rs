//! Tests for the verify module.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_proof_builder() {
    let proof = Proof::new("test")
        .with_variable("x", "i32")
        .with_assumption("positive", "x > 0")
        .with_assertion("x >= 0");

    assert_eq!(proof.name, "test");
    assert_eq!(proof.variables.len(), 1);
    assert_eq!(proof.assumptions.len(), 1);
    assert_eq!(proof.assertions.len(), 1);
    // with_assertion uses the condition as the name for descriptive error messages
    assert_eq!(proof.assertions[0].0, "x >= 0");
    assert_eq!(proof.assertions[0].1, "x >= 0");
}

#[test]
fn test_verifier_valid() {
    let proof = Proof::new("identity")
        .with_variable("x", "i32")
        .with_assertion("x + 0 == x");

    let result = Verifier::verify(&proof);
    assert!(result.is_verified(), "Expected Verified, got: {:?}", result);
}

#[test]
fn test_verifier_invalid() {
    let proof = Proof::new("contradiction")
        .with_variable("x", "i32")
        .with_assertion("x != x");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_counterexample(),
        "Expected Counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_verifier_with_assumption() {
    let proof = Proof::new("implication")
        .with_variable("x", "i32")
        .with_assumption("positive", "x > 0")
        .with_assertion("x >= 0");

    let result = Verifier::verify(&proof);
    assert!(result.is_verified(), "Expected Verified, got: {:?}", result);
}

#[test]
fn test_proof_macro() {
    let proof = proof! {
        name: "macro_test",
        vars: { x: i32, y: i32 },
        assume: { x_pos: "x > 0", y_pos: "y > 0" },
        assert: { sum_pos: "x + y > 0" }
    };

    assert_eq!(proof.name, "macro_test");
    assert_eq!(proof.variables.len(), 2);
    assert_eq!(proof.assumptions.len(), 2);
    assert_eq!(proof.assertions.len(), 1);
}

#[test]
fn test_result_helper_methods() {
    let verified = VerifyResult::Verified;
    assert!(verified.is_verified());
    assert!(!verified.is_counterexample());
    assert!(!verified.is_unknown());
    assert!(!verified.is_error());

    let counterexample = VerifyResult::Counterexample {
        obligation_name: "test".into(),
        model: None,
        bindings: Vec::new(),
    };
    assert!(!counterexample.is_verified());
    assert!(counterexample.is_counterexample());

    let unknown = VerifyResult::unknown("test", None);
    assert!(unknown.is_unknown());

    let error = VerifyResult::Error {
        message: "test".into(),
    };
    assert!(error.is_error());
}

#[test]
fn test_extract_type_string_proph_bool_erases() {
    let ty: syn::Type = syn::parse_str("Proph<bool>").expect("invariant: test input is valid");
    assert_eq!(extract_type_string(&ty), "bool");
}

#[test]
fn test_extract_type_string_snapshot_u32_erases() {
    let ty: syn::Type = syn::parse_str("Snapshot<u32>").expect("invariant: test input is valid");
    assert_eq!(extract_type_string(&ty), "u32");
}
