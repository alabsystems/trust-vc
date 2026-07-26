//! Integration tests for the high-level Proof builder API in verify.rs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests exercise the `Proof::new()` → `Verifier::verify()` pipeline,
//! which is distinct from the lower-level `VerificationContext` API tested in
//! ay_integration.rs. The Proof API is the user-facing entry point for
//! standalone verification.
//!
//! Rescued from orphaned `tests/ay_integration.rs` in workspace root, which
//! could never compile because no package target existed at workspace level.
//! See #1597.

use trust_vc_core::verify::{Proof, Verifier};

// ============================================================================
// Proof Builder API Tests
// ============================================================================

/// Test the Proof builder constructs a valid context and verifies identity law.
/// This exercises Proof::new → with_variable → with_assertion → Verifier::verify.
#[test]
fn test_proof_builder_identity() {
    let proof = Proof::new("identity")
        .with_variable("x", "i32")
        .with_assertion("x + 0 == x");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Identity law via Proof builder should verify: {:?}",
        result
    );
}

/// Test that Proof builder correctly propagates false assertions to counterexamples.
#[test]
fn test_proof_builder_counterexample() {
    let proof = Proof::new("false_assertion")
        .with_variable("x", "i32")
        .with_assertion("x != x");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_counterexample(),
        "False assertion via Proof builder should produce counterexample: {:?}",
        result
    );
}

/// Test Proof builder with assumptions (requires → ensures pattern).
#[test]
fn test_proof_builder_with_assumptions() {
    let proof = Proof::new("contract")
        .with_variable("x", "i32")
        .with_assumption("precondition", "x > 0")
        .with_assertion("x >= 0");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Contract via Proof builder should verify: {:?}",
        result
    );
}

/// Test Proof builder with multiple variables and bounded arithmetic.
#[test]
fn test_proof_builder_multi_variable_arithmetic() {
    let proof = Proof::new("arithmetic")
        .with_variable("x", "i32")
        .with_variable("y", "i32")
        .with_assumption("x_bounds", "x > 0 && x < 100")
        .with_assumption("y_bounds", "y > 0 && y < 100")
        .with_assertion("x + y > 0");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Bounded multi-variable arithmetic should verify: {:?}",
        result
    );
}

/// Test division with nonzero divisor does not error.
#[test]
fn test_proof_builder_division_nonzero() {
    let proof = Proof::new("safe_division")
        .with_variable("x", "i32")
        .with_variable("y", "i32")
        .with_assumption("y_nonzero", "y != 0")
        .with_assertion("x / y * y <= x");

    let result = Verifier::verify(&proof);
    // May be Unknown due to nonlinear arithmetic. Key: should not error.
    assert!(
        !result.is_error(),
        "Division with nonzero divisor should not error: {:?}",
        result
    );
}

/// Test hex literal support through the Proof API.
#[test]
fn test_proof_builder_hex_literals() {
    let proof = Proof::new("hex_literals")
        .with_variable("x", "i32")
        .with_assumption("x_is_ff", "x == 0xFF")
        .with_assertion("x == 255");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Hex literal 0xFF should equal 255: {:?}",
        result
    );
}

// ============================================================================
// Meta-validation: ay actually running
// ============================================================================

/// Meta-test: Proves ay is actually running by checking that we get both
/// Verified and Counterexample results from different proofs. If ay were
/// stubbed or broken, all results would be the same.
#[test]
fn test_ay_is_actually_running() {
    let mut verified_count = 0;
    let mut counterexample_count = 0;

    // Test 1: Should verify (tautology)
    let proof1 = Proof::new("tautology")
        .with_variable("x", "i32")
        .with_assertion("x == x");
    if Verifier::verify(&proof1).is_verified() {
        verified_count += 1;
    }

    // Test 2: Should produce counterexample (contradiction)
    let proof2 = Proof::new("contradiction")
        .with_variable("x", "i32")
        .with_assertion("x != x");
    if Verifier::verify(&proof2).is_counterexample() {
        counterexample_count += 1;
    }

    // Test 3: Another verified (with assumptions)
    let proof3 = Proof::new("modus_ponens")
        .with_variable("x", "i32")
        .with_assumption("x_pos", "x > 0")
        .with_assertion("x >= 1");
    if Verifier::verify(&proof3).is_verified() {
        verified_count += 1;
    }

    assert!(
        verified_count > 0 && counterexample_count > 0,
        "ay must produce both verified and counterexample results: \
         verified={}, counterexample={}",
        verified_count,
        counterexample_count
    );
}

// ============================================================================
// VerifyResult convenience method tests
// ============================================================================

/// Test that VerifyResult helper methods work correctly on known results.
#[test]
fn test_verify_result_verified() {
    let result = Verifier::verify(
        &Proof::new("trivial")
            .with_variable("x", "i32")
            .with_assertion("x == x"),
    );
    assert!(result.is_verified());
    assert!(!result.is_counterexample());
    assert!(!result.is_unknown());
    assert!(!result.is_error());
}

/// Test VerifyResult helpers on a counterexample result.
#[test]
fn test_verify_result_counterexample() {
    let result = Verifier::verify(
        &Proof::new("false")
            .with_variable("x", "i32")
            .with_assertion("x != x"),
    );
    assert!(!result.is_verified());
    assert!(result.is_counterexample());
    assert!(!result.is_unknown());
    assert!(!result.is_error());
}

// ============================================================================
// Restored tests: dropped during rescue (commit 6a47fc5, #1637)
// ============================================================================

/// Test u64 termination measure: n - 1 < n when n > 0.
/// Originally `test_termination_measure` in workspace-root ay_integration.rs.
#[test]
fn test_termination_measure() {
    let proof = Proof::new("termination")
        .with_variable("n", "u64")
        .with_assumption("n_positive", "n > 0")
        .with_assertion("n - 1 < n");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Termination measure should verify, got: {:?}",
        result
    );
}

/// Test Seq<i32> length is non-negative.
/// Originally `test_spec_collections` in workspace-root ay_integration.rs.
#[test]
fn test_spec_collections() {
    let proof = Proof::new("seq_length")
        .with_variable("s", "Seq<i32>")
        .with_assertion("s.len() >= 0");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Seq length non-negative should verify, got: {:?}",
        result
    );
}

/// Test Set<i32> membership tautology: assume s.contains(x), assert s.contains(x).
/// Originally `test_set_membership` in workspace-root ay_integration.rs.
#[test]
fn test_set_membership() {
    let proof = Proof::new("set_membership")
        .with_variable("s", "Set<i32>")
        .with_variable("x", "i32")
        .with_assumption("x_in_s", "s.contains(x)")
        .with_assertion("s.contains(x)");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Set membership tautology should verify, got: {:?}",
        result
    );
}

/// Test Map<i32, bool> lookup: assume m.get(k), assert m.get(k) == true.
/// Originally `test_map_lookup` in workspace-root ay_integration.rs.
/// Note: Map.get() support depends on ir_lowering CollectionOp::Get.
#[test]
fn test_map_lookup() {
    let proof = Proof::new("map_lookup")
        .with_variable("m", "Map<i32, bool>")
        .with_variable("k", "i32")
        .with_assumption("k_present", "m.contains_key(k)")
        .with_assumption("k_mapped", "m.get(k)")
        .with_assertion("m.get(k) == true");

    let result = Verifier::verify(&proof);
    assert!(
        result.is_verified(),
        "Map lookup should verify, got: {:?}",
        result
    );
}

// ============================================================================
// Proof::to_context integration
// ============================================================================

/// Test that Proof::to_context produces a valid VerificationContext
/// that can be verified directly.
#[test]
fn test_proof_to_context_roundtrip() {
    let proof = Proof::new("roundtrip")
        .with_variable("a", "i32")
        .with_assumption("a_pos", "a > 0")
        .with_assertion("a >= 1");

    // Verify via Proof API
    let result_proof = Verifier::verify(&proof);

    // Verify via direct context
    let ctx = proof.to_context();
    let result_ctx = Verifier::verify_context(&ctx);

    // Both paths should produce the same result
    assert!(
        result_proof.is_verified() && result_ctx.is_verified(),
        "Proof API and direct context should both verify: proof={:?}, ctx={:?}",
        result_proof,
        result_ctx
    );
}
