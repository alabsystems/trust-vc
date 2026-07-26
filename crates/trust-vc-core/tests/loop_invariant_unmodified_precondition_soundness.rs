// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Regression for the frame-condition inductive step carrying FUNCTION
// PRECONDITIONS over UNMODIFIED (frame-preserved) variables.
//
// Before: the loop inductive step bootstrapped with no assumptions, so a
// `#[requires]` constraining a loop-INVARIANT parameter was havoc'd away — a
// genuinely-preserved loop invariant that depends on that precondition refuted
// at the inductive step (a false negative). Now: a precondition whose variables
// are all unmodified by the loop is re-assumed at the loop head, where it is
// provably still true (an unmodified var keeps one value, so the predicate has
// the same truth value everywhere). The change is SOUND: dropping the
// precondition, or stating one over a MODIFIED var, still refutes.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture() -> String {
    format!(
        "{}/tests/fixtures/loop_invariant_unmodified_precondition.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(name: &str) -> VerifyResult {
    verify_function_from_file(&fixture(), name)
        .unwrap_or_else(|e| panic!("{name} should extract+verify, got error: {e}"))
}

/// The frame-preserved precondition makes the loop invariant provable.
#[test]
fn accumulate_entailed_verified() {
    let v = verify("accumulate_entailed");
    assert!(
        matches!(v, VerifyResult::Verified),
        "loop invariant must be PROVED once the unmodified-var precondition is \
         carried into the inductive step; got {v:?}"
    );
}

/// Load-bearing: the SAME loop without the step-entailment precondition refutes.
#[test]
fn accumulate_no_step_bound_refuted() {
    let v = verify("accumulate_no_step_bound");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "without the step entailment the invariant is NOT preserved; got {v:?}"
    );
}

/// Soundness of the gate: a precondition over a MODIFIED var is NOT carried in,
/// so the invariant over that var still refutes.
#[test]
fn modified_precondition_not_carried_refuted() {
    let v = verify("modified_precondition_not_carried");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "a precondition over a MODIFIED var must NOT be assumed in the inductive \
         step; the invariant must still refute; got {v:?}"
    );
}
