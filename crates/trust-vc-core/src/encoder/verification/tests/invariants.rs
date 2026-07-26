//! Invariant verification regression tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::verification::outcome::AssertionOutcome;
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::prepared_context::{prepare_context, PreparedObligation};
use crate::vc::{ProofObligation, VerificationContext};

/// Helper: run the inductive step for an `exists(|v: i32| s.push(v).len() == k)`
/// loop invariant given a pre-state `s.len() == 2`, returning the outcome.
fn run_push_len_inductive_step(invariant_body: &str) -> AssertionOutcome {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "s",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    ctx.declare_var_typed("i", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.obligations
        .push(ProofObligation::loop_invariant("push_inv", invariant_body));
    ctx.set_loop_modified_vars("push_inv", vec!["i".to_string()]);

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let invariant = prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "push_inv")
        .expect("prepared context should contain the loop invariant");
    let verified_invariants: Vec<&PreparedObligation> = Vec::new();

    AYEncoder::verify_invariant_inductive_step_typed(&prepared, invariant, &verified_invariants)
        .expect("inductive step should encode without error under Route A uniform-Int length")
}

/// Route A (#2779) makes every spec-collection `.len()` an unbounded `Int`, so
/// the inductive-step pre-state `exists(|v: i32| s.push(v).len() == 3)` no
/// longer builds the BV-vs-Int sort mismatch this case was constructed to
/// surface. The push-length comparison encodes cleanly, and because the only
/// loop-modified var is `i` (the sequence `s` is unmodified), the invariant is
/// trivially preserved across the step — so it now VERIFIES.
///
/// The discriminating companion below shows the inductive machinery is not
/// vacuously verifying everything: an invariant that the modified var `i` can
/// break is NOT verified.
#[test]
fn test_inductive_step_prestate_push_len_verifies_under_uniform_int() {
    let outcome = run_push_len_inductive_step("exists(|v: i32| s.push(v).len() == 3)");
    assert!(
        matches!(outcome, AssertionOutcome::Verified),
        "inductive step for a cleanly-encoded, preserved push-length invariant \
         must verify under Route A uniform-Int length, got: {outcome:?}"
    );
}

/// Discriminating companion to the test above: an invariant constraining the
/// loop-modified variable `i` (`i < 5`) is NOT preserved by the inductive step
/// (the step havocs `i`), so it must NOT verify. This guards against the
/// inductive machinery vacuously passing every cleanly-encoded invariant.
#[test]
fn test_inductive_step_non_preserved_invariant_over_modified_var_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "s",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    ctx.declare_var_typed("i", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.obligations
        .push(ProofObligation::loop_invariant("i_bound", "i < 5"));
    ctx.set_loop_modified_vars("i_bound", vec!["i".to_string()]);

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let invariant = prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "i_bound")
        .expect("prepared context should contain the loop invariant");
    let verified_invariants: Vec<&PreparedObligation> = Vec::new();

    let outcome = AYEncoder::verify_invariant_inductive_step_typed(
        &prepared,
        invariant,
        &verified_invariants,
    )
    .expect("inductive step should encode without error");
    assert!(
        !matches!(outcome, AssertionOutcome::Verified),
        "an invariant the modified var can break must NOT be verified by the \
         inductive step, got: {outcome:?}"
    );
}
