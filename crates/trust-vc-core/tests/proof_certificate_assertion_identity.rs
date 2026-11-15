// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Per-assertion proof certificates carry the identity of the goal they refute (#2654).
//!
//! The property under test is the one a per-assertion certificate is FOR:
//!
//! > if step `S` carries a proof certificate, that certificate is the solver's
//! > refutation of `NOT G_S`, where `G_S` is `S`'s own goal.
//!
//! Before #2654 the binding was positional — `record_proof_artifact` attached
//! whatever artifact arrived while a step was open, last writer winning. That is
//! correct for the single-solve path (one query per step) and WRONG for every
//! path that issues several queries under one step. `probe_conjunct_split_*`
//! below pins the measured instance: `try_verify_quantified_conjunction_split`
//! discharges `forall x. (C1 AND C2)` as two independent `forall x. Ck` queries,
//! and the parent step used to end up holding a refutation of one conjunct while
//! presenting it as the certificate for the whole universal.
//!
//! These tests do not assert verdicts. A verdict is the encoder's business; what
//! is pinned here is that no certificate outlives the goal it actually refutes.

#![cfg(feature = "proof-certificates")]

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::verification_report::{VerificationReport, VerificationReportOptions};

/// Every attached certificate must name the step it is attached to.
///
/// This is the whole invariant, checked over an entire report rather than at one
/// hand-picked step, so a new multi-query verification path cannot quietly
/// reintroduce positional binding.
fn assert_every_certificate_matches_its_step(report: &VerificationReport, context: &str) {
    for step in report.steps() {
        if let Some(proof) = step.proof() {
            assert!(
                proof.refutes_obligation(step.label()),
                "{context}: step {:?} carries a certificate that refutes {:?} — \
                 a certificate may only be attached to the goal it actually refutes (#2654)",
                step.label(),
                proof.refuted_obligation(),
            );
        }
    }
}

/// Ordinary path: N independent assertions, one solver query each.
///
/// This is the case that already worked, and it must keep working — the identity
/// check must not cost a genuine per-assertion certificate.
#[test]
fn independent_assertions_each_carry_their_own_refutation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_lower", "x >= 5"));
    ctx.push_obligation(ProofObligation::assume("x_upper", "x < 1000"));
    ctx.push_obligation(ProofObligation::assert("a_0", "x >= 0"));
    ctx.push_obligation(ProofObligation::assert("a_1", "x >= 1"));
    ctx.push_obligation(ProofObligation::assert("a_2", "x >= 2"));

    let report = ctx.verify_with_report(VerificationReportOptions::new());
    assert_every_certificate_matches_its_step(&report, "independent assertions");

    for label in ["a_0", "a_1", "a_2"] {
        let step = report
            .steps()
            .iter()
            .find(|step| step.label() == label)
            .unwrap_or_else(|| panic!("missing step for {label}"));
        let proof = step.proof().unwrap_or_else(|| {
            panic!(
                "{label}: a solver-decided assertion must keep its own certificate — \
                 the identity check must not cost a real refutation"
            )
        });
        assert_eq!(proof.refuted_obligation(), label);
    }

    // Distinct goals must produce distinct refutations. Identical Alethe text
    // across two assertions would mean one of them is carrying the other's
    // certificate, which is exactly the failure this file exists to catch.
    let alethe: Vec<&str> = ["a_0", "a_1", "a_2"]
        .iter()
        .map(|label| {
            report
                .steps()
                .iter()
                .find(|step| step.label() == *label)
                .and_then(|step| step.proof())
                .map(|proof| proof.alethe())
                .expect("certificate")
        })
        .collect();
    assert_ne!(alethe[0], alethe[1], "a_0 and a_1 share a certificate");
    assert_ne!(alethe[1], alethe[2], "a_1 and a_2 share a certificate");
}

/// A conjunct split runs several queries under ONE step. The parent must not
/// inherit a sub-query's refutation.
///
/// `try_verify_quantified_conjunction_split` fires on a triggerless
/// `forall|i| (C1 AND C2)` whose body contains a nested quantifier, and verifies
/// `forall|i| C1` and `forall|i| C2` separately. Whichever sub-query the solver
/// refutes last used to become the parent's certificate.
#[test]
fn conjunct_split_does_not_hand_the_parent_a_sub_query_certificate() {
    for (name, condition) in [
        (
            "qsplit_exists_first",
            "forall|i: int| (exists|j: int| j > i) && (i < 100 ==> i < 200)",
        ),
        (
            "qsplit_exists_last",
            "forall|i: int| (i < 100 ==> i < 200) && (exists|j: int| j > i)",
        ),
    ] {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(ProofObligation::assert(name, condition));
        let report = ctx.verify_with_report(VerificationReportOptions::new());

        assert_every_certificate_matches_its_step(&report, name);

        let step = report
            .steps()
            .iter()
            .find(|step| step.label() == name)
            .unwrap_or_else(|| panic!("{name}: missing parent step"));

        // The sub-queries are named "<parent> [forall conjunct k of n]". If a
        // certificate is present at all it must be the parent's own; a
        // sub-query's refutation is evidence for one conjunct, never for the
        // conjunction.
        if let Some(proof) = step.proof() {
            assert_eq!(
                proof.refuted_obligation(),
                name,
                "{name}: the parent step is carrying a sub-query's refutation"
            );
        }
    }
}

/// An assertion the solver never saw has no refutation, and must carry no
/// certificate.
///
/// A literal-`true` predicate is const-folded to `Verified` before any scope is
/// pushed (`encoder::verification::solve`), so there is no UNSAT core to
/// extract. Nothing may be minted here: an obligation whose proposition is
/// `true` was not proved by anyone, and a certificate for it would be a claim
/// about a refutation that does not exist.
#[test]
fn const_folded_assertion_carries_no_certificate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_lower", "x >= 5"));
    ctx.push_obligation(ProofObligation::assert("trivial", "true"));
    ctx.push_obligation(ProofObligation::assert("solved", "x >= 1"));

    let report = ctx.verify_with_report(VerificationReportOptions::new());
    assert_every_certificate_matches_its_step(&report, "const-folded");

    let trivial = report
        .steps()
        .iter()
        .find(|step| step.label() == "trivial")
        .expect("missing trivial step");
    assert!(
        trivial.proof().is_none(),
        "a const-folded assertion reached no solver, so it has no refutation to certify"
    );

    let solved = report
        .steps()
        .iter()
        .find(|step| step.label() == "solved")
        .expect("missing solved step");
    assert!(
        solved
            .proof()
            .is_some_and(|p| p.refutes_obligation("solved")),
        "the neighbouring solver-decided assertion must still carry its own refutation"
    );
}
