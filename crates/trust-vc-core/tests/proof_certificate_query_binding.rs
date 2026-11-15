// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A proof certificate is evidence for an obligation only when its `assume`
//! premises are clauses of the query trust-vc posed for that obligation.
//!
//! For `x <= 1000, y <= 1000, ret == x * y ⊢ ret == x * y` the negated goal
//! folds to the constant `false` while the query is built, and the
//! certificate is
//!
//! ```text
//! (assume t0 false)
//! (step t1 (cl (not false)) :rule false)
//! (step t2 (cl) :rule resolution :premises (t0 t1))
//! ```
//!
//! That `false` is the term trust-vc asserted for the negated goal, so the
//! certificate refutes the posed query. What it shows about the obligation
//! rests on AY's term-builder rewrite, as every certificate's evidence rests
//! on the builder's rewrites. It keeps its claims and discloses the collapse
//! (`query_collapsed`). Withholding them refused true obligations under the
//! release policy and added no soundness: a `false` premise binds only when
//! trust-vc itself asserted it.
//!
//! The verdict is not the subject: the goals are true and stay `Verified`.

#![cfg(feature = "proof-certificates")]

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::verification_report::{
    StepDiagnostic, StepResultKind, VerificationReport, VerificationReportOptions,
};

fn report(assumes: &[(&str, &str)], asserts: &[(&str, &str)]) -> VerificationReport {
    let mut ctx = VerificationContext::new();
    for v in ["x", "y", "ret"] {
        ctx.declare_var_typed(v, TrustVcType::Int { width: 32 });
    }
    ctx.declare_var_typed("p", TrustVcType::Bool);
    ctx.declare_var_typed("q", TrustVcType::Bool);
    for (name, expr) in assumes {
        ctx.push_obligation(ProofObligation::assume(*name, *expr));
    }
    for (name, expr) in asserts {
        ctx.push_obligation(ProofObligation::assert(*name, *expr));
    }
    ctx.verify_with_report(VerificationReportOptions::new())
}

fn verified_step<'r>(report: &'r VerificationReport, label: &str) -> &'r StepDiagnostic {
    let step = report
        .steps()
        .iter()
        .find(|step| step.label() == label)
        .unwrap_or_else(|| panic!("missing step {label}"));
    assert_eq!(
        step.result(),
        StepResultKind::Verified,
        "{label} must still verify: the fix changes claims, never verdicts"
    );
    step
}

/// The measured shape: the refutation of the collapsed query keeps its claims
/// and discloses the collapse.
#[test]
fn collapsed_query_certificate_keeps_its_claims_and_discloses_the_collapse() {
    let report = report(
        &[
            ("x_le", "x <= 1000"),
            ("y_le", "y <= 1000"),
            ("ret_def", "ret == x * y"),
        ],
        &[("post", "ret == x * y")],
    );
    let proof = verified_step(&report, "post")
        .proof()
        .expect("the solver still produces its refutation");
    assert!(
        proof.alethe().contains("(assume t0 false)"),
        "fixture drift: the query no longer collapses to `false`:\n{}",
        proof.alethe()
    );
    assert!(proof.query_collapsed(), "{proof:?}");
    assert!(
        proof.premises_bound(),
        "{:?}",
        proof.premise_binding_defect()
    );
    assert!(proof.strict_verified(), "{proof:?}");
    assert!(proof.kernel_verified(), "{proof:?}");
    assert!(proof.clean_supported(), "{proof:?}");
}

/// The same collapse with no background at all: the only premise is `false`.
#[test]
fn collapsed_query_without_background_keeps_its_claims() {
    let report = report(&[], &[("refl", "x * y == x * y")]);
    let proof = verified_step(&report, "refl")
        .proof()
        .expect("the solver still produces its refutation");
    assert!(
        proof.alethe().contains("(assume t0 false)"),
        "fixture drift: the query no longer collapses to `false`:\n{}",
        proof.alethe()
    );
    assert!(proof.query_collapsed(), "{proof:?}");
    assert!(proof.strict_verified(), "{proof:?}");
    assert!(proof.kernel_verified(), "{proof:?}");
}

/// Control: a genuine propositional refutation keeps both claims.
#[test]
fn genuine_propositional_certificate_keeps_its_claims() {
    let report = report(&[("pq", "p && q")], &[("g", "p")]);
    let proof = verified_step(&report, "g").proof().expect("certificate");
    assert!(
        !proof.alethe().contains("(assume t0 false)"),
        "{}",
        proof.alethe()
    );
    assert!(!proof.query_collapsed(), "{proof:?}");
    assert_eq!(proof.assumed_lemma_premises(), 0, "{proof:?}");
    assert!(proof.strict_verified(), "{proof:?}");
    assert!(proof.kernel_verified(), "{proof:?}");
}

/// Control: a genuine arithmetic refutation keeps both claims. Its theory
/// lemmas are checked by AY's strict checker and taken as given by the kernel.
#[test]
fn genuine_arithmetic_certificate_keeps_its_claims() {
    let report = report(&[("x_lower", "x >= 5")], &[("a_0", "x >= 0")]);
    let proof = verified_step(&report, "a_0").proof().expect("certificate");
    assert!(
        !proof.alethe().contains("(assume t0 false)"),
        "{}",
        proof.alethe()
    );
    assert!(proof.strict_verified(), "{proof:?}");
    assert!(proof.kernel_verified(), "{proof:?}");
}

// ----- the same certificates through the binding accessors -----

/// The collapsed certificate is bound to the posed query and its derivation
/// is fully checked: the refutation of `false` needs nothing on trust.
#[test]
fn collapsed_query_certificate_is_bound_and_fully_checked() {
    let report = report(&[("x_le", "x <= 1000")], &[("post", "x * y == x * y")]);
    let proof = verified_step(&report, "post").proof().expect("certificate");
    assert!(proof.query_collapsed(), "{proof:?}");
    assert!(proof.derivation_strict_verified(), "{proof:?}");
    assert!(proof.kernel_skeleton_accepted(), "{proof:?}");
    assert_eq!(proof.premise_binding_defect(), None, "{proof:?}");
    assert!(proof.kernel_fully_checked(), "{proof:?}");
}

/// Refuted twin of the collapse fixture: one line differs, the goal is false,
/// and there is no certificate to grade.
#[test]
fn collapse_fixture_refuted_twin_has_no_certificate() {
    let report = report(
        &[
            ("x_le", "x <= 1000"),
            ("y_le", "y <= 1000"),
            ("ret_def", "ret == x * y"),
        ],
        &[("post", "ret == x * y + 1")],
    );
    let step = report
        .steps()
        .iter()
        .find(|step| step.label() == "post")
        .expect("post step");
    assert_ne!(step.result(), StepResultKind::Verified, "{step:?}");
    assert!(step.proof().is_none(), "{step:?}");
}

/// A propositional refutation is checked end to end: the bridge derives its
/// Tseitin clauses itself, so the kernel takes nothing on trust.
#[test]
fn propositional_certificate_is_fully_kernel_checked() {
    let report = report(&[("pq", "p && q")], &[("g", "p")]);
    let proof = verified_step(&report, "g").proof().expect("certificate");
    assert!(
        proof.premises_bound(),
        "{:?}",
        proof.premise_binding_defect()
    );
    assert_eq!(proof.kernel_trusted_steps(), 0, "{}", proof.alethe());
    assert!(proof.kernel_fully_checked(), "{proof:?}");
}

/// An arithmetic refutation is bound and kernel-replayed, but its theory
/// lemmas are taken as given by the kernel: counted, so the end-to-end claim
/// is withheld while `kernel_verified` stands.
#[test]
fn arithmetic_certificate_discloses_its_trusted_theory_lemmas() {
    let report = report(&[("x_lower", "x >= 5")], &[("a_0", "x >= 0")]);
    let proof = verified_step(&report, "a_0").proof().expect("certificate");
    assert!(
        proof.premises_bound(),
        "{:?}",
        proof.premise_binding_defect()
    );
    assert!(proof.kernel_verified(), "{proof:?}");
    assert!(proof.kernel_trusted_steps() > 0, "{proof:?}");
    assert!(!proof.kernel_fully_checked(), "{proof:?}");
}

// ----- predicates trust-vc proved separately and then assumed -----

fn exec_report(goal: &str) -> VerificationReport {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.enable_overflow_checks();
    ctx.push_obligation(ProofObligation::assume("x_lo", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("x_hi", "x < 100"));
    ctx.push_obligation(ProofObligation::assert("inc", goal));
    ctx.verify_with_report(VerificationReportOptions::new())
}

/// Exec arithmetic: the no-overflow predicate of `x + 1` is proved by a
/// separate solve, which records no certificate, and then assumed in the
/// goal's query. The certificate refutes that posed query and counts the
/// premise, so a reader sees what it does not cover.
#[test]
fn assumed_overflow_predicates_are_counted() {
    let report = exec_report("x + 1 > x");
    let proof = verified_step(&report, "inc").proof().expect("certificate");
    assert!(
        proof.premises_bound(),
        "{:?}",
        proof.premise_binding_defect()
    );
    assert!(
        proof.assumed_lemma_premises() > 0,
        "fixture drift: the refutation no longer uses the assumed no-overflow \
         predicate:\n{}",
        proof.alethe()
    );
}

/// Refuted twin: one line differs, the goal is false, no certificate.
#[test]
fn assumed_overflow_fixture_refuted_twin_has_no_certificate() {
    let report = exec_report("x + 1 < x");
    let step = report
        .steps()
        .iter()
        .find(|step| step.label() == "inc")
        .expect("inc step");
    assert_ne!(step.result(), StepResultKind::Verified, "{step:?}");
    assert!(step.proof().is_none(), "{step:?}");
}
