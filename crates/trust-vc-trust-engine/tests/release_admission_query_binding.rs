// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Release admission rests on a certificate that refutes the obligation's own
//! query.
//!
//! `mul(x, y) = x * y` with `requires x <= 1000 && y <= 1000` and
//! `ensures ret == x * y`, `ret` bound to `x * y`: the ensures' negated goal
//! folds to `false` while the query is built, and its certificate is
//! `(assume t0 false) (step t1 (cl (not false)) :rule false) (step t2 (cl) ...)`.
//! That `false` is the term trust-vc asserted, so the certificate refutes the
//! posed query; its evidence for the obligation is AY's term-builder rewrite,
//! trusted as every builder rewrite is. It is release-admissible and discloses
//! the collapse (`query_collapsed`). Refusing it declined true obligations in
//! every lane that requires a release-admissible certificate, among them
//! tRust's own TMIR adapter fixture, and a whole request with them.

#![cfg(feature = "proof-certificates")]

use trust_vc_trust_engine::{
    TrustArithOp, TrustCompareOp, TrustExpr, TrustLogicOp, TrustObligation, TrustOutcome,
    TrustProofPolicy, TrustReleaseProofAdmissionStatus, TrustSort, TrustTrustIrAdapterRequest,
    TrustVariable, TrustVcTrustEngine, TrustVerificationRequest, TrustVerificationUnit,
    TrustVerifier,
};

fn int() -> TrustSort {
    TrustSort::signed(64)
}

fn var(name: &str) -> TrustExpr {
    TrustExpr::variable(name, int())
}

fn lit(value: i128) -> TrustExpr {
    TrustExpr::int_literal(value, int())
}

fn unit_body(name: &str, ensures: TrustExpr) -> TrustVerificationUnit {
    TrustVerificationUnit::new(name)
        .with_variable(TrustVariable::new("x", int()))
        .with_variable(TrustVariable::new("y", int()))
        .with_obligation(TrustObligation::requires_typed(
            "req",
            TrustExpr::logic(
                TrustLogicOp::And,
                TrustExpr::compare(TrustCompareOp::Le, var("x"), lit(1000)),
                TrustExpr::compare(TrustCompareOp::Le, var("y"), lit(1000)),
            ),
        ))
        .with_obligation(TrustObligation::ensures_typed("ens", ensures))
}

fn unit(name: &str, ensures: TrustExpr, policy: TrustProofPolicy) -> TrustVerificationRequest {
    TrustVerificationRequest::new("query-binding")
        .for_full_verification()
        .with_proof_policy(policy)
        .with_unit(unit_body(name, ensures))
}

/// `x * y == x * y`: the body substituted into `ret == x * y`.
fn collapsing_ensures() -> TrustExpr {
    let product = || TrustExpr::arith(TrustArithOp::Mul, var("x"), var("y"), int());
    TrustExpr::compare(TrustCompareOp::Eq, product(), product())
}

/// `x <= 2000`: follows from `requires`, and does not fold while built.
fn genuine_ensures() -> TrustExpr {
    TrustExpr::compare(TrustCompareOp::Le, var("x"), lit(2000))
}

#[test]
fn collapsed_query_certificate_is_release_admissible_and_disclosed() {
    let engine = TrustVcTrustEngine::new();

    let report = engine
        .verify(&unit(
            "demo::mul",
            collapsing_ensures(),
            TrustProofPolicy::AttachReplayableCertificates,
        ))
        .expect("the attach policy never fails a verified unit");
    let unit_report = &report.units()[0];
    assert!(
        matches!(unit_report.outcome(), TrustOutcome::Verified),
        "{unit_report:#?}"
    );
    let collapsed: Vec<_> = unit_report
        .proof_artifacts()
        .iter()
        .filter(|artifact| artifact.payload().contains("(assume t0 false)"))
        .collect();
    assert!(
        !collapsed.is_empty(),
        "fixture drift: the ensures no longer collapses to `false`: {unit_report:#?}"
    );
    for artifact in collapsed {
        assert!(artifact.query_collapsed(), "{artifact:#?}");
        assert!(
            artifact.strict_verified()
                && artifact.kernel_verified()
                && artifact.release_admission().status()
                    == TrustReleaseProofAdmissionStatus::Admissible,
            "a refutation of the posed query lost its claims: {artifact:#?}"
        );
    }

    let report = engine
        .verify(&unit(
            "demo::mul",
            collapsing_ensures(),
            TrustProofPolicy::RequireReleaseAdmissibleCertificate,
        ))
        .expect("the release lane admits the refutation of the posed query");
    assert!(
        matches!(report.units()[0].outcome(), TrustOutcome::Verified),
        "{report:#?}"
    );
}

/// One request, one genuine unit and one collapsed unit, under the release
/// policy: both verify. A unit the policy declines fails the whole request,
/// so refusing the collapsed unit dropped the genuine unit's verdict too.
#[test]
fn a_collapsed_unit_does_not_sink_its_request() {
    let request = TrustVerificationRequest::new("query-binding-batch")
        .for_full_verification()
        .with_proof_policy(TrustProofPolicy::RequireReleaseAdmissibleCertificate)
        .with_unit(unit_body("demo::bound", genuine_ensures()))
        .with_unit(unit_body("demo::mul", collapsing_ensures()));
    let report = TrustVcTrustEngine::new()
        .verify(&request)
        .expect("both units carry release-admissible certificates");
    assert_eq!(report.units().len(), 2);
    for unit_report in report.units() {
        assert!(
            matches!(unit_report.outcome(), TrustOutcome::Verified),
            "{unit_report:#?}"
        );
    }
}

/// `x <= 999`: one bound off, refuted by `x = 1000` under the same `requires`.
fn refuted_ensures() -> TrustExpr {
    TrustExpr::compare(TrustCompareOp::Le, var("x"), lit(999))
}

/// Refuted twin of the genuine control: one bound differs, the ensures is
/// false, and no certificate is minted for it.
#[test]
fn genuine_control_refuted_twin_has_no_certificate() {
    let report = TrustVcTrustEngine::new()
        .verify(&unit(
            "demo::bound",
            refuted_ensures(),
            TrustProofPolicy::AttachReplayableCertificates,
        ))
        .expect("a refuted unit is a report, not an engine error");
    let unit_report = &report.units()[0];
    assert!(
        matches!(unit_report.outcome(), TrustOutcome::Refuted { .. }),
        "{unit_report:#?}"
    );
    assert!(unit_report.proof_artifacts().is_empty(), "{unit_report:#?}");
}

/// Control: a genuine refutation under the same `requires` stays
/// release-admissible, so the binding does not refuse good certificates.
#[test]
fn genuine_certificate_stays_release_admissible() {
    let engine = TrustVcTrustEngine::new();
    let report = engine
        .verify(&unit(
            "demo::bound",
            genuine_ensures(),
            TrustProofPolicy::RequireReleaseAdmissibleCertificate,
        ))
        .expect("a genuine refutation is release-admissible");
    let unit_report = &report.units()[0];
    assert!(
        matches!(unit_report.outcome(), TrustOutcome::Verified),
        "{unit_report:#?}"
    );
    let artifacts = unit_report.proof_artifacts();
    assert!(!artifacts.is_empty(), "{unit_report:#?}");
    for artifact in artifacts {
        assert!(
            !artifact.payload().contains("(assume t0 false)"),
            "{artifact:#?}"
        );
        assert!(artifact.strict_verified(), "{artifact:#?}");
        assert!(artifact.kernel_verified(), "{artifact:#?}");
        assert_eq!(
            artifact.release_admission().status(),
            TrustReleaseProofAdmissionStatus::Admissible,
            "{artifact:#?}"
        );
    }
}

const TRUST_INCREMENT_CONTRACT_CFG_TRUST_IR_ADAPTER_GOLDEN: &str = include_str!(
    "../fixtures/trust_ir_adapter/trust_increment_contract_cfg_trust_ir_adapter_golden.json"
);

/// tRust's native TMIR adapter fixture under the policy tRust's bridge uses
/// for every local engine run. `ensures.old_result_reflexive` and
/// `trust_ir.cfg.entry_to_return` fold to `false` while built; every
/// assertion still carries a release-admissible certificate.
#[test]
fn trust_native_adapter_fixture_is_release_admissible() {
    let request: TrustTrustIrAdapterRequest =
        serde_json::from_str(TRUST_INCREMENT_CONTRACT_CFG_TRUST_IR_ADAPTER_GOLDEN)
            .expect("checked-in tRust native adapter fixture should decode");
    let request = request.with_proof_policy(TrustProofPolicy::RequireReleaseAdmissibleCertificate);
    let report = TrustVcTrustEngine::new()
        .verify_trust_ir_adapter_request(&request)
        .expect("the release lane verifies tRust's adapter fixture");
    let unit = &report.units()[0];
    assert!(
        matches!(unit.outcome(), TrustOutcome::Verified),
        "{unit:#?}"
    );
    assert!(!unit.proof_artifacts().is_empty(), "{unit:#?}");
    for artifact in unit.proof_artifacts() {
        assert_eq!(
            artifact.release_admission().status(),
            TrustReleaseProofAdmissionStatus::Admissible,
            "{artifact:#?}"
        );
    }
    assert!(
        unit.proof_artifacts()
            .iter()
            .any(|artifact| artifact.query_collapsed()),
        "fixture drift: no assertion of the fixture collapses any more: {unit:#?}"
    );
}
