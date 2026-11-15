// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Advisory metadata does not establish a hard assertion.
use super::{increment_context, result_and_old_tautology};
use trust_vc_trust_engine::{
    TrustAssuranceLevel, TrustExpr, TrustObligationKind, TrustOutcome, TrustProofEvidenceProfile,
    TrustProofLineage, TrustSourceSpan, TrustTrustIrAdapterRequest, TrustTrustIrObligation,
    TrustTrustIrObligationKind, TrustTrustIrProofUnit, TrustVcTrustEngine,
};

#[test]
fn trust_ir_adapter_preserves_recommends_as_soft_contract_obligation() {
    let engine = TrustVcTrustEngine::new();
    let soft_unit = TrustTrustIrProofUnit::new("crate::increment", increment_context())
        .with_obligation(
            TrustTrustIrObligation::expr(
                "recommends.false_soft",
                TrustTrustIrObligationKind::Recommends,
                TrustExpr::bool_literal(false),
                TrustProofLineage::trust_types_contract("trust-types-json-v1", "recommends-clause")
                    .with_input_digest("sha256:recommends"),
            )
            .with_span(TrustSourceSpan::new("src/lib.rs", 4, 5, 4, 42)),
        );
    let metadata_only =
        TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(soft_unit.clone());
    let metadata_report = engine
        .verify_trust_ir_adapter_request(&metadata_only)
        .expect("an advisory-only request should return a non-proof report");
    assert!(
        matches!(metadata_report.units()[0].outcome(), TrustOutcome::Error { message }
            if message == "Cannot verify empty context: no obligations to check"),
        "advisory metadata alone is not a verified assertion: {:?}",
        metadata_report.units()[0].outcome()
    );
    assert!(metadata_report.units()[0].proof_evidence().is_empty());

    // A real assertion is needed to exercise warning-only metadata alongside
    // verification. The false recommendation is never a hard hypothesis.
    let with_assertion = |predicate| {
        TrustTrustIrAdapterRequest::new("crate-under-test").with_unit(
            soft_unit
                .clone()
                .with_obligation(TrustTrustIrObligation::expr(
                    "ensures.actual",
                    TrustTrustIrObligationKind::Ensures,
                    predicate,
                    TrustProofLineage::trust_types_contract(
                        "trust-types-json-v1",
                        "ensures-clause",
                    )
                    .with_input_digest("sha256:ensures"),
                )),
        )
    };
    let request = with_assertion(result_and_old_tautology());

    engine
        .validate_trust_ir_adapter_request(&request)
        .expect("typed recommends TrustIr request should pass validation");
    let lowered = engine
        .lower_trust_ir_adapter_request(&request)
        .expect("typed recommends TrustIr request should lower");

    assert_eq!(
        lowered.units()[0].obligations()[0].kind(),
        &TrustObligationKind::Recommends
    );

    let report = engine
        .verify_trust_ir_adapter_request(&request)
        .expect("a true assertion should verify despite a false warning-only recommendation");
    assert!(matches!(
        report.units()[0].outcome(),
        TrustOutcome::Verified
    ));
    let evidence = &report.units()[0].proof_evidence()[0];
    assert_eq!(
        evidence.evidence_profile(),
        TrustProofEvidenceProfile::TypedContractFrame
    );
    assert_eq!(
        evidence.assurance_level(),
        TrustAssuranceLevel::MetadataOnly
    );
    let lineage = evidence
        .proof_lineage()
        .expect("report evidence should preserve recommends proof lineage");
    assert_eq!(lineage.rule(), "recommends-clause");
    assert_eq!(lineage.input_digest(), Some("sha256:recommends"));
    assert_eq!(report.units()[0].proof_evidence().len(), 2);
    assert_eq!(
        report.units()[0].proof_evidence()[1].assurance_level(),
        TrustAssuranceLevel::StaticProof
    );
    let false_assertion = engine
        .verify_trust_ir_adapter_request(&with_assertion(TrustExpr::bool_literal(false)))
        .expect("a false assertion should return its actual failed verdict");
    assert!(matches!(
        false_assertion.units()[0].outcome(),
        TrustOutcome::Refuted { .. }
    ));
    assert!(false_assertion.units()[0].proof_evidence().is_empty());
}
