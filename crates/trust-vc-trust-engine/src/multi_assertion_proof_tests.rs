// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The same multi-assertion request must bind distinct certificates when the
//! feature exists and explicitly refuse its required policy when it does not.

use super::*;

fn multi_assertion_request() -> TrustVerificationRequest {
    let i32_sort = TrustSort::signed(32);
    let x = TrustExpr::variable("x", i32_sort.clone());
    let positive = TrustExpr::compare(
        TrustCompareOp::Gt,
        x.clone(),
        TrustExpr::int_literal(0, i32_sort.clone()),
    );
    let non_negative = TrustExpr::compare(
        TrustCompareOp::Ge,
        x.clone(),
        TrustExpr::int_literal(0, i32_sort.clone()),
    );
    let self_equal = TrustExpr::compare(TrustCompareOp::Eq, x.clone(), x);
    TrustVerificationRequest::new("unit-test")
        .for_full_verification()
        .require_replayable_proof_artifacts()
        .with_unit(
            TrustVerificationUnit::new("crate::proof")
                .with_variable(TrustVariable::new("x", i32_sort))
                .with_obligation(TrustObligation::requires_typed("pre", positive))
                .with_obligation(TrustObligation::ensures_typed(
                    "post.non_negative",
                    non_negative,
                ))
                .with_obligation(TrustObligation::ensures_typed(
                    "post.self_equal",
                    self_equal,
                )),
        )
}

#[cfg(feature = "proof-certificates")]
#[test]
fn multi_assertion_full_verification_binds_distinct_step_artifacts() {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let engine = TrustVcTrustEngine::new();
    let request = multi_assertion_request();

    let report = engine
        .verify(&request)
        .expect("each assertion should produce a replayable proof artifact");
    let unit = &report.units()[0];

    assert_eq!(unit.proof_artifacts().len(), 2);
    assert!(
        unit.proof_artifact().is_none(),
        "multi-assertion reports must not expose a misleading singleton artifact"
    );

    for assertion_id in ["post.non_negative", "post.self_equal"] {
        let evidence = unit
            .proof_evidence()
            .iter()
            .find(|evidence| evidence.obligation_id() == assertion_id)
            .expect("assertion evidence present");
        let artifact_id = evidence
            .proof_artifact_id()
            .expect("assertion evidence should bind to its own artifact");
        let artifact = unit
            .proof_artifacts()
            .iter()
            .find(|artifact| artifact.artifact_id() == artifact_id)
            .expect("bound artifact should be serialized in the unit report");

        assert_eq!(artifact.unit_id(), "crate::proof");
        assert_eq!(
            artifact.assertion_obligation_ids(),
            &[assertion_id.to_string()]
        );
        assert_eq!(artifact.assumption_obligation_ids(), &["pre".to_string()]);
        assert!(artifact.binding_fingerprint().starts_with("sha256:"));
        assert_eq!(
            evidence.proof_artifact_binding_fingerprint(),
            Some(artifact.binding_fingerprint())
        );
    }

    let coverage = unit
        .proof_artifact_coverage()
        .expect("multi-assertion artifact request should report coverage");
    assert_eq!(
        coverage.assertion_obligation_ids(),
        &[
            "post.non_negative".to_string(),
            "post.self_equal".to_string()
        ]
    );
    assert_eq!(
        coverage.covered_assertion_obligation_ids(),
        &[
            "post.non_negative".to_string(),
            "post.self_equal".to_string()
        ]
    );
    assert!(coverage.missing_assertion_obligation_ids().is_empty());
    assert_eq!(coverage.artifact_count(), 2);
    assert!(coverage.is_complete());

    let pre = unit
        .proof_evidence()
        .iter()
        .find(|evidence| evidence.obligation_id() == "pre")
        .expect("precondition evidence present");
    assert_eq!(pre.proof_artifact_id(), None);
    assert_eq!(pre.proof_artifact_binding_fingerprint(), None);
}

#[cfg(not(feature = "proof-certificates"))]
#[test]
fn multi_assertion_full_verification_requires_certificate_feature() {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let engine = TrustVcTrustEngine::new();
    let request = multi_assertion_request();

    let error = engine.verify(&request).expect_err(
        "multiple verified assertions cannot satisfy required certificates without the feature",
    );

    assert_eq!(
        error,
        TrustEngineError::ReplayableProofCertificateUnavailable {
            unit_id: "crate::proof".to_string(),
            policy: TrustProofPolicy::RequireReplayableCertificate,
            reason: "trust-vc-trust-engine was built without the proof-certificates feature",
        }
    );
}
