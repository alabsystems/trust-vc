// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The wire is not evidence. An admission is a judgement against the bundle a
//! certificate cites; a serialized evidence item, report or proof artifact does
//! not carry that bundle, so decoding re-derives what its own fields support and
//! never reads the verdict it states. Each case below was measured admitting at
//! 806b8d3a. The decoded payloads start from a report the engine genuinely
//! admitted.

use trust_ir::request::NativeVerificationBundle;
use trust_ir::ProofEvidence;
use trust_vc_trust_engine::{
    TrustVcNativeArtifactAdmission, TrustVcNativeArtifactExpectation,
    TrustVcNativeArtifactRejection, TrustVcNativeProofArtifact, TrustVcNativeTrustIrBundleReport,
    TrustVcNativeTrustIrCertificateAdmission, TrustVcNativeTrustIrCertificateEvidence,
    TrustVcNativeTrustIrCertificateRejection, TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
};

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/admission_edits.rs"]
mod admission_edits;
use admission_baseline::{add_sibling_certificate, cite_certificates, native_bundle_fixture};
use admission_edits::forge_atom_id;

/// The baseline with the TrustVc request citing an SMT sibling of the
/// kernel-replayed CleanCic certificate instead: a certificate whose coverage
/// is NOT established (basis K is per certificate), so it is rejected
/// `CertificateCoverageBasisNotThisCertificate`.
fn sibling_cited_bundle() -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    let sibling = add_sibling_certificate(
        &mut bundle,
        "trust_vc-smt",
        ProofEvidence::SmtProof(b"(proof)".to_vec()),
        None,
    );
    cite_certificates(&mut bundle, vec![sibling]);
    bundle
}

/// Serialize `value`, apply `edit` to its JSON, and decode the result as `T`.
fn reencoded<T: serde::de::DeserializeOwned>(
    value: &impl serde::Serialize,
    edit: impl FnOnce(&mut serde_json::Value),
) -> Result<T, serde_json::Error> {
    let mut json = serde_json::to_value(value).expect("serializes");
    edit(&mut json);
    serde_json::from_value(json)
}

/// A certificate whose coverage is NOT established: an SMT certificate cited
/// beside its kernel-replayed CleanCic sibling (`sibling_cited_bundle`).
fn undetermined_evidence() -> TrustVcNativeTrustIrCertificateEvidence {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&sibling_cited_bundle())
        .expect("valid upstream");
    let evidence = report.requests()[0].proof_evidence()[0].clone();
    assert_eq!(
        evidence.release_admission().rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::CertificateCoverageBasisNotThisCertificate]
    );
    evidence
}

/// The baseline's report, genuinely ADMITTED: its kernel-replayed CleanCic
/// certificate has its coverage established and its assertion id published.
fn established_report() -> TrustVcNativeTrustIrBundleReport {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&native_bundle_fixture())
        .expect("baseline is consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert!(evidence.release_admission().coverage_established());
    assert!(evidence.release_admission().is_admissible());
    assert!(evidence
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
    report
}

/// The strongest honest evidence: admitted, coverage established.
fn established_evidence() -> TrustVcNativeTrustIrCertificateEvidence {
    established_report().requests()[0].proof_evidence()[0].clone()
}

/// MEASURED: an `Undetermined` certificate's evidence, edited to
/// `status: admissible, coverage_established: true`, decoded as admissible and
/// its artifact was ACCEPTED.
#[test]
fn an_edited_evidence_payload_cannot_admit_undetermined_coverage() {
    let forged: TrustVcNativeTrustIrCertificateEvidence =
        reencoded(&undetermined_evidence(), |json| {
            json["release_admission"] = serde_json::json!({
                "status": "admissible",
                "coverage_established": true,
            });
        })
        .expect("the payload decodes");
    assert!(!forged.release_admission().is_admissible());
    assert!(!forged.release_admission().coverage_established());
    let artifact = forged.admit_native_proof_artifact();
    assert!(
        !artifact.admission().is_accepted(),
        "a forged admission must not yield an accepted artifact: {:?}",
        artifact.admission()
    );
    // The coverage the wire cannot carry.
    assert_eq!(
        artifact.admission().rejection_reasons(),
        &[TrustVcNativeArtifactRejection::CertificateCoverageNotJudged]
    );

    // Nor does an honest payload whose coverage WAS established keep it once
    // decoded: coverage is not on the wire. The identity checks are re-derived
    // and refuse what they refused before.
    let honest: TrustVcNativeTrustIrCertificateEvidence =
        reencoded(&established_evidence(), |_| {}).expect("the payload decodes");
    assert!(!honest.release_admission().is_admissible());
    assert!(!honest.release_admission().coverage_established());
    assert_eq!(
        format!("{:?}", honest.release_admission().rejection_reasons()),
        "[CertificateCoverageNotJudged]"
    );
    assert!(!honest
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());

    // And a bare admission payload is never admissible either.
    let bare: TrustVcNativeTrustIrCertificateAdmission = serde_json::from_value(
        serde_json::json!({"status": "admissible", "coverage_established": true}),
    )
    .expect("decodes");
    assert!(!bare.is_admissible());
    assert!(!bare.coverage_established());
}

/// MEASURED: a report whose evidence predates `coverage_established` (the
/// field removed) decoded as `CertificatesAdmitted`. A certificate-mode verdict
/// is re-derived from the decoded admissions, so no decoded report with a
/// certificate declares a pass — not even the serialization of a report the
/// engine genuinely admitted; one declaring the rejection it re-derives to
/// still decodes, and yields no accepted artifact.
#[test]
fn a_decoded_report_never_declares_its_certificates_admitted() {
    let report = established_report();
    let declared = serde_json::to_value(&report).expect("the admitted report serializes");
    assert_eq!(declared["verdict"], "certificates_admitted");
    let strip_coverage = |json: &mut serde_json::Value| {
        for request in json["requests"].as_array_mut().expect("requests") {
            for evidence in request["proof_evidence"].as_array_mut().expect("evidence") {
                evidence["release_admission"]
                    .as_object_mut()
                    .expect("release admission is an object")
                    .remove("coverage_established");
            }
        }
    };
    let predating = reencoded::<TrustVcNativeTrustIrBundleReport>(&declared, strip_coverage);
    let error = match predating {
        Ok(decoded) => panic!(
            "a pre-field report must not decode as {:?}",
            decoded.verdict()
        ),
        Err(error) => error.to_string(),
    };
    assert!(error.contains("re-derived on decode"), "{error}");

    // The genuine admission, with every field present, is refused the same
    // way: its coverage was judged against a bundle the wire does not carry.
    reencoded::<TrustVcNativeTrustIrBundleReport>(&declared, |_| {})
        .expect_err("a report declaring admission cannot be re-admitted from the wire");

    // Declaring the verdict it re-derives to, it decodes — and admits nothing.
    let rejected = reencoded::<TrustVcNativeTrustIrBundleReport>(&report, |json| {
        for request in json["requests"].as_array_mut().expect("requests") {
            request["verdict"] = serde_json::json!("certificates_rejected");
        }
        json["verdict"] = serde_json::json!("certificates_rejected");
    })
    .expect("a report declaring the rejection it re-derives to decodes");
    assert_eq!(
        rejected.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );
    assert!(rejected
        .admit_native_proof_artifacts()
        .iter()
        .all(|artifact| !artifact.admission().is_accepted()));
}

/// MEASURED: a serialized proof artifact carried its admission verbatim — a
/// coverage-refused artifact edited to `accepted` decoded as accepted.
#[test]
fn a_serialized_proof_artifact_is_re_derived_not_believed() {
    let refused = undetermined_evidence().admit_native_proof_artifact();
    assert!(!refused.admission().is_accepted());
    let forged: TrustVcNativeProofArtifact = reencoded(&refused, |json| {
        json["admission"] = serde_json::json!({
            "replay_status": "replayable",
            "status": "accepted",
            "rejection_reasons": [],
        });
    })
    .expect("the payload decodes");
    assert!(
        !forged.admission().is_accepted(),
        "a forged admission must not decode as accepted: {:?}",
        forged.admission()
    );

    // An honest ACCEPTED artifact decodes to its re-derived self: the binding
    // is intact, the coverage is not judged, and so the fingerprint moves — an
    // expectation pinned to the original refuses it.
    let established = established_evidence().admit_native_proof_artifact();
    assert!(established.admission().is_accepted(), "{established:?}");
    assert!(!established
        .admission()
        .rejection_reasons()
        .contains(&TrustVcNativeArtifactRejection::CertificateCoverageNotJudged));
    let decoded: TrustVcNativeProofArtifact =
        reencoded(&established, |_| {}).expect("the payload decodes");
    assert!(!decoded.admission().is_accepted());
    assert!(decoded
        .admission()
        .rejection_reasons()
        .contains(&TrustVcNativeArtifactRejection::CertificateCoverageNotJudged));
    assert_eq!(
        decoded.certificate_digest(),
        established.certificate_digest()
    );
    let expectation = TrustVcNativeArtifactExpectation::new(
        established.assertion_id(),
        established.trust_ir_obligation_id(),
    )
    .with_artifact_fingerprint(established.artifact_fingerprint());
    assert!(decoded
        .admission_against(&expectation)
        .rejection_reasons()
        .contains(&TrustVcNativeArtifactRejection::ArtifactFingerprintMismatch));
}

/// MEASURED: `artifact_fingerprint` did not bind coverage — an artifact whose
/// coverage was never judged had the SAME fingerprint as the accepted one.
#[test]
fn the_artifact_fingerprint_binds_the_coverage_judgement() {
    let evidence = established_evidence();
    let established = evidence.admit_native_proof_artifact();
    assert!(!established
        .admission()
        .rejection_reasons()
        .contains(&TrustVcNativeArtifactRejection::CertificateCoverageNotJudged));
    let not_judged = reencoded::<TrustVcNativeTrustIrCertificateEvidence>(&evidence, |json| {
        json["release_admission"]
            .as_object_mut()
            .expect("release admission is an object")
            .remove("coverage_established");
    })
    .expect("the payload decodes")
    .admit_native_proof_artifact();
    assert!(not_judged
        .admission()
        .rejection_reasons()
        .contains(&TrustVcNativeArtifactRejection::CertificateCoverageNotJudged));
    assert_ne!(
        established.artifact_fingerprint(),
        not_judged.artifact_fingerprint(),
        "two proof objects whose admissions differ must not share a fingerprint"
    );
}

/// A proof artifact serialized under an older schema carried an admission and
/// a fingerprint the current rule cannot vouch for; it is refused as stale.
/// v7 is the schema whose fingerprint bound a coverage judgement made by the
/// retired row rule (no basis); v6 bound none.
#[test]
fn a_pre_v8_proof_artifact_is_refused_as_stale() {
    let artifact = established_evidence().admit_native_proof_artifact();
    assert_eq!(artifact.schema_version(), 8);
    // The current schema decodes (to its re-derived, not-judged self).
    let current =
        reencoded::<TrustVcNativeProofArtifact>(&artifact, |_| {}).expect("a v8 artifact decodes");
    assert_eq!(current.schema_version(), 8);
    for stale in [7, 6] {
        let error = reencoded::<TrustVcNativeProofArtifact>(&artifact, |json| {
            json["schema_version"] = serde_json::json!(stale);
        })
        .expect_err("a pre-v8 artifact must not decode");
        assert!(error.to_string().contains("stale"), "v{stale}: {error}");
        assert!(error.to_string().contains(&format!("v{stale}")), "{error}");
    }

    // A bare artifact admission payload is never accepted either.
    let admission: TrustVcNativeArtifactAdmission = serde_json::from_value(serde_json::json!({
        "replay_status": "replayable",
        "status": "accepted",
    }))
    .expect("decodes");
    assert!(!admission.is_accepted());
}

/// MEASURED at 8bbef1af: a REJECTED bundle report (its only certificate's
/// coverage is not established), edited on the wire so every request's
/// `proof_evidence` is `[]` and every verdict `certificates_admitted`, decoded
/// as `CertificatesAdmitted` with `is_ok() == true` — the decoder folded
/// "every certificate admissible" over an empty list, and the report did not
/// say which obligations its evidence had to cover. It now does
/// (`obligations`), and an admitted verdict needs admissible evidence for
/// every one of them.
#[test]
fn a_report_stripped_of_its_certificates_is_not_a_pass() {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&sibling_cited_bundle())
        .expect("valid upstream");
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );
    let strip = |json: &mut serde_json::Value, obligations: Option<serde_json::Value>| {
        for request in json["requests"].as_array_mut().expect("requests") {
            request["proof_evidence"] = serde_json::json!([]);
            request["verdict"] = serde_json::json!("certificates_admitted");
            if let Some(obligations) = &obligations {
                request["obligations"] = obligations.clone();
            }
        }
        json["verdict"] = serde_json::json!("certificates_admitted");
    };
    // Stripped, with the named obligations kept, emptied, or removed.
    for obligations in [None, Some(serde_json::json!([]))] {
        let forged = reencoded::<TrustVcNativeTrustIrBundleReport>(&report, |json| {
            strip(json, obligations.clone());
        });
        assert!(
            !forged
                .as_ref()
                .is_ok_and(|decoded| decoded.verdict().is_ok()),
            "a stripped report decoded as a clean pass: {:?}",
            forged.map(|decoded| decoded.verdict())
        );
    }
    let without_the_set = reencoded::<TrustVcNativeTrustIrBundleReport>(&report, |json| {
        strip(json, None);
        for request in json["requests"].as_array_mut().expect("requests") {
            request
                .as_object_mut()
                .expect("request is an object")
                .remove("obligations");
        }
    });
    assert!(
        without_the_set.is_err(),
        "a report that does not name its obligations must not decode"
    );
}

/// The same edit on a single request report.
#[test]
fn a_request_report_without_certificates_is_not_admitted() {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&sibling_cited_bundle())
        .expect("valid upstream");
    let request = report.requests()[0].clone();
    for obligations in [None, Some(serde_json::json!([]))] {
        let forged = reencoded::<trust_vc_trust_engine::TrustVcNativeTrustIrRequestReport>(
            &request,
            |json| {
                json["proof_evidence"] = serde_json::json!([]);
                json["verdict"] = serde_json::json!("certificates_admitted");
                if let Some(obligations) = &obligations {
                    json["obligations"] = obligations.clone();
                }
            },
        );
        assert!(
            !forged
                .as_ref()
                .is_ok_and(|decoded| decoded.verdict().is_ok()),
            "a stripped request report decoded as admitted: {:?}",
            forged.map(|decoded| decoded.verdict())
        );
    }
    // Declaring the rejection it re-derives to, it decodes and admits nothing.
    let rejected =
        reencoded::<trust_vc_trust_engine::TrustVcNativeTrustIrRequestReport>(&request, |json| {
            json["proof_evidence"] = serde_json::json!([]);
            json["verdict"] = serde_json::json!("certificates_rejected");
        })
        .expect("decodes");
    assert_eq!(
        rejected.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );

    // The honest producer names what its evidence covered.
    let admitted = established_report();
    // Read off the wire, so this file also compiles against the tree before
    // the report named its obligations (where the set is absent).
    let wire = serde_json::to_value(&admitted.requests()[0]).expect("serializes");
    let named: Vec<u32> = serde_json::from_value(wire["obligations"].clone())
        .expect("the report names its obligations");
    let covered: Vec<u32> = admitted.requests()[0]
        .proof_evidence()
        .iter()
        .map(TrustVcNativeTrustIrCertificateEvidence::obligation_id)
        .collect();
    assert!(!named.is_empty());
    assert_eq!(named, covered);
    assert_eq!(
        admitted.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
}

/// LIAR L1, re-derived. At the bundle, an atom whose id was forged is refused
/// at the door. On the wire, a genuinely admitted row whose ids are edited
/// admits nothing either: moving the row's id and its atom rendering off the
/// compiler fact's is an identity refusal, and moving all three together still
/// leaves the coverage the wire cannot carry.
#[test]
fn a_forged_assertion_id_is_refused_at_the_bundle_and_on_the_wire() {
    let mut forged = native_bundle_fixture();
    forge_atom_id(&mut forged, 0, trust_ir::ProofId::new(0), 2);
    TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&forged)
        .expect_err("a forged atom id is refused at the door");

    let evidence = established_evidence();
    assert_eq!(evidence.native_assertion_id(), Some(1));
    let moved_off_the_fact: TrustVcNativeTrustIrCertificateEvidence =
        reencoded(&evidence, |json| {
            json["assertion_id"] = serde_json::json!(2);
            json["independent_assertion_id"] = serde_json::json!(2);
        })
        .expect("the payload decodes");
    assert!(!moved_off_the_fact.release_admission().is_admissible());
    let artifact = moved_off_the_fact.admit_native_proof_artifact();
    assert!(!artifact.admission().is_accepted(), "{artifact:?}");
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch),
        "{artifact:?}"
    );

    let moved_together: TrustVcNativeTrustIrCertificateEvidence = reencoded(&evidence, |json| {
        json["assertion_id"] = serde_json::json!(2);
        json["independent_assertion_id"] = serde_json::json!(2);
        json["compiler_facts_binding"]["assertion_id"] = serde_json::json!(2);
    })
    .expect("the payload decodes");
    assert!(!moved_together.release_admission().is_admissible());
    assert!(!moved_together
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
}
