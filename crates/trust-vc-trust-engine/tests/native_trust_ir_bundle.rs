// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_ir::request::{
    NativeAssertionId, NativeEvidenceBundle, NativeVerificationBundle, NativeVerificationRequest,
    NativeVerifierSuite, TrustVcTrustedEvidencePolicy,
};
use trust_ir::{ProofEvidence, ProofId, ProofStatus};
use trust_vc_trust_engine::{
    TrustEngineError, TrustVcNativeArtifactAdmissionStatus, TrustVcNativeArtifactExpectation,
    TrustVcNativeArtifactRejection, TrustVcNativeArtifactReplayStatus,
    TrustVcNativeCompilerFactRef, TrustVcNativeCompilerFactsBinding, TrustVcNativeObligationCause,
    TrustVcNativeProofArtifact, TrustVcNativeProofArtifactInput, TrustVcNativeSolverIdentity,
    TrustVcNativeToolIdentity, TrustVcNativeTrustIrCertificateAdmissionStatus,
    TrustVcNativeTrustIrCertificateRejection, TrustVcNativeTrustIrEvidenceKind,
    TrustVcNativeTrustIrInputKind, TrustVcNativeTrustIrReplayMetadataSource,
    TrustVcNativeTrustIrRequestMode, TrustVcNativeVerifierSuite, TrustVcTrustEngine,
};

const NATIVE_REQUEST_TRUST_BUNDLE: &str =
    include_str!("../fixtures/trust_ir_native/native_request_trust_bundle.json");

fn native_bundle_fixture() -> NativeVerificationBundle {
    serde_json::from_str(NATIVE_REQUEST_TRUST_BUNDLE)
        .expect("checked-in TrustIr native request fixture should decode")
}

fn refresh_trust_vc_evidence_binding(bundle: &mut NativeVerificationBundle) {
    let NativeVerificationRequest::TrustVc(request) = &bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    let request_id = request.id;
    let obligations = request.obligations.clone();
    let request_digest = bundle.requests[0].stable_digest();

    for evidence in &mut bundle.evidence_bundles {
        if let NativeEvidenceBundle::TrustVc(evidence) = evidence {
            if evidence.request == request_id {
                evidence.obligations = obligations.clone();
                evidence.request_digest = request_digest;
            }
        }
    }
}

#[test]
fn consumes_upstream_native_trust_ir_trust_vc_request_variant() {
    let bundle = native_bundle_fixture();
    let trust_vc_request_count = bundle
        .requests
        .iter()
        .filter(|request| matches!(request, NativeVerificationRequest::TrustVc(_)))
        .count();
    assert_eq!(
        trust_vc_request_count, 1,
        "fixture should exercise the typed TrustVc variant directly"
    );

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");

    assert_eq!(report.producer(), "tRust");
    assert_eq!(report.input_kind(), TrustVcNativeTrustIrInputKind::RustMir);
    assert!(report.input_digest().is_some());
    assert_eq!(report.module_name(), "trust_native_request_bundle");
    assert_eq!(
        report.trust_ir_module_digest(),
        &bundle.trust_ir_module_digest.to_string()
    );
    assert_eq!(
        report.compiler_facts_digest(),
        &bundle.compiler_facts.stable_digest().to_string()
    );
    assert_eq!(report.requests().len(), trust_vc_request_count);

    let request = &report.requests()[0];
    assert_eq!(request.request_id(), 0);
    assert_eq!(
        request.mode(),
        TrustVcNativeTrustIrRequestMode::ImportProofCertificates
    );
    assert_eq!(request.lineage_roots(), &[0]);
    assert_eq!(request.proof_evidence().len(), 1);

    let evidence = &request.proof_evidence()[0];
    let certificate = &bundle.module.proof_certificates[0];
    assert_eq!(evidence.obligation_id(), 0);
    assert_eq!(evidence.native_assertion_id(), Some(1));
    assert_eq!(
        evidence.trust_ir_module_digest(),
        report.trust_ir_module_digest()
    );
    assert_eq!(evidence.obligation_kind(), "memory_safety");
    assert_eq!(evidence.obligation_status(), "discharged");
    assert_eq!(evidence.formula_schema(), Some("trust-types.Formula@1"));
    assert_eq!(evidence.formula_sort(), Some("Bool"));
    assert_eq!(evidence.prover(), "trust_vc");
    assert_eq!(
        evidence.evidence_digest(),
        &certificate.evidence_digest().to_string()
    );
    assert_eq!(
        evidence.certificate_digest(),
        &certificate.stable_digest().to_string()
    );
    assert_eq!(
        evidence.suite_identity().suite(),
        TrustVcNativeVerifierSuite::TrustVc
    );
    assert_eq!(evidence.suite_identity().name(), "trust_vc");
    assert_eq!(evidence.suite_identity().producer(), "trust-vc-2026-04-29");
    assert_eq!(evidence.suite_identity().version(), "semantics-v1");
    assert_eq!(evidence.suite_identity().tool_digest(), None);
    assert!(evidence
        .suite_identity()
        .fingerprint()
        .starts_with("sha256:"));
    assert_eq!(evidence.solver_identity().prover(), "trust_vc");
    assert_eq!(evidence.solver_identity().solvers().len(), 1);
    let solver = &evidence.solver_identity().solvers()[0];
    assert_eq!(solver.name(), "lean4");
    assert_eq!(solver.version(), Some("4.18.0"));
    assert_eq!(solver.revision(), Some("trust-vc-proof-kernel"));
    assert_eq!(solver.digest(), None);
    assert!(solver.fingerprint().starts_with("sha256:"));
    assert!(evidence
        .solver_identity()
        .fingerprint()
        .starts_with("sha256:"));
    assert_eq!(
        evidence.solver_identity().replay_engine(),
        Some("trust-full-verify")
    );
    assert_eq!(
        evidence.solver_identity().replay_invocation(),
        Some("trust verify --emit-trust_ir-bundle")
    );
    assert!(evidence.solver_identity().transcript_digest().is_some());
    let replay = evidence
        .replay_metadata()
        .expect("native report should expose replay/check metadata directly");
    assert_eq!(
        replay.source(),
        TrustVcNativeTrustIrReplayMetadataSource::LineageNode
    );
    assert_eq!(replay.lineage_node_id(), Some(0));
    assert_eq!(replay.engine(), "trust-full-verify");
    assert_eq!(replay.invocation(), "trust verify --emit-trust_ir-bundle");
    assert_eq!(
        replay.transcript_digest(),
        evidence.solver_identity().transcript_digest()
    );
    let compiler_facts = evidence.compiler_facts_binding();
    assert_eq!(
        compiler_facts.compiler_facts_digest(),
        report.compiler_facts_digest()
    );
    assert_eq!(compiler_facts.obligation_id(), evidence.obligation_id());
    assert_eq!(compiler_facts.function_id(), Some(0));
    assert_eq!(compiler_facts.assertion_id(), Some(1));
    assert_eq!(
        compiler_facts.source_span().map(|span| span.line()),
        Some(24)
    );
    assert_eq!(
        compiler_facts.cause(),
        TrustVcNativeObligationCause::BoundsCheck
    );
    assert_eq!(compiler_facts.monomorphization_id(), Some(0));
    assert_eq!(
        compiler_facts.fact_refs(),
        &[
            TrustVcNativeCompilerFactRef::adt_layout(0),
            TrustVcNativeCompilerFactRef::fat_pointer(2),
            TrustVcNativeCompilerFactRef::monomorphization(0),
        ]
    );
    assert!(compiler_facts
        .obligation_source_digest()
        .starts_with("sha256:"));
    assert_eq!(
        evidence.evidence_kind(),
        TrustVcNativeTrustIrEvidenceKind::LeanProof
    );
    assert!(!evidence.trusted());
    assert_eq!(
        evidence.release_admission().status(),
        TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
    );
    assert!(evidence.release_admission().is_admissible());
    assert!(evidence.release_admission().rejection_reasons().is_empty());
    assert!(evidence
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
}

#[test]
fn native_trust_ir_report_falls_back_to_request_replay_metadata() {
    let mut bundle = native_bundle_fixture();
    bundle.lineage.nodes[0].replay = None;

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let replay = evidence
        .replay_metadata()
        .expect("request provenance replay should be surfaced");

    assert_eq!(
        replay.source(),
        TrustVcNativeTrustIrReplayMetadataSource::RequestProvenance
    );
    assert_eq!(replay.lineage_node_id(), None);
    assert_eq!(replay.engine(), "trust_vc");
    assert_eq!(
        replay.invocation(),
        "trust_vc import --native-bundle native_request_trust_bundle"
    );
    assert_eq!(
        replay.transcript_digest(),
        evidence.solver_identity().transcript_digest()
    );
}

#[test]
fn admits_native_trust_ir_certificate_as_typed_proof_artifact() {
    let mut bundle = native_bundle_fixture();
    bundle.compiler_facts.obligation_sources[0].assertion_id = Some(NativeAssertionId::new(42));
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];

    assert_eq!(evidence.native_assertion_id(), Some(42));
    assert_eq!(evidence.compiler_facts_binding().assertion_id(), Some(42));
    assert_eq!(
        evidence.release_admission().status(),
        TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
    );
    assert!(evidence.release_admission().is_admissible());
    assert!(evidence.release_admission().rejection_reasons().is_empty());

    let artifact = evidence.admit_native_proof_artifact();
    let admission = artifact.admission();

    assert_eq!(artifact.assertion_id(), "42");
    assert_eq!(
        artifact.trust_ir_module_digest(),
        evidence.trust_ir_module_digest()
    );
    assert_eq!(artifact.trust_ir_obligation_id(), evidence.obligation_id());
    assert_eq!(artifact.suite_identity(), evidence.suite_identity());
    assert_eq!(artifact.solver_identity(), evidence.solver_identity());
    assert_eq!(artifact.evidence_digest(), evidence.evidence_digest());
    assert_eq!(artifact.certificate_digest(), evidence.certificate_digest());
    assert_eq!(
        artifact.compiler_facts_binding(),
        evidence.compiler_facts_binding()
    );
    assert!(artifact.artifact_fingerprint().starts_with("sha256:"));
    assert_eq!(
        admission.replay_status(),
        TrustVcNativeArtifactReplayStatus::Replayable
    );
    assert_eq!(
        admission.status(),
        TrustVcNativeArtifactAdmissionStatus::Accepted
    );
    assert!(admission.is_accepted());
    assert!(admission.rejection_reasons().is_empty());

    let expectation = TrustVcNativeArtifactExpectation::new(
        artifact.assertion_id(),
        artifact.trust_ir_obligation_id(),
    )
    .with_trust_ir_module_digest(artifact.trust_ir_module_digest())
    .with_suite_identity(artifact.suite_identity().clone())
    .with_solver_identity(artifact.solver_identity().clone())
    .with_evidence_digest(artifact.evidence_digest())
    .with_certificate_digest(artifact.certificate_digest())
    .with_compiler_facts_binding(artifact.compiler_facts_binding().clone())
    .with_artifact_fingerprint(artifact.artifact_fingerprint());
    assert!(artifact.admission_against(&expectation).is_accepted());
}

#[test]
fn rejects_native_trust_ir_artifact_when_assertion_id_disagrees_with_compiler_source() {
    let mut bundle = native_bundle_fixture();
    bundle.compiler_facts.obligation_sources[0].assertion_id = Some(NativeAssertionId::new(42));
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];

    assert!(
        evidence.release_admission().is_admissible(),
        "fixture should isolate the assertion/source mismatch from release-grade evidence"
    );

    let stale_artifact = evidence.admit_proof_artifact("43");
    let stale_admission = stale_artifact.admission();

    assert_eq!(stale_artifact.assertion_id(), "43");
    assert_eq!(
        stale_artifact.compiler_facts_binding().assertion_id(),
        Some(42)
    );
    assert_eq!(
        stale_admission.replay_status(),
        TrustVcNativeArtifactReplayStatus::Replayable
    );
    assert_eq!(
        stale_admission.status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert_eq!(
        stale_admission.rejection_reasons(),
        &[TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch]
    );

    assert!(evidence
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
}

#[test]
fn admits_multi_assertion_native_trust_ir_certificates_without_collapsing_bindings() {
    let mut bundle = native_bundle_fixture();
    bundle.compiler_facts.obligation_sources[0].assertion_id = Some(NativeAssertionId::new(42));

    let second_obligation_id = ProofId::new(3);
    let mut second_obligation = bundle.module.proof_obligations[0].clone();
    second_obligation.id = second_obligation_id;
    second_obligation.description = "second frontend assertion memory-safety proof".to_string();
    bundle.module.proof_obligations.push(second_obligation);

    let mut second_certificate = bundle.module.proof_certificates[0].clone();
    second_certificate.obligation = second_obligation_id;
    second_certificate.evidence =
        ProofEvidence::LeanProof("second frontend assertion certificate".to_string());
    let second_certificate_ref = second_certificate.lineage_ref();
    bundle.module.proof_certificates.push(second_certificate);

    let mut second_source = bundle.compiler_facts.obligation_sources[0].clone();
    second_source.obligation = second_obligation_id;
    second_source.assertion_id = Some(NativeAssertionId::new(43));
    bundle.compiler_facts.obligation_sources.push(second_source);

    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.obligations.push(second_obligation_id);
    request.certificates.push(second_certificate_ref.clone());
    bundle.lineage.nodes[0]
        .obligations
        .push(second_obligation_id);
    bundle.lineage.nodes[0]
        .certificates
        .push(second_certificate_ref);
    refresh_trust_vc_evidence_binding(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("multi-assertion native TrustIr request should be consumable");
    let request = &report.requests()[0];

    assert_eq!(request.proof_evidence().len(), 2);
    assert!(request
        .proof_evidence()
        .iter()
        .all(|evidence| evidence.release_admission().is_admissible()));

    let request_artifacts = request.admit_native_proof_artifacts();
    let bundle_artifacts = report.admit_native_proof_artifacts();

    assert_eq!(bundle_artifacts, request_artifacts);
    assert_eq!(request_artifacts.len(), 2);
    assert_eq!(request_artifacts[0].assertion_id(), "42");
    assert_eq!(request_artifacts[1].assertion_id(), "43");
    assert_eq!(request_artifacts[0].trust_ir_obligation_id(), 0);
    assert_eq!(request_artifacts[1].trust_ir_obligation_id(), 3);
    assert_ne!(
        request_artifacts[0].artifact_fingerprint(),
        request_artifacts[1].artifact_fingerprint()
    );
    assert!(request_artifacts
        .iter()
        .all(|artifact| artifact.admission().is_accepted()));
}

#[test]
fn rejects_stale_or_mismatched_native_trust_ir_proof_artifact_and_compiler_fact_bindings() {
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let artifact = evidence.admit_native_proof_artifact();
    let stale_compiler_facts = TrustVcNativeCompilerFactsBinding::new(
        "trust_ir-stable-v1:stale",
        artifact.trust_ir_obligation_id(),
        artifact.compiler_facts_binding().function_id(),
        artifact.compiler_facts_binding().source_span(),
        TrustVcNativeObligationCause::CastCheck,
        artifact.compiler_facts_binding().monomorphization_id(),
        vec![TrustVcNativeCompilerFactRef::cast(4)],
    );
    let stale_solver_identity = TrustVcNativeSolverIdentity::new("trust_vc")
        .with_solver(TrustVcNativeToolIdentity::new("z3").with_version("4.13.0"))
        .with_replay_identity(
            "trust-full-verify",
            "trust verify --emit-trust_ir-bundle",
            artifact
                .solver_identity()
                .transcript_digest()
                .map(str::to_string),
        );
    let stale_solver_artifact = TrustVcNativeProofArtifact::new(
        TrustVcNativeProofArtifactInput::new(
            artifact.assertion_id(),
            artifact.trust_ir_obligation_id(),
            artifact.evidence_digest(),
            artifact.certificate_digest(),
        )
        .with_trust_ir_module_digest(artifact.trust_ir_module_digest())
        .with_request_digest(artifact.request_digest())
        .with_suite_identity(artifact.suite_identity().clone())
        .with_solver_identity(stale_solver_identity.clone())
        .with_obligation_status(evidence.typed_obligation_status())
        .with_trusted(evidence.trusted())
        .with_compiler_facts_binding(artifact.compiler_facts_binding().clone()),
    );
    assert_ne!(
        stale_solver_artifact.artifact_fingerprint(),
        artifact.artifact_fingerprint()
    );
    let stale_expectation =
        TrustVcNativeArtifactExpectation::new("checked_add::different_assertion", 99)
            .with_trust_ir_module_digest("trust_ir-stable-v1:stale-module")
            .with_request_digest("trust_ir-stable-v1:stale-request")
            .with_suite_identity(artifact.suite_identity().clone())
            .with_solver_identity(stale_solver_identity)
            .with_evidence_digest("trust_ir-stable-v1:stale")
            .with_certificate_digest(artifact.certificate_digest())
            .with_compiler_facts_binding(stale_compiler_facts)
            .with_artifact_fingerprint("sha256:stale");

    let admission = artifact.admission_against(&stale_expectation);

    assert_eq!(
        admission.status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(!admission.is_accepted());
    assert_eq!(
        admission.rejection_reasons(),
        &[
            TrustVcNativeArtifactRejection::AssertionIdMismatch,
            TrustVcNativeArtifactRejection::TrustIrObligationIdMismatch,
            TrustVcNativeArtifactRejection::TrustIrModuleDigestMismatch,
            TrustVcNativeArtifactRejection::RequestDigestMismatch,
            TrustVcNativeArtifactRejection::SolverIdentityMismatch,
            TrustVcNativeArtifactRejection::EvidenceDigestMismatch,
            TrustVcNativeArtifactRejection::CompilerFactsDigestMismatch,
            TrustVcNativeArtifactRejection::CompilerFactSourceMismatch,
            TrustVcNativeArtifactRejection::CompilerFactReferencesMismatch,
            TrustVcNativeArtifactRejection::ArtifactFingerprintMismatch,
        ]
    );
}

#[test]
fn native_trust_ir_proof_artifact_admission_fails_closed_without_request_digest() {
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let assertion_id = evidence
        .native_assertion_id()
        .expect("fixture carries source assertion id")
        .to_string();
    let artifact = TrustVcNativeProofArtifact::new(
        TrustVcNativeProofArtifactInput::new(
            assertion_id,
            evidence.obligation_id(),
            evidence.evidence_digest(),
            evidence.certificate_digest(),
        )
        .with_trust_ir_module_digest(evidence.trust_ir_module_digest())
        .with_suite_identity(evidence.suite_identity().clone())
        .with_solver_identity(evidence.solver_identity().clone())
        .with_obligation_status(evidence.typed_obligation_status())
        .with_trusted(evidence.trusted())
        .with_compiler_facts_binding(evidence.compiler_facts_binding().clone()),
    );
    let admission = artifact.admission();

    assert_eq!(
        admission.replay_status(),
        TrustVcNativeArtifactReplayStatus::Replayable
    );
    assert_eq!(
        admission.status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert_eq!(
        admission.rejection_reasons(),
        &[TrustVcNativeArtifactRejection::MissingRequestDigest]
    );
}

#[test]
fn native_trust_ir_proof_artifact_admission_fails_closed_without_module_digest() {
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let assertion_id = evidence
        .native_assertion_id()
        .expect("fixture carries source assertion id")
        .to_string();
    let artifact = TrustVcNativeProofArtifact::new(
        TrustVcNativeProofArtifactInput::new(
            assertion_id,
            evidence.obligation_id(),
            evidence.evidence_digest(),
            evidence.certificate_digest(),
        )
        .with_request_digest(evidence.request_digest())
        .with_suite_identity(evidence.suite_identity().clone())
        .with_solver_identity(evidence.solver_identity().clone())
        .with_obligation_status(evidence.typed_obligation_status())
        .with_trusted(evidence.trusted())
        .with_compiler_facts_binding(evidence.compiler_facts_binding().clone()),
    );
    let admission = artifact.admission();

    assert_eq!(
        admission.replay_status(),
        TrustVcNativeArtifactReplayStatus::Replayable
    );
    assert_eq!(
        admission.status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert_eq!(
        admission.rejection_reasons(),
        &[TrustVcNativeArtifactRejection::MissingTrustIrModuleDigest]
    );
}

#[test]
fn native_trust_ir_proof_artifact_admission_fails_closed_without_suite_identity() {
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let assertion_id = evidence
        .native_assertion_id()
        .expect("fixture carries source assertion id")
        .to_string();
    let artifact = TrustVcNativeProofArtifact::new(
        TrustVcNativeProofArtifactInput::new(
            assertion_id,
            evidence.obligation_id(),
            evidence.evidence_digest(),
            evidence.certificate_digest(),
        )
        .with_trust_ir_module_digest(evidence.trust_ir_module_digest())
        .with_request_digest(evidence.request_digest())
        .with_solver_identity(evidence.solver_identity().clone())
        .with_obligation_status(evidence.typed_obligation_status())
        .with_trusted(evidence.trusted())
        .with_compiler_facts_binding(evidence.compiler_facts_binding().clone()),
    );
    let admission = artifact.admission();

    assert_eq!(
        admission.replay_status(),
        TrustVcNativeArtifactReplayStatus::Replayable
    );
    assert_eq!(
        admission.status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert_eq!(
        admission.rejection_reasons(),
        &[TrustVcNativeArtifactRejection::MissingSuiteIdentity]
    );
}

#[test]
fn rejects_native_trust_ir_bundle_without_source_assertion_id() {
    let mut bundle = native_bundle_fixture();
    bundle.compiler_facts.obligation_sources[0].assertion_id = None;

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("schema v3 must reject requested obligations without assertion ids");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream source assertion validation error, got {err:?}");
    };
    assert!(
        errors.contains("native verification request 0 obligation 0 has no source assertion id")
    );
}

#[test]
fn rejects_native_trust_ir_bundle_without_request_replay_transcript_digest() {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request
        .provenance
        .replay
        .as_mut()
        .expect("fixture carries request replay metadata")
        .transcript_digest = None;

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("schema v3 must reject replay metadata without transcript digests");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream replay transcript validation error, got {err:?}");
    };
    assert!(errors.contains("native verification request 0 requires a replay transcript digest"));
}

#[test]
fn rejects_native_trust_ir_bundle_without_typed_solver_identities() {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.provenance.solvers.clear();

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("TrustIr validation must reject missing typed solver identities");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream solver-identity validation error, got {err:?}");
    };
    assert!(errors.contains("native verification bundle has empty request.provenance.solvers"));
}

#[test]
fn rejects_native_trust_ir_bundle_without_release_evidence_bundles() {
    let mut bundle = native_bundle_fixture();
    bundle.evidence_bundles.clear();

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("release admission must require native evidence bundles");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected missing release evidence validation error, got {err:?}");
    };
    assert!(
        errors.contains("native verification request 0 requires a TrustVc native evidence bundle")
    );
}

#[test]
fn rejects_native_trust_ir_bundle_without_compiler_fact_source() {
    let mut bundle = native_bundle_fixture();
    bundle
        .compiler_facts
        .obligation_sources
        .retain(|source| source.obligation.index() != 0);

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("schema v3 must reject requested obligations without source mappings");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream source mapping validation error, got {err:?}");
    };
    assert!(errors.contains("native verification request 0 obligation 0 has no source mapping"));
}

#[test]
fn rejects_native_trust_ir_bundle_with_non_discharged_trust_vc_obligations() {
    for status in [
        ProofStatus::Pending,
        ProofStatus::Failed,
        ProofStatus::Trusted,
    ] {
        let mut bundle = native_bundle_fixture();
        bundle.module.proof_obligations[0].status = status;

        let err = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect_err("schema v3 must reject non-discharged TrustVc certificate evidence");

        let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
            panic!("expected upstream non-discharged certificate validation error, got {err:?}");
        };
        assert!(errors.contains("native verification request 0 rejects TrustVc certificate evidence 0/trust_vc with non-discharged status"));
    }
}

#[test]
fn native_trust_ir_certificate_admission_flags_trusted_evidence_payloads() {
    let mut bundle = native_bundle_fixture();
    bundle.module.proof_certificates[0].evidence =
        ProofEvidence::Trusted("manual trust assumption".to_string());
    let certificate_ref = bundle.module.proof_certificates[0].lineage_ref();
    bundle.lineage.nodes[0].certificates[0] = certificate_ref.clone();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.certificates[0] = certificate_ref;
    request.options.trusted_evidence = TrustVcTrustedEvidencePolicy::Allow;
    refresh_trust_vc_evidence_binding(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr request should surface trusted evidence as non-release");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let admission = evidence.release_admission();

    assert_eq!(
        evidence.evidence_kind(),
        TrustVcNativeTrustIrEvidenceKind::Trusted
    );
    assert!(evidence.trusted());
    assert_eq!(
        admission.status(),
        TrustVcNativeTrustIrCertificateAdmissionStatus::Rejected
    );
    assert!(!admission.is_admissible());
    assert_eq!(
        admission.rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::CertificateUsesTrustedEvidence]
    );
}

#[test]
fn rejects_native_trust_ir_bundle_without_trust_vc_requests() {
    let mut bundle = native_bundle_fixture();
    bundle
        .requests
        .retain(|request| !matches!(request, NativeVerificationRequest::TrustVc(_)));
    bundle.evidence_bundles.clear();

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("native bundle without TrustVc request should not silently pass");

    assert_eq!(
        err,
        TrustEngineError::NativeTrustIrBundleHasNoTrustVcRequests {
            module: "trust_native_request_bundle".to_string(),
        }
    );
}

#[test]
fn rejects_native_trust_ir_bundle_with_mismatched_verifier_suite() {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.provenance.verifier_suite = NativeVerifierSuite::TrustMc;

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("TrustIr validation must reject mismatched typed verifier suites");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream verifier-suite validation error, got {err:?}");
    };
    assert!(errors
        .contains("native verification request 0 has verifier suite trust_mc, expected trust_vc"));
}

#[test]
fn rejects_native_trust_ir_trust_vc_request_without_certificate_for_obligation() {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.certificates.clear();

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("TrustVc native request must bind certificate evidence");

    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream schema-v3 validation error, got {err:?}");
    };
    assert!(errors.contains(
        "native verification request 0 has no TrustVc certificate evidence for obligation 0"
    ));
}
