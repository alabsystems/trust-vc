// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Release admission derives a certificate's COVERAGE from evidence this
//! process re-checks — trust-ir-build's `coverage_establishment_report`,
//! basis K: the in-process Clean-kernel replay of exactly that certificate —
//! and never from a producer-written `ProofCertificate::assurance` row.
//!
//! Every new label is read off the WIRE (`serde_json`), not through a Rust
//! variant, so this file also compiles against the tree before the rule
//! changed; the A/B tests below were run there and fail on it.

use serde::Serialize;
use serde_json::{json, Value};
use trust_ir::proof::{CoverageAssurance, CoverageBound};
use trust_ir::request::{
    NativeVerificationBundle, NativeVerificationRequest, TrustMcVerificationMode,
    TrustVcTrustedEvidencePolicy,
};
use trust_ir::{ProofDigest, ProofEvidence, ProofId, ProofStatus};
use trust_vc_trust_engine::{
    TrustVcNativeTrustIrBundleReport, TrustVcNativeTrustIrCertificateAdmission,
    TrustVcNativeTrustIrCertificateEvidence, TrustVcNativeTrustIrVerdict, TrustVcTrustEngine,
};

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/admission_edits.rs"]
mod admission_edits;
use admission_baseline::{
    add_sibling_certificate, cite_certificates, install_bridge_atoms, native_bundle_fixture,
    reseal_module_identity, NATIVE_REQUEST_TRUST_BUNDLE, PENDING_CHC_REQUEST,
};
use admission_edits::assert_id_and_formula_liars_refused;

/// Basis K established THIS certificate's coverage and nothing refuses it.
fn established_and_admitted(admission: &TrustVcNativeTrustIrCertificateAdmission) -> bool {
    admission.coverage_established()
        && admission.is_admissible()
        && admission.rejection_reasons().is_empty()
}

/// The wire labels of `values` (snake_case enum names).
fn labels<T: Serialize>(values: &[T]) -> Vec<String> {
    values
        .iter()
        .map(|value| {
            serde_json::to_value(value)
                .expect("serializes")
                .as_str()
                .expect("a unit variant serializes as its label")
                .to_string()
        })
        .collect()
}

fn consume(bundle: &NativeVerificationBundle, label: &str) -> TrustVcNativeTrustIrBundleReport {
    TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(bundle)
        .unwrap_or_else(|error| panic!("{label}: the bundle is valid upstream: {error}"))
}

fn sole_evidence(
    report: &TrustVcNativeTrustIrBundleReport,
) -> TrustVcNativeTrustIrCertificateEvidence {
    let evidence = report.requests()[0].proof_evidence();
    assert_eq!(evidence.len(), 1, "one imported certificate");
    evidence[0].clone()
}

/// The admission's wire image: `coverage_basis` and `coverage_detail` are
/// read here, so this file compiles on a tree without the accessors.
fn admission_wire(admission: &TrustVcNativeTrustIrCertificateAdmission) -> Value {
    serde_json::to_value(admission).expect("admission serializes")
}

fn kernel_basis(bundle: &NativeVerificationBundle, certificate: usize) -> Value {
    let certificate = &bundle.module.proof_certificates[certificate];
    json!({
        "basis": "kernel_replayed_claim",
        "obligation_id": certificate.obligation.index(),
        "prover": certificate.prover,
        "evidence_digest": certificate.evidence_digest().to_string(),
        "family": "contract_ground_decision",
    })
}

fn smt_proof() -> ProofEvidence {
    ProofEvidence::SmtProof(b"(proof (asserted (>= 5 0)))".to_vec())
}

/// A/B. The one real release certificate in the corpus — the VERBATIM
/// upstream bundle: obligation 0 `Certified`, a directive-less CleanCic
/// contract certificate, NO `assurance` row — has its coverage ESTABLISHED:
/// this process replayed exactly that certificate in the Clean kernel, and its
/// claim is a closed contract decision (`Unbounded`). Before, it was refused
/// `certificate_coverage_unrecorded` (no row) beside `obligation_trusted`
/// (`Certified` was filed as `Trusted`). As upstream ships it, its TrustVc
/// request carries no `Assertion` replay atom, so the export seam publishes no
/// id and it is refused `missing_assertion_id` alone; with the atom Trust's
/// bridge writes it is release grade
/// (`corpus_kernel_replayed_certificate_with_its_atom_is_release_grade`).
#[test]
fn corpus_kernel_replayed_certificate_establishes_coverage_without_a_row() {
    let bundle: NativeVerificationBundle = serde_json::from_str(NATIVE_REQUEST_TRUST_BUNDLE)
        .expect("checked-in TrustIr native request fixture should decode");
    assert!(
        bundle
            .module
            .proof_certificates
            .iter()
            .all(|certificate| certificate.assurance.is_none()),
        "the corpus certificate records no coverage row"
    );
    assert_eq!(
        bundle.module.proof_obligations[0].status,
        ProofStatus::Certified,
        "the corpus ships obligation 0 Certified; if it no longer does, re-read this test"
    );

    let engine = TrustVcTrustEngine::new();
    let report = consume(&bundle, "verbatim corpus");
    let evidence = sole_evidence(&report);
    let admission = evidence.release_admission();
    assert!(
        admission.coverage_established()
            && labels(admission.rejection_reasons()) == ["missing_assertion_id"],
        "the kernel-replayed corpus certificate is refused for its missing id alone: {:?}",
        admission.rejection_reasons()
    );
    assert_eq!(evidence.obligation_status(), "certified");
    assert_eq!(
        admission_wire(admission)["coverage_basis"],
        kernel_basis(&bundle, 0),
        "established by the kernel replay of THIS certificate"
    );
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );
    let artifact = evidence.admit_native_proof_artifact();
    assert!(!artifact.admission().is_accepted());
    assert_eq!(
        labels(artifact.admission().rejection_reasons()),
        [
            "missing_assertion_id",
            "compiler_fact_assertion_id_mismatch"
        ]
    );
    assert!(engine.validate_native_trust_ir_bundle(&bundle).is_err());
}

/// The same verbatim corpus bundle with the `Assertion` replay atom Trust's
/// `trust-ir-bridge` writes in its TrustVc request: the obligation's formula
/// cloned, beside the compiler fact's number. Its certificate is release grade
/// on its own kernel replay, the rollup validates, and its artifact is
/// accepted under assertion id 1. Its liar twins — the atom's id forged, the
/// atom asserting another formula — are refused.
#[test]
fn corpus_kernel_replayed_certificate_with_its_atom_is_release_grade() {
    let mut bundle: NativeVerificationBundle = serde_json::from_str(NATIVE_REQUEST_TRUST_BUNDLE)
        .expect("checked-in TrustIr native request fixture should decode");
    install_bridge_atoms(&mut bundle);

    let engine = TrustVcTrustEngine::new();
    let report = consume(&bundle, "verbatim corpus with its atom");
    let evidence = sole_evidence(&report);
    let admission = evidence.release_admission();
    assert!(
        established_and_admitted(admission),
        "the kernel-replayed corpus certificate is release grade: {:?}",
        admission.rejection_reasons()
    );
    assert_eq!(evidence.obligation_status(), "certified");
    assert_eq!(evidence.native_assertion_id(), Some(1));
    assert_eq!(
        admission_wire(admission)["coverage_basis"],
        kernel_basis(&bundle, 0),
        "established by the kernel replay of THIS certificate"
    );
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
    let artifact = evidence.admit_native_proof_artifact();
    assert!(artifact.admission().is_accepted(), "{artifact:?}");
    assert_eq!(artifact.assertion_id(), "1");
    engine
        .validate_native_trust_ir_bundle(&bundle)
        .expect("an admitted rollup validates");
    assert_eq!(assert_id_and_formula_liars_refused(&bundle), 1);
}

/// A/B. THE FALSE-PROVENANCE ROUTE, CLOSED. An SMT certificate on obligation
/// 0 whose only coverage evidence is an in-module row recording `Unbounded`
/// and citing the corpus's PENDING TrustMc CHC request (made to list
/// obligation 0 — exactly the previous admission baseline). The retired rule
/// derived `Unbounded` from the request's MODE alone and admitted it. Now the
/// row claims more than anything derived for its certificate (it was never
/// kernel-replayed), trust-ir-build refuses the bundle
/// (`CoverageRowExceedsEstablished`), and the certificate is refused
/// `certificate_coverage_refused` with trust-ir-build's words as its detail.
#[test]
fn pending_chc_citation_no_longer_establishes() {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustMc(chc) = &mut bundle.requests[PENDING_CHC_REQUEST] else {
        panic!("fixture request {PENDING_CHC_REQUEST} should be TrustMc");
    };
    assert_eq!(chc.mode, TrustMcVerificationMode::Chc);
    chc.obligations.insert(0, ProofId::new(0));
    reseal_module_identity(&mut bundle);
    let request_digest = bundle.requests[PENDING_CHC_REQUEST].stable_digest();
    let smt = add_sibling_certificate(
        &mut bundle,
        "trust_vc-smt",
        smt_proof(),
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest,
        }),
    );
    cite_certificates(&mut bundle, vec![smt]);

    let report = consume(&bundle, "pending CHC citation");
    let evidence = sole_evidence(&report);
    assert_eq!(evidence.prover(), "trust_vc-smt");
    let admission = evidence.release_admission();
    assert!(
        !admission.is_admissible(),
        "a pending CHC request is a question, not an answer: {:?}",
        admission.rejection_reasons()
    );
    assert!(!admission.coverage_established());
    assert_eq!(
        labels(admission.rejection_reasons()),
        ["certificate_coverage_refused"]
    );
    let detail = admission_wire(admission)["coverage_detail"].clone();
    assert!(
        detail
            .as_str()
            .is_some_and(|detail| detail.contains("more than the consumer established")),
        "the refusal carries trust-ir-build's own words: {detail}"
    );
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );
    assert!(!evidence
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
    assert!(TrustVcTrustEngine::new()
        .validate_native_trust_ir_bundle(&bundle)
        .is_err());
}

/// Basis K is per CERTIFICATE. An SMT or `Trusted` certificate cited on an
/// obligation whose CleanCic sibling was kernel-replayed gains nothing from
/// that replay: `certificate_coverage_basis_not_this_certificate`, on the
/// certificate and on its artifact. Cited together, the CleanCic certificate
/// keeps its coverage and the sibling does not.
#[test]
fn smt_or_trusted_certificate_not_established_by_sibling_replay() {
    let cases = [
        ("trust_vc-smt", smt_proof(), false),
        (
            "trust_vc-manual-audit",
            ProofEvidence::Trusted("manual trust assumption".to_string()),
            true,
        ),
    ];
    for (prover, evidence, trusted) in cases {
        let mut bundle = native_bundle_fixture();
        if trusted {
            let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
                panic!("fixture first request should be TrustVc");
            };
            request.options.trusted_evidence = TrustVcTrustedEvidencePolicy::Allow;
        }
        let kernel = bundle.module.proof_certificates[0].lineage_ref();
        let sibling = add_sibling_certificate(&mut bundle, prover, evidence, None);

        cite_certificates(&mut bundle, vec![sibling.clone()]);
        let report = consume(&bundle, prover);
        let evidence = sole_evidence(&report);
        let admission = evidence.release_admission();
        assert!(!admission.is_admissible(), "{prover}");
        assert!(!admission.coverage_established(), "{prover}");
        let reasons = labels(admission.rejection_reasons());
        let mut expected = Vec::new();
        if trusted {
            expected.push("certificate_uses_trusted_evidence");
        }
        expected.push("certificate_coverage_basis_not_this_certificate");
        assert_eq!(reasons, expected, "{prover}");
        let artifact = evidence.admit_native_proof_artifact();
        assert!(!artifact.admission().is_accepted(), "{prover}");
        assert!(
            labels(artifact.admission().rejection_reasons())
                .contains(&"certificate_coverage_basis_not_this_certificate".to_string()),
            "{prover}: the artifact carries the refusal"
        );

        cite_certificates(&mut bundle, vec![kernel.clone(), sibling]);
        let report = consume(&bundle, prover);
        let evidence = report.requests()[0].proof_evidence();
        assert_eq!(evidence.len(), 2, "{prover}");
        let kernel_evidence = evidence
            .iter()
            .find(|evidence| evidence.prover() == kernel.prover)
            .expect("the CleanCic certificate is imported");
        let sibling_evidence = evidence
            .iter()
            .find(|evidence| evidence.prover() == prover)
            .expect("the sibling certificate is imported");
        assert!(
            established_and_admitted(kernel_evidence.release_admission()),
            "{prover}: {:?}",
            kernel_evidence.release_admission().rejection_reasons()
        );
        assert!(
            !sibling_evidence.release_admission().is_admissible(),
            "{prover}"
        );
        assert_eq!(
            report.verdict(),
            TrustVcNativeTrustIrVerdict::CertificatesRejected,
            "{prover}"
        );
    }
}

/// A REFUSAL anywhere in the bundle is fatal for every certificate of it — it
/// means a producer stated something false — while an UNDETERMINED verdict
/// elsewhere blocks nothing: the cited certificate stays admitted. The cited
/// CleanCic certificate is the same in
/// both bundles; only an UNCITED SMT sibling differs: without a row it is
/// merely undetermined, with a row claiming `Unbounded` it is a forgery.
#[test]
fn refusal_elsewhere_blocks_bundle_undetermined_elsewhere_does_not() {
    let mut undetermined = native_bundle_fixture();
    add_sibling_certificate(&mut undetermined, "trust_vc-smt", smt_proof(), None);
    let report = consume(&undetermined, "undetermined sibling");
    let evidence = sole_evidence(&report);
    assert!(
        established_and_admitted(evidence.release_admission()),
        "an undetermined sibling does not block: {:?}",
        evidence.release_admission().rejection_reasons()
    );
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
    assert_eq!(assert_id_and_formula_liars_refused(&undetermined), 1);

    let mut refused = native_bundle_fixture();
    let request_digest = refused.requests[0].stable_digest();
    add_sibling_certificate(
        &mut refused,
        "trust_vc-smt",
        smt_proof(),
        Some(CoverageAssurance {
            bound: CoverageBound::Unbounded,
            request_digest,
        }),
    );
    let report = consume(&refused, "refused sibling");
    let evidence = sole_evidence(&report);
    let admission = evidence.release_admission();
    assert!(
        !admission.is_admissible(),
        "a refusal anywhere rejects even the kernel-replayed certificate"
    );
    assert!(!admission.coverage_established());
    assert_eq!(
        labels(admission.rejection_reasons()),
        ["certificate_coverage_refused"]
    );
    assert_eq!(
        labels(
            evidence
                .admit_native_proof_artifact()
                .admission()
                .rejection_reasons()
        ),
        ["certificate_coverage_refused"]
    );
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );
}

/// A/B. The in-module row is NEVER read as coverage for a kernel-replayed
/// certificate: absent, `Unbounded` citing a digest no request hashes to or
/// the TrustVc request itself, or a bounded record citing the pending CHC
/// request — the certificate's coverage is established on its own replay
/// every time, and no citation is resolved. Beside a depth-1 BMC run of the
/// same obligation it is established too: there is no sibling REQUEST to
/// contest a basis that cites none. (The retired rule refused every one of these, as unrecorded,
/// unknown, undetermined, mismatched or contested.)
#[test]
fn in_module_rows_are_never_read_as_coverage() {
    let base = native_bundle_fixture();
    let trust_vc = base.requests[0].stable_digest();
    let chc = base.requests[PENDING_CHC_REQUEST].stable_digest();
    let row = |bound, request_digest| {
        Some(CoverageAssurance {
            bound,
            request_digest,
        })
    };
    let cases = [
        ("no row", None),
        (
            "Unbounded citing nothing",
            row(CoverageBound::Unbounded, ProofDigest::sha256([7u8; 32])),
        ),
        (
            "Unbounded citing the TrustVc request",
            row(CoverageBound::Unbounded, trust_vc),
        ),
        (
            "depth-1 citing the pending CHC request",
            row(CoverageBound::UnwindBounded { depth: 1 }, chc),
        ),
        (
            "model-bounded",
            row(CoverageBound::ModelBounded { size: 4 }, chc),
        ),
        ("recorded Unrecorded", row(CoverageBound::Unrecorded, chc)),
    ];
    for (label, assurance) in cases {
        let mut bundle = native_bundle_fixture();
        bundle.module.proof_certificates[0].assurance = assurance;
        reseal_module_identity(&mut bundle);
        let evidence = sole_evidence(&consume(&bundle, label));
        let admission = evidence.release_admission();
        assert!(
            established_and_admitted(admission),
            "{label}: {:?}",
            admission.rejection_reasons()
        );
        assert_eq!(
            admission_wire(admission)["coverage_basis"],
            kernel_basis(&bundle, 0),
            "{label}"
        );
        assert_eq!(assert_id_and_formula_liars_refused(&bundle), 1, "{label}");
    }

    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustMc(mut bmc) = bundle.requests[PENDING_CHC_REQUEST].clone()
    else {
        panic!("fixture request {PENDING_CHC_REQUEST} should be TrustMc");
    };
    bmc.id = trust_ir::request::NativeRequestId::new(
        bundle
            .requests
            .iter()
            .map(|request| request.id().index())
            .max()
            .expect("the fixture has requests")
            + 1,
    );
    bmc.mode = TrustMcVerificationMode::BoundedModelCheck;
    bmc.obligations = vec![ProofId::new(0)];
    bundle
        .requests
        .push(NativeVerificationRequest::TrustMc(bmc));
    let evidence = sole_evidence(&consume(&bundle, "BMC sibling request"));
    assert!(
        established_and_admitted(evidence.release_admission()),
        "a bounded run beside a kernel-replayed certificate contests nothing: {:?}",
        evidence.release_admission().rejection_reasons()
    );
    assert_eq!(assert_id_and_formula_liars_refused(&bundle), 1);
}

/// A/B. `Certified` is judged ON ITS REPLAY. The baseline certificate on a
/// `Certified` obligation is admitted (it used to be refused
/// `obligation_trusted`: the status was filed as `Trusted`), and the label
/// alone admits nothing — an SMT certificate cited on the same `Certified`
/// obligation is refused for its coverage, not waved through by the status.
#[test]
fn a_certified_obligation_is_judged_on_its_replay() {
    let mut bundle = native_bundle_fixture();
    bundle.module.proof_obligations[0].status = ProofStatus::Certified;
    reseal_module_identity(&mut bundle);
    let evidence = sole_evidence(&consume(&bundle, "Certified, kernel-replayed"));
    assert_eq!(evidence.obligation_status(), "certified");
    assert!(
        established_and_admitted(evidence.release_admission()),
        "{:?}",
        evidence.release_admission().rejection_reasons()
    );
    assert!(evidence
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
    assert_eq!(assert_id_and_formula_liars_refused(&bundle), 1);

    let smt = add_sibling_certificate(&mut bundle, "trust_vc-smt", smt_proof(), None);
    cite_certificates(&mut bundle, vec![smt]);
    let evidence = sole_evidence(&consume(&bundle, "Certified, SMT"));
    assert_eq!(evidence.obligation_status(), "certified");
    assert_eq!(
        labels(evidence.release_admission().rejection_reasons()),
        ["certificate_coverage_basis_not_this_certificate"]
    );
}

/// A/B. The retired row rule's coverage labels still DECODE — as
/// `certificate_coverage_not_judged`, once — so a payload it wrote stays
/// readable, and rejected.
#[test]
fn retired_coverage_labels_decode_as_not_judged() {
    let decoded: TrustVcNativeTrustIrCertificateAdmission = serde_json::from_value(json!({
        "status": "admissible",
        "coverage_established": true,
        "rejection_reasons": [
            "certificate_coverage_unrecorded",
            "certificate_coverage_request_unknown",
            "certificate_coverage_obligation_not_requested",
            "certificate_coverage_bound_mismatch",
            "certificate_coverage_contested",
            "certificate_coverage_not_established_for_module",
        ],
    }))
    .expect("a payload of the previous rule decodes");
    assert!(!decoded.is_admissible());
    assert!(!decoded.coverage_established());
    assert_eq!(
        labels(decoded.rejection_reasons()),
        ["certificate_coverage_not_judged"]
    );
}
