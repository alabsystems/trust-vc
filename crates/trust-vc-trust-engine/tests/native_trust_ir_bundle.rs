// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_ir::proof::{
    clean_cic_lineage_digest, CoverageAssurance, CoverageBound, SpecObligationRef,
};
use trust_ir::request::{
    NativeAssertionId, NativeEvidenceBundle, NativeVerificationBundle, NativeVerificationRequest,
    NativeVerifierSuite, TrustVcTrustedEvidencePolicy, TrustVcVerificationMode,
};
use trust_ir::{FuncId, ObligationKind, ProofEvidence, ProofId, ProofObligation, ProofStatus};
use trust_vc_trust_engine::{
    TrustEngineError, TrustVcNativeArtifactAdmissionStatus, TrustVcNativeArtifactExpectation,
    TrustVcNativeArtifactRejection, TrustVcNativeArtifactReplayStatus,
    TrustVcNativeCompilerFactRef, TrustVcNativeCompilerFactsBinding, TrustVcNativeObligationCause,
    TrustVcNativeProofArtifact, TrustVcNativeProofArtifactInput, TrustVcNativeSolverIdentity,
    TrustVcNativeToolIdentity, TrustVcNativeTrustIrBundleReport,
    TrustVcNativeTrustIrCertificateAdmissionStatus, TrustVcNativeTrustIrCertificateEvidence,
    TrustVcNativeTrustIrCertificateRejection, TrustVcNativeTrustIrDischargeOutcome,
    TrustVcNativeTrustIrDischargeStatus, TrustVcNativeTrustIrEvidenceKind,
    TrustVcNativeTrustIrInputKind, TrustVcNativeTrustIrPremise, TrustVcNativeTrustIrPremiseKind,
    TrustVcNativeTrustIrReplayMetadataSource, TrustVcNativeTrustIrRequestMode,
    TrustVcNativeTrustIrVerdict, TrustVcNativeVerifierSuite, TrustVcTrustEngine,
};
use trust_vc_trust_engine::{TrustVcNativeCoverageBasis, TrustVcNativeKernelClaimFamily};

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/admission_edits.rs"]
mod admission_edits;
use admission_baseline::{
    add_sibling_certificate, assertion_atoms_mut, cite_certificates,
    edit_replayed_obligation_keeping_atom, install_bridge_atoms, install_payload_assertion_id,
    native_bundle_fixture, reseal_clean_cic_lineage, reseal_module_identity,
    set_compiler_fact_assertion_id, sync_assertion_atoms, unatomed_bundle_fixture,
    PAYLOAD_ID_REFUSAL, PENDING_CHC_REQUEST, TRUST_WP_SP_REQUEST,
};
use admission_edits::{
    assert_id_and_formula_liars_refused, corrupt_clean_cic_term, relabel_assertion_identity,
    steal_assertion_identity,
};

/// THE OLD SHAPE, IN THE PRODUCER'S OTHER PAYLOAD FORM.
///
/// Trust's `trust-ir-bridge` writes the source record as the WHOLE payload
/// under `trust.trust_ir.obligation-source.v1` for every obligation whose
/// predicate it could not render machine-readably — a non-contract MIR assert
/// with no reconstructed safety formula, an unparseable contract, the
/// whole-function panic-freedom aggregate. The bytes below are exactly
/// `source_json()`'s.
///
/// DERIVED, NEVER FORGED, in the same way as
/// `admission_baseline::install_payload_assertion_id`: the string rendering is
/// the obligation's OWN `source.assertion_id`, the numeric one is the number
/// installed on the compiler fact and on the request's atom, which is also
/// rewritten to the new formula, and every digest is recomputed with trust-ir's
/// own functions.
fn install_top_level_payload_assertion_id(
    bundle: &mut NativeVerificationBundle,
    obligation_index: usize,
    native_assertion_id: u32,
) {
    let obligation = &mut bundle.module.proof_obligations[obligation_index];
    let obligation_id = obligation.id;
    let assertion_id = obligation
        .source
        .as_ref()
        .expect("corpus obligations carry a source identity")
        .assertion_id
        .clone();
    let formula = obligation
        .formula
        .as_mut()
        .expect("corpus obligations carry a formula");
    formula.schema = "trust.trust_ir.obligation-source.v1".to_string();
    formula.payload = serde_json::json!({
        "source_id": "mir-assert:probe:bb0:0",
        "assertion_id": assertion_id,
        "native_assertion_id": native_assertion_id,
        "span": {
            "file": "probe.rs",
            "line_start": 1,
            "col_start": 1,
            "line_end": 1,
            "col_end": 2,
        },
    })
    .to_string();
    // `smtlib`/`sort` are left ALONE. The bridge does emit this shape with both
    // `None`, but upstream's Clean-kernel authority grounds its goal from
    // `formula.smtlib.unwrap_or(payload)`, so clearing them here would unbind
    // the corpus certificate for a reason that has nothing to do with the
    // identity rendering this helper is about (measured: "rejects TrustVc
    // certificate evidence 0/trust_vc with non-discharged status discharged").
    set_compiler_fact_assertion_id(bundle, obligation_id, native_assertion_id);
    sync_assertion_atoms(bundle, obligation_id);
    reseal_clean_cic_lineage(bundle, obligation_id);
    reseal_module_identity(bundle);
}

/// The admission baseline turned into a DISCHARGE request.
///
/// Three edits, each of which is what a compiler-minted discharge request
/// actually looks like:
///   * mode `DischargeProofObligations`,
///   * NO input certificates — the point of the mode is that the proof does not
///     exist yet,
///   * NO input TrustVc evidence bundle — that is the mode's OUTPUT. (Upstream
///     also refuses an evidence bundle whose mode disagrees with its request's,
///     so leaving the import-mode one in place fails validation outright.)
///   * NO certificate for the obligation anywhere in the request's lineage
///     closure, for the same reason the request carries none (refused
///     otherwise: `discharge_request_whose_lineage_already_certifies_its_obligation_is_refused`).
///
/// `function` names the module's only function, which is what the lowering will
/// read once it exists. trust-ir refuses a discharge request citing an
/// obligation that is not sited in that function, so obligation 0 is scoped to
/// it and sited at its `Return` (`checked_add`'s body is `[BinOp, Return]`).
fn discharge_bundle_fixture() -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    let function = FuncId::new(0);
    {
        let obligation = &mut bundle.module.proof_obligations[0];
        obligation.function = Some(function);
        obligation.site = Some(trust_ir::ObligationSite::new(
            function,
            trust_ir::BlockId::new(0),
            1,
        ));
    }
    reseal_clean_cic_lineage(&mut bundle, ProofId::new(0));
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.mode = TrustVcVerificationMode::DischargeProofObligations;
    request.certificates.clear();
    request.function = Some(FuncId::new(0));
    for node in &mut bundle.lineage.nodes {
        node.certificates
            .retain(|certificate| certificate.obligation != ProofId::new(0));
    }
    bundle
        .evidence_bundles
        .retain(|evidence| !matches!(evidence, NativeEvidenceBundle::TrustVc(_)));
    reseal_module_identity(&mut bundle);
    bundle
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
    // The compiler fact numbers this assertion 1, and the TrustVc request's
    // `Assertion` replay atom for obligation 0 states the same number beside
    // the obligation's own formula, so the row publishes it. Without the atom
    // it publishes none:
    // `the_upstream_corpus_publishes_no_assertion_id_because_it_renders_it_once`.
    assert_eq!(evidence.native_assertion_id(), Some(1));
    assert_eq!(evidence.independent_assertion_id(), Some(1));
    assert_eq!(
        evidence.trust_ir_module_digest(),
        report.trust_ir_module_digest()
    );
    // Tracks the corpus fixture's obligation 0, which is a Postcondition. This
    // pins the kind ROUND-TRIP (module obligation -> evidence), so a drift here
    // means either the corpus changed shape or the engine stopped carrying the
    // kind through — check which before editing the string.
    assert_eq!(evidence.obligation_kind(), "postcondition");
    assert_eq!(evidence.obligation_status(), "discharged");
    // Corpus fixture's obligation 0 carries an smtlib2 formula. Like the kind
    // above, this pins the round-trip, not the literal — if it drifts, check
    // whether the corpus changed or the engine stopped carrying the schema.
    assert_eq!(evidence.formula_schema(), Some("smtlib2"));
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
    assert_eq!(evidence.suite_identity().producer(), "trust_vc-2026-04-29");
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
    assert_eq!(solver.revision(), Some("trust_vc-proof-kernel"));
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
        TrustVcNativeObligationCause::Postcondition
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
    // The corpus certificate is a kernel-recheckable CIC term, and the report
    // now says so instead of flattening it to `Trusted`. `trusted()` stays
    // false: a CleanCic term is checked, not taken on faith.
    assert_eq!(
        evidence.evidence_kind(),
        TrustVcNativeTrustIrEvidenceKind::CleanCic
    );
    assert!(!evidence.trusted());
    // The baseline row is release-admissible: its formula is one SMT-LIB text
    // and its request's atom corroborates its assertion id.
    assert_eq!(
        evidence.release_admission().status(),
        TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
    );
    assert!(evidence.release_admission().rejection_reasons().is_empty());
    // Coverage was DERIVED from the kernel replay of this very certificate
    // (basis K), not read from a row: the baseline records none.
    assert!(certificate.assurance.is_none());
    assert!(evidence.release_admission().coverage_established());
    assert_eq!(
        evidence.release_admission().coverage_basis(),
        Some(&TrustVcNativeCoverageBasis::KernelReplayedClaim {
            obligation_id: 0,
            prover: "trust_vc".to_string(),
            evidence_digest: certificate.evidence_digest().to_string(),
            family: TrustVcNativeKernelClaimFamily::ContractGroundDecision,
        })
    );
    assert_eq!(evidence.release_admission().coverage_detail(), None);
    assert!(evidence
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );
    TrustVcTrustEngine::new()
        .validate_native_trust_ir_bundle(&bundle)
        .expect("an admitted rollup validates");
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

/// The baseline certificate becomes a typed proof artifact stamped with its
/// assertion id, every binding field is the evidence's own, and the artifact
/// is ACCEPTED, against itself and against an expectation built from it.
///
/// Its liar twins are refused: the atom's id forged (L1) and the atom asserting
/// another formula than the certificate's obligation (L3). So is the OLD shape
/// (L9), the id rendered inside a `trust-types.Formula@1` payload, which is no
/// SMT-LIB text, so trust-ir never replays its certificate.
#[test]
fn admits_native_trust_ir_certificate_as_typed_proof_artifact() {
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];

    assert_eq!(evidence.native_assertion_id(), Some(1));
    assert_eq!(evidence.independent_assertion_id(), Some(1));
    assert_eq!(evidence.compiler_facts_binding().assertion_id(), Some(1));
    assert_eq!(
        evidence.release_admission().status(),
        TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
    );
    assert!(evidence.release_admission().is_admissible());
    assert!(evidence.release_admission().rejection_reasons().is_empty());

    let artifact = evidence.admit_native_proof_artifact();
    let admission = artifact.admission();

    assert_eq!(artifact.assertion_id(), "1");
    assert_eq!(
        artifact.trust_ir_module_digest(),
        evidence.trust_ir_module_digest()
    );
    assert_eq!(artifact.request_digest(), evidence.request_digest());
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

    assert_eq!(assert_id_and_formula_liars_refused(&bundle), 1);

    let mut payload_id = native_bundle_fixture();
    install_payload_assertion_id(&mut payload_id, 0, 1);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&payload_id)
        .expect_err("a payload that renders the id is no SMT-LIB text and is not replayed");
    assert!(error.to_string().contains(PAYLOAD_ID_REFUSAL), "{error}");
}

/// LIAR L2: the compiler fact's number forged, the request's atom kept. The atom
/// is the certificate's own statement of its id, so the two disagree and the
/// bundle is refused (trust-ir first; trust-vc's own gate is pinned by
/// `native_assertion_id::tests::a_forged_compiler_fact_refuses_the_bundle`).
#[test]
fn a_forged_compiler_fact_beside_the_atom_is_refused() {
    let mut bundle = native_bundle_fixture();
    bundle.compiler_facts.obligation_sources[0].assertion_id = Some(NativeAssertionId::new(2));
    reseal_module_identity(&mut bundle);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a compiler fact the atom contradicts must be refused");
    assert!(
        error
            .to_string()
            .contains("does not match obligation 0 source assertion"),
        "{error}"
    );
}

/// LIAR L4: the atom's formula differs from its obligation's in its BINDINGS
/// alone. Neither the atom's payload digest nor the request digest covers
/// bindings, and trust-ir does not compare them, so the bundle is well formed
/// upstream; trust-vc compares whole formulas and refuses it.
#[test]
fn an_atom_whose_formula_bindings_alone_differ_is_refused() {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let mut bundle = native_bundle_fixture();
    for atom in assertion_atoms_mut(&mut bundle, 0, ProofId::new(0)) {
        atom.formula.bindings.push((
            "x".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        ));
    }
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("an atom whose bindings differ asserts another formula");
    assert!(
        matches!(
            error,
            TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree { .. }
        ),
        "refused by trust-vc's atom gate: {error}"
    );
}

/// LIAR L5: the OBLIGATION's formula edited and its certificate honestly
/// re-bound to it (lineage recomputed, bundle resealed), while the request's
/// atom still asserts the formula the obligation stated before. The atom and
/// the certificate no longer state one formula, so the bundle is refused. The
/// same edit with the atom rewritten is the control.
#[test]
fn an_obligation_edited_under_a_stale_atom_is_refused() {
    let edit = |obligation: &mut ProofObligation| {
        let formula = obligation.formula.as_mut().expect("baseline formula");
        formula.payload = "(>= 7 0)".to_string();
        formula.smtlib = Some("(>= 7 0)".to_string());
    };
    let mut stale = native_bundle_fixture();
    edit_replayed_obligation_keeping_atom(&mut stale, edit);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&stale)
        .expect_err("a stale atom must be refused");
    assert!(
        matches!(
            error,
            TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree { .. }
        ),
        "refused by trust-vc's atom gate: {error}"
    );

    let mut honest = native_bundle_fixture();
    admission_baseline::edit_replayed_obligation(&mut honest, edit);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&honest)
        .expect("the same edit with the atom rewritten is well formed");
    assert!(
        report.requests()[0].proof_evidence()[0]
            .release_admission()
            .is_admissible(),
        "{:?}",
        report.requests()[0].proof_evidence()[0].release_admission()
    );
}

/// LIAR L8: the atom edited and the request NOT resealed. The TrustVc evidence
/// bundle still quotes the request digest from before the edit, and trust-ir
/// recomputes it: the atom is bound to the certificate by that digest.
#[test]
fn an_atom_edited_without_resealing_the_request_is_refused() {
    let mut bundle = native_bundle_fixture();
    for atom in assertion_atoms_mut(&mut bundle, 0, ProofId::new(0)) {
        atom.span = None;
    }
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("an atom edited under a stale request digest must be refused");
    assert!(
        error.to_string().contains("request digest"),
        "refused for the request digest: {error}"
    );
}

/// THE RESIDUAL, pinned so that closing it flips this test. Every check
/// compares renderings inside one bundle; none shows that the number is the
/// COMPILER's. Move the compiler fact AND the request's atom to a number no
/// other assertion carries and reseal, and the certificate is admitted under
/// the moved number while the obligation's own string still names
/// `rust-assertion:1`. Binding the number to the string would mean enforcing one
/// producer's derivation (`stable_u32_id`; see `native_assertion_id`'s module
/// docs).
#[test]
fn the_residual_a_fact_and_atom_moved_together_are_admitted_under_the_moved_number() {
    let mut bundle = native_bundle_fixture();
    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(0), 4242);
    reseal_module_identity(&mut bundle);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("an internally consistent bundle is consumed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), Some(4242));
    assert!(evidence.release_admission().is_admissible());
    assert_eq!(
        bundle.module.proof_obligations[0]
            .source
            .as_ref()
            .map(|source| source.assertion_id.as_str()),
        Some("rust-assertion:1")
    );
}

/// An artifact bound to an assertion id the compiler fact does not name is
/// refused for exactly that. The ids here come from the caller's side table:
/// 43 disagrees with the compiler fact's 1, and 1 agrees with it.
#[test]
fn rejects_native_trust_ir_artifact_when_assertion_id_disagrees_with_compiler_source() {
    let bundle = native_bundle_fixture();
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
        Some(1)
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

    assert!(evidence.admit_proof_artifact("1").admission().is_accepted());
}

/// The row for obligation 0 publishes no assertion id, and neither artifact
/// path accepts one: not the row's own, and not `number` named by a caller.
#[track_caller]
fn assert_obligation_0_publishes_no_id(report: &TrustVcNativeTrustIrBundleReport, number: u32) {
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 0);
    assert_eq!(evidence.native_assertion_id(), None, "{evidence:?}");
    assert_eq!(evidence.independent_assertion_id(), None, "{evidence:?}");
    assert_eq!(
        evidence.release_admission().rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::MissingAssertionId],
        "only the id is missing: {evidence:?}"
    );

    let artifacts = report.admit_native_proof_artifacts();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(artifacts[0].assertion_id(), "", "{:?}", artifacts[0]);
    assert!(
        !artifacts[0].admission().is_accepted(),
        "{:?}",
        artifacts[0]
    );
    assert!(
        artifacts[0]
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{:?}",
        artifacts[0]
    );

    let named = evidence.admit_proof_artifact(number.to_string());
    assert_eq!(named.assertion_id(), "", "{named:?}");
    assert!(!named.admission().is_accepted(), "{named:?}");
    assert!(
        named
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{named:?}"
    );
}

/// ROUND 13, THE BLOCKER, as liars. Obligation 0 steals obligation 1's whole
/// assertion identity (`rust-assertion:2`, compiler fact 2, atom id 2), or
/// obligation 2's (`rust-assertion:0`, 0, 0); lineage and module are resealed.
/// Every input gate passes: the strings agree with the numbers, B -> A is a
/// function, and the atom equals its fact. The review measured obligation 0's
/// certificate for `(>= 5 0)` ADMITTED under the stolen number while the
/// victim, still `Pending`, carried it for another formula. Two obligations
/// with different formulas and public ids now carry the number, so it names
/// neither, and nothing is published.
#[test]
fn a_stolen_assertion_identity_publishes_no_id() {
    for victim in [ProofId::new(1), ProofId::new(2)] {
        let mut bundle = native_bundle_fixture();
        let stolen = steal_assertion_identity(&mut bundle, ProofId::new(0), victim);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect("every rendering agrees, so the bundle is consumed");
        assert_obligation_0_publishes_no_id(&report, stolen);
    }
}

/// ROUND 13, THE VARIANT: obligations 0 and 1 relabeled to ONE fresh identity
/// (`rust-assertion:9`, 9). The review measured it admitted under 9 while 9
/// named two formulas. Round 14 re-measured it, and the same with obligation 2
/// as the partner (its TrustWp atom moved to 9 too), refused.
#[test]
fn one_fresh_assertion_identity_on_two_obligations_publishes_no_id() {
    for partner in [ProofId::new(1), ProofId::new(2)] {
        let mut bundle = native_bundle_fixture();
        relabel_assertion_identity(
            &mut bundle,
            &[ProofId::new(0), partner],
            "rust-assertion:9",
            9,
        );
        set_trust_wp_atom_assertion_id(&mut bundle, partner, 9);
        reseal_module_identity(&mut bundle);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect("every rendering agrees, so the bundle is consumed");
        assert_obligation_0_publishes_no_id(&report, 9);
    }
}

/// CONTROL for the two liars above, and the residual's other shape. The same
/// relabel on obligation 0 ALONE (string, fact and atom moved together to a
/// fresh identity) is admitted under the fresh number: the helper leaves a
/// well-formed bundle, so the refusals above are the ambiguity rule's and not
/// a broken reseal. It is also the residual with the string moved too: no
/// field in the bundle says which number the compiler gave this assertion
/// (see `native_assertion_id`'s module docs).
#[test]
fn the_residual_one_obligation_relabeled_to_a_fresh_identity_is_admitted() {
    let mut bundle = native_bundle_fixture();
    relabel_assertion_identity(&mut bundle, &[ProofId::new(0)], "rust-assertion:9", 9);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("an internally consistent bundle is consumed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), Some(9));
    assert!(evidence.release_admission().is_admissible());
    let artifacts = report.admit_native_proof_artifacts();
    assert_eq!(artifacts[0].assertion_id(), "9");
    assert!(artifacts[0].admission().is_accepted(), "{:?}", artifacts[0]);
    assert!(evidence.admit_proof_artifact("9").admission().is_accepted());
}

/// ROUND 13, THE SECOND HOLE, as liars. `admit_proof_artifact(id)` compared a
/// caller-named id with the compiler fact alone. It never consulted the atom,
/// the row's own `MissingAssertionId`, or the ambiguity rule, so a row the
/// export seam refused still minted an ACCEPTED artifact for any id the caller
/// named that equalled the fact. It now goes through the row's rule.
#[test]
fn a_caller_named_id_the_row_does_not_license_is_refused() {
    let engine = TrustVcTrustEngine::new();

    // NO ATOM (the verbatim corpus shape). The row is refused
    // `missing_assertion_id` and nothing else, its coverage is established,
    // and "1" is the compiler fact's number: this used to be accepted.
    let report = engine
        .consume_native_trust_ir_bundle(&unatomed_bundle_fixture())
        .expect("the corpus shape is well formed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), None);
    assert_eq!(
        evidence.release_admission().rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::MissingAssertionId]
    );
    assert_eq!(evidence.compiler_facts_binding().assertion_id(), Some(1));
    let named = evidence.admit_proof_artifact("1");
    assert_eq!(named.assertion_id(), "", "{named:?}");
    assert_eq!(
        named.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        named
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{named:?}"
    );

    // SHARED: 9 names obligations 0 and 1 at once (see
    // `one_fresh_assertion_identity_on_two_obligations_publishes_no_id`, whose
    // helper also calls `admit_proof_artifact("9")`).
    let mut shared = native_bundle_fixture();
    relabel_assertion_identity(
        &mut shared,
        &[ProofId::new(0), ProofId::new(1)],
        "rust-assertion:9",
        9,
    );
    let report = engine
        .consume_native_trust_ir_bundle(&shared)
        .expect("every rendering agrees, so the bundle is consumed");
    let named = report.requests()[0].proof_evidence()[0].admit_proof_artifact("9");
    assert_eq!(named.assertion_id(), "", "{named:?}");
    assert!(!named.admission().is_accepted(), "{named:?}");

    // STOLEN: on the admitted baseline, which licenses 1, a caller names
    // obligation 1's number 2 or obligation 2's number 0.
    let report = engine
        .consume_native_trust_ir_bundle(&native_bundle_fixture())
        .expect("the baseline is admitted");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), Some(1));
    for stolen in ["2", "0"] {
        let named = evidence.admit_proof_artifact(stolen);
        assert!(!named.admission().is_accepted(), "{stolen}: {named:?}");
        assert!(
            named
                .admission()
                .rejection_reasons()
                .contains(&TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch),
            "{stolen}: {named:?}"
        );
    }
    // Another spelling of the licensed number is not a second name for it.
    for spelling in ["01", "+1"] {
        let named = evidence.admit_proof_artifact(spelling);
        assert_eq!(named.assertion_id(), "", "{spelling}: {named:?}");
        assert!(!named.admission().is_accepted(), "{spelling}: {named:?}");
        assert!(
            named
                .admission()
                .rejection_reasons()
                .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
            "{spelling}: {named:?}"
        );
    }
    // CONTROL: the licensed id is exactly the row's own artifact, accepted.
    assert_eq!(
        evidence.admit_proof_artifact("1"),
        evidence.admit_native_proof_artifact()
    );
    assert!(evidence.admit_proof_artifact("1").admission().is_accepted());
}

/// ROUND 13, THE SECOND HOLE, the payload-only id. The discharge fixture's
/// payload renders obligation 1's number (rendering C, `native_assertion_id`
/// 1, equal to the compiler fact) and its request's atoms are stripped, so no
/// atom corroborates it. The row publishes nothing, and a caller naming the
/// payload's number is refused for the id, not only for the produced
/// certificate's coverage.
#[cfg(feature = "proof-certificates")]
#[test]
fn a_caller_named_id_only_a_payload_renders_is_refused() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    strip_request_atoms(&mut bundle);
    reseal_module_identity(&mut bundle);
    let payload = &bundle.module.proof_obligations[1]
        .formula
        .as_ref()
        .expect("fixture carries formulas")
        .payload;
    assert!(
        payload.contains("\"native_assertion_id\":1"),
        "the payload renders the number: {payload}"
    );

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a bundle with no atom is well formed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    assert_eq!(evidence.compiler_facts_binding().assertion_id(), Some(1));
    assert_eq!(evidence.native_assertion_id(), None, "{evidence:?}");
    let named = evidence.admit_proof_artifact("1");
    assert_eq!(named.assertion_id(), "", "{named:?}");
    assert!(!named.admission().is_accepted(), "{named:?}");
    assert!(
        named
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{named:?}"
    );
}

/// The admission baseline plus obligation 7: a clone of obligation 2 with its
/// own public id `vc:checked_add:assert:7` and string `rust-assertion:7`, NO
/// compiler fact, listed by no request, whose formula is `payload` under
/// `schema`. The round-14 review's carrier.
fn with_unrequested_factless_obligation(schema: &str, payload: &str) -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    let mut extra = bundle.module.proof_obligations[2].clone();
    extra.id = ProofId::new(7);
    let source = extra
        .source
        .as_mut()
        .expect("corpus obligations carry a source identity");
    if let Some(public) = source.public.as_mut() {
        public.obligation_id = "vc:checked_add:assert:7".to_string();
    }
    source.assertion_id = "rust-assertion:7".to_string();
    let formula = extra
        .formula
        .as_mut()
        .expect("corpus obligation 2 states a formula");
    formula.schema = schema.to_string();
    formula.payload = payload.to_string();
    formula.smtlib = None;
    bundle.module.proof_obligations.push(extra);
    reseal_module_identity(&mut bundle);
    bundle
}

const FORMULA_SCHEMA: &str = "trust-types.Formula@1";
const SOURCE_RECORD_SCHEMA: &str = "trust.trust_ir.obligation-source.v1";

/// The round-14 review's unreadable spellings of obligation 0's number 1.
const ROUND_14_UNREADABLE: &[(&str, &str, &str)] = &[
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
        "C as the string \"1\"",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1.0}}"#,
        "C as the float 1.0",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":4294967297}}"#,
        "C as 2^32 + 1, which truncates to 1 as a u32",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1},"#,
        "a truncated payload that is not JSON",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":"native_assertion_id=1"}"#,
        "a source block that is not an object",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"assertion_id":7}}"#,
        "D as a number, not a string",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":"1","assertion_id":"rust-assertion:7"}"#,
        "top-level C as the string \"1\"",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":1.0,"assertion_id":"rust-assertion:7"}"#,
        "top-level C as the float 1.0",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":4294967297,"assertion_id":"rust-assertion:7"}"#,
        "top-level C as 2^32 + 1",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#""native_assertion_id=1""#,
        "a top-level document that is not an object",
    ),
];

/// ROUND 14, as liars. An unrequested obligation with no compiler fact spells
/// obligation 0's number 1 UNREADABLY in its payload, in either payload shape.
/// The review measured every one of these ADMITTED under 1, with default
/// features and with proof-certificates, while the same number written as a
/// `u32` was refused: the ambiguity index counted only numbers that read as a
/// `u32`, so an unreadable one made its obligation no carrier at all. trust-ir
/// cannot see it (the obligation is requested by nobody and has no fact), and
/// the bundle input gate refuses an unreadable payload only beside an A. An
/// unreadable rendering might carry any number, so it now withdraws every id
/// the bundle would publish.
#[test]
fn an_unreadable_payload_on_an_unrequested_obligation_publishes_no_id() {
    for (schema, payload, label) in ROUND_14_UNREADABLE {
        let bundle = with_unrequested_factless_obligation(schema, payload);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{label}: the bundle is still consumed: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);
    }
}

/// CONTROLS for the liar above. The same carrier with a READABLE number: 1 as
/// a `u32` is counted and refused (it always was), and an unused readable
/// number leaves obligation 0 admitted under 1, so the refusals above are the
/// unreadable rule's and not the added obligation's.
#[test]
fn a_readable_payload_on_an_unrequested_obligation_withdraws_only_its_number() {
    for (schema, shared, unused) in [
        (
            FORMULA_SCHEMA,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1}}"#,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7}}"#,
        ),
        (
            SOURCE_RECORD_SCHEMA,
            r#"{"native_assertion_id":1,"assertion_id":"rust-assertion:7"}"#,
            r#"{"native_assertion_id":7,"assertion_id":"rust-assertion:7"}"#,
        ),
    ] {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_unrequested_factless_obligation(schema, shared))
            .expect("a readable carrier is well formed");
        assert_obligation_0_publishes_no_id(&report, 1);

        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_unrequested_factless_obligation(schema, unused))
            .expect("a readable carrier is well formed");
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert_eq!(evidence.native_assertion_id(), Some(1), "{schema}");
        assert!(
            evidence.release_admission().is_admissible(),
            "{schema}: {evidence:?}"
        );
        assert!(evidence.admit_proof_artifact("1").admission().is_accepted());
    }
}

/// ROUND 14, the discharge lane. The round-9 bundle (an unrequested row whose
/// payload is not JSON, which does not refuse the bundle) used to publish the
/// discharged row's id 1 beside that unreadable payload. It now publishes
/// none. The control is the same fixture without the unreadable row.
#[cfg(feature = "proof-certificates")]
#[test]
fn an_unreadable_payload_withdraws_the_discharged_rows_id() {
    let control = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&control)
        .expect("the discharge fixture is well formed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    assert_eq!(
        evidence.native_assertion_id(),
        Some(1),
        "control: {evidence:?}"
    );

    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(7),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "an unrequested obligation whose payload spells 1 unreadably",
        )
        .with_source(trust_ir::ProofObligationSourceIdentity::new(
            "probe",
            "rust-assertion:7",
        ))
        .with_formula(trust_ir::ProofFormula {
            schema: FORMULA_SCHEMA.to_string(),
            payload: r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#
                .to_string(),
            smtlib: None,
            sort: None,
            bindings: Vec::new(),
        }),
    );
    reseal_module_identity(&mut bundle);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("no A beside the unreadable payload, so no bundle refusal");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    assert_eq!(evidence.native_assertion_id(), None, "{evidence:?}");
    assert_eq!(evidence.independent_assertion_id(), None, "{evidence:?}");
    assert!(
        evidence
            .release_admission()
            .rejection_reasons()
            .contains(&TrustVcNativeTrustIrCertificateRejection::MissingAssertionId),
        "{evidence:?}"
    );
    let named = evidence.admit_proof_artifact("1");
    assert!(!named.admission().is_accepted(), "{named:?}");
}

/// A key repeated inside one JSON object, in the payload shapes the round-15
/// review measured admitted, plus two of the same kind: the repeated key
/// spelled with an escape, and a key repeated outside the source record.
const REPEATED_KEY_PAYLOADS: &[(&str, &str, &str)] = &[
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1","native_assertion_id":7}}"#,
        "an unreadable C hidden by a later readable 7",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1,"native_assertion_id":7}}"#,
        "C twice, 1 then 7",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1},"source":{"native_assertion_id":7}}"#,
        "the source block twice, 1 then 7",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1},"source":{}}"#,
        "the source block twice, 1 then empty",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":1,"native_assertion_id":7,"assertion_id":"rust-assertion:7"}"#,
        "top-level C twice, 1 then 7",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1,"native\u005fassertion_id":7}}"#,
        "C twice, the second key spelled with an escape",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true,"Bool":false},"source":{"native_assertion_id":7}}"#,
        "a key repeated outside the source record",
    ),
];

/// ROUND 15, as liars: a repeated JSON key hides a rendering. The payload was
/// read through `serde_json::Value`, which keeps the LAST value of a repeated
/// key and raises no error, so the round-14 liar (an unrequested obligation
/// with no compiler fact rendering obligation 0's number) plus one trailing
/// duplicate key read as the harmless 7, and obligation 0 was ADMITTED under 1
/// through both artifact paths. RFC 8259 leaves which value a reader takes
/// unspecified, so such a document has no single reading: it is unreadable,
/// and withdraws every id.
#[test]
fn a_payload_that_repeats_a_key_publishes_no_id() {
    for (schema, payload, label) in REPEATED_KEY_PAYLOADS {
        let bundle = with_unrequested_factless_obligation(schema, payload);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{label}: no A, so the bundle is consumed: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);
    }
}

/// ROUND 15, the repeated key beside a compiler fact. Obligation 1 carries
/// A = 2, and its payload renders C twice, 1 then 2. A last-wins reader saw 2,
/// equal to A, so the A-vs-C gate passed; a first-wins reader sees obligation
/// 0's number. An unreadable rendering beside an A refuses the bundle.
#[test]
fn a_repeated_key_beside_a_compiler_fact_refuses_the_bundle() {
    let mut bundle = native_bundle_fixture();
    {
        let formula = bundle.module.proof_obligations[1]
            .formula
            .as_mut()
            .expect("corpus obligations carry a formula");
        formula.schema = FORMULA_SCHEMA.to_string();
        formula.payload = r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:2","native_assertion_id":1,"native_assertion_id":2}}"#.to_string();
        formula.smtlib = None;
    }
    reseal_module_identity(&mut bundle);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a repeated key beside an A must refuse the bundle");
    assert!(
        matches!(
            error,
            TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                obligation_id: 1,
                ..
            }
        ),
        "{error}"
    );
    assert!(error.to_string().contains("repeats a key"), "{error}");
}

/// Round 15's further spellings of obligation 0's number, none a `u32`.
const FURTHER_UNREADABLE_SPELLINGS: &[&str] = &[
    r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1e0}}"#,
    r#"{"formula":{"Bool":true},"source":{"native_assertion_id":-0}}"#,
    r#"{"formula":{"Bool":true},"source":{"native_assertion_id":[1]}}"#,
    r#"{"formula":{"Bool":true},"source":{"native_assertion_id":null}}"#,
    r#"{"formula":{"Bool":true},"source":{"native_assertion_id":{"0":1}}}"#,
    r#"{"formula":{"Bool":true},"source":{"assertion_id":null}}"#,
];

/// ROUND 15, more spellings of obligation 0's number that are not a `u32`.
/// The review found each already refused; they are pinned here so they stay
/// that way.
#[test]
fn further_unreadable_spellings_publish_no_id() {
    for payload in FURTHER_UNREADABLE_SPELLINGS {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_unrequested_factless_obligation(
                FORMULA_SCHEMA,
                payload,
            ))
            .unwrap_or_else(|error| panic!("{payload}: no A, so the bundle is consumed: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);
    }
}

/// A `trust-types.Formula@1` clause whose payload is `payload`, as a function
/// summary or a spec machine states it.
#[cfg(feature = "proof-certificates")]
fn stated_clause(payload: &str) -> trust_ir::ProofFormula {
    stated_clause_under(FORMULA_SCHEMA, payload)
}

/// A clause whose payload is `payload` under `schema`.
fn stated_clause_under(schema: &str, payload: &str) -> trust_ir::ProofFormula {
    trust_ir::ProofFormula {
        schema: schema.to_string(),
        payload: payload.to_string(),
        smtlib: None,
        sort: Some("Bool".to_string()),
        bindings: Vec::new(),
    }
}

/// The admission baseline, with `checked_add` given an unproved summary whose
/// `clause` list (`requires`, `ensures` or `decreases`) holds one clause with
/// `payload`.
fn with_summary_clause(clause: &str, payload: &str) -> NativeVerificationBundle {
    with_summary_clause_under(clause, FORMULA_SCHEMA, payload)
}

/// [`with_summary_clause`] with the clause's payload under `schema`.
fn with_summary_clause_under(
    clause: &str,
    schema: &str,
    payload: &str,
) -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    let mut summary = trust_ir::FunctionSummary {
        params: vec!["lhs".to_string(), "rhs".to_string()],
        ..trust_ir::FunctionSummary::default()
    };
    let formula = stated_clause_under(schema, payload);
    match clause {
        "requires" => summary.requires.push(formula),
        "ensures" => summary.ensures.push(formula),
        "decreases" => summary.decreases.push(formula),
        other => panic!("no summary clause list {other}"),
    }
    bundle.module.functions[0].summary = Some(summary);
    reseal_module_identity(&mut bundle);
    bundle
}

/// The admission baseline plus one `DesignOnly` spec machine that states
/// `payload` as a typed invariant (`"invariant"`) or as an `Always` temporal
/// formula (`"temporal"`).
fn with_spec_formula(site: &str, payload: &str) -> NativeVerificationBundle {
    with_spec_formula_under(site, FORMULA_SCHEMA, payload)
}

/// [`with_spec_formula`] with the formula's payload under `schema`.
fn with_spec_formula_under(site: &str, schema: &str, payload: &str) -> NativeVerificationBundle {
    use trust_ir::spec::{SpecInvariant, SpecModule, SpecTemporal, TemporalForm};
    let mut bundle = native_bundle_fixture();
    let mut machine = SpecModule::new("probe_machine");
    let formula = stated_clause_under(schema, payload);
    match site {
        "invariant" => machine
            .invariants
            .push(SpecInvariant::new("probe_invariant", "true").with_typed(formula)),
        "temporal" => machine.temporal.push(SpecTemporal::new(
            "probe_property",
            TemporalForm::Always(formula),
        )),
        other => panic!("no spec formula site {other}"),
    }
    bundle.module.spec_modules.push(machine);
    reseal_module_identity(&mut bundle);
    bundle
}

/// Obligation 0's number 1 rendered readably, unreadably, and in bytes that
/// are not JSON: the round-15 review's three clause payloads.
const CLAUSE_LIARS: &[(&str, &str)] = &[
    (
        r#"{"formula":{"Bool":true},"source":{"assertion_id":"rust-assertion:5","native_assertion_id":1}}"#,
        "readable C = 1",
    ),
    (
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
        "unreadable C = \"1\"",
    ),
    (r#"{"formula":{"Bool":true},"source":"#, "not JSON"),
];

/// ROUND 15, THE BLOCKER, as liars. A function summary clause that renders
/// obligation 0's number, readably, unreadably or as bytes that are not JSON,
/// left obligation 0 ADMITTED under 1 through both artifact paths: the index
/// read obligation formulas and replay-atom formulas only, never a summary
/// clause, although the docs said an unreadable payload anywhere in the bundle
/// withdraws every id. It is the round-14 atom-formula hole one field over: a
/// number given to a formula no obligation states. Every clause list is
/// covered (`requires`, `ensures`, `decreases`).
#[test]
fn a_number_a_function_summary_clause_renders_publishes_no_id() {
    for clause in ["requires", "ensures", "decreases"] {
        for (payload, label) in CLAUSE_LIARS {
            let report = TrustVcTrustEngine::new()
                .consume_native_trust_ir_bundle(&with_summary_clause(clause, payload))
                .unwrap_or_else(|error| {
                    panic!("{clause} {label}: an unproved summary is well formed: {error}")
                });
            assert_obligation_0_publishes_no_id(&report, 1);
        }
    }
}

/// ROUND 15, the same hole in the other formulas trust-ir's inventory lists: a
/// spec machine's typed invariant and its temporal formulas.
#[test]
fn a_number_a_spec_formula_renders_publishes_no_id() {
    for site in ["invariant", "temporal"] {
        for (payload, label) in CLAUSE_LIARS {
            let report = TrustVcTrustEngine::new()
                .consume_native_trust_ir_bundle(&with_spec_formula(site, payload))
                .unwrap_or_else(|error| {
                    panic!("{site} {label}: a DesignOnly machine is well formed: {error}")
                });
            assert_obligation_0_publishes_no_id(&report, 1);
        }
    }
}

/// CONTROLS for the two liars above. The same clauses rendering an UNUSED
/// number leave obligation 0 admitted under 1, so the refusals are the
/// index's and not a broken bundle.
#[test]
fn a_stated_formula_rendering_an_unused_number_leaves_the_id_published() {
    let unused = r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7}}"#;
    let bundles = ["requires", "ensures", "decreases"]
        .into_iter()
        .map(|clause| (clause, with_summary_clause(clause, unused)))
        .chain(
            ["invariant", "temporal"]
                .into_iter()
                .map(|site| (site, with_spec_formula(site, unused))),
        );
    for (site, bundle) in bundles {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{site}: {error}"));
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert_eq!(evidence.native_assertion_id(), Some(1), "{site}");
        assert!(
            evidence.release_admission().is_admissible(),
            "{site}: {evidence:?}"
        );
        assert!(
            evidence.admit_proof_artifact("1").admission().is_accepted(),
            "{site}"
        );
    }
}

/// ROUND 15, pinned: the thief as the ONLY carrier. Obligation 0 takes
/// obligation 1's identity and obligation 1's number is deleted everywhere
/// (compiler fact and atoms), or obligation 1 keeps no fact number and its
/// payload renders obligation 0's number instead. trust-ir refuses both: a
/// requested obligation must carry a source assertion id.
#[test]
fn a_requested_obligation_stripped_of_its_number_is_refused() {
    let strip_number = |bundle: &mut NativeVerificationBundle, obligation: ProofId| {
        for source in &mut bundle.compiler_facts.obligation_sources {
            if source.obligation == obligation {
                source.assertion_id = None;
            }
        }
    };

    let mut thief_only = native_bundle_fixture();
    steal_assertion_identity(&mut thief_only, ProofId::new(0), ProofId::new(1));
    strip_number(&mut thief_only, ProofId::new(1));
    for request in &mut thief_only.requests {
        let atoms = match request {
            NativeVerificationRequest::TrustVc(request) => {
                &mut request.provenance.replay_context.atoms
            }
            NativeVerificationRequest::TrustMc(request) => {
                &mut request.provenance.replay_context.atoms
            }
            NativeVerificationRequest::TrustWp(request) => {
                &mut request.provenance.replay_context.atoms
            }
        };
        for atom in atoms {
            if atom.obligation == Some(ProofId::new(1)) {
                atom.assertion_id = None;
            }
        }
    }
    reseal_module_identity(&mut thief_only);

    let mut payload_only = native_bundle_fixture();
    strip_number(&mut payload_only, ProofId::new(1));
    {
        let formula = payload_only.module.proof_obligations[1]
            .formula
            .as_mut()
            .expect("corpus obligations carry a formula");
        formula.schema = SOURCE_RECORD_SCHEMA.to_string();
        formula.payload =
            r#"{"native_assertion_id":1,"assertion_id":"rust-assertion:2"}"#.to_string();
        formula.smtlib = None;
    }
    reseal_module_identity(&mut payload_only);

    for (label, bundle) in [("thief only", thief_only), ("payload only", payload_only)] {
        let error = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect_err(label);
        assert!(
            error.to_string().contains("has no source assertion id"),
            "{label}: {error}"
        );
    }
}

/// The discharge fixture's `clamp` given an unproved summary whose `ensures`
/// holds `clause`.
#[cfg(feature = "proof-certificates")]
fn discharge_with_summary_ensures(clause: trust_ir::ProofFormula) -> NativeVerificationBundle {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.functions[0].summary = Some(trust_ir::FunctionSummary {
        ensures: vec![clause],
        params: vec!["x".to_string()],
        ..trust_ir::FunctionSummary::default()
    });
    reseal_module_identity(&mut bundle);
    bundle
}

/// The discharged row (obligation 1, clamp's postcondition): the id it
/// publishes and the independent id it records beside it.
#[cfg(feature = "proof-certificates")]
fn discharged_row_ids(bundle: &NativeVerificationBundle) -> (Option<u32>, Option<u32>) {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(bundle)
        .expect("the discharge bundle is consumed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    (
        evidence.native_assertion_id(),
        evidence.independent_assertion_id(),
    )
}

/// ROUND 15, the discharge lane. With proof-certificates the review measured
/// the discharged row still publishing id 1 (independent id 1) beside a summary
/// clause rendering 1 unreadably, and beside an unrequested obligation whose
/// payload repeats its `native_assertion_id` key; only coverage refused its
/// artifact. The row now publishes no id for any of them.
///
/// And the CONTROL the index rule rests on: a summary clause that restates the
/// obligation's own formula exactly (bindings included), as a proved summary's
/// clause must, is that obligation's rendering, so the row still publishes 1.
/// The same clause with only its predicate changed renders 1 for another
/// formula, and withdraws it.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_discharge_lane_publishes_no_id_beside_a_stray_rendering() {
    let own = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH)
        .module
        .proof_obligations[1]
        .formula
        .clone()
        .expect("fixture carries formulas");
    assert!(
        own.payload.contains("\"native_assertion_id\":1"),
        "the discharged obligation's payload renders its number: {}",
        own.payload
    );
    assert_eq!(
        discharged_row_ids(&discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH)),
        (Some(1), Some(1)),
        "control: the fixture publishes 1"
    );
    assert_eq!(
        discharged_row_ids(&discharge_with_summary_ensures(own.clone())),
        (Some(1), Some(1)),
        "control: a clause that IS the obligation's formula is its rendering"
    );

    let mut restated_elsewhere = own.clone();
    let mut document: serde_json::Value =
        serde_json::from_str(&restated_elsewhere.payload).expect("fixture payloads are JSON");
    document["formula"] = serde_json::json!({ "Bool": true });
    restated_elsewhere.payload = document.to_string();
    assert_ne!(restated_elsewhere, own);
    let mut liars = vec![
        (
            "a summary clause rendering 1 for another formula",
            discharge_with_summary_ensures(restated_elsewhere),
        ),
        (
            "a summary clause rendering 1 unreadably",
            discharge_with_summary_ensures(stated_clause(
                r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
            )),
        ),
    ];
    for payload in [
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1","native_assertion_id":7}}"#,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1,"native_assertion_id":7}}"#,
    ] {
        let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
        bundle.module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(7),
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "an unrequested obligation whose payload repeats a key",
            )
            .with_source(trust_ir::ProofObligationSourceIdentity::new(
                "probe",
                "rust-assertion:7",
            ))
            .with_formula(trust_ir::ProofFormula {
                schema: FORMULA_SCHEMA.to_string(),
                payload: payload.to_string(),
                smtlib: None,
                sort: None,
                bindings: Vec::new(),
            }),
        );
        reseal_module_identity(&mut bundle);
        liars.push(("an unrequested obligation repeating a key", bundle));
    }
    for (label, bundle) in &liars {
        assert_eq!(discharged_row_ids(bundle), (None, None), "{label}");
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(bundle)
            .expect("the discharge bundle is consumed");
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert!(
            evidence
                .release_admission()
                .rejection_reasons()
                .contains(&TrustVcNativeTrustIrCertificateRejection::MissingAssertionId),
            "{label}: {evidence:?}"
        );
        let named = evidence.admit_proof_artifact("1");
        assert_eq!(named.assertion_id(), "", "{label}: {named:?}");
        assert!(!named.admission().is_accepted(), "{label}: {named:?}");
    }
}

/// Moves the `assertion_id` of every atom citing `obligation` in the TrustWp
/// request 4 that states one.
fn set_trust_wp_atom_assertion_id(
    bundle: &mut NativeVerificationBundle,
    obligation: ProofId,
    number: u32,
) {
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[TRUST_WP_SP_REQUEST]
    else {
        panic!("request {TRUST_WP_SP_REQUEST} is the corpus's TrustWp request");
    };
    for atom in &mut request.provenance.replay_context.atoms {
        if atom.obligation == Some(obligation) && atom.assertion_id.is_some() {
            atom.assertion_id = Some(NativeAssertionId::new(number));
        }
    }
}

/// ROUND 14, the same hole one field over: a REPLAY ATOM's formula. The
/// TrustWp request's first `Assumption` atom (it cites obligation 2) is given
/// a payload that renders obligation 0's number 1, readably or not, in a
/// formula that is not obligation 2's own. Neither is refused at the door, and
/// before round 14 the index read no atom formula at all, so obligation 0 was
/// admitted under 1 beside it. It now publishes no id.
#[test]
fn a_number_an_atom_formula_renders_publishes_no_id() {
    for payload in [
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1}}"#,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":"1"}}"#,
    ] {
        let mut bundle = native_bundle_fixture();
        let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[TRUST_WP_SP_REQUEST]
        else {
            panic!("request {TRUST_WP_SP_REQUEST} is the corpus's TrustWp request");
        };
        let atom = request
            .provenance
            .replay_context
            .atoms
            .iter_mut()
            .find(|atom| atom.kind == trust_ir::request::NativeReplayAtomKind::Assumption)
            .expect("the corpus's TrustWp request carries an Assumption atom");
        atom.formula.schema = FORMULA_SCHEMA.to_string();
        atom.formula.payload = payload.to_string();
        atom.formula.smtlib = None;
        atom.payload_digest = atom.expected_payload_digest();
        reseal_module_identity(&mut bundle);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{payload}: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);
    }
}

/// Predicate documents (`trust-types.Formula@1`) that are JSON but not an
/// object, as the round-16 review measured them: obligation 0's number 1
/// wrapped in an array or a JSON string, or a bare document. `Value::get`
/// finds no `source` key in any of them, so each read as "no source record".
const NON_OBJECT_DOCUMENTS: &[(&str, &str)] = &[
    (
        r#"[{"formula":{"Bool":true},"source":{"native_assertion_id":1}}]"#,
        "the source record wrapped in an array",
    ),
    (
        r#""{\"formula\":{\"Bool\":true},\"source\":{\"native_assertion_id\":1}}""#,
        "the record as a JSON string",
    ),
    ("1", "the bare number 1"),
    ("true", "a boolean"),
    ("null", "null"),
];

/// Identity keys stated outside the record the payload's schema reads: the
/// round-16 review's three wrong-schema shapes, each rendering obligation 0's
/// number 1, and a C hidden inside the predicate beside a harmless record.
const STRAY_IDENTITY_KEYS: &[(&str, &str, &str)] = &[
    (
        FORMULA_SCHEMA,
        r#"{"native_assertion_id":1,"assertion_id":"rust-assertion:7"}"#,
        "the top-level record under the nested schema",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"native_assertion_id":"1"}"#,
        "an unreadable top-level C under the nested schema",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"source":{"native_assertion_id":1},"assertion_id":"rust-assertion:7"}"#,
        "a nested record under the top-level schema",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"And":[{"Bool":true},{"native_assertion_id":1}]},"source":{"native_assertion_id":7}}"#,
        "a C inside the predicate beside a record rendering 7",
    ),
];

/// Every round-16 liar payload, with its schema and a label.
fn round_16_liars() -> impl Iterator<Item = (&'static str, &'static str, &'static str)> {
    NON_OBJECT_DOCUMENTS
        .iter()
        .map(|(payload, label)| (FORMULA_SCHEMA, *payload, *label))
        .chain(STRAY_IDENTITY_KEYS.iter().copied())
}

/// ROUND 16, THE BLOCKER, as liars: the round-14 carrier (obligation 7, no
/// compiler fact, requested by nobody) with a predicate document that is not
/// an object. The review measured obligation 0 ADMITTED under 1 beside each,
/// through both artifact paths, while the same record unwrapped withdrew 1.
/// And the hardening: an identity key outside the record the schema reads
/// rendered nothing either. Each is now unreadable, and withdraws every id.
#[test]
fn a_payload_document_that_is_not_an_object_publishes_no_id() {
    for (schema, payload, label) in round_16_liars() {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_unrequested_factless_obligation(schema, payload))
            .unwrap_or_else(|error| panic!("{label}: no A, so the bundle is consumed: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);
    }
}

/// CONTROLS for the liar above. The producer's own payload shapes on the same
/// carrier, rendering an UNUSED number, leave obligation 0 admitted under 1:
/// the nested record with its `span`, and the top-level record with its `span`
/// and the parse-failure strings `trust-ir-bridge` adds (a string VALUE that
/// spells an identity key is not a key). So the refusals above are the new
/// rule's, and the rule does not refuse the producer.
#[test]
fn the_producers_payload_shapes_rendering_an_unused_number_leave_the_id_published() {
    for (schema, payload) in [
        (
            FORMULA_SCHEMA,
            r#"{"formula":{"Bool":true},"source":{"source_id":"rust:probe","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":0,"line_start":1,"col_start":1,"line_end":1,"col_end":2}}}"#,
        ),
        (
            SOURCE_RECORD_SCHEMA,
            r#"{"source_id":"rust:probe","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":0,"line_start":1,"col_start":1,"line_end":1,"col_end":2},"predicate_parse_failed":"unparseable-contract-predicate","attempted_predicate":"native_assertion_id == 1"}"#,
        ),
        (FORMULA_SCHEMA, r#"{"formula":{"Bool":true}}"#),
    ] {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_unrequested_factless_obligation(schema, payload))
            .unwrap_or_else(|error| panic!("{payload}: {error}"));
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert_eq!(evidence.native_assertion_id(), Some(1), "{payload}");
        assert!(
            evidence.release_admission().is_admissible(),
            "{payload}: {evidence:?}"
        );
        assert!(
            evidence.admit_proof_artifact("1").admission().is_accepted(),
            "{payload}"
        );
    }
}

/// ROUND 16, the same payloads in every other formula the module states: a
/// function summary's `requires`, `ensures` and `decreases` clause, a spec
/// invariant and a temporal formula. The review measured the wrapped record in
/// a summary `ensures` clause admitted under 1.
#[test]
fn a_non_object_document_in_a_stated_formula_publishes_no_id() {
    for (schema, payload, label) in round_16_liars() {
        let bundles = ["requires", "ensures", "decreases"]
            .into_iter()
            .map(|clause| (clause, with_summary_clause_under(clause, schema, payload)))
            .chain(
                ["invariant", "temporal"]
                    .into_iter()
                    .map(|site| (site, with_spec_formula_under(site, schema, payload))),
            );
        for (site, bundle) in bundles {
            let report = TrustVcTrustEngine::new()
                .consume_native_trust_ir_bundle(&bundle)
                .unwrap_or_else(|error| panic!("{site} {label}: {error}"));
            assert_obligation_0_publishes_no_id(&report, 1);
        }
    }
}

/// ROUND 16, the same payloads in a replay atom's formula: the TrustWp
/// request's first `Assumption` atom (it cites obligation 2). The review
/// measured the wrapped record there admitted under 1.
#[test]
fn a_non_object_document_in_an_atom_formula_publishes_no_id() {
    for (schema, payload, label) in round_16_liars() {
        let mut bundle = native_bundle_fixture();
        let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[TRUST_WP_SP_REQUEST]
        else {
            panic!("request {TRUST_WP_SP_REQUEST} is the corpus's TrustWp request");
        };
        let atom = request
            .provenance
            .replay_context
            .atoms
            .iter_mut()
            .find(|atom| atom.kind == trust_ir::request::NativeReplayAtomKind::Assumption)
            .expect("the corpus's TrustWp request carries an Assumption atom");
        atom.formula.schema = schema.to_string();
        atom.formula.payload = payload.to_string();
        atom.formula.smtlib = None;
        atom.payload_digest = atom.expected_payload_digest();
        reseal_module_identity(&mut bundle);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);
    }
}

/// ROUND 16, beside a compiler fact. Obligation 2 carries A = 0; its payload
/// is replaced by each liar. The review measured the wrapped record CONSUMED
/// (and obligation 0 admitted under 1), while the unwrapped one refused the
/// bundle (A vs C). That contradicted the gate's own rule: a present-but-
/// unreadable rendering beside an A refuses the bundle. Each now does.
#[test]
fn a_non_object_document_beside_a_compiler_fact_refuses_the_bundle() {
    let unwrapped = (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":1}}"#,
        "CONTROL: the record unwrapped, C = 1 against A = 0",
    );
    for (schema, payload, label) in round_16_liars().chain([unwrapped]) {
        let mut bundle = native_bundle_fixture();
        {
            let formula = bundle.module.proof_obligations[2]
                .formula
                .as_mut()
                .expect("corpus obligations carry a formula");
            formula.schema = schema.to_string();
            formula.payload = payload.to_string();
            formula.smtlib = None;
        }
        reseal_module_identity(&mut bundle);
        let error = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect_err(label);
        assert!(
            matches!(
                error,
                TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                    obligation_id: 2,
                    ..
                }
            ),
            "{label}: {error}"
        );
    }
}

/// ROUND 17: shapes only the STRICT reader refuses. Each is an object in the
/// right place that the round-16 reader read as a record, or as a stated
/// absence, while it hides obligation 0's number 1 (or a key another reader
/// might take for an identity): a key the shape does not have, at a level it
/// defines, or a value of the wrong type. The same list is in
/// `native_assertion_id`'s unit tests.
const STRICT_SHAPE_LIARS: &[(&str, &str, &str)] = &[
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"note":"native_assertion_id"}"#,
        "a note beside the predicate (round 16's absence control)",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7},"assertion":"rust-assertion:1"}"#,
        "an unknown key beside the record",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"nativeAssertionId":1}}"#,
        "C under a camel-case key",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id ":1}}"#,
        "C under a key with a trailing space",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"Native_Assertion_Id":1}}"#,
        "C under a capitalised key",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native-assertion-id":1}}"#,
        "C under a hyphenated key",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"native_assertion_ids":[1]}}"#,
        "a plural C key beside a readable one",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"source_id":1}}"#,
        "source_id as a number",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"source_id":null}}"#,
        "source_id as null",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"span":"rust-assertion:1"}}"#,
        "a span that is a string",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"span":{"file":0,"line_start":"1"}}}"#,
        "a span line as a string",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"span":{"file":0,"id":1}}}"#,
        "an unknown key in the span",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"span":{"file":{"n":1}}}}"#,
        "a span file that is an object",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7,"predicate_parse_failed":"x"}}"#,
        "a top-level marker inside a predicate document's record",
    ),
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"Source":{"native_assertion_id":1}}"#,
        "the record under a capitalised key",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":7,"source":{}}"#,
        "an empty `source` wrapper beside a top-level record",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":7,"formula":{"Bool":true}}"#,
        "a predicate under the top-level schema",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":7,"predicate_parse_failed":1}"#,
        "a marker that is not a string",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":7,"nativeAssertionId":1}"#,
        "a camel-case C beside a readable one",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"native_assertion_id":7,"span":[1]}"#,
        "a span that is an array",
    ),
];

/// Every UNREADABLE payload shape the reviews produced (rounds 14 to 16) and
/// every shape only the strict reader refuses (round 17), with its schema and
/// a label. The readable liars of those rounds (a `u32` that names obligation
/// 0's number) are refused by the ambiguity rule, not by the reader, and are
/// pinned where they were found.
fn every_reviewed_shape() -> Vec<(&'static str, &'static str, &'static str)> {
    ROUND_14_UNREADABLE
        .iter()
        .copied()
        .chain(REPEATED_KEY_PAYLOADS.iter().copied())
        .chain(
            FURTHER_UNREADABLE_SPELLINGS
                .iter()
                .map(|payload| (FORMULA_SCHEMA, *payload, "a further spelling (round 15)")),
        )
        .chain(round_16_liars())
        .chain(STRICT_SHAPE_LIARS.iter().copied())
        .collect()
}

/// THE ONE ACCEPTED SHAPE per schema, as `trust-ir-bridge` writes it, rendering
/// the unused number 7 and the string `rust-assertion:7` (obligation 7's own,
/// in [`with_unrequested_factless_obligation`]).
const CANONICAL_SHAPES: &[(&str, &str, &str)] = &[
    (
        FORMULA_SCHEMA,
        r#"{"formula":{"Bool":true},"source":{"source_id":"rust:probe","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":"probe.rs","line_start":1,"col_start":1,"line_end":1,"col_end":2}}}"#,
        "the predicate document",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"source_id":"rust:probe","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":"probe.rs","line_start":1,"col_start":1,"line_end":1,"col_end":2}}"#,
        "the source record",
    ),
    (
        SOURCE_RECORD_SCHEMA,
        r#"{"source_id":"rust:probe","assertion_id":"rust-assertion:7","native_assertion_id":7,"span":{"file":0,"line_start":1,"col_start":1,"line_end":1,"col_end":2},"predicate_parse_failed":"unparseable-contract-predicate","attempted_predicate":"native_assertion_id == 1","safety_formula_not_reconstructed":"outside the faithful envelope"}"#,
        "the source record with the producer's three markers",
    ),
];

/// The admission baseline with the TrustWp request's first `Assumption` atom
/// (it cites obligation 2) stating `payload` under `schema`.
fn with_trust_wp_atom_formula_under(schema: &str, payload: &str) -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[TRUST_WP_SP_REQUEST]
    else {
        panic!("request {TRUST_WP_SP_REQUEST} is the corpus's TrustWp request");
    };
    let atom = request
        .provenance
        .replay_context
        .atoms
        .iter_mut()
        .find(|atom| atom.kind == trust_ir::request::NativeReplayAtomKind::Assumption)
        .expect("the corpus's TrustWp request carries an Assumption atom");
    atom.formula.schema = schema.to_string();
    atom.formula.payload = payload.to_string();
    atom.formula.smtlib = None;
    atom.payload_digest = atom.expected_payload_digest();
    reseal_module_identity(&mut bundle);
    bundle
}

/// Every place a payload can sit without refusing the bundle, each carrying
/// `payload` under `schema`: the round-14 unrequested obligation with no
/// compiler fact, a function summary's three clause lists, a spec invariant, a
/// temporal formula, and a TrustWp replay atom's formula.
fn carriers_of(schema: &str, payload: &str) -> Vec<(&'static str, NativeVerificationBundle)> {
    let mut carriers = vec![(
        "an unrequested obligation",
        with_unrequested_factless_obligation(schema, payload),
    )];
    for clause in ["requires", "ensures", "decreases"] {
        carriers.push((clause, with_summary_clause_under(clause, schema, payload)));
    }
    for site in ["invariant", "temporal"] {
        carriers.push((site, with_spec_formula_under(site, schema, payload)));
    }
    carriers.push((
        "a TrustWp atom formula",
        with_trust_wp_atom_formula_under(schema, payload),
    ));
    carriers
}

/// ROUND 17, THE STRICT READER, TABLE-DRIVEN, END TO END. Every unreadable
/// payload shape the reviews produced, and every shape only the strict reader
/// refuses, in every carrier that does not refuse the bundle, leaves obligation
/// 0 with no id through both artifact paths. The ONLY accepted control is the
/// producer's canonical shape, which in the same carriers leaves obligation 0
/// admitted under 1.
#[test]
fn every_reviewed_payload_shape_publishes_no_id_in_every_carrier() {
    for (schema, payload, label) in every_reviewed_shape() {
        for (carrier, bundle) in carriers_of(schema, payload) {
            let report = TrustVcTrustEngine::new()
                .consume_native_trust_ir_bundle(&bundle)
                .unwrap_or_else(|error| {
                    panic!("{carrier}: {label}: no A, so the bundle is consumed: {error}")
                });
            let evidence = &report.requests()[0].proof_evidence()[0];
            assert_eq!(
                evidence.native_assertion_id(),
                None,
                "{carrier}: {label}: {payload}"
            );
            assert_obligation_0_publishes_no_id(&report, 1);
        }
    }
    for (schema, payload, label) in CANONICAL_SHAPES {
        for (carrier, bundle) in carriers_of(schema, payload) {
            let report = TrustVcTrustEngine::new()
                .consume_native_trust_ir_bundle(&bundle)
                .unwrap_or_else(|error| panic!("{carrier}: {label}: {error}"));
            let evidence = &report.requests()[0].proof_evidence()[0];
            assert_eq!(
                evidence.native_assertion_id(),
                Some(1),
                "{carrier}: {label} CONTROL"
            );
            assert!(
                evidence.release_admission().is_admissible(),
                "{carrier}: {label} CONTROL: {evidence:?}"
            );
            assert!(
                evidence.admit_proof_artifact("1").admission().is_accepted(),
                "{carrier}: {label} CONTROL"
            );
        }
    }
}

/// ROUND 17, beside a compiler fact. Obligation 2 carries A = 0; its payload is
/// replaced by each reviewed shape, and each refuses the bundle: an unreadable
/// rendering beside an A is never read as absent. CONTROL: the canonical shape
/// rendering obligation 2's own identity (0, `rust-assertion:0`) is consumed,
/// and obligation 0 stays admitted under 1.
#[test]
fn every_reviewed_payload_shape_beside_a_compiler_fact_refuses_the_bundle() {
    let with_obligation_2_payload = |schema: &str, payload: &str| {
        let mut bundle = native_bundle_fixture();
        {
            let formula = bundle.module.proof_obligations[2]
                .formula
                .as_mut()
                .expect("corpus obligations carry a formula");
            formula.schema = schema.to_string();
            formula.payload = payload.to_string();
            formula.smtlib = None;
        }
        reseal_module_identity(&mut bundle);
        bundle
    };
    for (schema, payload, label) in every_reviewed_shape() {
        let error = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_obligation_2_payload(schema, payload))
            .expect_err(label);
        assert!(
            matches!(
                error,
                TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                    obligation_id: 2,
                    ..
                }
            ),
            "{label}: {error}"
        );
        assert!(error.to_string().contains("unreadable"), "{label}: {error}");
    }
    for (schema, payload) in [
        (
            FORMULA_SCHEMA,
            r#"{"formula":{"Bool":true},"source":{"source_id":"rust:probe","assertion_id":"rust-assertion:0","native_assertion_id":0,"span":{"file":"probe.rs","line_start":1,"col_start":1,"line_end":1,"col_end":2}}}"#,
        ),
        (
            SOURCE_RECORD_SCHEMA,
            r#"{"source_id":"rust:probe","assertion_id":"rust-assertion:0","native_assertion_id":0,"span":{"file":"probe.rs","line_start":1,"col_start":1,"line_end":1,"col_end":2},"predicate_parse_failed":"unparseable-contract-predicate"}"#,
        ),
    ] {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&with_obligation_2_payload(schema, payload))
            .unwrap_or_else(|error| panic!("CONTROL {schema}: {error}"));
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert_eq!(evidence.native_assertion_id(), Some(1), "CONTROL {schema}");
        assert!(
            evidence.admit_proof_artifact("1").admission().is_accepted(),
            "CONTROL {schema}"
        );
    }
}

/// ROUND 16, pinned: the victim is an UNREQUESTED obligation (7, string
/// `rust-assertion:7`, compiler fact 7), and obligation 0 takes its string and
/// number. With the victim's number kept, 7 has two carriers (round 13). The
/// review found the victim's number DELETED from its fact admitted under 7:
/// trust-ir refuses a numberless obligation only when it is requested. The
/// victim still names `rust-assertion:7`, and B -> A is a function, so its
/// string still carries 7: it now publishes no id either.
///
/// The RESIDUAL, pinned so that closing it flips this test: the same steal
/// under a FRESH string (`rust-assertion:9`, number 7) is the documented move
/// residual. After it no field in the bundle ties 7 to the victim, so it is
/// admitted under 7.
#[test]
fn a_number_taken_from_an_unrequested_obligation_publishes_no_id() {
    let mut honest = native_bundle_fixture();
    let mut victim = honest.module.proof_obligations[2].clone();
    victim.id = ProofId::new(7);
    {
        let source = victim
            .source
            .as_mut()
            .expect("corpus obligations carry a source identity");
        if let Some(public) = source.public.as_mut() {
            public.obligation_id = "vc:checked_add:assert:7".to_string();
        }
        source.assertion_id = "rust-assertion:7".to_string();
    }
    honest.module.proof_obligations.push(victim);
    let mut fact = honest.compiler_facts.obligation_sources[2].clone();
    fact.obligation = ProofId::new(7);
    fact.public_obligation_id = "vc:checked_add:assert:7".to_string();
    fact.assertion_id = Some(NativeAssertionId::new(7));
    honest.compiler_facts.obligation_sources.push(fact);
    reseal_module_identity(&mut honest);

    let engine = TrustVcTrustEngine::new();
    let report = engine
        .consume_native_trust_ir_bundle(&honest)
        .expect("CONTROL: an unrequested obligation with its own fact is well formed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), Some(1), "CONTROL");
    assert!(evidence.admit_proof_artifact("1").admission().is_accepted());

    let delete_victim_number = |bundle: &mut NativeVerificationBundle| {
        for source in &mut bundle.compiler_facts.obligation_sources {
            if source.obligation == ProofId::new(7) {
                source.assertion_id = None;
            }
        }
        reseal_module_identity(bundle);
    };

    let mut kept = honest.clone();
    relabel_assertion_identity(&mut kept, &[ProofId::new(0)], "rust-assertion:7", 7);
    let mut deleted = kept.clone();
    delete_victim_number(&mut deleted);
    for (label, bundle) in [
        ("victim number kept", kept),
        ("victim number deleted", deleted),
    ] {
        let report = engine
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert_obligation_0_publishes_no_id(&report, 7);
    }

    let mut moved = honest.clone();
    relabel_assertion_identity(&mut moved, &[ProofId::new(0)], "rust-assertion:9", 7);
    delete_victim_number(&mut moved);
    let report = engine
        .consume_native_trust_ir_bundle(&moved)
        .expect("RESIDUAL: an internally consistent move is consumed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), Some(7), "RESIDUAL");
    assert!(
        evidence.admit_proof_artifact("7").admission().is_accepted(),
        "RESIDUAL"
    );
}

/// Adds to request `index` of `bundle` a replay atom of `kind` citing
/// obligation 0 with its number 1 and stating `formula`, listing obligation 0
/// in that request if it does not already, and reseals.
fn add_atom_for_obligation_0(
    bundle: &mut NativeVerificationBundle,
    index: usize,
    kind: trust_ir::request::NativeReplayAtomKind,
    formula: trust_ir::ProofFormula,
) {
    use trust_ir::request::{NativeReplayAtom, NativeReplayAtomId, NativeReplayAtomKind};
    let id = NativeReplayAtomId::new(99);
    let atom = match kind {
        NativeReplayAtomKind::Assertion => NativeReplayAtom::assertion(id, formula),
        NativeReplayAtomKind::Assumption => NativeReplayAtom::assumption(id, formula),
    }
    .with_obligation(ProofId::new(0))
    .with_assertion_id(NativeAssertionId::new(1));
    let (obligations, atoms) = match &mut bundle.requests[index] {
        NativeVerificationRequest::TrustVc(request) => (
            &mut request.obligations,
            &mut request.provenance.replay_context.atoms,
        ),
        NativeVerificationRequest::TrustMc(request) => (
            &mut request.obligations,
            &mut request.provenance.replay_context.atoms,
        ),
        NativeVerificationRequest::TrustWp(request) => (
            &mut request.obligations,
            &mut request.provenance.replay_context.atoms,
        ),
    };
    if !obligations.contains(&ProofId::new(0)) {
        obligations.push(ProofId::new(0));
    }
    atoms.push(atom);
    reseal_module_identity(bundle);
}

/// ROUND 16, the review's observation, closed: an atom that states obligation
/// 0's number 1 beside a formula other than obligation 0's own. The review
/// measured three shapes admitted under 1: an `Assertion` atom in the TrustWp
/// request and in the TrustMc request (the TrustVc gate reads no other suite's
/// atoms), and an `Assumption` atom in the citing TrustVc request (the gate
/// compares formulas only for `Assertion` atoms). Each states obligation 1's
/// formula. The number then names two formulas, so it names neither.
///
/// CONTROLS: the same atoms stating obligation 0's OWN formula leave it
/// admitted under 1, so the refusals are the new rule's.
#[test]
fn an_atom_stating_obligation_0s_number_beside_another_formula_publishes_no_id() {
    use trust_ir::request::NativeReplayAtomKind;
    let shapes = [
        (
            "a TrustWp Assertion atom",
            TRUST_WP_SP_REQUEST,
            NativeReplayAtomKind::Assertion,
        ),
        (
            "a TrustMc Assertion atom",
            PENDING_CHC_REQUEST,
            NativeReplayAtomKind::Assertion,
        ),
        (
            "an Assumption atom in the citing TrustVc request",
            0,
            NativeReplayAtomKind::Assumption,
        ),
    ];
    let engine = TrustVcTrustEngine::new();
    for (label, index, kind) in shapes {
        let baseline = native_bundle_fixture();
        let own = baseline.module.proof_obligations[0]
            .formula
            .clone()
            .expect("corpus obligations carry a formula");
        let other = baseline.module.proof_obligations[1]
            .formula
            .clone()
            .expect("corpus obligations carry a formula");

        let mut liar = baseline.clone();
        add_atom_for_obligation_0(&mut liar, index, kind, other);
        let report = engine
            .consume_native_trust_ir_bundle(&liar)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert_obligation_0_publishes_no_id(&report, 1);

        let mut control = baseline;
        add_atom_for_obligation_0(&mut control, index, kind, own);
        let report = engine
            .consume_native_trust_ir_bundle(&control)
            .unwrap_or_else(|error| panic!("{label} CONTROL: {error}"));
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert_eq!(evidence.native_assertion_id(), Some(1), "{label} CONTROL");
        assert!(
            evidence.admit_proof_artifact("1").admission().is_accepted(),
            "{label} CONTROL"
        );
    }
}

/// The discharge fixture plus obligation 7: unrequested, no compiler fact,
/// its formula `payload` under `schema`. The round-16 review's discharge-lane
/// carrier.
#[cfg(feature = "proof-certificates")]
fn discharge_with_unrequested(schema: &str, payload: &str) -> NativeVerificationBundle {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(7),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "an unrequested obligation with no compiler fact",
        )
        .with_source(trust_ir::ProofObligationSourceIdentity::new(
            "probe",
            "rust-assertion:7",
        ))
        .with_formula(trust_ir::ProofFormula {
            schema: schema.to_string(),
            payload: payload.to_string(),
            smtlib: None,
            sort: None,
            bindings: Vec::new(),
        }),
    );
    reseal_module_identity(&mut bundle);
    bundle
}

/// ROUND 16, the discharge lane. The review measured the discharged row
/// (obligation 1, clamp's postcondition) publishing id 1 and independent id 1
/// beside an unrequested obligation whose payload wraps the record in an
/// array; only coverage refused its artifact. The row now publishes no id
/// beside any round-16 liar, in that carrier or in a summary `ensures` clause.
/// CONTROL: the same carrier rendering an unused number leaves 1 published.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_discharge_lane_publishes_no_id_beside_a_non_object_document() {
    assert_eq!(
        discharged_row_ids(&discharge_with_unrequested(
            FORMULA_SCHEMA,
            r#"{"formula":{"Bool":true},"source":{"native_assertion_id":7}}"#,
        )),
        (Some(1), Some(1)),
        "control: an unused number"
    );
    for (schema, payload, label) in round_16_liars() {
        for (carrier, bundle) in [
            (
                "an unrequested obligation",
                discharge_with_unrequested(schema, payload),
            ),
            (
                "a summary ensures clause",
                discharge_with_summary_ensures(stated_clause_under(schema, payload)),
            ),
        ] {
            assert_eq!(
                discharged_row_ids(&bundle),
                (None, None),
                "{carrier}: {label}"
            );
            let report = TrustVcTrustEngine::new()
                .consume_native_trust_ir_bundle(&bundle)
                .expect("the discharge bundle is consumed");
            let evidence = &report.requests()[0].proof_evidence()[0];
            assert!(
                evidence
                    .release_admission()
                    .rejection_reasons()
                    .contains(&TrustVcNativeTrustIrCertificateRejection::MissingAssertionId),
                "{carrier}: {label}: {evidence:?}"
            );
            let named = evidence.admit_proof_artifact("1");
            assert!(!named.admission().is_accepted(), "{carrier}: {label}");
            assert!(
                named
                    .admission()
                    .rejection_reasons()
                    .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
                "{carrier}: {label}: {named:?}"
            );
        }
    }
}

/// ROUND 17, the discharge lane, table-driven: every reviewed payload shape
/// beside the discharged row, on an unrequested obligation with no compiler
/// fact and in a summary `ensures` clause, leaves the row with no id and no
/// independent id. CONTROL: the canonical shapes rendering an unused number
/// leave it published under 1.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_discharge_lane_publishes_no_id_beside_any_reviewed_payload_shape() {
    for (schema, payload, label) in CANONICAL_SHAPES {
        assert_eq!(
            discharged_row_ids(&discharge_with_unrequested(schema, payload)),
            (Some(1), Some(1)),
            "CONTROL: {label}"
        );
    }
    for (schema, payload, label) in every_reviewed_shape() {
        for (carrier, bundle) in [
            (
                "an unrequested obligation",
                discharge_with_unrequested(schema, payload),
            ),
            (
                "a summary ensures clause",
                discharge_with_summary_ensures(stated_clause_under(schema, payload)),
            ),
        ] {
            assert_eq!(
                discharged_row_ids(&bundle),
                (None, None),
                "{carrier}: {label}"
            );
        }
    }
}

/// THE RESIDUAL'S OTHER SHAPE, pinned so that closing it flips this test: a
/// PERMUTATION of assertion numbers. Every rendering of each obligation moves
/// consistently, so after the swap every number is carried by exactly one
/// obligation and nothing is ambiguous. No field in the bundle says which
/// number the compiler gave which assertion (see `native_assertion_id`'s
/// module docs), so each certificate is admitted under the number it was
/// swapped to.
#[test]
fn the_residual_a_permutation_of_assertion_numbers_is_admitted_under_the_swapped_numbers() {
    let engine = TrustVcTrustEngine::new();
    let admitted = |report: &TrustVcNativeTrustIrBundleReport| {
        report.requests()[0]
            .proof_evidence()
            .iter()
            .map(|evidence| {
                let artifact = evidence.admit_native_proof_artifact();
                assert!(artifact.admission().is_accepted(), "{artifact:?}");
                (
                    evidence.obligation_id(),
                    artifact.assertion_id().to_string(),
                )
            })
            .collect::<Vec<_>>()
    };

    // Obligations 0 and 1 swap their whole identities: string, fact and atom.
    let mut bundle = native_bundle_fixture();
    relabel_assertion_identity(&mut bundle, &[ProofId::new(1)], "rust-assertion:1", 1);
    relabel_assertion_identity(&mut bundle, &[ProofId::new(0)], "rust-assertion:2", 2);
    let report = engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a consistent swap is well formed");
    assert_eq!(admitted(&report), vec![(0, "2".to_string())]);

    // The numbers alone swap; each string stays where it was.
    let mut bundle = native_bundle_fixture();
    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(1), 1);
    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(0), 2);
    reseal_module_identity(&mut bundle);
    let report = engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a consistent swap is well formed");
    assert_eq!(admitted(&report), vec![(0, "2".to_string())]);

    // Obligations 0 and 2 swap, with obligation 2's TrustWp atom moved too.
    let mut bundle = native_bundle_fixture();
    relabel_assertion_identity(&mut bundle, &[ProofId::new(2)], "rust-assertion:1", 1);
    relabel_assertion_identity(&mut bundle, &[ProofId::new(0)], "rust-assertion:0", 0);
    set_trust_wp_atom_assertion_id(&mut bundle, ProofId::new(2), 1);
    reseal_module_identity(&mut bundle);
    let report = engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a consistent swap is well formed");
    assert_eq!(admitted(&report), vec![(0, "0".to_string())]);

    // Two certified obligations swap: each certificate is admitted under the
    // other's original number.
    let mut bundle = with_second_certificate(native_bundle_fixture());
    relabel_assertion_identity(&mut bundle, &[ProofId::new(0)], "rust-assertion:3", 43);
    relabel_assertion_identity(&mut bundle, &[ProofId::new(3)], "rust-assertion:1", 1);
    let report = engine
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a consistent swap is well formed");
    assert_eq!(
        admitted(&report),
        vec![(0, "43".to_string()), (3, "1".to_string())]
    );
}

/// ROUND 14, the review's other refused probes, pinned as liars. Obligation 0
/// takes obligation 1's number 2 and keeps its own string: 2 is then carried by
/// two obligations, under two strings, and names neither.
#[test]
fn a_number_taken_with_the_string_kept_publishes_no_id() {
    let mut bundle = native_bundle_fixture();
    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(0), 2);
    reseal_module_identity(&mut bundle);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("every rendering agrees, so the bundle is consumed");
    assert_obligation_0_publishes_no_id(&report, 2);
}

/// Every row of `report`'s TrustVc request publishes no id, and no artifact is
/// accepted, whether minted by the row or named by a caller.
#[track_caller]
fn assert_no_row_publishes_an_id(report: &TrustVcNativeTrustIrBundleReport, named: &[u32]) {
    let rows = report.requests()[0].proof_evidence();
    assert!(!rows.is_empty());
    for evidence in rows {
        assert_eq!(evidence.native_assertion_id(), None, "{evidence:?}");
        assert!(
            evidence
                .release_admission()
                .rejection_reasons()
                .contains(&TrustVcNativeTrustIrCertificateRejection::MissingAssertionId),
            "{evidence:?}"
        );
        for number in named {
            let artifact = evidence.admit_proof_artifact(number.to_string());
            assert!(
                !artifact.admission().is_accepted(),
                "{number}: {artifact:?}"
            );
        }
    }
    assert!(report
        .admit_native_proof_artifacts()
        .iter()
        .all(|artifact| !artifact.admission().is_accepted()));
}

/// ROUND 14, with a second CERTIFIED obligation (3, number 43). Obligation 3
/// steals obligation 0's identity; obligations 0 and 3 share one fresh
/// identity (they state one formula, so only their public ids differ); and
/// obligation 3 takes number 1 keeping its string. Each time both certificates
/// publish no id.
#[test]
fn two_certified_obligations_sharing_a_number_publish_no_id() {
    let engine = TrustVcTrustEngine::new();
    let baseline = engine
        .consume_native_trust_ir_bundle(&with_second_certificate(native_bundle_fixture()))
        .expect("two certificates are well formed");
    assert_eq!(
        baseline.requests()[0]
            .proof_evidence()
            .iter()
            .map(|evidence| evidence.native_assertion_id())
            .collect::<Vec<_>>(),
        vec![Some(1), Some(43)],
        "control"
    );

    let mut stolen = with_second_certificate(native_bundle_fixture());
    steal_assertion_identity(&mut stolen, ProofId::new(3), ProofId::new(0));
    let mut fresh = with_second_certificate(native_bundle_fixture());
    relabel_assertion_identity(
        &mut fresh,
        &[ProofId::new(0), ProofId::new(3)],
        "rust-assertion:9",
        9,
    );
    let mut taken = with_second_certificate(native_bundle_fixture());
    set_compiler_fact_assertion_id(&mut taken, ProofId::new(3), 1);
    reseal_module_identity(&mut taken);
    for (label, bundle, named) in [
        ("3 steals 0's identity", stolen, [1, 43]),
        ("0 and 3 share fresh identity 9", fresh, [9, 43]),
        ("3 takes 1, keeping its string", taken, [1, 43]),
    ] {
        let report = engine
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert_no_row_publishes_an_id(&report, &named);
    }
}

/// ROUND 14: the basis-R shape (a cited SMT sibling whose in-module row claims
/// `Unbounded`) is refused for coverage, and under a stolen identity it is
/// refused for the id as well.
#[test]
fn a_basis_r_sibling_under_a_stolen_identity_is_refused_for_both() {
    for steal in [false, true] {
        let mut bundle = native_bundle_fixture();
        if steal {
            steal_assertion_identity(&mut bundle, ProofId::new(0), ProofId::new(1));
        }
        let request_digest = bundle.requests[0].stable_digest();
        let sibling = add_sibling_certificate(
            &mut bundle,
            "trust_vc-smt",
            ProofEvidence::SmtProof(b"(proof)".to_vec()),
            Some(CoverageAssurance {
                bound: CoverageBound::Unbounded,
                request_digest,
            }),
        );
        cite_certificates(&mut bundle, vec![sibling]);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("steal={steal}: {error}"));
        for evidence in report.requests()[0].proof_evidence() {
            let reasons = evidence.release_admission().rejection_reasons();
            assert!(
                reasons.contains(
                    &TrustVcNativeTrustIrCertificateRejection::CertificateCoverageRefused
                ),
                "steal={steal}: {reasons:?}"
            );
            assert_eq!(
                reasons.contains(&TrustVcNativeTrustIrCertificateRejection::MissingAssertionId),
                steal,
                "steal={steal}: {reasons:?}"
            );
            assert!(!evidence
                .admit_native_proof_artifact()
                .admission()
                .is_accepted());
        }
        assert!(report
            .admit_native_proof_artifacts()
            .iter()
            .all(|artifact| !artifact.admission().is_accepted()));
    }
}

/// ROUND 14: on the licensed baseline, only the exact licensed spelling "1" is
/// accepted. Every other spelling, number or string is refused.
#[test]
fn only_the_licensed_spelling_of_an_id_is_accepted() {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&native_bundle_fixture())
        .expect("the baseline is admitted");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert!(evidence.admit_proof_artifact("1").admission().is_accepted());
    for named in [
        "01",
        "+1",
        " 1",
        "1 ",
        "1\n",
        "\u{ff11}",
        "rust-assertion:1",
        "0",
        "2",
        "9",
        "4294967297",
        "-1",
        "",
        "1.0",
        "0x1",
    ] {
        let artifact = evidence.admit_proof_artifact(named);
        assert!(
            !artifact.admission().is_accepted(),
            "{named:?}: {artifact:?}"
        );
    }
}

/// ROUND 14: a DECODED evidence row is never accepted, edited to a stolen
/// number or untouched, and a decoded report admits nothing. Coverage is
/// judged only against the bundle a certificate cites, which neither carries.
#[test]
fn a_decoded_row_or_report_is_never_accepted() {
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&native_bundle_fixture())
        .expect("the baseline is admitted");
    let evidence = &report.requests()[0].proof_evidence()[0];

    let mut edited = serde_json::to_value(evidence).expect("evidence serializes");
    edited["assertion_id"] = serde_json::json!(2);
    edited["independent_assertion_id"] = serde_json::json!(2);
    edited["compiler_facts_binding"]["assertion_id"] = serde_json::json!(2);
    let edited: TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(edited).expect("the edited row decodes");
    assert!(!edited
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());
    assert!(!edited.admit_proof_artifact("2").admission().is_accepted());

    let untouched: TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(serde_json::to_value(evidence).expect("evidence serializes"))
            .expect("the row decodes");
    assert!(!untouched
        .admit_native_proof_artifact()
        .admission()
        .is_accepted());

    let json = serde_json::to_string(&report).expect("the report serializes");
    if let Ok(decoded) = serde_json::from_str::<TrustVcNativeTrustIrBundleReport>(&json) {
        assert!(decoded
            .admit_native_proof_artifacts()
            .iter()
            .all(|artifact| !artifact.admission().is_accepted()));
    }
}

/// ROUND 14, the discharge lane: obligation 1 (clamp's postcondition, the one
/// discharged) takes obligation 0's identity everywhere: B, the compiler fact,
/// the atom, and the payload's C and D. It publishes no id, and the caller
/// naming 0 is refused.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_discharge_lane_publishes_no_id_for_a_stolen_identity() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let obligation = &mut bundle.module.proof_obligations[1];
        obligation
            .source
            .as_mut()
            .expect("fixture obligations carry a source identity")
            .assertion_id = "rust-assertion:0".to_string();
        let formula = obligation
            .formula
            .as_mut()
            .expect("fixture obligations carry a formula");
        let stolen = formula
            .payload
            .replace(
                "\"assertion_id\":\"rust-assertion:1\"",
                "\"assertion_id\":\"rust-assertion:0\"",
            )
            .replace("\"native_assertion_id\":1", "\"native_assertion_id\":0");
        assert_ne!(stolen, formula.payload, "the payload renders the identity");
        formula.payload = stolen;
    }
    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(1), 0);
    sync_assertion_atoms(&mut bundle, ProofId::new(1));
    reseal_module_identity(&mut bundle);
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("every rendering agrees, so the bundle is consumed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    assert_eq!(evidence.native_assertion_id(), None, "{evidence:?}");
    assert!(
        evidence
            .release_admission()
            .rejection_reasons()
            .contains(&TrustVcNativeTrustIrCertificateRejection::MissingAssertionId),
        "{evidence:?}"
    );
    for named in ["0", "1"] {
        let artifact = evidence.admit_proof_artifact(named);
        assert!(!artifact.admission().is_accepted(), "{named}: {artifact:?}");
    }
}

/// `bundle` plus a second obligation (id 3, a clone of obligation 0 with its
/// own public id and frontend assertion 43), a second CleanCic certificate for
/// it, its compiler source row, and the TrustVc request and lineage node both
/// listing it. Neither certificate records a coverage row: each is
/// established by its own kernel replay.
fn with_second_certificate(mut bundle: NativeVerificationBundle) -> NativeVerificationBundle {
    let second_obligation_id = ProofId::new(3);
    let mut second_obligation = bundle.module.proof_obligations[0].clone();
    second_obligation.id = second_obligation_id;
    second_obligation.description = "second frontend assertion memory-safety proof".to_string();
    // The obligation EMBEDS its own public id, and upstream cross-checks it
    // against the compiler source row below — a clone that keeps obligation 0's
    // id is both an alias and a disagreement.
    if let Some(source) = second_obligation.source.as_mut() {
        if let Some(public) = source.public.as_mut() {
            public.obligation_id = "vc:checked_add:postcondition:3".to_string();
        }
        // ROUND 8: and so is a clone that keeps obligation 0's ASSERTION id
        // while the compiler-fact row below gets a new one. This test is about
        // two DISTINCT assertions, and the assertion identity is rendered in
        // both places; moving only the numeric one made the bundle say "the
        // same assertion" and "two assertions" at once. The export seam's input
        // gate now refuses that (`the_export_seam_refuses_one_numeric_\
        // assertion_id_shared_by_two_identities`), and under the real producer
        // it cannot arise at all: `native_request.rs` derives the compiler-fact
        // id as `stable_u32_id(source.assertion_id)`.
        source.assertion_id = "rust-assertion:3".to_string();
    }
    bundle.module.proof_obligations.push(second_obligation);

    let mut second_certificate = bundle.module.proof_certificates[0].clone();
    second_certificate.obligation = second_obligation_id;
    // Keep the original's CleanCic evidence rather than substituting a LeanProof:
    // upstream admits a certificate only when its obligation carries REPLAY
    // authority, and only a kernel-rechecked CleanCic term supplies that. This
    // test is about not collapsing two assertion BINDINGS, not about the
    // evidence flavour, so it must not accidentally assert the weaker path.
    //
    // But a cloned CleanCic term carries the ORIGINAL obligation's lineage
    // digest, and the rechecker requires
    // `lineage == clean_cic_lineage_digest(obligation)` — so re-derive it for
    // the clone using trust-ir's own function rather than copying bytes.
    if let ProofEvidence::CleanCic { lineage, .. } = &mut second_certificate.evidence {
        *lineage = clean_cic_lineage_digest(
            bundle
                .module
                .proof_obligations
                .last()
                .expect("second obligation was pushed above"),
        );
    }
    let second_certificate_ref = second_certificate.lineage_ref();
    bundle.module.proof_certificates.push(second_certificate);

    let mut second_source = bundle.compiler_facts.obligation_sources[0].clone();
    second_source.obligation = second_obligation_id;
    // A cloned source must NOT inherit the original's public identity: upstream
    // rejects two native obligations aliasing one public obligation id, which is
    // exactly what this field exists to prevent. Mint the id the same way the
    // producer does — `vc:{def_path}:{kind_label}:{index}`.
    second_source.public_obligation_id = "vc:checked_add:postcondition:3".to_string();
    // The SECOND assertion's own number, which the request's atom for the
    // second obligation states too (installed below).
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
    // The request now lists two obligations, so it carries the bridge's atom
    // for each; this also reseals the mutated module.
    install_bridge_atoms(&mut bundle);
    bundle
}

/// Two assertions, two certificates, two bindings that do not collapse: each
/// artifact carries its own obligation, assertion id and fingerprint, and both
/// are accepted. Each atom's liar twins are refused.
#[test]
fn admits_multi_assertion_native_trust_ir_certificates_without_collapsing_bindings() {
    let bundle = with_second_certificate(native_bundle_fixture());

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
    assert_eq!(request_artifacts[0].assertion_id(), "1");
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
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    );

    assert_eq!(assert_id_and_formula_liars_refused(&bundle), 2);
}

/// L6, a sibling's atom: the request carries an atom for the second obligation
/// only. The second certificate publishes its id; the first publishes none and
/// is refused `missing_assertion_id` alone.
#[test]
fn an_atom_for_a_sibling_obligation_licenses_nothing_for_this_one() {
    let mut bundle = with_second_certificate(native_bundle_fixture());
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request
        .provenance
        .replay_context
        .atoms
        .retain(|atom| atom.obligation != Some(ProofId::new(0)));
    reseal_module_identity(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a request may carry atoms for some obligations only");
    let evidence = report.requests()[0].proof_evidence();
    assert_eq!(evidence[0].obligation_id(), 0);
    assert_eq!(evidence[0].native_assertion_id(), None);
    assert_eq!(
        evidence[0].release_admission().rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::MissingAssertionId]
    );
    assert_eq!(evidence[1].obligation_id(), 3);
    assert_eq!(evidence[1].native_assertion_id(), Some(43));
    assert!(evidence[1].release_admission().is_admissible());
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    );
}

#[test]
fn rejects_stale_or_mismatched_native_trust_ir_proof_artifact_and_compiler_fact_bindings() {
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let artifact = evidence.admit_native_proof_artifact();
    assert!(artifact.admission().is_accepted(), "{artifact:?}");
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
    // This test is about a DIFFERENT missing binding, so the artifact is built
    // with the compiler fact's own number, which the row also publishes.
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let assertion_id = evidence
        .compiler_facts_binding()
        .assertion_id()
        .expect("the corpus renders the id on its compiler fact")
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
    // A hand-built artifact carries no coverage judgement, so it is also
    // refused as not judged: only the validated bundle path can establish a
    // certificate's coverage.
    assert_eq!(
        admission.rejection_reasons(),
        &[
            TrustVcNativeArtifactRejection::MissingRequestDigest,
            TrustVcNativeArtifactRejection::CertificateCoverageNotJudged,
        ]
    );
}

#[test]
fn native_trust_ir_proof_artifact_admission_fails_closed_without_module_digest() {
    // This test is about a DIFFERENT missing binding, so the artifact is built
    // with the compiler fact's own number, which the row also publishes.
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let assertion_id = evidence
        .compiler_facts_binding()
        .assertion_id()
        .expect("the corpus renders the id on its compiler fact")
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
    // A hand-built artifact carries no coverage judgement, so it is also
    // refused as not judged: only the validated bundle path can establish a
    // certificate's coverage.
    assert_eq!(
        admission.rejection_reasons(),
        &[
            TrustVcNativeArtifactRejection::MissingTrustIrModuleDigest,
            TrustVcNativeArtifactRejection::CertificateCoverageNotJudged,
        ]
    );
}

#[test]
fn native_trust_ir_proof_artifact_admission_fails_closed_without_suite_identity() {
    // This test is about a DIFFERENT missing binding, so the artifact is built
    // with the compiler fact's own number, which the row also publishes.
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("native TrustIr TrustVc request should be consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let assertion_id = evidence
        .compiler_facts_binding()
        .assertion_id()
        .expect("the corpus renders the id on its compiler fact")
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
    // A hand-built artifact carries no coverage judgement, so it is also
    // refused as not judged: only the validated bundle path can establish a
    // certificate's coverage.
    assert_eq!(
        admission.rejection_reasons(),
        &[
            TrustVcNativeArtifactRejection::MissingSuiteIdentity,
            TrustVcNativeArtifactRejection::CertificateCoverageNotJudged,
        ]
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
        // The producer's own validator (the input gate, which runs first)
        // refuses two of these rows before the request-level check is
        // reached: a `Failed` row beside a discharging certificate contradicts
        // itself, and a `Trusted` row needs a certificate that attributes the
        // trust.
        let validator_refusal = match status {
            ProofStatus::Failed => Some(
                "carries a discharging (non-inherited) certificate but its recorded status is Failed",
            ),
            ProofStatus::Trusted => Some(
                "status is Trusted but no certificate carries ProofEvidence::Trusted with a non-blank justification",
            ),
            _ => None,
        };
        let mut bundle = native_bundle_fixture();
        bundle.module.proof_obligations[0].status = status;

        let err = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect_err("schema v3 must reject non-discharged TrustVc certificate evidence");

        if let Some(needle) = validator_refusal {
            let TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { errors, .. } =
                err
            else {
                panic!("expected the producer validator to refuse the row, got {err:?}");
            };
            assert!(errors.contains(needle), "{errors}");
            continue;
        }
        let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
            panic!("expected upstream non-discharged certificate validation error, got {err:?}");
        };
        assert!(errors.contains("native verification request 0 rejects TrustVc certificate evidence 0/trust_vc with non-discharged status"));
    }
}

#[test]
fn native_trust_ir_certificate_admission_flags_trusted_evidence_payloads() {
    // THIS LANE IS REACHABLE, and an earlier revision of this test wrongly
    // claimed it was not. The mistake is worth stating because it is easy to
    // repeat: upstream's admissibility check is keyed on the OBLIGATION, not on
    // the cited certificate. `replayed_authority` is built per-obligation
    // (trust-ir bundle.rs:1923) via `obligation_has_replayed_authority`, which
    // is `certificates.iter().any(..)` over ALL module certificates
    // (evidence.rs:867). So an obligation that ALSO holds a kernel-replayed
    // CleanCic certificate stays in the set even when the request cites a
    // different, `Trusted` one — and that request is then admitted upstream and
    // lands squarely in trust-vc's own classifier.
    //
    // Replacing the CleanCic certificate outright (the earlier shape) removed
    // the obligation's replay authority and so was refused a layer up, which is
    // what made the lane look dead. ADDING a Trusted certificate alongside it
    // is what exercises the real path. Request-certificate uniqueness is keyed
    // on (obligation, prover) (bundle.rs:2123), so the addition needs its own
    // prover name.
    let mut bundle = native_bundle_fixture();

    let mut trusted_certificate = bundle.module.proof_certificates[0].clone();
    trusted_certificate.prover = "trust_vc-manual-audit".to_string();
    trusted_certificate.evidence = ProofEvidence::Trusted("manual trust assumption".to_string());
    let trusted_ref = trusted_certificate.lineage_ref();
    bundle.module.proof_certificates.push(trusted_certificate);
    bundle.lineage.nodes[0]
        .certificates
        .push(trusted_ref.clone());

    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    // Cite ONLY the trusted certificate, so the report's evidence is the one
    // whose admission we are pinning. The CleanCic certificate stays in the
    // module, which is what keeps the obligation replay-authoritative.
    request.certificates[0] = trusted_ref;
    request.options.trusted_evidence = TrustVcTrustedEvidencePolicy::Allow;
    reseal_module_identity(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("trusted evidence on a replay-authoritative obligation is admitted upstream");
    let evidence = &report.requests()[0].proof_evidence()[0];
    let admission = evidence.release_admission();

    // Upstream admits it; trust-vc still refuses it RELEASE grade. That split is
    // the whole point of the lane — `Allow` governs whether the bundle is
    // accepted at all, not whether the evidence is release-worthy.
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
    assert!(
        admission
            .rejection_reasons()
            .contains(&TrustVcNativeTrustIrCertificateRejection::CertificateUsesTrustedEvidence),
        "trusted evidence must be flagged non-release: {:?}",
        admission.rejection_reasons()
    );
    // And its coverage rests on its CleanCic sibling's replay, not its own.
    assert!(
        admission.rejection_reasons().contains(
            &TrustVcNativeTrustIrCertificateRejection::CertificateCoverageBasisNotThisCertificate
        ),
        "{:?}",
        admission.rejection_reasons()
    );
}

/// THE ARTIFACT PATH. `admit_native_proof_artifact(s)` used to rebuild the
/// artifact's admission from obligation status, trust flag and identities
/// alone, so a certificate its own release admission refused for coverage
/// still produced an artifact whose admission was `accepted`. Every coverage
/// refusal now travels onto the artifact under the same name; an artifact
/// built with no coverage judgement at all is refused as NOT JUDGED.
#[test]
fn a_certificate_refused_for_coverage_never_yields_an_accepted_artifact() {
    let smt = || ProofEvidence::SmtProof(b"(proof)".to_vec());
    let refused = {
        // An UNCITED SMT sibling whose in-module row claims `Unbounded`: a
        // refusal, fatal for the cited CleanCic certificate too.
        let mut bundle = native_bundle_fixture();
        let request_digest = bundle.requests[0].stable_digest();
        add_sibling_certificate(
            &mut bundle,
            "trust_vc-smt",
            smt(),
            Some(CoverageAssurance {
                bound: CoverageBound::Unbounded,
                request_digest,
            }),
        );
        bundle
    };
    let sibling_basis = {
        // The SMT sibling CITED: its coverage rests on its sibling's replay.
        let mut bundle = native_bundle_fixture();
        let sibling = add_sibling_certificate(&mut bundle, "trust_vc-smt", smt(), None);
        cite_certificates(&mut bundle, vec![sibling]);
        bundle
    };
    // Each artifact carries its own coverage refusal and nothing else.
    let cases = vec![
        (
            "refused",
            refused,
            vec![TrustVcNativeArtifactRejection::CertificateCoverageRefused],
        ),
        (
            "sibling basis",
            sibling_basis,
            vec![TrustVcNativeArtifactRejection::CertificateCoverageBasisNotThisCertificate],
        ),
    ];
    for (label, bundle, expected) in cases {
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .unwrap_or_else(|error| panic!("{label}: valid upstream: {error}"));
        let evidence = &report.requests()[0].proof_evidence()[0];
        assert!(!evidence.release_admission().is_admissible(), "{label}");
        let artifact = evidence.admit_native_proof_artifact();
        assert!(!artifact.admission().is_accepted(), "{label}");
        assert_eq!(
            artifact.admission().rejection_reasons(),
            expected.as_slice(),
            "{label}: the artifact names the certificate's coverage refusal"
        );
        assert!(
            report
                .admit_native_proof_artifacts()
                .iter()
                .all(|artifact| !artifact.admission().is_accepted()),
            "{label}"
        );
    }

    // The baseline certificate IS established; its evidence, re-read from a
    // payload that predates `coverage_established`, is not — so the artifact
    // built from it is refused as not judged, never accepted by silence.
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&native_bundle_fixture())
        .expect("baseline is consumable");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert!(evidence.release_admission().coverage_established());
    assert!(
        evidence
            .admit_native_proof_artifact()
            .admission()
            .is_accepted(),
        "established coverage: the baseline's artifact is accepted"
    );
    let mut payload = serde_json::to_value(evidence).expect("evidence serializes");
    payload["release_admission"]
        .as_object_mut()
        .expect("release admission is an object")
        .remove("coverage_established")
        .expect("the field is serialized");
    let old_payload: TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(payload).expect("an old payload still decodes");
    assert!(!old_payload.release_admission().coverage_established());
    assert_eq!(old_payload.release_admission().coverage_basis(), None);
    assert_eq!(
        old_payload
            .admit_native_proof_artifact()
            .admission()
            .rejection_reasons(),
        &[TrustVcNativeArtifactRejection::CertificateCoverageNotJudged]
    );
}

/// Apply `edit` to obligation 0 and re-derive everything that quotes it: the
/// CleanCic lineage digest (it hashes the obligation's kind and spec), and
/// with it the certificate's lineage ref in the request and lineage nodes.
fn with_obligation_zero(edit: impl FnOnce(&mut ProofObligation)) -> NativeVerificationBundle {
    let mut bundle = native_bundle_fixture();
    let previous_ref = bundle.module.proof_certificates[0].lineage_ref();
    edit(&mut bundle.module.proof_obligations[0]);
    let lineage_digest = clean_cic_lineage_digest(&bundle.module.proof_obligations[0]);
    if let ProofEvidence::CleanCic { lineage, .. } =
        &mut bundle.module.proof_certificates[0].evidence
    {
        *lineage = lineage_digest;
    }
    let current_ref = bundle.module.proof_certificates[0].lineage_ref();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    for certificate in &mut request.certificates {
        if *certificate == previous_ref {
            *certificate = current_ref.clone();
        }
    }
    for node in &mut bundle.lineage.nodes {
        for certificate in &mut node.certificates {
            if *certificate == previous_ref {
                *certificate = current_ref.clone();
            }
        }
    }
    let obligation = bundle.module.proof_obligations[0].id;
    sync_assertion_atoms(&mut bundle, obligation);
    reseal_module_identity(&mut bundle);
    bundle
}

/// The import path used to file every kind it had no label for — temporal
/// safety, liveness, and through a `_` arm everything trust-ir has grown
/// since — as `panic_freedom`, and admit the certificate. Through the
/// validated path none of them may come back admitted.
///
/// At trust-ir 4f09dab8 every one of the six is refused UPSTREAM first
/// (measured): trust-ir admits an imported TrustVc certificate for a
/// `Discharged` obligation only when a CleanCic term was kernel-replayed for
/// it, and its grounder certifies only the four contract kinds, so these
/// bundles fail with `TrustVcCertificateNotDischarged` before trust-vc runs. trust-vc's own
/// named refusal (`NativeTrustIrImportObligationKindUnrepresentable`) is the
/// second gate for the day upstream grows another authority; it is pinned
/// directly in the crate's `import_obligation_tests`. Either refusal passes
/// here; an `Ok` never does.
#[test]
fn imports_never_admit_obligation_kinds_they_cannot_represent() {
    for kind in [
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::GiveBackRefinement,
        ObligationKind::Termination,
        ObligationKind::Ownership,
        // A namespace the producer validator admits, so the bundle reaches
        // the import rather than being refused for an unpinned namespace.
        ObligationKind::Custom {
            namespace: "trust.vc".to_string(),
            name: "deadlock_freedom".to_string(),
        },
    ] {
        let label = kind.to_string();
        let bundle = with_obligation_zero(|obligation| obligation.kind = kind);
        match TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle) {
            Ok(report) => panic!(
                "{label}: imported as {:?}",
                report.requests()[0].proof_evidence()[0].typed_obligation_kind()
            ),
            Err(TrustEngineError::NativeTrustIrImportObligationKindUnrepresentable {
                request_id: 0,
                obligation_id: 0,
                kind,
            }) => assert_eq!(kind, label),
            Err(TrustEngineError::InvalidNativeTrustIrBundle { errors })
                if errors.contains(
                    "rejects TrustVc certificate evidence 0/trust_vc with non-discharged status",
                ) => {}
            Err(other) => panic!("{label}: refused for an unrelated reason: {other}"),
        }
    }
}

/// `ProofObligation::spec` (trust-ir v46) attributes the obligation to a named
/// temporal property. The body lane refuses it; the import path ignored it,
/// so a certificate whose obligation carries the attribution was admitted
/// with it silently dropped.
///
/// The producer-validator gate refuses this bundle first: trust-ir-build
/// admits a `spec` only on a `Liveness` / `TemporalSafety` row whose machine
/// and property resolve, and upstream certifies neither kind, so no bundle
/// carrying the attribution reaches the import. trust-vc's own named refusal
/// (`NativeTrustIrImportObligationAttributesTemporalProperty`) is the second
/// gate behind it and is pinned directly by the crate's
/// `import_obligation_tests::a_temporal_property_attribution_is_refused_whatever_the_kind`.
#[test]
fn imports_refuse_obligations_attributed_to_a_temporal_property() {
    let bundle = with_obligation_zero(|obligation| {
        obligation.spec = Some(SpecObligationRef::new("Mutex", "EventuallyReleased"));
    });
    match TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle) {
        Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator {
            errors, ..
        }) => {
            assert!(
                errors.contains("spec backref \"Mutex\"/\"EventuallyReleased\""),
                "the refusal must name the temporal-property attribution: {errors}"
            );
        }
        other => panic!("a temporal-property attribution is not importable: {other:?}"),
    }
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

/// The IMPORT half of the verdict channel.
///
/// Before the verdict channel existed, the report carried no outcome and the
/// runner exited 0, so "I discharged nothing" and "I admitted everything" were
/// the same observable. This pins the import fold: a request whose certificate
/// is release-REJECTED is not reported as a clean pass.
///
/// The discharge half is no longer unreachable — see
/// `discharge_request_without_input_certificates_reaches_the_verdict_channel`,
/// which exercises the mode end to end now that the two adapter guards and
/// upstream's mode-blind certificate rule are conditional on the mode.
///
/// (Merged 2026-09-23: the in-process ADVISORY body lane upstream built for the
/// same mode is pinned separately, in `tests/native_trust_ir_discharge.rs`; the
/// serialized bundle path here routes to `native_discharge`.)
#[test]
fn discharge_mode_is_reportable_and_import_verdicts_are_computed() {
    // The baseline request is an import; whatever its certificates'
    // admission, the request verdict must be their fold, and the rollup the
    // request's.
    let bundle = native_bundle_fixture();
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("import bundle is consumable");

    let request = &report.requests()[0];
    assert_eq!(
        request.mode(),
        TrustVcNativeTrustIrRequestMode::ImportProofCertificates
    );
    assert_eq!(
        request.verdict(),
        if request
            .proof_evidence()
            .iter()
            .all(|evidence| evidence.release_admission().is_admissible())
        {
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted
        } else {
            TrustVcNativeTrustIrVerdict::CertificatesRejected
        },
        "request verdict must fold its certificates' release admission"
    );
    assert_eq!(
        report.verdict(),
        request.verdict(),
        "single-request bundle rollup must equal that request's verdict"
    );

    // An import request never produces a discharge outcome, and never a
    // `Discharged` verdict: the mode match in `build_request_report` is what
    // makes that structural rather than a convention.
    assert!(request.discharge().is_empty());
    assert!(!TrustVcNativeTrustIrVerdict::DischargeNotAnswerable.is_ok());
    assert!(TrustVcNativeTrustIrVerdict::CertificatesAdmitted.is_ok());
    assert!(!TrustVcNativeTrustIrVerdict::CertificatesRejected.is_ok());
}

/// A discharge request with NO input certificates now reaches the verdict
/// channel instead of being refused as a malformed import.
///
/// Two guards used to refuse it before it started, and a third lives upstream:
///   * an evidence bundle per TrustVc request (adapter, now Import/Merge-only),
///   * a certificate per requested obligation (adapter, now Import/Merge-only),
///   * the same certificate rule inside trust-ir's own `validate()`, which is
///     MODE-BLIND at the pinned schema — relaxed here for a discharge request's
///     own obligations and for nothing else.
///
/// What arrives is a DECLINE, not a pass: the verdict is not `is_ok`, and the
/// per-obligation vector says why.
#[test]
fn discharge_request_without_input_certificates_reaches_the_verdict_channel() {
    let bundle = discharge_bundle_fixture();

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a discharge request must not be refused as a malformed import");

    let request = &report.requests()[0];
    assert_eq!(
        request.mode(),
        TrustVcNativeTrustIrRequestMode::DischargeProofObligations
    );
    assert!(
        !request.verdict().is_ok(),
        "an unlowered discharge request must never read as a pass"
    );
    assert!(
        request.proof_evidence().is_empty(),
        "a discharge request's INPUT certificates are never this run's evidence"
    );
    assert_eq!(
        request.discharge().len(),
        1,
        "every requested obligation gets exactly one outcome"
    );
    let outcome = &request.discharge()[0];
    assert_eq!(outcome.obligation_id(), 0);
    assert_eq!(
        outcome.public_obligation_id(),
        Some("vc:checked_add:postcondition:0")
    );
    assert!(
        outcome.semantic_digest().is_some(),
        "the outcome must bind the public obligation's semantic digest"
    );
    assert!(
        outcome.formula_payload_sha256().is_some(),
        "the outcome must bind sha256 of the formula bytes it was decided from"
    );
}

/// Twin of the test above with one edit: the request's lineage root carries the
/// certificate for the obligation it asks trust-vc to discharge. A request may
/// not ask for a proof its own lineage already holds, so the bundle is refused
/// before any report is built.
#[test]
fn discharge_request_whose_lineage_already_certifies_its_obligation_is_refused() {
    let mut bundle = discharge_bundle_fixture();
    let certificate = bundle
        .module
        .proof_certificates
        .iter()
        .find(|certificate| certificate.obligation == ProofId::new(0))
        .expect("the corpus certifies obligation 0")
        .lineage_ref();
    let NativeVerificationRequest::TrustVc(request) = &bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    let root = request.lineage_roots[0];
    bundle
        .lineage
        .nodes
        .iter_mut()
        .find(|node| node.id == root)
        .expect("the request's lineage root is a node")
        .certificates
        .push(certificate);

    let engine = TrustVcTrustEngine::new();
    for result in [
        engine.consume_native_trust_ir_bundle(&bundle).map(|_| ()),
        engine.validate_native_trust_ir_bundle(&bundle),
    ] {
        match result {
            Err(TrustEngineError::InvalidNativeTrustIrBundle { errors }) => assert!(
                errors.contains(
                    "discharge request 0 asks for obligation 0 but its lineage node"
                ) && errors.contains("already carries a certificate for it"),
                "the refusal must name the request, the obligation and the node: {errors}"
            ),
            other => panic!(
                "a discharge request whose lineage certifies its obligation must be refused: {other:?}"
            ),
        }
    }
}

/// The relaxation above is keyed on the request's MODE. An import request that
/// is missing certificate evidence still fails upstream validation.
///
/// Guards the exact hole the relaxation could have opened: "discharge mode may
/// skip the evidence rule" must not become "the evidence rule is optional".
#[test]
fn import_request_missing_evidence_is_still_refused_after_the_discharge_relaxation() {
    let mut bundle = native_bundle_fixture();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    assert_eq!(
        request.mode,
        TrustVcVerificationMode::ImportProofCertificates
    );
    request.certificates.clear();
    reseal_module_identity(&mut bundle);

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("an IMPORT request must still carry certificate evidence");
    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream schema validation error, got {err:?}");
    };
    assert!(errors.contains(
        "native verification request 0 has no TrustVc certificate evidence for obligation 0"
    ));
}

/// A discharge request is relaxed for the missing-evidence rule ONLY. Every
/// other upstream rule stays fatal.
#[test]
fn discharge_request_still_fails_every_other_upstream_rule() {
    let mut bundle = discharge_bundle_fixture();
    // Break something unrelated: name a function the module does not define.
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.function = Some(FuncId::new(97));
    reseal_module_identity(&mut bundle);

    let err = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("an unknown function must still fail upstream validation");
    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = err else {
        panic!("expected upstream schema validation error, got {err:?}");
    };
    assert!(
        errors.contains("function"),
        "unexpected error text: {errors}"
    );
}

/// A discharge request that names no `function` never reaches the lowering.
///
/// trust-ir refuses it as a malformed bundle (`MissingTrustVcDischargeFunction`),
/// so no report is produced and the lane's own request-level refusal behind it
/// is not reached.
#[test]
fn discharge_request_without_a_function_is_not_answerable() {
    let mut bundle = discharge_bundle_fixture();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.function = None;
    reseal_module_identity(&mut bundle);

    let engine = TrustVcTrustEngine::new();
    for result in [
        engine.consume_native_trust_ir_bundle(&bundle).map(|_| ()),
        engine.validate_native_trust_ir_bundle(&bundle),
    ] {
        match result {
            Err(TrustEngineError::InvalidNativeTrustIrBundle { errors }) => assert!(
                errors.contains("asks TrustVc to discharge obligations without naming a function"),
                "the refusal must name the missing function: {errors}"
            ),
            other => panic!("a discharge request with no function must be refused: {other:?}"),
        }
    }
}

/// The verdict fold and the mode/verdict pairing.
#[test]
fn discharge_verdicts_fold_worst_wins_and_only_discharge_passes() {
    use TrustVcNativeTrustIrVerdict as V;

    assert!(V::Discharged.is_ok());
    assert!(V::CertificatesAdmitted.is_ok());
    assert!(!V::Refuted.is_ok());
    assert!(!V::DischargeDeclined.is_ok());
    assert!(!V::DischargeNotAnswerable.is_ok());
    assert!(!V::CertificatesRejected.is_ok());
}

// ---------------------------------------------------------------------------
// The DISCHARGE lane end to end.
//
// `discharge_scalar_branch.json` is
// `fn clamp(x: u32) -> u32 { if x > 10 { 10 } else { x } }` with
// `requires x >= 1` and `ensures result >= 1`, written in the shape the compiler
// actually emits: a `trust-types.Formula@1` payload whose leaves carry the
// clause parser's `Sort::Int` placeholder and whose `result` is spelled `_0`.
// It exercises the whole body lane — a conditional branch, two arms, a block
// parameter (phi) join — and its postcondition genuinely NEEDS the precondition,
// so the assumption path is load-bearing rather than decorative.
// `discharge_scalar_branch_liar.json` is the SAME module with one character
// changed, `ensures result >= 2`, which is false at `x = 1`.
//
// `discharge_scalar_inc.json` is `fn inc(x: u32) -> u32 { x + 1 }` with
// `ensures result == x + 1`, and it DECLINES: a `Formula@1` `Add` is
// mathematical, this lane decides at a machine width, and the two readings part
// company exactly where the review's probe put them (`x = u32::MAX`). The three
// tests over it are the decline, the `MachineArithmetic` premise on an
// arithmetic-free clause over the same machine-arithmetic body, and the ay
// certification-funnel refusal at 64 bits (spelled with `BvAdd`, the node that
// denotes the fixed-width operation).
//
// Every fixture carries a placeholder module digest and is resealed on load by
// `reseal_module_identity` — the same derivation every other test in this file
// uses, never a hand-written digest. Their public obligation ids are PROVISIONAL
// until `-Ztrust-dump=native-bundle` reproduces them from the compiler.
// ---------------------------------------------------------------------------

const DISCHARGE_SCALAR_BRANCH: &str =
    include_str!("../fixtures/trust_ir_native/discharge_scalar_branch.json");
const DISCHARGE_SCALAR_BRANCH_LIAR: &str =
    include_str!("../fixtures/trust_ir_native/discharge_scalar_branch_liar.json");
const DISCHARGE_SCALAR_INC: &str =
    include_str!("../fixtures/trust_ir_native/discharge_scalar_inc.json");
const DISCHARGE_CALLEE_CONTRACT_LIAR: &str =
    include_str!("../fixtures/trust_ir_native/discharge_callee_contract_liar.json");

fn discharge_scalar_fixture(source: &str) -> NativeVerificationBundle {
    let mut bundle: NativeVerificationBundle =
        serde_json::from_str(source).expect("discharge fixture should decode");
    reseal_module_identity(&mut bundle);
    bundle
}

/// Removes rendering C (`native_assertion_id`) from every obligation's payload,
/// and rewrites the request's atoms to the edited formulas, as a producer that
/// did not render the number in its payload would have written them.
#[cfg(feature = "proof-certificates")]
fn strip_payload_renderings(bundle: &mut NativeVerificationBundle) {
    let mut edited = Vec::new();
    for obligation in &mut bundle.module.proof_obligations {
        let formula = obligation
            .formula
            .as_mut()
            .expect("fixture carries formulas");
        formula.payload = formula
            .payload
            .replace("\"native_assertion_id\":0,", "")
            .replace("\"native_assertion_id\":1,", "");
        assert!(!formula.payload.contains("native_assertion_id"));
        edited.push(obligation.id);
    }
    for obligation in edited {
        sync_assertion_atoms(bundle, obligation);
    }
}

/// Removes every replay atom from every TrustVc request: rendering E is gone.
#[cfg(feature = "proof-certificates")]
fn strip_request_atoms(bundle: &mut NativeVerificationBundle) {
    for request in &mut bundle.requests {
        if let NativeVerificationRequest::TrustVc(request) = request {
            request.provenance.replay_context.atoms.clear();
        }
    }
}

fn discharge_report(bundle: &NativeVerificationBundle) -> TrustVcNativeTrustIrBundleReport {
    TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(bundle)
        .expect("the discharge fixture is a structurally valid bundle")
}

fn outcome_for<'report>(
    report: &'report TrustVcNativeTrustIrBundleReport,
    public_id: &str,
) -> &'report TrustVcNativeTrustIrDischargeOutcome {
    report.requests()[0]
        .discharge()
        .iter()
        .find(|outcome| outcome.public_obligation_id() == Some(public_id))
        .unwrap_or_else(|| panic!("no discharge outcome for {public_id}"))
}

const CLAMP_POST: &str = "vc:clamp:postcondition:0";
const CLAMP_PRE: &str = "vc:clamp:precondition:0";
const INC_POST: &str = "vc:inc:postcondition:0";
const CALLER_POST: &str = "vc:caller:postcondition:0";

/// THE POINT OF THE LANE: trust-vc proves a compiler-minted postcondition from
/// the trust-ir body, with no certificate on the way in.
#[test]
fn discharges_a_scalar_postcondition_from_the_trust_ir_body() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);

    let postcondition = outcome_for(&report, CLAMP_POST);
    assert_eq!(
        postcondition.outcome(),
        &TrustVcNativeTrustIrDischargeStatus::Verified,
        "unexpected outcome: {postcondition:?}"
    );
    // The outcome binds the formula BYTES it was decided from, not just an
    // obligation id: neither the module digest nor the request digest covers a
    // formula, so an id-only outcome would replay against an edited `ensures`.
    assert!(postcondition.semantic_digest().is_some());
    assert_eq!(
        postcondition.formula_payload_sha256(),
        Some(
            sha256_hex_of(
                bundle
                    .module
                    .proof_obligations
                    .iter()
                    .find(|obligation| obligation.id == ProofId::new(1))
                    .and_then(|obligation| obligation.formula.as_ref())
                    .expect("the postcondition carries a formula")
                    .payload
                    .as_bytes()
            )
            .as_str()
        )
    );
    // No arithmetic in this body, so nothing rests on machine-width reasoning.
    // The one premise is the def-site `requires` this unit ASSUMED — disclosed
    // since round 7 rather than folded in silently. Pinned as an EXACT set, not
    // as "non-empty": a premise appearing here that is not this one means the
    // outcome rests on something new.
    assert_eq!(
        postcondition
            .premises()
            .iter()
            .map(TrustVcNativeTrustIrPremise::kind)
            .collect::<Vec<_>>(),
        vec![TrustVcNativeTrustIrPremiseKind::DefSiteRequires],
        "{postcondition:?}"
    );

    // The request cites the postcondition alone, which is sited at `clamp`'s
    // one `Return`. The def-site `requires` it rests on stays in the module,
    // unsited, and is ASSUMED; it is not an obligation of this request, so the
    // request is a clean discharge.
    assert_eq!(report.requests()[0].discharge().len(), 1);
    assert_eq!(report.verdict(), TrustVcNativeTrustIrVerdict::Discharged);
}

/// A def-site `requires` is ASSUMED at its definition site, never proved
/// there, and a request cannot ask for it. It is unsited (a sited
/// `Precondition` is a call-site VC), and trust-ir refuses a discharge request
/// citing an obligation not sited in the requested function, so such a
/// request is refused before the lane is reached; the lane's own decline
/// ("ASSUMED, never proved") stays behind that refusal.
#[test]
fn a_discharge_request_cannot_cite_a_def_site_precondition() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let precondition = bundle
        .module
        .proof_obligations
        .iter()
        .find(|obligation| {
            obligation
                .source
                .as_ref()
                .and_then(|source| source.public.as_ref())
                .is_some_and(|public| public.obligation_id == CLAMP_PRE)
        })
        .expect("the fixture carries clamp's precondition");
    assert!(
        precondition.site.is_none(),
        "a def-site `requires` is unsited"
    );
    let precondition = precondition.id;
    {
        let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
            panic!("fixture first request should be TrustVc");
        };
        request.obligations.insert(0, precondition);
    }
    reseal_module_identity(&mut bundle);

    match TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle) {
        Err(TrustEngineError::InvalidNativeTrustIrBundle { errors }) => assert!(
            errors.contains(&format!(
                "asks TrustVc to discharge obligation {} in function 0, but it has no site",
                precondition.index()
            )),
            "the refusal must name the unsited precondition: {errors}"
        ),
        other => panic!("citing a def-site precondition must be refused: {other:?}"),
    }
}

/// ADVERSARIAL REVIEW ROUND 6, BLOCKER 1, END TO END: the input gate's carve-out
/// and the callee-contract status gate COMBINED into a false `Discharged`.
///
/// `validate_producer_module` deliberately carries
/// `DischargedWithoutCertificate` past — the rejecting authority's own
/// capability verdict, load-bearing for the import/merge grading path. At the
/// pinned rev that verdict fires for EVERY `Discharged` row with no
/// authority-admitted certificate, i.e. unconditionally. So a module may reach
/// the discharge lane with a `Discharged` row that nothing backs, and upstream
/// says so in the error's own words: "opaque evidence and status labels are not
/// proof authority".
///
/// Round 5's status gate then read that bare label as ESTABLISHED and assumed
/// the callee's `ensures` as fact. This probe is the consequence: `g` is the
/// IDENTITY, so `g(0) == 0`, yet it publishes `ensures result >= 100` at
/// `Discharged` with no certificate, and `caller(x) { g(x) }` claims the same.
/// The claim is FALSE at `x = 0`, and before the fix the lane answered
/// `Verified`/`Discharged` and (under `proof-certificates`) minted a
/// release-admissible kernel-checked certificate for it.
///
/// The first assertion keeps the probe honest: the module's ONLY validator
/// error is the carve-out, so this test measures the status gate and nothing
/// else.
#[test]
fn a_callee_ensures_at_a_bare_discharged_label_never_reaches_the_caller() {
    let bundle = discharge_scalar_fixture(DISCHARGE_CALLEE_CONTRACT_LIAR);

    let errors = trust_ir_build::validate_module(&bundle.module);
    assert!(
        !errors.is_empty()
            && errors.iter().all(|error| matches!(
                error,
                trust_ir_build::ValidationError::DischargedWithoutCertificate { .. }
            )),
        "the probe must isolate the carve-out, not some other malformedness: {errors:?}"
    );

    let report = discharge_report(&bundle);
    let postcondition = outcome_for(&report, CALLER_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { reason }
                if reason.contains("Certified")
        ),
        "a bare `Discharged` label is not proof authority: {postcondition:?}"
    );
    assert_ne!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::Discharged,
        "the caller's claim is false at x = 0"
    );
    assert!(!report.verdict().is_ok());
    assert!(
        report.produced_certificates().is_empty(),
        "nothing may be certified from an unbacked callee label: {:?}",
        report.produced_certificates()
    );
    assert!(report.produced_evidence_bundles().is_empty());
    // No `CalleeContract` premise either: the contract was never assumed, so
    // there is nothing for a consumer to "read with the verdict".
    assert!(
        !postcondition
            .premises()
            .iter()
            .any(|premise| premise.kind() == TrustVcNativeTrustIrPremiseKind::CalleeContract),
        "{postcondition:?}"
    );
}

/// The same module with one character changed: `ensures result >= 2`, false at
/// `x = 1`. This is the mutation-sensitive discriminator — if the lane were
/// rubber-stamping, this would pass too.
#[test]
fn refutes_the_liar_twin_with_a_counterexample() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH_LIAR);
    let report = discharge_report(&bundle);

    let postcondition = outcome_for(&report, CLAMP_POST);
    let TrustVcNativeTrustIrDischargeStatus::Counterexample { bindings } = postcondition.outcome()
    else {
        panic!("the liar must be refuted with a model, got {postcondition:?}");
    };
    assert!(
        bindings
            .iter()
            .any(|binding| binding.display_name == "x" || binding.raw_name == "x"),
        "the counterexample must bind the parameter it refutes on: {bindings:?}"
    );
    assert_eq!(report.verdict(), TrustVcNativeTrustIrVerdict::Refuted);
    assert!(!report.verdict().is_ok());
    assert!(
        report.produced_certificates().is_empty(),
        "a refuted request must mint no certificate"
    );
    assert!(report.produced_evidence_bundles().is_empty());
}

/// REGRESSION, adversarial review round 3: a PATH-LOCAL CONTRADICTION must
/// DECLINE, never silently erase the path that carries the counterexample.
///
/// Every block fact is asserted under that block's path condition, so a block
/// whose facts contradict each other has NO model: the solver never explores
/// that path and the counterexample living on it disappears, leaving the
/// obligation "proved" over what survives. The engine's `VacuousTruth` detector
/// does not fire — it answers for a GLOBALLY contradictory assumption set, and
/// the other paths here are perfectly satisfiable — so the row came back
/// `Verified` with a kernel-checked certificate and a produced evidence bundle.
///
/// Each mutation below puts one such contradiction on the LIAR fixture's
/// falsifying path (`ensures result >= 2`, false at `x = 1`), which is exactly
/// how the review reached a false `Discharged`. The control is the first case:
/// the same reshaped program WITHOUT the contradiction still refutes, so the
/// counterexample is genuinely reachable and it is the contradiction — not the
/// reshaping — that hid it.
#[test]
fn a_path_local_contradiction_declines_rather_than_proving_the_liar() {
    fn liar_result(
        mutate: impl FnOnce(&mut trust_ir::Function),
    ) -> Result<TrustVcNativeTrustIrBundleReport, TrustEngineError> {
        let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH_LIAR);
        mutate(&mut bundle.module.functions[0]);
        reseal_module_identity(&mut bundle);
        TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
    }

    fn liar_report(
        mutate: impl FnOnce(&mut trust_ir::Function),
    ) -> TrustVcNativeTrustIrBundleReport {
        liar_result(mutate).expect("this mutation keeps the module well-formed")
    }

    /// The producer validator refused the MODULE, naming the shape. Strictly
    /// stronger than a per-obligation decline: nothing was lowered at all, so no
    /// obligation of this module can be answered, let alone discharged.
    fn assert_refused_by_the_producer_gate(
        result: Result<TrustVcNativeTrustIrBundleReport, TrustEngineError>,
        naming: &str,
    ) {
        let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator {
            errors, ..
        }) = result
        else {
            panic!("a module the producer validator rejects must be refused, not decided");
        };
        assert!(
            errors.contains(naming),
            "the refusal must name what it refused ({naming}): {errors}"
        );
    }

    /// `switch x { <case value> => <target>, … , _ => bb1 }` as the entry
    /// terminator. `bb1` returns 10 and `bb2` returns `x`, so an arm reaching
    /// `bb2` at `x = 1` is what makes `result >= 2` false.
    fn switch_entry(cases: Vec<(i128, u32)>) -> trust_ir::node::InstrNode {
        trust_ir::node::InstrNode::new(trust_ir::inst::Inst::Switch {
            value: trust_ir::ValueId::new(0),
            default: trust_ir::BlockId::new(1),
            default_args: vec![],
            cases: cases
                .into_iter()
                .map(|(value, target)| trust_ir::inst::SwitchCase {
                    value: trust_ir::Constant::Int(value),
                    target: trust_ir::BlockId::new(target),
                    args: vec![],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        })
    }

    fn retarget_entry(function: &mut trust_ir::Function, cases: Vec<(i128, u32)>) {
        let entry = &mut function.blocks[0];
        entry.body.pop();
        entry.body.push(switch_entry(cases));
    }

    /// Replace the falsifying arm's body: define value 4 as `head`, then pass
    /// it to the join instead of `x`.
    fn rewrite_false_arm(function: &mut trust_ir::Function, head: Vec<trust_ir::node::InstrNode>) {
        let arm = &mut function.blocks[2];
        arm.body = head;
        arm.body
            .push(trust_ir::node::InstrNode::new(trust_ir::inst::Inst::Br {
                target: trust_ir::BlockId::new(3),
                args: vec![trust_ir::ValueId::new(4)],
            }));
    }

    fn u32_const(value: i128) -> trust_ir::node::InstrNode {
        trust_ir::node::InstrNode::new(trust_ir::inst::Inst::Const {
            ty: trust_ir::Ty::U32,
            value: trust_ir::Constant::Int(value),
        })
        .with_result(trust_ir::ValueId::new(4))
    }

    // (0) CONTROL. One case `x == 1 -> bb2`, default `bb1`: the reshaped program
    //     still returns `x` at `x = 1`, and the lane REFUTES it with a model.
    //     Everything below differs from this by the contradiction alone.
    let control = liar_report(|function| retarget_entry(function, vec![(1, 2)]));
    assert!(
        matches!(
            outcome_for(&control, CLAMP_POST).outcome(),
            TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
        ),
        "the counterexample must be reachable through a Switch: {:?}",
        outcome_for(&control, CLAMP_POST)
    );

    // (1) F1 — two cases carrying the SAME value. Both guards are `x == 1`, so
    //     both arms are live at once and the join parameter is pinned to 10 and
    //     to 1; trust-ir's interpreter takes the FIRST matching case and returns
    //     1, so the clause is false. Was VERIFIED with a certificate.
    //
    //     ROUND 4: this is the one mutation of the five that the PRODUCER
    //     VALIDATOR input gate subsumes, so the refusal now happens a layer
    //     earlier — the whole module is refused instead of this obligation
    //     declining. The lane's own gate is unchanged and is still exercised
    //     directly by `native_discharge::body::tests::
    //     duplicate_switch_case_values_decline`, which lowers the module without
    //     going through the bundle gate. Defence in depth, both layers tested.
    assert_refused_by_the_producer_gate(
        liar_result(|function| retarget_entry(function, vec![(1, 2), (1, 1)])),
        "duplicate switch case value",
    );

    // (2) F2 — a case value outside the selector's width. `2^32 + 1` at `u32` IS
    //     `1` for trust-ir's interpreter (`InterpretInt::from_i128` masks), so
    //     the program takes that arm at `x = 1`; the lane emitted an
    //     unsatisfiable guard and dropped the arm.
    //
    //     The third of the five the PRODUCER VALIDATOR input gate subsumes, since
    //     trust-ir's shared switch-literal contract types every `SwitchCase.value`
    //     against its selector (it used to be reachable from a module that passed
    //     the full validator). The lane's own gate is unchanged and still
    //     exercised directly by `native_discharge::body::tests::
    //     an_integer_constant_outside_its_declared_width_declines`.
    assert_refused_by_the_producer_gate(
        liar_result(|function| retarget_entry(function, vec![(4_294_967_297, 2)])),
        "const type mismatch",
    );

    // (3) F3 — an `Inst::Const` outside its declared width ON the falsifying
    //     arm. `2^32` at `u32` is `0`, so the program returns 0 and the clause
    //     is false; the literal as written is an equality nothing satisfies.
    //
    //     ROUND 4: the second of the five that the PRODUCER VALIDATOR input gate
    //     subsumes (it types the constant against its declared `ty`). The lane's
    //     own gate is unchanged and still exercised directly by
    //     `native_discharge::body::tests::
    //     an_integer_constant_outside_its_declared_width_declines`.
    assert_refused_by_the_producer_gate(
        liar_result(|function| rewrite_false_arm(function, vec![u32_const(4_294_967_296)])),
        "const type mismatch",
    );

    // (4) F4 — one `ValueId` defined twice on the falsifying arm. Two
    //     `pc$2 => v4 == k` equations that disagree. Round 2's probe put this in
    //     the ENTRY block, where the contradiction is global and `VacuousTruth`
    //     caught it; on a conditional arm nothing did.
    //
    //     ROUND 4: the third of the five that the PRODUCER VALIDATOR input gate
    //     subsumes. The lane's own gate is unchanged and still exercised directly
    //     by `native_discharge::body::tests::a_value_defined_twice_declines`.
    assert_refused_by_the_producer_gate(
        liar_result(|function| rewrite_false_arm(function, vec![u32_const(1), u32_const(0)])),
        "defined more than once",
    );

    // (5) The general case: a value used before anything defines it. `v4 == v4 +
    //     10` is unsatisfiable at every width, with every value defined exactly
    //     once and every case value in range.
    //
    //     ROUND 4: the fourth of the five that the PRODUCER VALIDATOR input gate
    //     subsumes — as a WITHIN-A-BLOCK rule. The lane's gate is a reachability
    //     rule over the whole linearized body (two values defining each other
    //     across blocks name neither themselves nor a later instruction in their
    //     own block), so it is not redundant; it is still exercised directly by
    //     `native_discharge::body::tests::a_value_used_before_it_is_defined_declines`.
    assert_refused_by_the_producer_gate(
        liar_result(|function| {
            rewrite_false_arm(
                function,
                vec![trust_ir::node::InstrNode::new(trust_ir::inst::Inst::BinOp {
                    op: trust_ir::inst::BinOp::Add,
                    ty: trust_ir::Ty::U32,
                    lhs: trust_ir::ValueId::new(4),
                    rhs: trust_ir::ValueId::new(1),
                })
                .with_result(trust_ir::ValueId::new(4))],
            );
        }),
        "used before its definition",
    );
}

/// DISCLOSURE, adversarial review round 3 (minor): a PATH-LOCAL `Inst::Assume`
/// can prove the liar by itself, and the only thing that says so is the premise.
///
/// An assume is a fact the PRODUCER asserted and trust-vc did not check. One
/// that cannot hold on its path removes that path from the model — the same
/// erasure the four gates above refuse — and a path-local one does not trip the
/// engine's `VacuousTruth` detector either. This is the documented reading of an
/// assume at this pin and NOT a defect, so the mitigation is disclosure: the row
/// carries a `BodyAssume` premise naming the instruction. A consumer that reads
/// the verdict without the premise vector is reading a trusted assertion as a
/// proof, which is exactly why this pins the premise rather than the verdict.
///
/// (Unlike the gate regressions, this test passes before and after the fix —
/// there is no behaviour change to catch. It guards the disclosure the design
/// rests on, so a silent loss of the premise fails here instead of downstream.)
#[test]
fn a_path_local_assume_proves_the_liar_and_says_so_in_its_premises() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH_LIAR);
    {
        // `bb2` is the arm taken when `x <= 10`, and value 2 is `x > 10`.
        // Assuming it THERE is a claim false on that path, which erases the
        // `x = 1` counterexample the liar is refuted by.
        let arm = &mut bundle.module.functions[0].blocks[2];
        arm.body.insert(
            0,
            trust_ir::node::InstrNode::new(trust_ir::inst::Inst::Assume {
                cond: trust_ir::ValueId::new(2),
            }),
        );
    }
    reseal_module_identity(&mut bundle);
    let report = discharge_report(&bundle);

    let outcome = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            outcome.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Verified
        ),
        "the producer's assume is taken at its word: {outcome:?}"
    );
    let assumed: Vec<_> = outcome
        .premises()
        .iter()
        .filter(|premise| premise.kind() == TrustVcNativeTrustIrPremiseKind::BodyAssume)
        .collect();
    assert_eq!(
        assumed.len(),
        1,
        "a verdict resting on an assume must disclose it: {:?}",
        outcome.premises()
    );
    assert!(
        assumed[0].detail().contains("`Inst::Assume`"),
        "the premise must name what was assumed: {:?}",
        assumed[0]
    );
}

/// Dropping the `requires` makes the SAME postcondition false: `clamp(0)` is 0,
/// so `result >= 1` no longer holds. The assumption is load-bearing, not
/// decorative.
#[test]
fn dropping_the_requires_refutes_the_postcondition() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        bundle.module.proof_obligations.remove(0);
        bundle.module.proof_obligations[0].id = ProofId::new(1);
        let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
            panic!("fixture first request should be TrustVc");
        };
        request.obligations = vec![ProofId::new(1)];
        bundle.compiler_facts.obligation_sources.remove(0);
        bundle.lineage.nodes[0].obligations = vec![ProofId::new(1)];
    }
    reseal_module_identity(&mut bundle);
    let report = discharge_report(&bundle);
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
    ));
    assert!(!report.verdict().is_ok());
}

/// A verified obligation mints a certificate, and the certificate is graded by
/// the SAME release-admission rules an imported one is graded by.
#[cfg(feature = "proof-certificates")]
#[test]
fn a_discharged_obligation_produces_a_kernel_checked_certificate() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);

    assert_eq!(report.produced_certificates().len(), 1);
    let certificate = &report.produced_certificates()[0];
    assert_eq!(certificate.obligation_id(), 1);
    assert_eq!(certificate.unit_id(), CLAMP_POST);
    assert!(certificate.kernel_verified(), "{certificate:?}");
    assert!(!certificate.alethe().is_empty());
    // Checklist A again, on the certificate this time.
    assert!(certificate.semantic_digest().is_some());
    assert!(certificate.formula_payload_sha256().is_some());
    // It mints a real upstream certificate for the obligation it proved.
    let minted = certificate.to_trust_ir_certificate();
    assert_eq!(minted.obligation, ProofId::new(1));
    assert!(matches!(minted.evidence, ProofEvidence::SmtProof(_)));

    // The evidence row is the ordinary import-lane row, so
    // `admit_native_proof_artifacts` works over a produced certificate.
    let evidence = report.requests()[0].proof_evidence();
    assert_eq!(evidence.len(), 1);
    assert_eq!(evidence[0].obligation_id(), 1);
    assert_eq!(evidence[0].obligation_status(), "discharged");
    assert!(!evidence[0].trusted());
    assert_eq!(
        evidence[0].evidence_kind(),
        TrustVcNativeTrustIrEvidenceKind::SmtProof
    );
    assert_eq!(report.admit_native_proof_artifacts().len(), 1);

    // And the request leaves with the evidence bundle it arrived without.
    assert_eq!(report.produced_evidence_bundles().len(), 1);
    let produced = &report.produced_evidence_bundles()[0];
    assert_eq!(produced.obligations, vec![ProofId::new(1)]);
    assert_eq!(
        produced.trust_ir_module_digest,
        bundle.trust_ir_module_digest
    );
}

/// THE FAIL-CLOSED SURFACE, at the request level. Each mutation is a shape the
/// lane does not model, and each must produce a decline naming it rather than a
/// silent pass.
#[test]
fn unmodelled_shapes_decline_by_name() {
    // (1) A LOOP. The pinned schema carries no loop-invariant anchor, so
    //     unrolling would be a bounded check reported as a proof.
    let mut looping = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let join = &mut looping.module.functions[0].blocks[3];
        join.body.pop();
        // The back edge must carry bb0's parameter: a `Br` with no argument is
        // a MALFORMED module (the producer validator rejects "branch to bb0
        // passes 0 args, expected 1"), and this probe is about the lane's back
        // edge gate, not about well-formedness.
        join.body
            .push(trust_ir::node::InstrNode::new(trust_ir::inst::Inst::Br {
                target: trust_ir::BlockId::new(0),
                args: vec![trust_ir::ValueId::new(3)],
            }));
    }
    reseal_module_identity(&mut looping);
    let report = discharge_report(&looping);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
    );
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { reason } if reason.contains("back edge")
    ));

    // (2) AN UNMODELLED TYPE. A float parameter is outside the scalar fragment.
    //     Added as a SECOND, unused formal rather than by retyping `x`: retyping
    //     `x` alone leaves the `icmp` and the branch arguments at u32, which is a
    //     MALFORMED module the producer validator rejects — a different refusal
    //     than the one this probe is about.
    let mut floating = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        floating.module.func_types[0].params.push(trust_ir::Ty::F64);
        floating.module.functions[0].blocks[0]
            .params
            .push((trust_ir::ValueId::new(9), trust_ir::Ty::F64));
    }
    reseal_module_identity(&mut floating);
    let report = discharge_report(&floating);
    assert!(!report.verdict().is_ok());
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { reason } if reason.contains("F64")
    ));

    // (3) AN UNMODELLED FORMULA NODE. `Select` is an array read; nothing in the
    //     scalar fragment reads arrays, and mapping it to anything would be a
    //     guess about what the obligation says.
    let mut array_read = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let obligation = &mut array_read.module.proof_obligations[1];
        let formula = obligation.formula.as_mut().expect("has a formula");
        formula.payload = formula.payload.replace(
            r#"{"Ge":[{"Var":["_0","Int"]},{"Int":1}]}"#,
            r#"{"Select":[{"Var":["x","Int"]},{"Int":0}]}"#,
        );
    }
    sync_assertion_atoms(&mut array_read, ProofId::new(1));
    reseal_module_identity(&mut array_read);
    let report = discharge_report(&array_read);
    assert!(!report.verdict().is_ok());
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { reason } if reason.contains("Select")
    ));

    // (4) A FORMULA THE PRODUCER COULD NOT PARSE. Its payload carries source
    //     metadata and no predicate; an absent predicate is not an empty one.
    let mut source_only = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let obligation = &mut source_only.module.proof_obligations[1];
        let formula = obligation.formula.as_mut().expect("has a formula");
        formula.payload = r#"{"source":{"source_id":"rust:probe/clamp.rs::clamp"}}"#.to_string();
    }
    sync_assertion_atoms(&mut source_only, ProofId::new(1));
    reseal_module_identity(&mut source_only);
    let report = discharge_report(&source_only);
    assert!(!report.verdict().is_ok());
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { reason }
            if reason.contains("no `formula` node")
    ));

    // (5) AN OBLIGATION ANCHORED AT AN INSTRUCTION SITE. A per-check VC must be
    //     bound to the condition generated AT its own instruction, never to the
    //     function's contract.
    let mut anchored = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        anchored.module.proof_obligations[1].site = Some(trust_ir::ObligationSite::new(
            trust_ir::FuncId::new(0),
            trust_ir::BlockId::new(0),
            1,
        ));
    }
    reseal_module_identity(&mut anchored);
    let report = discharge_report(&anchored);
    assert!(!report.verdict().is_ok());
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { reason }
            if reason.contains("instruction site")
    ));
}

/// A postcondition is decided only when it is sited at the function's ONE
/// `Return`: the lane checks it at every return, so a row sited at one of
/// several returns would be answered for paths it is not about. Here `clamp`'s
/// else arm returns directly instead of joining, and the row stays sited at the
/// join's `Return`. The control is the unmodified fixture, whose one `Return`
/// verifies (`discharges_a_scalar_postcondition_from_the_trust_ir_body`).
#[test]
fn a_postcondition_sited_at_one_of_several_returns_declines() {
    use trust_ir::node::InstrNode;
    use trust_ir::{BlockId, Inst, ValueId};

    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let clamp = &mut bundle.module.functions[0];
        let else_arm = clamp
            .blocks
            .iter_mut()
            .find(|block| block.id == BlockId::new(2))
            .expect("clamp has an else arm");
        else_arm.body = vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })];
    }
    reseal_module_identity(&mut bundle);
    let report = discharge_report(&bundle);
    assert!(!report.verdict().is_ok());
    let outcome = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            outcome.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { reason }
                if reason.contains("not the one `Return`")
        ),
        "{outcome:?}"
    );
}

/// A `requires` that cannot be lowered refuses the WHOLE request rather than
/// being dropped: dropping an assumption strengthens every obligation of the
/// function, so a proof under the remainder would claim more than the program
/// promises.
#[test]
fn an_unreadable_requires_refuses_the_request_rather_than_being_dropped() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let obligation = &mut bundle.module.proof_obligations[0];
        let formula = obligation.formula.as_mut().expect("has a formula");
        formula.payload = formula.payload.replace(
            r#"{"Ge":[{"Var":["x","Int"]},{"Int":1}]}"#,
            r#"{"Select":[{"Var":["x","Int"]},{"Int":0}]}"#,
        );
    }
    reseal_module_identity(&mut bundle);
    let report = discharge_report(&bundle);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
    );
    assert!(matches!(
        outcome_for(&report, CLAMP_POST).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { reason }
            if reason.contains("strengthen")
    ));
}

/// WHAT A POSTCONDITION OVER MACHINE ARITHMETIC DOES NOT CLAIM, pinned so
/// nobody reads more into it later.
///
/// A contract clause's `+` is SPEC arithmetic, and
/// `obligation_carries_spec_arithmetic` disables overflow checking for an
/// `Ensures` obligation on purpose — so `ensures result == x + 1` is decided at
/// the declared width and says nothing about `x + 1` overflowing.
///
/// CORRECTED after adversarial review: the premise is DISCLOSURE of the width
/// decision, not a claim that the operation cannot overflow, and it is about the
/// BODY — where a plain trust-ir `BinOp` really does denote the machine's
/// wrapping operation. No CLAUSE is read at a width any more: a mathematical
/// `Formula@1` arithmetic node over machine operands declines.
#[test]
fn machine_arithmetic_is_recorded_as_a_premise() {
    // `ensures result >= 1` for `fn inc(x: u32) -> u32 { x + 1 }` under
    // `requires x < u32::MAX`: the CLAUSE is arithmetic-free (a mathematical
    // arithmetic node over machine operands declines), and the BODY's `+` is
    // still the machine's, so this is the shape the premise is about.
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_INC);
    set_formula(&mut bundle, 1, r#"{"Ge":[{"Var":["_0","Int"]},{"Int":1}]}"#);
    reseal_module_identity(&mut bundle);
    let report = discharge_report(&bundle);
    let outcome = outcome_for(&report, INC_POST);
    assert_eq!(
        outcome.outcome(),
        &TrustVcNativeTrustIrDischargeStatus::Verified,
        "{outcome:?}"
    );
    let premises = outcome.premises();
    assert!(
        premises.iter().any(|premise| {
            premise.kind() == TrustVcNativeTrustIrPremiseKind::MachineArithmetic
                && premise.detail().contains("WRAPPING")
        }),
        "an outcome over machine arithmetic must record what it rests on: {premises:?}"
    );

    // And a body with no machine arithmetic records NO `MachineArithmetic`
    // premise, so that premise is a real signal rather than boilerplate on every
    // row. (The def-site `requires` premise is unconditional and is pinned as an
    // exact set in `discharges_a_scalar_postcondition_from_the_trust_ir_body`.)
    let report = discharge_report(&discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH));
    assert!(!outcome_for(&report, CLAMP_POST)
        .premises()
        .iter()
        .any(|premise| premise.kind() == TrustVcNativeTrustIrPremiseKind::MachineArithmetic));
}

/// CHECKLIST L: the lane reports what ay PUBLISHES, never what it computed.
///
/// `ensures result == BvAdd(x, 1)` on `u64` was the measured case. ay used to
/// COMPUTE the UNSAT and then refuse to publish it ("computed UNSAT rejected
/// by mandatory strict certification: step t12 uses unsupported theory lemma
/// kind Generic in strict mode"), and the lane answered `Unknown`, never a
/// discharge. The pinned ay publishes it, so the claim, which is true of `inc`
/// under the wrapping model its `MachineArithmetic` premise names, is
/// `Verified`. Its liar twin `result == BvAdd(x, 2)` is false at every `x` and
/// is refuted, so the discharge is not vacuous.
///
/// The clause is spelled with the machine-width `BvAdd` node, which is the one
/// that DENOTES the 64-bit operation; the mathematical `Add` declines in the
/// decoder before ay is asked anything.
#[test]
fn a_published_machine_width_postcondition_is_discharged_and_its_liar_refuted() {
    use trust_ir::Ty;
    let at_u64 = |postcondition: &str| {
        let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_INC);
        bundle.module.func_types[0].params[0] = Ty::U64;
        bundle.module.func_types[0].returns[0] = Ty::U64;
        bundle.module.functions[0].blocks[0].params[0].1 = Ty::U64;
        if let trust_ir::inst::Inst::Const { ty, .. } =
            &mut bundle.module.functions[0].blocks[0].body[0].inst
        {
            *ty = Ty::U64;
        }
        if let trust_ir::inst::Inst::BinOp { ty, .. } =
            &mut bundle.module.functions[0].blocks[0].body[1].inst
        {
            *ty = Ty::U64;
        }
        let formula = bundle.module.proof_obligations[0]
            .formula
            .as_mut()
            .expect("the requires carries a formula");
        formula.payload = formula
            .payload
            .replace("4294967295", "18446744073709551615");
        set_formula(&mut bundle, 1, postcondition);
        reseal_module_identity(&mut bundle);
        discharge_report(&bundle)
    };

    let report =
        at_u64(r#"{"Eq":[{"Var":["_0","Int"]},{"BvAdd":[{"Var":["x","Int"]},{"Int":1},64]}]}"#);
    let postcondition = outcome_for(&report, INC_POST);
    assert_eq!(
        postcondition.outcome(),
        &TrustVcNativeTrustIrDischargeStatus::Verified,
        "{postcondition:?}"
    );
    assert!(
        postcondition.premises().iter().any(|premise| {
            premise.kind() == TrustVcNativeTrustIrPremiseKind::MachineArithmetic
        }),
        "the discharge rests on the wrapping model and must say so: {postcondition:?}"
    );

    let report =
        at_u64(r#"{"Eq":[{"Var":["_0","Int"]},{"BvAdd":[{"Var":["x","Int"]},{"Int":2},64]}]}"#);
    let liar = outcome_for(&report, INC_POST);
    assert!(
        matches!(
            liar.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
        ),
        "`result == x + 2` is false of `inc` and must be refuted: {liar:?}"
    );
    assert!(!report.verdict().is_ok());
    assert!(report.produced_certificates().is_empty());
}

// ---------------------------------------------------------------------------
// ADVERSARIAL REVIEW ROUND 1 — the four false `Discharged` probes, as
// regressions. Each of these produced a kernel-checked certificate for a claim
// that is FALSE in the program; each must now decline or refute.
// ---------------------------------------------------------------------------

/// Set an obligation's `trust-types.Formula@1` predicate, keeping the source
/// half of the payload the producer emits.
/// ADVERSARIAL REVIEW ROUND 7, MAJOR 1 — END TO END, on the path that is
/// actually reachable in this build.
///
/// A [`trust_ir::ProofFormula`] carries TWO producer-supplied renderings:
/// `payload` (which this lane decodes) and `smtlib`. trust-ir's own
/// `clean_expr_lowering::contract::predicate_text` — the grounding used by the
/// Clean-kernel re-check, and by anything else that reads an obligation's
/// predicate as SMT-LIB — is `smtlib.unwrap_or(payload)`: it PREFERS `smtlib`.
/// Nothing binds the two.
///
/// The callee-import half of that divergence is masked today by the input gate
/// (no `Certified` contract row survives it in this build, see
/// `a_certified_callee_contract_cannot_reach_the_lane_in_this_build`). THIS half
/// is not masked: the obligation the lane DECIDES is an ordinary `Pending`
/// postcondition, so a divergent `smtlib` on it would have the lane prove the
/// `payload` reading and mint a certificate — and its `formula_payload_sha256`
/// would bind the bytes it decided while every SMT-LIB reader of the same row
/// sees the other formula. It DECLINES.
#[test]
fn a_decided_obligation_with_two_disagreeing_renderings_declines() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_INC);
    // `ensures result >= 0` in the payload — provable, and the shape the lane
    // would otherwise discharge.
    set_formula(&mut bundle, 1, r#"{"Ge":[{"Var":["_0","Int"]},{"Int":0}]}"#);
    bundle.module.proof_obligations[1]
        .formula
        .as_mut()
        .expect("fixture has a formula")
        .smtlib = Some("(>= _0 0)".to_string());
    sync_assertion_atoms(&mut bundle, ProofId::new(1));
    reseal_module_identity(&mut bundle);

    let report = discharge_report(&bundle);
    let outcome = outcome_for(&report, INC_POST);
    let TrustVcNativeTrustIrDischargeStatus::Declined { reason } = outcome.outcome() else {
        panic!("two disagreeing renderings must not be decided: {outcome:?}");
    };
    assert!(reason.contains("smtlib"), "{reason}");
    assert!(
        report.produced_certificates().is_empty(),
        "nothing may be minted for a formula the lane cannot uniquely identify: {report:?}"
    );
}

/// Replaces one obligation's predicate, keeping its source record, and rewrites
/// the request's `Assertion` atom for it to the new formula, as a producer
/// would have written it. Not resealed.
fn set_formula(bundle: &mut NativeVerificationBundle, obligation: usize, formula_json: &str) {
    let obligation = &mut bundle.module.proof_obligations[obligation];
    let obligation_id = obligation.id;
    let formula = obligation.formula.as_mut().expect("fixture has a formula");
    let document: serde_json::Value =
        serde_json::from_str(&formula.payload).expect("payload is JSON");
    let source = document
        .get("source")
        .cloned()
        .unwrap_or(serde_json::json!({}));
    let predicate: serde_json::Value =
        serde_json::from_str(formula_json).expect("replacement predicate is JSON");
    formula.payload = serde_json::json!({ "formula": predicate, "source": source }).to_string();
    sync_assertion_atoms(bundle, obligation_id);
}

/// PROBE p12: one `CondBr` whose two targets are the SAME block, passing
/// DIFFERENT arguments.
///
/// `fn clamp(x: u32) -> u32 { if x > 10 { 10 } else { x } }` written with one
/// terminator: `CondBr x > 10 ? join([10]) : join([x])`. Resolving the block
/// arguments by TARGET bound both edges to the first list found, so the phi
/// assumption asserted `join_param == 10` on the else edge too — false in the
/// program — and `ensures result == 10` came back `Verified` with a certificate
/// and a produced evidence bundle. The arguments belong to the EDGE.
#[test]
fn two_edges_into_one_block_do_not_prove_a_false_postcondition() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let function = &mut bundle.module.functions[0];
        match &mut function.blocks[0].body[2].inst {
            trust_ir::inst::Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                *then_target = trust_ir::BlockId::new(3);
                *then_args = vec![trust_ir::ValueId::new(1)];
                *else_target = trust_ir::BlockId::new(3);
                *else_args = vec![trust_ir::ValueId::new(0)];
            }
            other => panic!("the fixture's entry ends in a CondBr, got {other:?}"),
        }
        function
            .blocks
            .retain(|block| !matches!(block.id.index(), 1 | 2));
    }
    // FALSE at x = 1, which `requires x >= 1` admits.
    set_formula(
        &mut bundle,
        1,
        r#"{"Eq":[{"Var":["_0","Int"]},{"Int":10}]}"#,
    );
    reseal_module_identity(&mut bundle);

    let report = discharge_report(&bundle);
    let postcondition = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
        ),
        "a claim that is false on the else edge must not verify: {postcondition:?}"
    );
    assert!(!report.verdict().is_ok());
    assert!(report.produced_certificates().is_empty());
    assert!(report.produced_evidence_bundles().is_empty());
}

/// PROBE p16: the same shape through a `Switch`, where a case and the default
/// share one target. `match x { 1 => 10, _ => x }` proving `ensures result == x`
/// — false at `x = 1`.
#[test]
fn a_switch_case_and_default_sharing_a_target_do_not_prove_a_false_postcondition() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let function = &mut bundle.module.functions[0];
        function.blocks[0].body.truncate(2);
        function.blocks[0].body.push(trust_ir::node::InstrNode::new(
            trust_ir::inst::Inst::Switch {
                value: trust_ir::ValueId::new(0),
                default: trust_ir::BlockId::new(3),
                default_args: vec![trust_ir::ValueId::new(0)],
                cases: vec![trust_ir::inst::SwitchCase {
                    value: trust_ir::Constant::Int(1),
                    target: trust_ir::BlockId::new(3),
                    args: vec![trust_ir::ValueId::new(1)],
                }],
                exhaustive_enum_unreachable: false,
            },
        ));
        function
            .blocks
            .retain(|block| !matches!(block.id.index(), 1 | 2));
    }
    set_formula(
        &mut bundle,
        1,
        r#"{"Eq":[{"Var":["_0","Int"]},{"Var":["x","Int"]}]}"#,
    );
    reseal_module_identity(&mut bundle);

    let report = discharge_report(&bundle);
    let postcondition = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
        ),
        "the case edge returns 10, so `result == x` is false at x = 1: {postcondition:?}"
    );
    assert!(report.produced_certificates().is_empty());
}

/// PROBE p18: a clause's `+` is MATHEMATICAL, and this lane decides at a
/// machine width, so it declines rather than proving a different predicate.
///
/// `ensures result == x + 1` for `fn inc(x: u32) -> u32 { x + 1 }` was certified
/// with the precondition pinned to `x = u32::MAX`, where the clause's own value
/// is 2^32 and the program returns 0. The old disclosure — "the no-overflow
/// claim is a separate arithmetic-safety obligation" — does not cover this: a
/// `wrapping_add` lowers to the same plain `BinOp` the body lane accepts (a
/// CHECKED add lowers to `Inst::Overflow`, which declines), so for a wrapping
/// body no panic-freedom row can ever fail.
#[test]
fn spec_arithmetic_is_never_decided_at_a_machine_width() {
    // The checked-in fixture, unmodified: the shape declines outright.
    let report = discharge_report(&discharge_scalar_fixture(DISCHARGE_SCALAR_INC));
    let postcondition = outcome_for(&report, INC_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { reason }
                if reason.contains("MATHEMATICAL") && reason.contains("u32")
        ),
        "{postcondition:?}"
    );
    assert!(!report.verdict().is_ok());
    assert!(report.produced_certificates().is_empty());

    // And at the one input where the two readings differ, which is what the
    // probe pinned: the precondition no longer excludes the overflow.
    let mut wrapped = discharge_scalar_fixture(DISCHARGE_SCALAR_INC);
    set_formula(
        &mut wrapped,
        0,
        r#"{"Ge":[{"Var":["x","Int"]},{"Int":4294967295}]}"#,
    );
    reseal_module_identity(&mut wrapped);
    let report = discharge_report(&wrapped);
    assert!(
        matches!(
            outcome_for(&report, INC_POST).outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { .. }
        ),
        "{report:?}"
    );
    assert!(report.produced_certificates().is_empty());
}

/// PROBE p19: a def-site `requires` that names the RETURN PLACE is not assumed.
///
/// The clause parser maps `result` to `_0` unconditionally, so a `requires`
/// mentioning the result arrives as a constraint on the output. Assumed
/// verbatim it PINS `_0` and proves any postcondition about it — `ensures
/// result == 7` was `Verified` with a certificate for a function that returns 1
/// at x = 1. Preconditions are lowered in a scope without `_0`, so the row
/// refuses the request instead.
#[test]
fn a_requires_naming_the_return_place_refuses_the_request() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    set_formula(&mut bundle, 0, r#"{"Eq":[{"Var":["_0","Int"]},{"Int":7}]}"#);
    set_formula(&mut bundle, 1, r#"{"Eq":[{"Var":["_0","Int"]},{"Int":7}]}"#);
    reseal_module_identity(&mut bundle);

    let report = discharge_report(&bundle);
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
    );
    let postcondition = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { reason }
                if reason.contains("_0") && reason.contains("precondition")
        ),
        "{postcondition:?}"
    );
    assert!(report.produced_certificates().is_empty());
}

/// PROBE p11: an obligation that names NO owning function is not decided
/// against whatever body the request happens to name.
///
/// `ProofObligation.function` is an `Option`. A row with `function: None` was
/// decided against the requested function's body and, when it verified, minted a
/// certificate and an evidence row binding that obligation id as `Discharged`.
/// Ownership is now required POSITIVELY.
#[test]
fn an_obligation_with_no_owning_function_declines() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.proof_obligations[1].function = None;
    reseal_module_identity(&mut bundle);

    let report = discharge_report(&bundle);
    let postcondition = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { reason }
                if reason.contains("names no owning function")
        ),
        "{postcondition:?}"
    );
    assert!(!report.verdict().is_ok());
    assert!(report.produced_certificates().is_empty());
    assert!(report.produced_evidence_bundles().is_empty());
}

/// PROBE (round 2): a producer value spelled `_0` IS the return place.
///
/// `declare_values` wrote the value under its own name and then wrote the
/// return place over the top, so the two became ONE unit variable. Here the
/// constant `10` of `fn clamp(x: u32) -> u32 { if x > 10 { 10 } else { x } }`
/// carries that name, so `pc$0 => _0 == 10` pins the RESULT to 10 on every
/// path, and `ensures result == 10` came back `Verified` with a certificate
/// although `clamp(1) == 1` and `requires x >= 1` admits `x = 1`. The name is
/// reserved now, and the body refuses to lower rather than renaming it — a
/// rename would silently change what a clause spelling `_0` resolves to.
#[test]
fn a_value_named_like_the_return_place_refuses_the_request() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.functions[0].value_names = Some(vec![
        (trust_ir::ValueId::new(0), "x".to_string()),
        (trust_ir::ValueId::new(1), "_0".to_string()),
    ]);
    // FALSE at x = 1, which `requires x >= 1` admits.
    set_formula(
        &mut bundle,
        1,
        r#"{"Eq":[{"Var":["_0","Int"]},{"Int":10}]}"#,
    );
    reseal_module_identity(&mut bundle);

    let report = discharge_report(&bundle);
    let postcondition = outcome_for(&report, CLAMP_POST);
    assert!(
        matches!(
            postcondition.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Declined { reason }
                if reason.contains("_0") && reason.contains("reserved")
        ),
        "{postcondition:?}"
    );
    assert_eq!(
        report.verdict(),
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
    );
    assert!(report.produced_certificates().is_empty());
    assert!(report.produced_evidence_bundles().is_empty());
}

/// PROBE (round 2): a terminator that is not the block's last instruction.
///
/// `successor_ids` and `collect_edges` read `body.last()` rather than trust-ir's
/// own `Block::terminator()`. With a dead `Return 10` appended after the
/// `CondBr`, the branch was silently ignored, both arms and the join became
/// unreachable, and the dead `Return` was read as the terminator — so
/// `ensures result == 10` verified with a certificate for a body every real
/// path of which returns `x` or `10`. `NativeVerificationBundle::validate()`
/// does not reject the shape; trust-ir-build's `validate_module` does, and this
/// crate does not depend on it.
#[test]
fn a_terminator_that_is_not_last_refuses_the_request() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.functions[0].blocks[0]
        .body
        .push(trust_ir::node::InstrNode::new(
            trust_ir::inst::Inst::Return {
                values: vec![trust_ir::ValueId::new(1)],
            },
        ));
    // FALSE at x = 1, which `requires x >= 1` admits.
    set_formula(
        &mut bundle,
        1,
        r#"{"Eq":[{"Var":["_0","Int"]},{"Int":10}]}"#,
    );
    reseal_module_identity(&mut bundle);

    // ROUND 4: the PRODUCER VALIDATOR input gate subsumes this shape, so the
    // refusal now happens a layer earlier — the whole module is refused instead
    // of this obligation declining, which is strictly stronger. The lane's own
    // terminator-position gate is unchanged and is still exercised directly by
    // `native_discharge::body::tests::
    // a_terminator_that_is_not_the_last_instruction_declines`.
    let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { errors, .. }) =
        TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
    else {
        panic!("a terminator that is not last must be refused, not decided");
    };
    assert!(
        errors.contains("is not the final instruction"),
        "the refusal must name what it refused: {errors}"
    );
}

/// No certificate the discharge lane mints has coverage basis K establishes
/// (trust-ir-build never kernel-replays it), so release admission refuses
/// every produced artifact `CertificateCoverageUndetermined`.
/// The assertion-id rules are measured against that one refusal: an unedited
/// produced artifact carries its id and is refused for coverage and nothing
/// else.
#[cfg(feature = "proof-certificates")]
#[track_caller]
fn assert_refused_for_coverage_alone(artifact: &TrustVcNativeProofArtifact) {
    assert_eq!(
        artifact.admission().rejection_reasons(),
        &[TrustVcNativeArtifactRejection::CertificateCoverageUndetermined],
        "the unedited row must be refused for coverage alone, or this test proves nothing: \
         {artifact:?}"
    );
}

fn sha256_hex_of(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Regenerate the checked-in discharge fixtures' identities in place.
///
/// The fixtures are authored by hand (a compiler that can dump them does not
/// exist on this machine yet), so their module digest starts as a placeholder.
/// This rewrites it — and everything that quotes it — using trust-ir's own
/// `Module::stable_digest`, never a hand-written value, so the files on disk are
/// self-consistent and the runner CLI can consume them directly.
///
/// Env-gated because it WRITES to the source tree. Run it after editing a
/// fixture by hand:
///
/// ```text
/// TRUST_VC_REGENERATE_DISCHARGE_FIXTURES=1 targo --unverified test \
///     -p trust-vc-trust-engine --test native_trust_ir_bundle -- regenerate
/// ```
#[test]
fn regenerate_discharge_fixtures() {
    if std::env::var_os("TRUST_VC_REGENERATE_DISCHARGE_FIXTURES").is_none() {
        return;
    }
    for name in [
        "discharge_scalar_branch",
        "discharge_scalar_branch_liar",
        "discharge_scalar_inc",
        "discharge_callee_contract_liar",
    ] {
        let path = format!(
            "{}/fixtures/trust_ir_native/{name}.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let source = std::fs::read_to_string(&path).expect("fixture should read");
        let authored: NativeVerificationBundle =
            serde_json::from_str(&source).expect("fixture should decode");
        // These are authored request-only fixtures, not persisted verifier
        // results. Construct their current producer envelope through trust-ir;
        // never relabel an old wire envelope or carry old evidence into it.
        assert!(
            authored.evidence_bundles.is_empty(),
            "fixture regeneration cannot migrate verifier evidence"
        );
        let mut bundle = NativeVerificationBundle::new(
            authored.producer,
            authored.input,
            authored.trust_ir_module_digest,
            authored.module,
            authored.lineage,
        );
        bundle.provenance = authored.provenance;
        bundle.diagnostics = authored.diagnostics;
        bundle.compiler_facts = authored.compiler_facts;
        bundle.requests = authored.requests;
        // Preserve every authored serialization choice. The new constructor
        // owns the schema; the ordinary consumer still judges the policy.
        bundle.serialization.canonical_order = authored.serialization.canonical_order;
        bundle.serialization.sort_unordered_sets = authored.serialization.sort_unordered_sets;
        bundle.serialization.messagepack_named_fields =
            authored.serialization.messagepack_named_fields;
        bundle.serialization.unknown_fields = authored.serialization.unknown_fields;
        // Each TrustVc request carries the `Assertion` replay atoms a producer
        // writes (the obligation's formula and compiler-fact number), rebuilt
        // from the edited module; this also reseals.
        install_bridge_atoms(&mut bundle);
        // Through the ADAPTER, not `bundle.validate()` directly: the adapter
        // also runs the producer validator and the export seam's input gates,
        // which a fixture must pass to be consumable.
        //
        // MERGED 2026-09-23: `consume_`, not `validate_`. Upstream made
        // `validate_native_trust_ir_bundle` refuse any bundle whose rollup does
        // not exit `Ok`, and `discharge_scalar_branch_liar` is DESIGNED to come
        // back `Refuted`; what this regenerator checks is that each fixture is
        // consumable, which is exactly `consume_`.
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect("a regenerated fixture must be consumable");
        assert_eq!(report.module_name(), bundle.module.name);
        assert_eq!(
            report.trust_ir_module_digest(),
            bundle.trust_ir_module_digest.to_string()
        );
        assert_eq!(
            report.compiler_facts_digest(),
            bundle.compiler_facts.stable_digest().to_string()
        );
        let expected_requests = bundle
            .requests
            .iter()
            .filter(|request| matches!(request, NativeVerificationRequest::TrustVc(_)))
            .count();
        assert!(
            expected_requests > 0,
            "a discharge fixture must contain TrustVc requests"
        );
        assert_eq!(report.requests().len(), expected_requests);
        // Consumability is the requirement here. The liar fixtures intentionally
        // return refuted verdicts, so regeneration must not require an Ok rollup.
        let json = serde_json::to_string_pretty(&bundle).expect("fixture should encode");
        let bytes = format!("{json}\n");
        if std::fs::read(&path).ok().as_deref() != Some(bytes.as_bytes()) {
            std::fs::write(&path, bytes).expect("fixture should write");
        }
    }
}

/// REGRESSION, adversarial review round 4 (F1): the SIGNATURE and the ENTRY
/// BLOCK may disagree about a parameter, and the clause was decided at the
/// BLOCK sort.
///
/// `declare_values` reads the formals from `entry.params`; `function_return_sort`
/// reads the return from `module.func_types`. Nothing related the two. A module
/// whose signature says `i32` while its entry block says `u32` therefore had
/// `ensures x >= 0` decided at u32 — vacuously true — and published as a
/// `Discharged` claim about a parameter every caller sees as SIGNED, where it is
/// false at `x = -1`. Measured before the gate: `outcome: Verified`, a
/// kernel-checked certificate and a produced evidence bundle.
///
/// The fix is the PRODUCER's own validator as an input gate: this exact shape is
/// `trust-ir-build`'s `entry block params … do not match signature params`
/// (validate.rs:1812 at the pinned rev). The control is the first case: at the
/// honest signature the very same clause still verifies, so it is the
/// disagreement — not the clause — that is refused.
#[test]
fn a_signature_that_disagrees_with_its_entry_block_is_refused() {
    fn consume(
        signature_param: Option<trust_ir::Ty>,
    ) -> Result<TrustVcNativeTrustIrBundleReport, TrustEngineError> {
        let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
        set_formula(&mut bundle, 1, r#"{"Ge":[{"Var":["x","Int"]},{"Int":0}]}"#);
        if let Some(ty) = signature_param {
            bundle.module.func_types[0].params[0] = ty;
        }
        reseal_module_identity(&mut bundle);
        TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
    }

    // CONTROL: signature u32, entry block u32. `x >= 0` holds at u32, and the
    // gate lets the honest module through untouched.
    let honest = consume(None).expect("the honest fixture is a valid module");
    assert_eq!(
        outcome_for(&honest, CLAMP_POST).outcome(),
        &TrustVcNativeTrustIrDischargeStatus::Verified,
        "the control must still verify, or the probe below proves nothing"
    );

    // PROBE: signature i32, entry block u32. Deciding `x >= 0` at the block sort
    // publishes a false claim about a signed parameter.
    let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { module, errors }) =
        consume(Some(trust_ir::Ty::I32))
    else {
        panic!("a signature/entry-block disagreement must be REFUSED, not decided");
    };
    assert_eq!(module, "trust_discharge_scalar_branch");
    assert!(
        errors.contains("entry block params") && errors.contains("signature params"),
        "the refusal must name the validation error it refused on: {errors}"
    );
}

/// REGRESSION, adversarial review round 4 (F2): two proof obligations sharing
/// one `ProofId` were read TWO WAYS.
///
/// `consume_native_trust_ir_bundle` collects the rows into a `BTreeMap` keyed by
/// id, so the LAST duplicate wins and feeds the ownership/site/kind gates and the
/// report's attribution; `lower_predicate` re-found the row with `.iter().find()`,
/// so the FIRST won and THAT is the predicate the solver decided. The gates clear
/// on one row while the solver proves the other, and the certificate binds the
/// formula bytes of the row that was never decided. Measured before the gate:
/// `outcome: Verified` with `formula_payload_sha256` equal to the digest of the
/// `_0 == 5` row, while `_0 >= 0` is what ay was asked.
///
/// `trust-ir-build`'s validator rejects this shape too (`duplicate proof
/// obligation id`, validate.rs:1819 at the pinned rev).
#[test]
fn two_obligations_sharing_one_id_are_refused() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    // Rows are [id 0 precondition, id 1 postcondition]. Put a TRIVIALLY TRUE
    // decoy that also claims id 1 FIRST, and make the row the gates and the
    // report read — the last — a claim that is FALSE of this body.
    let decoy = bundle.module.proof_obligations[1].clone();
    bundle.module.proof_obligations.insert(1, decoy);
    set_formula(&mut bundle, 1, r#"{"Ge":[{"Var":["_0","Int"]},{"Int":0}]}"#);
    set_formula(&mut bundle, 2, r#"{"Eq":[{"Var":["_0","Int"]},{"Int":5}]}"#);
    reseal_module_identity(&mut bundle);

    let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { errors, .. }) =
        TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
    else {
        panic!("one id read two ways must be REFUSED, not decided");
    };
    assert!(
        errors.contains("duplicate proof obligation id"),
        "the refusal must name the validation error it refused on: {errors}"
    );
}

/// The gate is the PRODUCER's validator, not a copy of two of its checks: a
/// shape neither blocker covers is refused by the same path, with the
/// validator's own wording.
#[test]
fn the_producer_validator_gate_refuses_shapes_no_hand_written_gate_covers() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    // An embedded source RANGE naming a file-table index that does not exist.
    // Nothing in this crate reads `Module::files`, so no hand-written gate here
    // would ever have been written for it.
    let source = bundle.module.proof_obligations[1]
        .source
        .as_mut()
        .expect("the fixture obligation carries a source");
    source.range = Some(trust_ir::proof::ProofObligationSourceRange {
        file: 9999,
        start_line: 1,
        start_col: 1,
        end_line: 1,
        end_col: 2,
    });
    reseal_module_identity(&mut bundle);

    let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { errors, .. }) =
        TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
    else {
        panic!("a module the producer validator rejects must be refused");
    };
    assert!(
        errors.contains("file") && errors.contains("#1"),
        "unexpected refusal text: {errors}"
    );
}

/// The ONE verdict the gate deliberately carries past it is the REJECTING
/// AUTHORITY's own capability verdict — a `Discharged` row with no certificate
/// THAT authority admits — and the checked-in import fixture at its admission
/// baseline depends on exactly that, and on nothing else.
///
/// Round 5: this asserted a two-variant OR, so it did not pin WHICH variant the
/// fixture produces and would have kept passing if the fixture drifted onto the
/// kernel-recheck rejection. It now names the one variant.
#[test]
fn the_gate_relaxes_only_the_validators_own_replay_capability_verdicts() {
    let bundle = native_bundle_fixture();
    let errors = trust_ir_build::validate_module(&bundle.module);
    assert_eq!(
        errors.len(),
        1,
        "the import fixture should produce exactly one validator error: {errors:?}"
    );
    assert!(
        matches!(
            errors[0],
            trust_ir_build::ValidationError::DischargedWithoutCertificate { .. }
        ),
        "the relaxation is pinned to `DischargedWithoutCertificate` alone; the import fixture \
         now produces: {errors:?}"
    );
    // And the lane still consumes it.
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("the import fixture must still be consumable");
    assert!(!report.requests().is_empty());
}

// ---------------------------------------------------------------------------
// Adversarial review round 5 — an UNESTABLISHED callee contract must never be
// assumed, and the producer validator's kernel-recheck rejection is a module
// defect, not a capability verdict.
// ---------------------------------------------------------------------------

/// `fn inc(x: u32) -> u32 { g(x) }` with `fn g(a: u32) -> u32 { a }`, built on
/// the `inc` discharge fixture. `g` publishes one def-site `ensures` at
/// `status`, carrying `formula_json` in `g`'s own names; `inc`'s own
/// postcondition (obligation 1, the only one the request asks about) carries
/// `caller_json`.
///
/// DERIVED, NEVER FORGED: every identity downstream of the edit is recomputed
/// by `reseal_module_identity` from trust-ir's own `Module::stable_digest`.
fn callee_contract_bundle(
    status: ProofStatus,
    formula_json: &str,
    caller_json: &str,
) -> NativeVerificationBundle {
    callee_contract_bundle_at(status, formula_json, caller_json, trust_ir::Ty::U32, None)
}

/// As above, over `ty`, and with an optional SMT-LIB rendering for the callee
/// contract. The SMT-LIB text is what trust-ir's own contract lowering reads
/// (`predicate_text` prefers `smtlib`), so it is what decides whether a
/// `Certified` row can carry a kernel-checkable certificate at all.
fn callee_contract_bundle_at(
    status: ProofStatus,
    formula_json: &str,
    caller_json: &str,
    ty: trust_ir::Ty,
    callee_smtlib: Option<&str>,
) -> NativeVerificationBundle {
    use trust_ir::node::InstrNode;
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    use trust_ir::{
        Block, BlockId, FuncTyId, Function, Inst, ObligationKind, ProofFormula, ProofObligation,
        ValueId,
    };

    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_INC);

    // 0. The whole fixture moves to `ty`: the shared function type and both
    //    entry blocks, so signature and entry params still agree (round 4).
    bundle.module.func_types[0].params = vec![ty.clone()];
    bundle.module.func_types[0].returns = vec![ty.clone()];

    // 1. `inc` becomes a single call to `g`, returning its result.
    {
        let inc = &mut bundle.module.functions[0];
        let entry = &mut inc.blocks[0];
        entry.params[0].1 = ty.clone();
        entry.body.clear();
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
    }

    // 2. `g` is the identity on its only parameter. Same signature as `inc`, so
    //    it reuses func type 0 — entry-block params and signature params agree,
    //    which is what the round-4 gate requires.
    {
        let mut callee = Function::new(FuncId::new(1), "g", FuncTyId::new(0), BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.params.push((ValueId::new(0), ty.clone()));
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        callee.blocks.push(entry);
        callee.value_names = Some(vec![(ValueId::new(0), "a".to_string())]);
        // Bundle schema 8: a function's producer must be covered by the
        // bundle's `source_languages` (`Rust` here).
        callee.producer = Some(trust_ir::Producer::TRust);
        bundle.module.functions.push(callee);
    }

    // 3. `g`'s published def-site contract, at the status under test.
    bundle.module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(7),
            ObligationKind::Postcondition,
            status,
            "g ensures",
        )
        .with_function(FuncId::new(1))
        .with_formula(ProofFormula {
            schema: "trust-types.Formula@1".to_string(),
            payload: serde_json::json!({
                "formula": serde_json::from_str::<serde_json::Value>(formula_json)
                    .expect("callee predicate is JSON"),
            })
            .to_string(),
            smtlib: callee_smtlib.map(ToString::to_string),
            sort: Some("Bool".to_string()),
            bindings: Vec::new(),
        }),
    );

    // 3b. A `Certified` row means nothing without the certificate the tier
    //     stands for, so attach the lineage-bound `CleanCic` the lane requires.
    //     DERIVED: the lineage digest comes from trust-ir's own
    //     `clean_cic_lineage_digest`, never hand-written.
    //     The kernel grounds a clause that names `_0` only when the module
    //     binds `_0` to an unsigned place, so the row carries that typed
    //     binding and the certificate is minted with the module in scope.
    if status == ProofStatus::Certified {
        let row = bundle
            .module
            .proof_obligations
            .last_mut()
            .expect("the callee contract was just pushed");
        if let Some(formula) = row.formula.as_mut() {
            formula.bindings = vec![(
                "_0".to_string(),
                ClauseBinding {
                    sort: ClauseSort::Int,
                    place: ClausePlace::ResultSlot { index: 0 },
                },
            )];
        }
        let obligation = row.clone();
        let certificate =
            trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in(
                &bundle.module,
                &obligation,
                "trust_vc",
            )
            .expect(
                "a `Certified` row needs a certificate trust-ir's own Clean kernel actually \
                 discharges; there is no way to hand-write one",
            );
        bundle.module.proof_certificates.push(certificate);
    }

    // 4. The caller claims `caller_json`, and the request asks about that row
    //    alone — the def-site `requires` (obligation 0) stays in the module and
    //    is still assumed. `inc`'s body is now `[Call, Return]`, so the row is
    //    re-sited at that `Return`.
    set_formula(&mut bundle, 1, caller_json);
    bundle.module.proof_obligations[1].site = Some(trust_ir::ObligationSite::new(
        FuncId::new(0),
        BlockId::new(0),
        1,
    ));
    {
        let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
            panic!("fixture first request should be TrustVc");
        };
        request.obligations = vec![ProofId::new(1)];
    }
    bundle.lineage.nodes[0].obligations = vec![ProofId::new(1)];

    reseal_module_identity(&mut bundle);
    bundle
}

/// THE ROUND-5 BLOCKER. `lower_call` assumed a callee's published `ensures`
/// with no look at its `ProofStatus`, so a contract the producer has stamped
/// `Failed` — explicitly NOT established — was imported as a fact and the
/// caller's postcondition published as `verdict=Discharged` with a
/// kernel-checked certificate.
///
/// `inc(0) == 0`, so `ensures _0 >= 100` is FALSE of this program; only the
/// assumed contract can make it provable. Every unestablished status must
/// refuse, and the refusal must name the status it refused on.
#[test]
fn an_unestablished_callee_contract_is_refused_never_assumed() {
    const FALSE_OF_THE_PROGRAM: &str = r#"{"Ge":[{"Var":["_0","Int"]},{"Int":100}]}"#;

    for (status, label) in [
        (ProofStatus::Pending, "Pending"),
        (ProofStatus::Failed, "Failed"),
        (ProofStatus::Trusted, "Trusted"),
    ] {
        let bundle = callee_contract_bundle(status, FALSE_OF_THE_PROGRAM, FALSE_OF_THE_PROGRAM);
        // A `Trusted` row with no certificate that attributes the trust is
        // refused by the producer's own validator before the lane runs, so the
        // contract cannot be assumed either. The lane's own refusal of a
        // `Trusted` contract is pinned by the lib test
        // `a_callee_contract_at_an_unestablished_status_declines`.
        if label == "Trusted" {
            let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator {
                errors,
                ..
            }) = TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
            else {
                panic!("an unattributed Trusted callee contract must be refused at the door");
            };
            assert!(
                errors.contains(
                    "status is Trusted but no certificate carries ProofEvidence::Trusted"
                ),
                "{errors}"
            );
            continue;
        }
        let report = discharge_report(&bundle);
        let outcome = outcome_for(&report, INC_POST);
        assert!(
            matches!(
                outcome.outcome(),
                TrustVcNativeTrustIrDischargeStatus::Declined { .. }
            ),
            "a callee contract at `{label}` must be REFUSED, not assumed: {outcome:?}"
        );
        let rendered = format!("{outcome:?}");
        assert!(
            rendered.contains(label),
            "the refusal must name the status it refused on: {rendered}"
        );
        assert!(
            !report.verdict().is_ok(),
            "an unestablished callee contract must never publish a Discharged verdict: {:?}",
            report.verdict()
        );
        assert!(
            report.produced_certificates().is_empty(),
            "a refused request mints no certificate: {:?}",
            report.produced_certificates()
        );
    }
}

/// THE MEASURED COST of round 6's blocker-1 fix, end to end. This REPLACES
/// round 5's positive control, which rested on a `Discharged` label.
///
/// Requiring `Certified` means requiring a certificate something actually
/// re-checks: trust-ir's own minter makes it, and `trust_ir_build`'s
/// `validate_certified_evidence_with_catalog`, run as this crate's input gate,
/// re-checks it. At this pin trust-ir grounds a contract only from a formula
/// stating one SMT-LIB text (schema `smtlib2`), while this lane decodes only
/// `trust-types.Formula@1`. So the callee contract this lane could read — the
/// clause bound to an unsigned result, with or without its SMT-LIB rendering —
/// cannot be minted, and no `Certified` callee contract row can reach the lane
/// (`one_rendering_and_a_kernel_certificate_cannot_both_hold_at_this_pin`
/// pins the disjointness). A callee `ensures` cannot be imported through the
/// bundle entry point at this pin; the seam itself stays exercised by the lib
/// tests in `native_discharge::body`, which lower a `Certified` row with its
/// lineage-bound certificate directly.
#[test]
fn a_certified_callee_contract_cannot_be_minted_at_this_pin() {
    use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};

    const NON_NEGATIVE: &str = r#"{"Ge":[{"Var":["_0","Int"]},{"Int":0}]}"#;
    const NON_NEGATIVE_SMT: &str = "(>= _0 0)";

    // `u32`: trust-ir grounds `_0 >= 0` only when `_0` is bound to an unsigned
    // place. The helper mints only for `Certified`, so the row is built
    // `Pending` and the mint is attempted here.
    for smtlib in [None, Some(NON_NEGATIVE_SMT)] {
        let mut bundle = callee_contract_bundle_at(
            ProofStatus::Pending,
            NON_NEGATIVE,
            NON_NEGATIVE,
            trust_ir::Ty::U32,
            smtlib,
        );
        let row = bundle
            .module
            .proof_obligations
            .last_mut()
            .expect("the callee contract was pushed");
        row.formula
            .as_mut()
            .expect("the callee contract has a formula")
            .bindings = vec![(
            "_0".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        )];
        let contract = row.clone();
        assert!(
            contract_clean_cic_certificate_in(&bundle.module, &contract, "trust_vc").is_none(),
            "a callee contract this lane decodes minted a certificate (rendering: {smtlib:?}); \
             the E11 import path is reachable again and must be re-measured"
        );
    }
}

/// THE MEASURED COST of round 6's blocker-1 fix, disclosed rather than smoothed
/// over.
///
/// Requiring `Certified` means requiring a certificate the Clean kernel
/// re-checks in process, and at the pinned trust-ir that kernel grounds only a
/// NARROW predicate fragment: literal-only propositions and the single
/// free-variable tautology `x >= 0`, the latter only with `x` bound to an
/// unsigned place of the module. A callee contract that relates two
/// names — `ensures result == a`, the ordinary case — cannot carry a
/// kernel-checkable certificate at all, so it can no longer be imported through
/// the bundle entry point. It DECLINES; it never publishes.
///
/// This test pins that boundary so a pin that widens the fragment flips a test
/// rather than passing unnoticed. The refusal comes from the producer validator
/// itself, which is the point: the lane is not deciding what counts as evidence.
#[test]
fn a_relational_callee_contract_cannot_be_certified_at_this_pin() {
    const G_IS_THE_IDENTITY: &str = r#"{"Eq":[{"Var":["_0","Int"]},{"Var":["a","Int"]}]}"#;
    let obligation = trust_ir::ProofObligation::new(
        ProofId::new(7),
        trust_ir::ObligationKind::Postcondition,
        ProofStatus::Certified,
        "g ensures",
    )
    .with_function(FuncId::new(1))
    .with_formula(trust_ir::ProofFormula {
        schema: "trust-types.Formula@1".to_string(),
        payload: G_IS_THE_IDENTITY.to_string(),
        smtlib: Some("(= _0 a)".to_string()),
        sort: Some("Bool".to_string()),
        bindings: Vec::new(),
    });
    assert!(
        trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
            &obligation,
            "trust_vc"
        )
        .is_none(),
        "if this starts minting, the relational case is importable again and the disclosure \
         below is stale"
    );
}

/// THE MEASURED COST of round 7's `smtlib`/`payload` binding, pinned rather than
/// asserted in a doc comment.
///
/// The binding says a formula must have ONE rendering: `smtlib` absent, or
/// byte-identical to `payload`. Under the one schema this lane accepts,
/// `trust-types.Formula@1`, the two halves are then disjoint by construction:
///
/// * trust-ir grounds a contract only from a formula stating ONE SMT-LIB text,
///   schema `smtlib2`, so a `trust-types.Formula@1` row mints NO certificate,
///   with a JSON payload or an SMT-LIB one, with a rendering or without, and
///   the row cannot be `Certified`;
/// * an `smtlib2` row mints, and this lane's decoder needs a JSON document
///   with a `formula` key, so the row DECLINES here.
///
/// So the E11 import path — a callee `ensures` imported on a kernel-rechecked
/// certificate — is structurally unreachable end to end at this pin. That is a
/// real capability cost and it is recorded as a test so a pin that unifies the
/// two renderings (or grounds the kernel from `payload`) flips a test rather
/// than passing unnoticed. The seam itself stays exercised by the
/// `native_discharge::body` lib tests, which lower a `Certified` row directly.
#[test]
fn one_rendering_and_a_kernel_certificate_cannot_both_hold_at_this_pin() {
    use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_in;
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};

    // The kernel grounds `_0 >= 0` only with the module in scope and `_0` bound
    // to an unsigned place: `inc` returns `u32`, so both halves bind the result
    // slot and differ only in the rendering.
    let module = discharge_scalar_fixture(DISCHARGE_SCALAR_INC).module;
    let result_binding = || {
        vec![(
            "_0".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        )]
    };
    let mintable = |formula: trust_ir::ProofFormula| {
        contract_clean_cic_certificate_in(
            &module,
            &trust_ir::ProofObligation::new(
                ProofId::new(7),
                trust_ir::ObligationKind::Postcondition,
                ProofStatus::Certified,
                "inc ensures",
            )
            .with_function(FuncId::new(0))
            .with_formula(formula),
            "trust_vc",
        )
        .is_some()
    };

    // Half 1: no `smtlib`, so the kernel is handed the JSON payload.
    assert!(
        !mintable(trust_ir::ProofFormula {
            schema: "trust-types.Formula@1".to_string(),
            payload: r#"{"formula":{"Ge":[{"Var":["_0","Int"]},{"Int":0}]}}"#.to_string(),
            smtlib: None,
            sort: Some("Bool".to_string()),
            bindings: result_binding(),
        }),
        "if a JSON payload starts minting, the two renderings have converged and the binding          can be relaxed"
    );

    // Half 2: `smtlib` == `payload` and both are SMT-LIB, under the lane's
    // schema. trust-ir grounds only an `smtlib2` formula, so this does not mint
    // either.
    assert!(
        !mintable(trust_ir::ProofFormula {
            schema: "trust-types.Formula@1".to_string(),
            payload: "(>= _0 0)".to_string(),
            smtlib: Some("(>= _0 0)".to_string()),
            sort: Some("Bool".to_string()),
            bindings: result_binding(),
        }),
        "if an opaque schema starts minting, re-read the disjointness above"
    );

    // Control: the same clause as an `smtlib2` formula mints, so the two halves
    // above measure the schema and the rendering, not the clause. This lane's
    // decoder cannot read an `smtlib2` payload, which is the other half of the
    // disjointness.
    assert!(
        mintable(trust_ir::ProofFormula {
            schema: "smtlib2".to_string(),
            payload: "(>= _0 0)".to_string(),
            smtlib: None,
            sort: Some("Bool".to_string()),
            bindings: result_binding(),
        }),
        "the SMT-LIB half must still mint, or this test is measuring the wrong thing"
    );
}

/// THE ROUND-5 MAJOR. `CertifiedCleanCicKernelRecheckFailed` is the kernel
/// re-checker's own rejection, and at the pinned rev it is
/// authority-INDEPENDENT (`validate_certified_evidence_with_catalog` takes no
/// authority argument), so a permissive authority would not remove it. Carrying
/// it past the input gate on the "capability verdict" rationale was wrong. It is
/// refused.
#[test]
fn the_gate_refuses_the_validators_kernel_recheck_rejection() {
    let mut bundle = native_bundle_fixture();
    // Back to the upstream corpus's own `Certified` tier, with the certificate
    // TERM corrupted so the in-process Clean-kernel re-check fails. (The
    // corpus's own term re-checks.)
    bundle.module.proof_obligations[0].status = ProofStatus::Certified;
    corrupt_clean_cic_term(&mut bundle);

    let errors = trust_ir_build::validate_module(&bundle.module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            trust_ir_build::ValidationError::CertifiedCleanCicKernelRecheckFailed { .. }
        )),
        "the fixture must actually produce the recheck rejection: {errors:?}"
    );

    let Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator {
        errors: refusal,
        ..
    }) = TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
    else {
        panic!("a failed kernel recheck must REFUSE the bundle at the input gate");
    };
    assert!(
        refusal.contains("kernel") || refusal.contains("recheck") || refusal.contains("Clean"),
        "the refusal must name the validation error it refused on: {refusal}"
    );
}

// ---------------------------------------------------------------------------
// ADVERSARIAL REVIEW ROUND 8 — THE EXPORT SEAM
//
// Everything before this point is about what the lane IMPORTS. These are about
// what it PUBLISHES. See `crate::native_assertion_id` for the table of the four
// renderings of one assertion identity and the corroboration grades.
// ---------------------------------------------------------------------------

/// THE RE-ATTRIBUTION PROBE, as a regression pin.
///
/// One field edited: `compiler_facts.obligation_sources[1].assertion_id` 1 -> 0.
/// Obligation 1 is `clamp`'s postcondition, which trust-vc PROVES; assertion 0
/// is `clamp`'s PRECONDITION, status `Pending`, which trust-vc only ASSUMES.
/// Unrefused, this publishes a release-admissible kernel-checked artifact
/// `{ assertion_id: "0", trust_ir_obligation_id: 1 }` — trust-vc claiming an
/// assertion it never proved is discharged, into the fleet's coverage join.
///
/// The discharge request's `Assertion` atom still says 1, so trust-ir refuses
/// the edit at the door (and trust-vc's atom gate would too:
/// `native_assertion_id::tests::a_forged_compiler_fact_refuses_the_bundle`).
/// Moving the atom WITH the fact leaves the payload's own rendering, which
/// trust-vc's input gate refuses, naming every rendering it saw.
#[test]
fn the_export_seam_refuses_a_compiler_fact_assertion_id_that_no_rendering_corroborates() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    assert_eq!(
        bundle.compiler_facts.obligation_sources[1].obligation,
        ProofId::new(1),
        "the probe re-attributes obligation 1, `clamp`'s postcondition"
    );
    let mut fact_alone = bundle.clone();
    fact_alone.compiler_facts.obligation_sources[1].assertion_id = Some(NativeAssertionId::new(0));
    reseal_module_identity(&mut fact_alone);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&fact_alone)
        .expect_err("a compiler fact its request's atom contradicts must be refused");
    assert!(
        error
            .to_string()
            .contains("does not match obligation 1 source assertion"),
        "{error}"
    );

    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(1), 0);
    reseal_module_identity(&mut bundle);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a bundle whose assertion-id renderings disagree must be refused");
    let TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
        obligation_id,
        renderings,
        ..
    } = &error
    else {
        panic!("unexpected error: {error}");
    };
    assert_eq!(*obligation_id, 1);
    // The refusal names EVERY rendering it saw, present and absent: a message
    // naming only the two that differ leaves a reader unable to tell which one
    // was edited.
    for expected in [
        "compiler_facts.obligation_sources[].assertion_id",
        "proof_obligations[].source.assertion_id",
        "payload source record `native_assertion_id`",
        "payload `source` object",
        "\"rust-assertion:1\"",
    ] {
        assert!(
            renderings.contains(expected),
            "refusal must name {expected}: {renderings}"
        );
    }
}

/// ISOLATES the A-vs-C rule. The pin above ends with two identities sharing
/// assertion 0, so it cannot tell which rule is load-bearing. Here obligation
/// 1's compiler-fact id and its request's atom both become 42, which no other
/// obligation uses: the atom agrees, the bundle-wide injection still holds, and
/// the ONLY thing wrong is that the payload this lane decodes says 1.
#[test]
fn the_export_seam_refuses_a_numeric_rendering_the_payload_contradicts() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    set_compiler_fact_assertion_id(&mut bundle, ProofId::new(1), 42);
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("the compiler fact and the decoded payload must render one identity");
    let TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
        obligation_id,
        reason,
        ..
    } = &error
    else {
        panic!("unexpected error: {error}");
    };
    assert_eq!(*obligation_id, 1);
    assert!(
        reason.contains("embedded in the formula payload"),
        "unexpected reason: {reason}"
    );
}

/// The same identity rendered as a STRING in two places, disagreeing.
#[test]
fn the_export_seam_refuses_two_string_renderings_that_disagree() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.proof_obligations[1]
        .source
        .as_mut()
        .expect("the postcondition carries a source identity")
        .assertion_id = "rust-assertion:7".to_string();
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("two string renderings of one identity may not disagree");
    assert!(
        matches!(
            &error,
            TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree { obligation_id, .. }
                if *obligation_id == 1
        ),
        "unexpected error: {error}"
    );
}

/// LIAR L7, AND WHAT A COLLISION COSTS.
///
/// A number two assertion identities share names neither of them. The
/// producer's own derivation makes that legitimate — `stable_u32_id` is
/// `sha256(..)[..4]` with 0 remapped to 1, so collisions are inevitable, and
/// refusing the bundle would accuse a conforming producer of contradicting
/// itself.
///
/// What a collision costs is the IDENTITY, not the bundle: every compiler fact
/// AND the request's atom move to 7, so the atom agrees with its fact, and the
/// row still publishes NO assertion id — a fail-closed `MissingAssertionId` on
/// the artifact rather than a number that could join to the wrong assertion
/// downstream. (The payload renderings are stripped first, so the payload rule
/// does not refuse the bundle before the seam is reached.)
#[cfg(feature = "proof-certificates")]
#[test]
fn a_numeric_assertion_id_two_identities_share_is_published_for_neither() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    strip_payload_renderings(&mut bundle);
    for obligation in [ProofId::new(0), ProofId::new(1)] {
        set_compiler_fact_assertion_id(&mut bundle, obligation, 7);
    }
    reseal_module_identity(&mut bundle);
    assert_eq!(
        assertion_atoms_mut(&mut bundle, 0, ProofId::new(1))[0].assertion_id,
        Some(NativeAssertionId::new(7)),
        "the atom moved with its fact"
    );

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a hash collision is a well-formed bundle, not a contradiction");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(
        evidence.native_assertion_id(),
        None,
        "a number two identities share may not be published: {evidence:?}"
    );
    let artifacts = report.admit_native_proof_artifacts();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(artifacts[0].assertion_id(), "");
    assert_eq!(
        artifacts[0].admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifacts[0]
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{:?}",
        artifacts[0]
    );
}

/// The direction that IS a contradiction under any derivation: one
/// `source.assertion_id` string carrying two different numbers. No hash function
/// maps one input to two outputs, so this stays a bundle refusal.
#[test]
fn the_export_seam_refuses_one_identity_rendered_as_two_numbers() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    for obligation in &mut bundle.module.proof_obligations {
        let formula = obligation
            .formula
            .as_mut()
            .expect("fixture carries formulas");
        formula.payload = formula
            .payload
            .replace("\"native_assertion_id\":0,", "")
            .replace("\"native_assertion_id\":1,", "");
        formula.payload = formula
            .payload
            .replace(
                "\"assertion_id\":\"rust-assertion:0\"",
                "\"assertion_id\":\"rust-assertion:same\"",
            )
            .replace(
                "\"assertion_id\":\"rust-assertion:1\"",
                "\"assertion_id\":\"rust-assertion:same\"",
            );
        obligation
            .source
            .as_mut()
            .expect("fixture carries source identities")
            .assertion_id = "rust-assertion:same".to_string();
    }
    sync_assertion_atoms(&mut bundle, ProofId::new(1));
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("one identity may not carry two numbers");
    let TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree { reason, .. } = &error else {
        panic!("unexpected error: {error}");
    };
    assert!(
        reason.contains("is not a function of the identity it re-encodes"),
        "unexpected reason: {reason}"
    );
}

/// ROUND 9's SECOND EXPORT-SEAM RENDERING — the obligation KIND.
///
/// The kind is what declines a row as a def-site precondition and what
/// dispatches `callee_contract_facts`; the compiler fact's `cause` is a second
/// rendering of it that this crate republishes on the artifact binding and folds
/// into `obligation_source_digest`. Probe R9-P12 moved only the `cause` of the
/// row trust-vc PROVES to `Precondition`: the bundle was accepted and the
/// published row said `obligation_kind = Postcondition` and
/// `compiler_facts_binding.cause = Precondition` at once.
#[test]
fn the_export_seam_refuses_an_obligation_kind_its_compiler_cause_contradicts() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let postcondition = bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(1))
        .expect("the fixture maps obligation 1");
    postcondition.cause = trust_ir::request::NativeObligationCause::Precondition;
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("one obligation may not be both a precondition and a postcondition");
    assert!(
        matches!(
            &error,
            TrustEngineError::NativeTrustIrObligationKindRenderingsDisagree { obligation_id, .. }
                if *obligation_id == 1
        ),
        "unexpected error: {error}"
    );
}

/// THE OVER-REJECTION GUARD for the rule above. The two vocabularies are not in
/// bijection — a compiler-side cause like `Assert` or `Other` legitimately
/// carries several kinds — so only the flat contradictions refuse. A
/// postcondition caused `Assert` is a bundle upstream considers well-formed and
/// this lane still consumes.
#[test]
fn a_compiler_cause_that_merely_differs_from_the_kind_is_not_a_contradiction() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let postcondition = bundle
        .compiler_facts
        .obligation_sources
        .iter_mut()
        .find(|source| source.obligation == ProofId::new(1))
        .expect("the fixture maps obligation 1");
    postcondition.cause = trust_ir::request::NativeObligationCause::Assert;
    reseal_module_identity(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a cause that is not the OPPOSITE kind is not a contradiction");
    assert_eq!(report.requests().len(), 1);
}

/// ROUND 9, THE NARROWED UNREADABLE RULE — a row with nothing to protect no
/// longer kills the bundle.
///
/// Round 8 ran the present-but-unreadable refusal over EVERY obligation in the
/// module, so one unrequested row whose payload is not JSON refused the whole
/// bundle — including the import lane, which never decodes a payload — and the
/// refusal's own text printed `A = absent; C = absent`: there was no numeric
/// rendering for the rule to protect (probe R9-P10). The rule now applies to
/// rows that carry a numeric rendering the seam could publish.
#[test]
fn an_unreadable_payload_on_a_row_with_no_numeric_rendering_is_not_a_bundle_refusal() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    bundle.module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            ProofId::new(7),
            trust_ir::ObligationKind::Postcondition,
            ProofStatus::Pending,
            "an unrequested obligation nothing asks about",
        )
        .with_source(trust_ir::ProofObligationSourceIdentity::new(
            "probe",
            "rust-assertion:7",
        ))
        .with_formula(trust_ir::ProofFormula {
            schema: "trust-types.Formula@1".to_string(),
            payload: "this is not json".to_string(),
            smtlib: None,
            sort: None,
            bindings: Vec::new(),
        }),
    );
    reseal_module_identity(&mut bundle);

    // No compiler-fact source row for obligation 7, so it carries no numeric
    // rendering at all — and the bundle is still consumed.
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a row with no numeric rendering has nothing for the rule to protect");
    assert_eq!(report.requests().len(), 1);
}

/// The same rule where it DOES have a subject: an unreadable payload beside a
/// numeric rendering still refuses the bundle, because an unreadable rendering
/// may not be treated as an absent one.
/// A rendering that is PRESENT and unreadable is not an absent one.
#[test]
fn the_export_seam_refuses_an_unreadable_assertion_id_rendering() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    {
        let formula = bundle.module.proof_obligations[1]
            .formula
            .as_mut()
            .expect("the postcondition carries a formula");
        formula.payload = formula
            .payload
            .replace("\"native_assertion_id\":1", "\"native_assertion_id\":\"1\"");
    }
    sync_assertion_atoms(&mut bundle, ProofId::new(1));
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("an unreadable rendering must fail closed, not default to absent");
    let TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree { reason, .. } = &error else {
        panic!("unexpected error: {error}");
    };
    assert!(reason.contains("unreadable"), "unexpected reason: {reason}");
}

/// NOTHING CORROBORATES IT — AND UPSTREAM GETS THERE FIRST.
///
/// MEASURED, and recorded rather than asserted: the `None` corroboration arm
/// (compiler-fact id present, no payload rendering, no `source.assertion_id`)
/// is UNREACHABLE for a requested obligation at this pin. Upstream's own
/// `NativeVerificationBundle::validate()` refuses the bundle first —
/// "native verification request 0 obligation 0 has no embedded source
/// identity" — so every obligation that can reach the export seam carries
/// rendering B, and therefore at least the bundle-wide-injection corroboration.
///
/// The arm stays as defence in depth (it is exercised directly in
/// `native_assertion_id`'s own unit tests), and this test pins WHY it is not
/// reachable, so a future relaxation of upstream's rule turns into a failing
/// test here rather than a silently stamped uncorroborated id.
#[test]
fn an_obligation_with_no_source_identity_cannot_reach_the_export_seam_at_all() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    for obligation in &mut bundle.module.proof_obligations {
        obligation.source = None;
        let formula = obligation
            .formula
            .as_mut()
            .expect("fixture carries formulas");
        formula.payload = formula
            .payload
            .replace("\"native_assertion_id\":0,", "")
            .replace("\"native_assertion_id\":1,", "");
    }
    sync_assertion_atoms(&mut bundle, ProofId::new(1));
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("upstream refuses a requested obligation with no embedded source identity");
    let TrustEngineError::InvalidNativeTrustIrBundle { errors } = &error else {
        panic!("unexpected error: {error}");
    };
    assert!(
        errors.contains("has no embedded source identity"),
        "unexpected errors: {errors}"
    );
}

/// THE ARTIFACT IS STAMPED ONLY WITH THE ID EVERY RENDERING AGREES ON.
///
/// `CompilerFactAssertionIdMismatch` compared the artifact's id against the
/// compiler fact's id, and on the discharge path BOTH came from the compiler
/// fact — a check on one field against itself. Round 8 stamped the payload's
/// rendering instead, which gave that check two independently-sourced sides and
/// left the row's own republished `assertion_id` compared against nothing
/// (round 9's blocker). The rule now has no preferred rendering at all: the
/// stamp is the value every rendering of the row agrees on.
#[cfg(feature = "proof-certificates")]
#[test]
fn a_produced_artifact_is_stamped_only_with_the_id_every_rendering_agrees_on() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);

    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    assert_eq!(evidence.native_assertion_id(), Some(1));
    assert_eq!(
        evidence.independent_assertion_id(),
        Some(1),
        "the discharge request's `Assertion` atom is the second rendering"
    );
    assert_eq!(evidence.compiler_facts_binding().assertion_id(), Some(1));
    let artifacts = report.admit_native_proof_artifacts();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(artifacts[0].assertion_id(), "1");
    assert_refused_for_coverage_alone(&artifacts[0]);
}

/// ROUND 9, THE BLOCKER — the shape the branch PUBLISHED and nothing compared.
///
/// A `TrustVcNativeTrustIrCertificateEvidence` row is what trust-runner
/// serializes into its report and what a consumer deserializes to mint
/// artifacts. Round 8 stamped the artifact from `independent_assertion_id` and
/// fell back to `assertion_id`, but never compared the two, so ONE JSON object
/// could report assertion 1, grade assertion 1 admissible, and mint an artifact
/// stamped assertion 0 with no rejection reason (probe R9-P9: move
/// `independent_assertion_id` and `compiler_facts_binding.assertion_id`
/// together, leave the row's own `assertion_id` alone).
///
/// DISCRIMINATOR: this test fails if the disagreement refusal in
/// `admit_native_proof_artifact` is removed — with it removed the artifact is
/// stamped "0" and ACCEPTED, which is the defect verbatim.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_export_seam_refuses_a_row_whose_own_renderings_disagree() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_refused_for_coverage_alone(&evidence.admit_native_proof_artifact());

    let mut row = serde_json::to_value(evidence).expect("evidence row serializes");
    row["independent_assertion_id"] = serde_json::json!(0);
    row["compiler_facts_binding"]["assertion_id"] = serde_json::json!(0);
    let moved: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(row).expect("evidence row round-trips");
    assert_eq!(moved.native_assertion_id(), Some(1));
    assert_eq!(moved.independent_assertion_id(), Some(0));

    let artifact = moved.admit_native_proof_artifact();
    assert_eq!(
        artifact.assertion_id(),
        "",
        "a disagreement publishes NO assertion id: {artifact:?}"
    );
    assert_eq!(
        artifact.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::AssertionIdRenderingsDisagree),
        "{artifact:?}"
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "the refusal travels with the missing id it caused: {artifact:?}"
    );
}

/// The SAME rule from the other side: move the row's own `assertion_id` and the
/// binding together and leave the payload's rendering alone (round 8's probe
/// R8-P8 shape, at the row layer). Round 8 caught this one; round 9's rule must
/// not lose it while gaining the one above.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_export_seam_refuses_a_row_whose_compiler_fact_renderings_were_moved() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);
    let evidence = &report.requests()[0].proof_evidence()[0];

    let mut row = serde_json::to_value(evidence).expect("evidence row serializes");
    row["assertion_id"] = serde_json::json!(0);
    row["compiler_facts_binding"]["assertion_id"] = serde_json::json!(0);
    let moved: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(row).expect("evidence row round-trips");
    assert_eq!(moved.independent_assertion_id(), Some(1));

    let artifact = moved.admit_native_proof_artifact();
    assert_eq!(artifact.assertion_id(), "", "{artifact:?}");
    assert_eq!(
        artifact.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::AssertionIdRenderingsDisagree),
        "{artifact:?}"
    );
}

/// WHAT IS PUBLISHED IS WHAT THE ROW REPORTS, and only that.
///
/// The row's own `assertion_id` is the id its `release_admission` graded and the
/// id a reader of the report sees. The other renderings CORROBORATE it; they are
/// never promoted into an id of their own. So a row that reports none publishes
/// none even when the payload or the compiler-fact binding still carries a
/// number — which is the shape a declined corroboration leaves behind (a number
/// two identities share, say).
///
/// DISCRIMINATOR: fails if the seam falls back to another rendering, which is
/// round 8's `independent_assertion_id.or(assertion_id)` and any widening of it.
#[cfg(feature = "proof-certificates")]
#[test]
fn a_row_publishes_the_id_it_reports_and_never_another_rendering() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);
    let evidence = &report.requests()[0].proof_evidence()[0];
    let row = serde_json::to_value(evidence).expect("evidence row serializes");

    // ROUND 11 CORRECTS THIS SUB-CASE. Round 9 asserted that a row stripped of
    // BOTH corroborating renderings still publishes the id it reports, on the
    // ground that "what is published is what the row reports". Round 10's probe
    // R10-P9 is exactly that shape, and it published a moved id: with no
    // independent rendering left, `assertion_id` and
    // `compiler_facts_binding.assertion_id` are two copies of ONE compiler-fact
    // field, so they agree by construction and corroborate nothing. Agreement
    // among copies is not corroboration; a row with no independent rendering
    // publishes NOTHING.
    let mut reported_only = row.clone();
    reported_only
        .as_object_mut()
        .expect("row is an object")
        .remove("independent_assertion_id");
    reported_only["compiler_facts_binding"]
        .as_object_mut()
        .expect("binding is an object")
        .remove("assertion_id");
    let reported_only: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(reported_only).expect("evidence row round-trips");
    assert_eq!(reported_only.native_assertion_id(), Some(1));
    assert_eq!(reported_only.independent_assertion_id(), None);
    let artifact = reported_only.admit_native_proof_artifact();
    assert_eq!(
        artifact.assertion_id(),
        "",
        "a reported id no independent rendering corroborates may not be published: {artifact:?}"
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{artifact:?}"
    );

    // R10-P9 ITSELF: move the reported id AND the republished compiler-fact
    // rendering together, with no independent rendering to contradict them.
    // Round 10 measured `assertion_id="0"`. Nothing is published now.
    let mut moved_together = row.clone();
    moved_together
        .as_object_mut()
        .expect("row is an object")
        .remove("independent_assertion_id");
    moved_together["assertion_id"] = serde_json::json!(0);
    moved_together["compiler_facts_binding"]["assertion_id"] = serde_json::json!(0);
    let moved_together: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(moved_together).expect("evidence row round-trips");
    let artifact = moved_together.admit_native_proof_artifact();
    assert_eq!(
        artifact.assertion_id(),
        "",
        "R10-P9: two copies of one field agreeing is not corroboration: {artifact:?}"
    );
    assert_eq!(
        artifact.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );

    // NOT reported, with both corroborating renderings intact: published as
    // nothing, and NOT as a disagreement — declining to license an id is a
    // decision, not a contradiction.
    let mut unreported = row;
    unreported
        .as_object_mut()
        .expect("row is an object")
        .remove("assertion_id");
    let unreported: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(unreported).expect("evidence row round-trips");
    assert_eq!(unreported.native_assertion_id(), None);
    assert_eq!(unreported.independent_assertion_id(), Some(1));
    assert_eq!(unreported.compiler_facts_binding().assertion_id(), Some(1));
    let artifact = unreported.admit_native_proof_artifact();
    assert_eq!(
        artifact.assertion_id(),
        "",
        "an unreported id may not be resurrected from another rendering: {artifact:?}"
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{artifact:?}"
    );
}

/// A row with NO numeric rendering at all publishes no assertion id — absence
/// never defaults to a value.
#[cfg(feature = "proof-certificates")]
#[test]
fn a_row_carrying_no_rendering_publishes_no_assertion_id() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);
    let evidence = &report.requests()[0].proof_evidence()[0];
    let mut row = serde_json::to_value(evidence).expect("evidence row serializes");
    let object = row.as_object_mut().expect("row is an object");
    object.remove("assertion_id");
    object.remove("independent_assertion_id");
    row["compiler_facts_binding"]
        .as_object_mut()
        .expect("binding is an object")
        .remove("assertion_id");
    let bare: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(row).expect("evidence row round-trips");

    let artifact = bare.admit_native_proof_artifact();
    assert_eq!(artifact.assertion_id(), "");
    assert_eq!(
        artifact.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{artifact:?}"
    );
}

/// `CompilerFactAssertionIdMismatch` IS NOT VACUOUS ANY MORE — pinned without
/// neutralizing anything.
///
/// Round 8's method finding: on the discharge path the artifact's assertion id
/// and the compiler fact it was compared against BOTH came from
/// `compiler_facts.obligation_sources[].assertion_id`, so that rejection could
/// never fire. Here the row is taken from a REAL discharge report and only the
/// compiler-fact BINDING is moved.
///
/// Round 9 corrected what this pins. The stamp is no longer taken from a
/// preferred rendering and compared against the binding — it is the value EVERY
/// rendering agrees on, so a moved binding means there IS no such value: the
/// artifact publishes no id and carries both
/// `AssertionIdRenderingsDisagree` and the `CompilerFactAssertionIdMismatch`
/// that the empty stamp still trips. Both are asserted, because the second is
/// the one round 8 claimed to have made non-vacuous.
#[cfg(feature = "proof-certificates")]
#[test]
fn the_artifact_level_assertion_id_cross_check_is_not_vacuous() {
    let bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let report = discharge_report(&bundle);
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_refused_for_coverage_alone(&evidence.admit_native_proof_artifact());

    let mut row = serde_json::to_value(evidence).expect("evidence row serializes");
    row["compiler_facts_binding"]["assertion_id"] = serde_json::json!(0);
    let moved: trust_vc_trust_engine::TrustVcNativeTrustIrCertificateEvidence =
        serde_json::from_value(row).expect("evidence row round-trips");
    assert_eq!(moved.independent_assertion_id(), Some(1));
    assert_eq!(moved.compiler_facts_binding().assertion_id(), Some(0));

    let artifact = moved.admit_native_proof_artifact();
    assert_eq!(artifact.assertion_id(), "", "{artifact:?}");
    assert_eq!(
        artifact.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch),
        "{artifact:?}"
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::AssertionIdRenderingsDisagree),
        "{artifact:?}"
    );
}

/// ROUND 8, THE SECOND MINOR — the two `ObligationSite` readings, and the guard
/// that was written and then DELETED.
///
/// `callee_contract_facts` concludes NOTHING from `site`, while
/// `discharge_request` selects a def-site `requires` with `site.is_none()`. The
/// reading applied at both seams is upstream's own: `None` means "no position
/// recorded" and is never a witness; at both seams it only NARROWS a selection
/// whose admitting condition is `function == Some(f) && kind == Precondition`,
/// the producer's own definition of a `requires`.
///
/// The shape that would make the difference bite is a row scoped to `f` that a
/// call declares is ITS callee's precondition — `ProofContext.establishes` is
/// upstream's per-call-site "callee preconditions the caller must establish", so
/// such a row is two incompatible claims about whose it is. A trust-vc guard for
/// it was written and then deleted as unjustified, because
/// `trust_ir_build::validate_module` (the P1 input gate) already refuses the
/// shape and that refusal is not one of the carried-past verdicts — so the guard
/// could never have a discriminating test.
///
/// THIS TEST IS THE PIN ON THAT UPSTREAM REFUSAL. If it ever stops failing at
/// the gate, the guard has to come back.
#[test]
fn a_requires_that_a_call_lists_as_someone_elses_precondition_is_refused_upstream() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_CALLEE_CONTRACT_LIAR);
    // `caller`'s OWN `requires`, scoped to it, with no site.
    bundle.module.proof_obligations.push(
        trust_ir::ProofObligation::new(
            ProofId::new(2),
            trust_ir::ObligationKind::Precondition,
            ProofStatus::Pending,
            "caller requires x >= 1",
        )
        .with_function(FuncId::new(0))
        .with_formula(trust_ir::ProofFormula::new(
            "trust-types.Formula@1",
            r#"{"formula":{"Ge":[{"Var":["x","Int"]},{"Int":1}]}}"#,
        )),
    );
    // And the call inside `caller` claims that row is ITS callee's precondition.
    bundle.module.functions[0].blocks[0].body[0].proof_context =
        Some(trust_ir::proof::ProofContext {
            assumes: Vec::new(),
            establishes: vec![ProofId::new(2)],
        });
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("the producer validator refuses a `ProofContext` scope mismatch");
    let TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { errors, .. } = &error
    else {
        panic!("unexpected error: {error}");
    };
    assert!(errors.contains("scope mismatch (B5.1)"), "{errors}");

    // The neighbouring shape, pinned with it: a `ProofContext` on an instruction
    // that is not a call at all.
    let mut misplaced = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    misplaced.module.functions[0].blocks[0].body[0].proof_context =
        Some(trust_ir::proof::ProofContext {
            assumes: Vec::new(),
            establishes: vec![ProofId::new(0)],
        });
    reseal_module_identity(&mut misplaced);
    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&misplaced)
        .expect_err("the producer validator refuses a `ProofContext` off a call");
    let TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator { errors, .. } = &error
    else {
        panic!("unexpected error: {error}");
    };
    assert!(errors.contains("non-call instruction"), "{errors}");
}

// ---------------------------------------------------------------------------
// ADVERSARIAL REVIEW ROUND 11 — THE CORROBORATION GRADE THAT WAS NOT
// CORROBORATION
//
// `AssertionIdCorroboration::BundleStringMap` licensed the compiler-fact number
// whenever the bundle-wide `source.assertion_id` -> u32 map was a FUNCTION. That
// property is invariant under any relabeling of the numbers, so it corroborated
// nothing, and every row at that grade carried no independent rendering: the
// artifact's two "renderings" were then two copies of ONE field, which always
// agree. The grade is DELETED. These pin the three probes that got through it,
// and the cost the deletion makes visible.
// ---------------------------------------------------------------------------

/// WHAT STILL PUBLISHES NO ID: a TrustVc request with no `Assertion` atom.
///
/// trust-ir's conformance corpus ships its TrustVc request that way: the
/// compiler fact carries number 1 and the formula is one SMT-LIB text, but
/// nothing in the citing request states the number beside the formula, so
/// trust-vc publishes none — a fail-closed `MissingAssertionId`, not a number
/// that could join to the wrong assertion downstream. The same bundle with the
/// bridge's atom is the admission baseline.
#[test]
fn the_upstream_corpus_publishes_no_assertion_id_because_it_renders_it_once() {
    let bundle = unatomed_bundle_fixture();
    assert_eq!(
        bundle.compiler_facts.obligation_sources[0]
            .assertion_id
            .map(|assertion_id| assertion_id.index()),
        Some(1),
        "the bundle DOES carry the number; the point is that nothing corroborates it"
    );
    let NativeVerificationRequest::TrustVc(request) = &bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    assert!(request.provenance.replay_context.atoms.is_empty());
    assert_eq!(
        bundle.module.proof_obligations[0]
            .formula
            .as_ref()
            .expect("corpus obligation carries a formula")
            .schema,
        "smtlib2",
        "the corpus formula is one SMT-LIB text"
    );

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("an uncorroborated id is a well-formed bundle, not a contradiction");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), None);
    assert_eq!(evidence.independent_assertion_id(), None);

    let artifact = evidence.admit_native_proof_artifact();
    assert_eq!(artifact.assertion_id(), "");
    assert_eq!(
        artifact.admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifact
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{artifact:?}"
    );
    assert_eq!(
        evidence.release_admission().rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::MissingAssertionId],
        "coverage holds; the id is the one refusal"
    );
}

/// LIAR L6, the atom in ANOTHER request: the corpus's TrustWp request carries an
/// `Assertion` atom (for its own obligation), and the TrustVc request that
/// cites the certificate carries none. Only the citing request can license, so
/// nothing is published.
#[test]
fn an_atom_in_another_request_licenses_nothing() {
    let bundle = unatomed_bundle_fixture();
    let NativeVerificationRequest::TrustWp(trust_wp) = &bundle.requests[TRUST_WP_SP_REQUEST] else {
        panic!("the corpus's request 4 is its TrustWp strongest-postcondition request");
    };
    assert!(
        trust_wp
            .provenance
            .replay_context
            .atoms
            .iter()
            .any(|atom| atom.assertion_id.is_some()),
        "the TrustWp request carries an atom stating an id"
    );
    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("the bundle is well formed");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.native_assertion_id(), None);
    assert_eq!(
        evidence.release_admission().rejection_reasons(),
        &[TrustVcNativeTrustIrCertificateRejection::MissingAssertionId]
    );
}

/// LIAR L9, THE OLD SHAPE: the id rendered inside the payload, as the source
/// record under `trust.trust_ir.obligation-source.v1` (what `trust-ir-bridge`
/// emits for every obligation whose predicate it could not render). A
/// source-record payload is no SMT-LIB text, so trust-ir never replays the
/// certificate that cites it and refuses the bundle at the door; and the export
/// seam would license nothing from it anyway (the lib test
/// `native_assertion_id::the_top_level_source_record_is_read_and_licenses_nothing`).
#[test]
fn a_top_level_source_record_payload_is_refused_upstream_at_this_pin() {
    let mut bundle = native_bundle_fixture();
    install_top_level_payload_assertion_id(&mut bundle, 0, 42);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a source-record payload is no SMT-LIB text and is not replayed");
    assert!(error.to_string().contains(PAYLOAD_ID_REFUSAL), "{error}");
}

/// A moved compiler fact beside a top-level source record is refused. The
/// export seam's cross-check of the two numbers is pinned by the lib test
/// `native_assertion_id::a_top_level_source_record_that_disagrees_refuses_the_bundle`;
/// at this pin trust-ir refuses the bundle first, since the source-record
/// payload is no SMT-LIB text (see
/// `a_top_level_source_record_payload_is_refused_upstream_at_this_pin`).
#[test]
fn a_moved_compiler_fact_is_refused_against_the_top_level_source_record() {
    let mut bundle = native_bundle_fixture();
    install_top_level_payload_assertion_id(&mut bundle, 0, 42);
    let obligation_id = bundle.module.proof_obligations[0].id;
    for source in &mut bundle.compiler_facts.obligation_sources {
        if source.obligation == obligation_id {
            source.assertion_id = Some(NativeAssertionId::new(4242));
        }
    }
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("two numeric renderings of one identity that differ must refuse");
    assert!(error.to_string().contains(PAYLOAD_ID_REFUSAL), "{error}");
}

/// PROBE R10-P1, the round-8 blocker restored through the fake grade.
///
/// Strip `native_assertion_id` from BOTH payloads, then move
/// `obligation_sources[0].assertion_id` 0 -> 99 and `[1].assertion_id` 1 -> 0.
/// Every remaining check passes — the string renderings still agree, and the
/// bundle-wide string -> number map is still a function — so round 10 measured
/// a published artifact `assertion_id="0" obligation=1 admission={Replayable,
/// Accepted, rejection_reasons: []}`: trust-vc's proof of `clamp`'s
/// POSTcondition stamped with the PREcondition's id.
///
/// The request's atom is stripped too, so no independent rendering is left:
/// there is nothing to corroborate, and nothing is published.
#[cfg(feature = "proof-certificates")]
#[test]
fn r10_p1_stripping_both_payload_renderings_publishes_no_assertion_id() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    strip_payload_renderings(&mut bundle);
    strip_request_atoms(&mut bundle);
    bundle.compiler_facts.obligation_sources[0].assertion_id = Some(NativeAssertionId::new(99));
    bundle.compiler_facts.obligation_sources[1].assertion_id = Some(NativeAssertionId::new(0));
    reseal_module_identity(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("the probe leaves a structurally well-formed bundle");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1, "{evidence:?}");
    assert_eq!(
        evidence.native_assertion_id(),
        None,
        "nothing corroborates the moved number: {evidence:?}"
    );

    let artifacts = report.admit_native_proof_artifacts();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(
        artifacts[0].assertion_id(),
        "",
        "R10-P1 published `assertion_id=\"0\"` here: {:?}",
        artifacts[0]
    );
    assert_eq!(
        artifacts[0].admission().status(),
        TrustVcNativeArtifactAdmissionStatus::Rejected
    );
    assert!(
        artifacts[0]
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{:?}",
        artifacts[0]
    );
}

/// PROBE R10-P10, and the ENABLER it rode in on.
///
/// Two edits: delete the whole `"source"` block from obligation 1's payload, and
/// set `obligation_sources[1].assertion_id = 4242`. Round 10 measured a
/// published `assertion_id="4242"` — because an ABSENT payload `source` produced
/// no rendering AND no signal, silently downgrading the row to the fake grade.
///
/// The absence is an explicit state (`PayloadSourceBlock::Absent`), it is
/// named in the seam's own description, and it licenses nothing. The request's
/// atom is stripped too, so no independent rendering is left.
#[cfg(feature = "proof-certificates")]
#[test]
fn r10_p10_deleting_the_payload_source_block_publishes_no_assertion_id() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let formula = bundle.module.proof_obligations[1]
        .formula
        .as_mut()
        .expect("fixture carries formulas");
    let mut document: serde_json::Value =
        serde_json::from_str(&formula.payload).expect("fixture payload is JSON");
    document
        .as_object_mut()
        .expect("payload is an object")
        .remove("source")
        .expect("fixture payload carries a source block");
    formula.payload = document.to_string();
    strip_request_atoms(&mut bundle);
    bundle.compiler_facts.obligation_sources[1].assertion_id = Some(NativeAssertionId::new(4242));
    reseal_module_identity(&mut bundle);

    let report = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect("a payload with no source block is well formed, not a contradiction");
    let evidence = &report.requests()[0].proof_evidence()[0];
    assert_eq!(evidence.obligation_id(), 1);
    assert_eq!(evidence.native_assertion_id(), None, "{evidence:?}");

    let artifacts = report.admit_native_proof_artifacts();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(
        artifacts[0].assertion_id(),
        "",
        "R10-P10 published `assertion_id=\"4242\"` here: {:?}",
        artifacts[0]
    );
    assert!(
        artifacts[0]
            .admission()
            .rejection_reasons()
            .contains(&TrustVcNativeArtifactRejection::MissingAssertionId),
        "{:?}",
        artifacts[0]
    );
}

/// THE OTHER HALF OF THE ENABLER: a payload `source` that is PRESENT but is not
/// an object. Present-and-unreadable is not absent, so this refuses the bundle
/// rather than quietly dropping a rendering.
#[test]
fn a_payload_source_that_is_not_an_object_refuses_the_bundle() {
    let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
    let formula = bundle.module.proof_obligations[1]
        .formula
        .as_mut()
        .expect("fixture carries formulas");
    let mut document: serde_json::Value =
        serde_json::from_str(&formula.payload).expect("fixture payload is JSON");
    document["source"] = serde_json::json!("rust-assertion:1");
    formula.payload = document.to_string();
    sync_assertion_atoms(&mut bundle, ProofId::new(1));
    reseal_module_identity(&mut bundle);

    let error = TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(&bundle)
        .expect_err("a present-but-unreadable rendering must refuse the bundle");
    let TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
        obligation_id,
        reason,
        renderings,
        ..
    } = &error
    else {
        panic!("unexpected error: {error}");
    };
    assert_eq!(*obligation_id, 1);
    assert!(
        reason.contains("unreadable"),
        "the refusal must say the rendering is unreadable: {reason}"
    );
    assert!(
        renderings.contains("payload `source` is not an object"),
        "the refusal must name the state it saw: {renderings}"
    );
}

/// THE DELETED GRADE, AS A PROPERTY. Corroboration must not be invariant under
/// relabeling: if a rule accepts a bundle and also accepts the same bundle with
/// every assertion number replaced by a different one, it constrains nothing
/// about which assertion a number names.
///
/// With the payload renderings and the request's atom stripped, both
/// labellings are accepted — that is what makes a string map worthless — and
/// NEITHER publishes an id.
#[cfg(feature = "proof-certificates")]
#[test]
fn a_relabeling_of_every_assertion_number_publishes_no_id_either_way() {
    let published = |labels: [u32; 2]| {
        let mut bundle = discharge_scalar_fixture(DISCHARGE_SCALAR_BRANCH);
        strip_payload_renderings(&mut bundle);
        strip_request_atoms(&mut bundle);
        for (source, label) in bundle
            .compiler_facts
            .obligation_sources
            .iter_mut()
            .zip(labels)
        {
            source.assertion_id = Some(NativeAssertionId::new(label));
        }
        reseal_module_identity(&mut bundle);
        let report = TrustVcTrustEngine::new()
            .consume_native_trust_ir_bundle(&bundle)
            .expect("a relabeled bundle is still well formed");
        report
            .admit_native_proof_artifacts()
            .iter()
            .map(|artifact| artifact.assertion_id().to_string())
            .collect::<Vec<_>>()
    };

    assert_eq!(published([0, 1]), published([13, 20]));
    assert_eq!(published([0, 1]), vec![String::new()]);
}
