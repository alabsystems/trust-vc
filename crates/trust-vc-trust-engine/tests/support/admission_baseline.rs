// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The native-bundle ADMISSION BASELINE, shared by the integration tests that
//! break one admission property of a well-formed bundle
//! (`native_trust_ir_bundle.rs`, `native_wire_rederivation.rs`,
//! `trust_runner_cli.rs` and others). The baseline is ADMITTED: its
//! certificate states its formula as one SMT-LIB text, and its TrustVc request
//! carries the `Assertion` replay atom Trust's `trust-ir-bridge` writes, so the
//! export seam publishes the assertion id. Each test breaks one property and
//! asserts its own refusal. Included with `#[path]`; not a test target itself.

#![allow(dead_code)]

use trust_ir::proof::{clean_cic_lineage_digest, CoverageAssurance};
use trust_ir::request::{
    NativeCompilerFacts, NativeEvidenceBundle, NativeReplayAtom, NativeReplayAtomId,
    NativeReplayAtomKind, NativeReplayContext, NativeVerificationBundle, NativeVerificationRequest,
};
use trust_ir::{Module, ProofCertificateRef, ProofEvidence, ProofId, ProofObligation, ProofStatus};

pub const NATIVE_REQUEST_TRUST_BUNDLE: &str =
    include_str!("../../fixtures/trust_ir_native/native_request_trust_bundle.json");

/// Index (and id) of the corpus's TrustMc `Chc` request: a PENDING request —
/// a question, not an answer — with no evidence bundle. The retired row rule
/// derived `Unbounded` from its mode alone, and the old admission baseline
/// cited it to make its certificate admissible; nothing is established by
/// citing it now.
pub const PENDING_CHC_REQUEST: usize = 1;

/// Index (and id) of the corpus's TrustWp `StrongestPostcondition` request,
/// whose replay context carries an `Assertion` atom for obligation 2.
pub const TRUST_WP_SP_REQUEST: usize = 4;

/// Upstream's refusal of a bundle whose certificate's obligation renders its
/// id inside a JSON payload (the old shape): such a payload is no SMT-LIB
/// text, so trust-ir never replays the certificate and refuses the TrustVc
/// evidence that cites it.
pub const PAYLOAD_ID_REFUSAL: &str =
    "rejects TrustVc certificate evidence 0/trust_vc with non-discharged status discharged";

/// The admission baseline: the corpus normalized
/// ([`normalize_to_trust_vc_admission_baseline`]) and its TrustVc request
/// given the replay context Trust's bridge writes ([`install_bridge_atoms`]).
/// Its one certificate is release-admissible and publishes assertion id 1.
pub fn native_bundle_fixture() -> NativeVerificationBundle {
    let mut bundle = unatomed_bundle_fixture();
    install_bridge_atoms(&mut bundle);
    bundle
}

/// The normalized baseline WITHOUT the replay atom, as upstream's corpus ships
/// its TrustVc request. Coverage is established and no assertion id is
/// published, so release admission refuses it `missing_assertion_id`.
pub fn unatomed_bundle_fixture() -> NativeVerificationBundle {
    let mut bundle: NativeVerificationBundle = serde_json::from_str(NATIVE_REQUEST_TRUST_BUNDLE)
        .expect("checked-in TrustIr native request fixture should decode");
    normalize_to_trust_vc_admission_baseline(&mut bundle);
    bundle
}

/// Exactly what Trust's `trust-ir-bridge` `native_replay_context` writes for
/// one request: per listed obligation (atom id = its index in the list), an
/// `Assertion` atom stating the obligation's formula cloned, carrying the
/// compiler fact's assertion id and span when there is one. An obligation with
/// no formula, or an empty schema or payload, gets no atom.
pub fn bridge_replay_context(
    module: &Module,
    compiler_facts: &NativeCompilerFacts,
    obligations: &[ProofId],
) -> NativeReplayContext {
    let mut context = NativeReplayContext::default();
    for (index, obligation_id) in obligations.iter().enumerate() {
        let Some(obligation) = module
            .proof_obligations
            .iter()
            .find(|obligation| obligation.id == *obligation_id)
        else {
            continue;
        };
        let Some(formula) = obligation.formula.clone() else {
            continue;
        };
        if formula.schema.trim().is_empty() || formula.payload.trim().is_empty() {
            continue;
        }
        let index = u32::try_from(index).expect("an obligation list fits u32");
        let mut atom = NativeReplayAtom::assertion(NativeReplayAtomId::new(index), formula)
            .with_obligation(*obligation_id);
        if let Some(source) = compiler_facts.obligation_source(*obligation_id) {
            if let Some(assertion_id) = source.assertion_id {
                atom = atom.with_assertion_id(assertion_id);
            }
            if let Some(span) = source.span {
                atom = atom.with_span(span);
            }
        }
        context = context.with_atom(atom);
    }
    context
}

/// Gives EVERY TrustVc request the replay context the bridge writes for it
/// ([`bridge_replay_context`]), replacing whatever it carried, and reseals.
pub fn install_bridge_atoms(bundle: &mut NativeVerificationBundle) {
    let module = bundle.module.clone();
    let compiler_facts = bundle.compiler_facts.clone();
    for request in &mut bundle.requests {
        if let NativeVerificationRequest::TrustVc(request) = request {
            request.provenance.replay_context =
                bridge_replay_context(&module, &compiler_facts, &request.obligations);
        }
    }
    reseal_module_identity(bundle);
}

/// Rewrites every TrustVc `Assertion` atom citing `obligation_id` to state that
/// obligation's CURRENT formula, as the bridge would have written it after the
/// edit, recomputing each atom's payload digest. Call it after an honest edit
/// of an obligation's formula, before resealing; a test whose subject is an
/// atom that disagrees with its obligation must not.
pub fn sync_assertion_atoms(bundle: &mut NativeVerificationBundle, obligation_id: ProofId) {
    let formula = bundle
        .module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == obligation_id)
        .and_then(|obligation| obligation.formula.clone());
    for request in &mut bundle.requests {
        let NativeVerificationRequest::TrustVc(request) = request else {
            continue;
        };
        for atom in &mut request.provenance.replay_context.atoms {
            if atom.kind != NativeReplayAtomKind::Assertion
                || atom.obligation != Some(obligation_id)
            {
                continue;
            }
            if let Some(formula) = formula.clone() {
                atom.formula = formula;
                atom.payload_digest = atom.expected_payload_digest();
            }
        }
    }
}

/// The `Assertion` atoms of TrustVc request `request_index` that cite
/// `obligation_id`, for a test to edit in place. Reseal afterwards.
pub fn assertion_atoms_mut(
    bundle: &mut NativeVerificationBundle,
    request_index: usize,
    obligation_id: ProofId,
) -> Vec<&mut NativeReplayAtom> {
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[request_index] else {
        panic!("request {request_index} should be a TrustVc request");
    };
    request
        .provenance
        .replay_context
        .atoms
        .iter_mut()
        .filter(|atom| {
            atom.kind == NativeReplayAtomKind::Assertion && atom.obligation == Some(obligation_id)
        })
        .collect()
}

/// THE OLD SHAPE: one obligation's assertion id rendered a second time INSIDE
/// its payload, as a `trust-types.Formula@1` document whose `source` record
/// carries it. Such a payload is no SMT-LIB text, so upstream never replays
/// the certificate and refuses the bundle ([`PAYLOAD_ID_REFUSAL`]); the tests
/// that use it pin that refusal.
///
/// The request's replay atoms are rewritten along with the formula, so the
/// refusal is upstream's, never the atom gate's. The payload's string
/// rendering is the obligation's OWN `source.assertion_id`, its numeric one is
/// the number installed on the compiler fact, and every digest is recomputed
/// with trust-ir's own functions.
pub fn install_payload_assertion_id(
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
    formula.schema = "trust-types.Formula@1".to_string();
    formula.payload = serde_json::json!({
        "formula": {"Bool": true},
        "source": {
            "assertion_id": assertion_id,
            "native_assertion_id": native_assertion_id,
        },
    })
    .to_string();
    set_compiler_fact_assertion_id(bundle, obligation_id, native_assertion_id);
    sync_assertion_atoms(bundle, obligation_id);
    reseal_clean_cic_lineage(bundle, obligation_id);
    reseal_module_identity(bundle);
}

/// Moves one obligation's compiler-fact assertion id AND every TrustVc atom id
/// citing it to `native_assertion_id`, as a producer that numbered the
/// assertion that way would have written both. Not resealed.
pub fn set_compiler_fact_assertion_id(
    bundle: &mut NativeVerificationBundle,
    obligation_id: ProofId,
    native_assertion_id: u32,
) {
    let mut installed = false;
    for source in &mut bundle.compiler_facts.obligation_sources {
        if source.obligation == obligation_id {
            source.assertion_id = Some(trust_ir::request::NativeAssertionId::new(
                native_assertion_id,
            ));
            installed = true;
        }
    }
    assert!(
        installed,
        "obligation {obligation_id:?} has no compiler-fact source row"
    );
    for request in &mut bundle.requests {
        let NativeVerificationRequest::TrustVc(request) = request else {
            continue;
        };
        for atom in &mut request.provenance.replay_context.atoms {
            if atom.obligation == Some(obligation_id) && atom.assertion_id.is_some() {
                atom.assertion_id = Some(trust_ir::request::NativeAssertionId::new(
                    native_assertion_id,
                ));
            }
        }
    }
}

/// Re-derives the CleanCic lineage binding of every certificate for one
/// obligation, and rewrites every reference to it BY VALUE.
///
/// `clean_cic_lineage_digest` covers the obligation's FORMULA, so editing a
/// formula unbinds its kernel-checkable certificate — upstream then answers
/// "rejects TrustVc certificate evidence … with non-discharged status
/// discharged", because the obligation is no longer in the replayed-authority
/// set. Re-derived with trust-ir's own function, exactly as the multi-assertion
/// test already does for the certificate it clones; a certificate's
/// `lineage_ref` quotes its evidence digest, so the refs the request and the
/// lineage nodes hold are rewritten to match rather than left dangling.
pub fn reseal_clean_cic_lineage(bundle: &mut NativeVerificationBundle, obligation_id: ProofId) {
    let obligation = bundle
        .module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == obligation_id)
        .expect("obligation exists")
        .clone();
    let lineage_digest = clean_cic_lineage_digest(&obligation);

    let mut rewrites = Vec::new();
    for certificate in &mut bundle.module.proof_certificates {
        if certificate.obligation != obligation_id {
            continue;
        }
        let previous = certificate.lineage_ref();
        let ProofEvidence::CleanCic { lineage, .. } = &mut certificate.evidence else {
            continue;
        };
        if *lineage == lineage_digest {
            continue;
        }
        *lineage = lineage_digest;
        rewrites.push((previous, certificate.lineage_ref()));
    }

    for (previous, current) in rewrites {
        for node in &mut bundle.lineage.nodes {
            for certificate in &mut node.certificates {
                if *certificate == previous {
                    *certificate = current.clone();
                }
            }
        }
        for request in &mut bundle.requests {
            if let NativeVerificationRequest::TrustVc(request) = request {
                for certificate in &mut request.certificates {
                    if *certificate == previous {
                        *certificate = current.clone();
                    }
                }
            }
        }
    }
}

/// Turns the upstream corpus bundle into the ADMISSION BASELINE's module: a
/// TrustVc request whose certificate has kernel-established coverage, so each
/// test can mutate exactly one property and assert the resulting rejection.
/// [`native_bundle_fixture`] then installs the request's replay atom.
///
/// WHY THIS EXISTS. The fixture is copied verbatim from TrustIr's conformance
/// corpus, and that corpus answers a different question — it ships obligation 0
/// as `Certified` under prover `trust_vc-clean-kernel`, exercising the CIC
/// tier. Those are upstream's to choose. But every negative test here works by
/// taking a GOOD bundle and breaking one thing (see the `ProofStatus` loop
/// below, which assigns `Pending`/`Failed`/`Trusted`); against a bundle that is
/// already rejected for an unrelated reason, all of them pass for the wrong
/// reason or fail on the wrong message.
///
/// DERIVED, NEVER FORGED. The edits are semantic — a status and a prover
/// name — and every digest downstream of them is RECOMPUTED from the edited
/// module via trust-ir's own `Module::stable_digest`, not copied or invented.
/// Hand-writing a digest to satisfy a validator is the one thing this must not
/// do: it would make the suite agree with itself while disagreeing with the
/// producer. Because the digest is recomputed, this normalization also keeps
/// working when the corpus evolves again.
pub fn normalize_to_trust_vc_admission_baseline(bundle: &mut NativeVerificationBundle) {
    const TRUST_VC_PROVER: &str = "trust_vc";

    // 1. The obligation the TrustVc request cites must be DISCHARGED — upstream
    //    rejects any other status for TrustVc certificate evidence.
    if let Some(obligation) = bundle.module.proof_obligations.first_mut() {
        obligation.status = ProofStatus::Discharged;
    }

    // 2. Name the prover the way this suite asserts on it. Both the module's
    //    certificate and the request's must agree, or the bundle self-conflicts.
    for certificate in &mut bundle.module.proof_certificates {
        certificate.prover = TRUST_VC_PROVER.to_string();
    }
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        for certificate in &mut request.certificates {
            certificate.prover = TRUST_VC_PROVER.to_string();
        }
    }
    // The lineage nodes name the prover too, and upstream checks that a
    // request's certificate is BOUND BY its lineage roots — so missing these
    // leaves the certificate unbound rather than merely misnamed.
    for node in &mut bundle.lineage.nodes {
        for certificate in &mut node.certificates {
            certificate.prover = TRUST_VC_PROVER.to_string();
        }
    }

    // 3. NO coverage row. Coverage is DERIVED by the consumer from evidence
    //    it re-checks: the corpus certificate is a directive-less CleanCic
    //    contract certificate, which `NativeVerificationBundle::validate`
    //    replays in the Clean kernel against the claim re-derived from its
    //    obligation, so trust-ir-build's basis K establishes it `Unbounded`
    //    with `assurance: None`. (The previous baseline recorded `Unbounded`
    //    citing the pending CHC request — the false-provenance route
    //    `pending_chc_citation_no_longer_establishes` now pins as refused.)

    // 4. Re-derive every identity the edits above invalidate.
    reseal_module_identity(bundle);
}

/// Adds a SIBLING certificate on obligation 0 — `evidence` under `prover`,
/// carrying the in-module coverage row `row` — binds it into lineage node 0,
/// reseals, and returns its lineage reference. The kernel-replayed CleanCic
/// certificate stays in the module, so the obligation keeps its replay
/// authority upstream; the TrustVc request still cites only the CleanCic one
/// (see [`cite_certificates`]).
///
/// Basis K is per CERTIFICATE: the CleanCic certificate's replay establishes
/// nothing for the sibling.
pub fn add_sibling_certificate(
    bundle: &mut NativeVerificationBundle,
    prover: &str,
    evidence: ProofEvidence,
    row: Option<CoverageAssurance>,
) -> ProofCertificateRef {
    let mut sibling = bundle.module.proof_certificates[0].clone();
    sibling.prover = prover.to_string();
    sibling.evidence = evidence;
    sibling.assurance = row;
    let sibling_ref = sibling.lineage_ref();
    bundle.module.proof_certificates.push(sibling);
    bundle.lineage.nodes[0]
        .certificates
        .push(sibling_ref.clone());
    reseal_module_identity(bundle);
    sibling_ref
}

/// Edits obligation 0 with `edit`, then RE-BINDS certificate 0 — the corpus's
/// directive-less CleanCic certificate — to the edited obligation: its
/// lineage digest is recomputed with trust-ir's own
/// `clean_cic_lineage_digest`, the new reference replaces the old one
/// wherever the TrustVc request and the lineage cite it, the request's
/// `Assertion` atom is rewritten to the edited formula (as the bridge would
/// write it), and the module is resealed. The kernel therefore replays the
/// certificate against the EDITED obligation, and a refusal of the result is
/// the consumer's, never a stale digest's or a stale atom's.
pub fn edit_replayed_obligation(
    bundle: &mut NativeVerificationBundle,
    edit: impl FnOnce(&mut ProofObligation),
) {
    rebind_replayed_obligation(bundle, edit);
    let obligation_id = bundle.module.proof_obligations[0].id;
    sync_assertion_atoms(bundle, obligation_id);
    reseal_module_identity(bundle);
}

/// [`edit_replayed_obligation`] WITHOUT rewriting the request's atom: the
/// certificate is re-bound to the edited obligation and the bundle resealed,
/// while the atom still asserts the formula the obligation stated before.
pub fn edit_replayed_obligation_keeping_atom(
    bundle: &mut NativeVerificationBundle,
    edit: impl FnOnce(&mut ProofObligation),
) {
    rebind_replayed_obligation(bundle, edit);
    reseal_module_identity(bundle);
}

fn rebind_replayed_obligation(
    bundle: &mut NativeVerificationBundle,
    edit: impl FnOnce(&mut ProofObligation),
) {
    let previous = bundle.module.proof_certificates[0].lineage_ref();
    edit(&mut bundle.module.proof_obligations[0]);
    let lineage_now = clean_cic_lineage_digest(&bundle.module.proof_obligations[0]);
    let ProofEvidence::CleanCic { lineage, .. } = &mut bundle.module.proof_certificates[0].evidence
    else {
        panic!("the corpus certificate 0 should be CleanCic");
    };
    *lineage = lineage_now;
    let current = bundle.module.proof_certificates[0].lineage_ref();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    let lineage_certificates = bundle
        .lineage
        .nodes
        .iter_mut()
        .flat_map(|node| node.certificates.iter_mut());
    for certificate in request.certificates.iter_mut().chain(lineage_certificates) {
        if *certificate == previous {
            *certificate = current.clone();
        }
    }
}

/// Makes the TrustVc request cite exactly `certificates`, and reseals.
pub fn cite_certificates(
    bundle: &mut NativeVerificationBundle,
    certificates: Vec<ProofCertificateRef>,
) {
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture first request should be TrustVc");
    };
    request.certificates = certificates;
    reseal_module_identity(bundle);
}

/// Re-derives every identity that quotes the module digest.
///
/// ANY test that mutates `bundle.module` must call this afterwards, or the
/// bundle fails with "claims TrustIr module digest X, but the embedded module
/// hashes to Y" — which looks like a broken fixture and is really just an
/// unsealed edit.
///
/// The digest is not one field. Upstream checks it independently in the bundle
/// header, in every lineage node's source/target module, and in every evidence
/// bundle, so this rewrites BY VALUE: whatever equalled the previous module
/// digest now equals the recomputed one. Recomputed via trust-ir's own
/// `Module::stable_digest` — never hand-written to satisfy a validator.
pub fn reseal_module_identity(bundle: &mut NativeVerificationBundle) {
    // Coverage rows quote REQUEST digests and the module digest covers the
    // rows, so they are re-cited before the module is hashed.
    recite_coverage_rows(bundle);
    let previous = bundle.trust_ir_module_digest;
    let recomputed = bundle.module.stable_digest();

    for node in &mut bundle.lineage.nodes {
        if node.target_module == previous {
            node.target_module = recomputed;
        }
        if node.source_module == previous {
            node.source_module = recomputed;
        }
    }
    for evidence in &mut bundle.evidence_bundles {
        match evidence {
            NativeEvidenceBundle::TrustVc(evidence) => {
                if evidence.trust_ir_module_digest == previous {
                    evidence.trust_ir_module_digest = recomputed;
                }
            }
            NativeEvidenceBundle::TrustMc(evidence) => {
                if evidence.trust_ir_module_digest == previous {
                    evidence.trust_ir_module_digest = recomputed;
                }
            }
            NativeEvidenceBundle::TrustWp(evidence) => {
                if evidence.trust_ir_module_digest == previous {
                    evidence.trust_ir_module_digest = recomputed;
                }
            }
        }
    }
    bundle.trust_ir_module_digest = recomputed;

    // The request digest depends on the request, which the prover rename above
    // changed, so this must run AFTER the module rewrite, not with it.
    refresh_evidence_bindings(bundle);
}

/// Re-cites every coverage row (`ProofCertificate::assurance.request_digest`,
/// trust-ir v41) whose request an edit moved.
///
/// BY VALUE, like the module digest: a row that cited a request as it stood
/// BEFORE the edit — the digest that request's evidence bundle still copies,
/// because evidence is refreshed only after this runs — now cites the request
/// as it stands. A row citing anything else keeps its citation, so a test
/// that plants a foreign or unknown citation keeps exactly what it planted.
pub fn recite_coverage_rows(bundle: &mut NativeVerificationBundle) {
    let moved = bundle
        .requests
        .iter()
        .filter_map(|request| {
            let previous = bundle
                .evidence_bundles
                .iter()
                .find(|evidence| {
                    evidence.request() == request.id()
                        && evidence.verifier_suite() == request.verifier_suite()
                })?
                .request_digest();
            let current = request.stable_digest();
            (previous != current).then_some((previous, current))
        })
        .collect::<Vec<_>>();
    for certificate in &mut bundle.module.proof_certificates {
        let Some(assurance) = certificate.assurance.as_mut() else {
            continue;
        };
        if let Some((_, current)) = moved
            .iter()
            .find(|(previous, _)| *previous == assurance.request_digest)
        {
            assurance.request_digest = *current;
        }
    }
}

/// Re-binds every evidence bundle to its request as the request now stands:
/// the listed obligations, the mode, and the request digest the evidence
/// copies. Recomputed via trust-ir's own `stable_digest`.
pub fn refresh_evidence_bindings(bundle: &mut NativeVerificationBundle) {
    for request in &bundle.requests {
        let request_digest = request.stable_digest();
        for evidence in &mut bundle.evidence_bundles {
            match (request, evidence) {
                (
                    NativeVerificationRequest::TrustVc(request),
                    NativeEvidenceBundle::TrustVc(evidence),
                ) if evidence.request == request.id => {
                    evidence.mode = request.mode;
                    evidence.obligations = request.obligations.clone();
                    evidence.request_digest = request_digest;
                }
                (
                    NativeVerificationRequest::TrustMc(request),
                    NativeEvidenceBundle::TrustMc(evidence),
                ) if evidence.request == request.id => {
                    evidence.mode = request.mode;
                    evidence.obligations = request.obligations.clone();
                    evidence.request_digest = request_digest;
                }
                (
                    NativeVerificationRequest::TrustWp(request),
                    NativeEvidenceBundle::TrustWp(evidence),
                ) if evidence.request == request.id => {
                    evidence.mode = request.mode;
                    evidence.obligations = request.obligations.clone();
                    evidence.request_digest = request_digest;
                }
                _ => {}
            }
        }
    }
}
