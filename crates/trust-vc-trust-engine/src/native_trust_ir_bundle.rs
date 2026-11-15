//! Direct consumer for upstream `trust_ir::NativeVerificationBundle` requests.
//!
//! This module handles the typed `NativeVerificationRequest::TrustVc` variant
//! directly. It does not route through adapter-name strings or source-text
//! verifier payloads.

use crate::native_artifact::NativeArtifactCoverage;
use crate::native_coverage::{CoverageJudge, TrustVcNativeCoverageBasis};
use crate::native_discharge::{discharge_request, DischargeReport};
use crate::trust_ir_body::{
    wire_identity_gap, BodyReading, TrustIrBodyObligationReport, TrustIrBodyOptions,
    TrustIrBodyRefusal, TrustIrBodyReport, TrustIrBodyVerdict, HAVOC_INSTANTIATION_NOTE,
    TRUST_IR_BODY_LANE_SCHEMA, UNOBLIGATED_ASSERT_LABEL,
};
use crate::{
    TrustCounterexampleBinding, TrustEngineError, TrustVcNativeArtifactObligationStatus,
    TrustVcNativeArtifactRejection, TrustVcNativeAssertionIdRendering,
    TrustVcNativeCompilerFactRef, TrustVcNativeCompilerFactsBinding, TrustVcNativeObligationCause,
    TrustVcNativeProofArtifact, TrustVcNativeProofArtifactInput, TrustVcNativeSolverIdentity,
    TrustVcNativeSourceSpan, TrustVcNativeToolIdentity, TrustVcNativeVerifierSuite,
    TrustVcNativeVerifierSuiteIdentity, TrustVcTrustEngine,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use trust_ir::{
    FuncId, Module, ObligationKind, ProofCertificate, ProofCertificateRef, ProofDigest,
    ProofEvidence, ProofId, ProofLineageId, ProofLineageNode, ProofObligation, ProofStatus,
    SourceSpan,
};
// The `Native*` / `TrustVc*` request-bundle types live in `trust_ir::request`;
// their crate-root re-exports are gated behind trust-ir's default-on
// `request-reexports` feature (audit #55), which trust-vc builds with disabled —
// so import them via the always-available canonical `request::` path.
use trust_ir::request::{
    NativeAdapterInput, NativeBundleProducer, NativeCompilerFactRef, NativeEvidenceArtifact,
    NativeEvidenceArtifactKind, NativeObligationCause, NativeObligationSource,
    NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
    NativeVerificationBundleError, NativeVerificationRequest, NativeVerifierSuite,
    TrustVcNativeEvidenceBundle, TrustVcNativeRequest, TrustVcVerificationMode,
};

/// Report produced after TrustVc consumes native TrustIr TrustVc requests.
///
/// # `verdict` is REQUIRED on the wire, and is re-derived on the way in
///
/// It used to be `#[serde(default)]`ed to `CertificatesAdmitted`, which meant a
/// report that simply omitted the key deserialized as a CLEAN PASS — including
/// a discharge-mode report whose advisory answer was sitting right there in
/// `discharge`. `verdict` is the only field [`Self::verdict`]'s consumers read
/// to decide success, so it gets the same discipline
/// [`TrustVcNativeTrustIrDischargeAnswer::authority`] already had: required,
/// and checked. [`TryFrom`] additionally re-folds the rollup and refuses a
/// declared bundle verdict that disagrees with its own requests, so the
/// rollup cannot be forged by hand-writing the outer number.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "WireBundleReport")]
#[must_use]
pub struct TrustVcNativeTrustIrBundleReport {
    producer: String,
    input_kind: TrustVcNativeTrustIrInputKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    input_digest: Option<String>,
    #[serde(alias = "tmir_module_digest")]
    trust_ir_module_digest: String,
    compiler_facts_digest: String,
    module_name: String,
    requests: Vec<TrustVcNativeTrustIrRequestReport>,
    /// Worst-wins rollup over `requests`. Required; see the type doc.
    verdict: TrustVcNativeTrustIrVerdict,
    /// Proof certificates trust-vc PRODUCED on the discharge lane.
    ///
    /// Empty for Import/Merge by construction: those modes check certificates
    /// that arrived, they never mint one.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    produced_certificates: Vec<TrustVcNativeTrustIrProducedCertificate>,
    /// Evidence bundles trust-vc PRODUCED on the discharge lane — the output
    /// half of the per-request evidence rule that Import/Merge require on input.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    produced_evidence_bundles: Vec<TrustVcNativeEvidenceBundle>,
}

/// Deserialization mirror of [`TrustVcNativeTrustIrBundleReport`].
///
/// Exists only so `verdict` can be a REQUIRED field that is then re-checked
/// against the requests, which a plain derive cannot express.
#[derive(Deserialize)]
struct WireBundleReport {
    producer: String,
    input_kind: TrustVcNativeTrustIrInputKind,
    #[serde(default)]
    input_digest: Option<String>,
    #[serde(alias = "tmir_module_digest")]
    trust_ir_module_digest: String,
    compiler_facts_digest: String,
    module_name: String,
    requests: Vec<WireRequestReport>,
    verdict: TrustVcNativeTrustIrVerdict,
    #[serde(default)]
    produced_certificates: Vec<TrustVcNativeTrustIrProducedCertificate>,
    #[serde(default)]
    produced_evidence_bundles: Vec<TrustVcNativeEvidenceBundle>,
}

impl TryFrom<WireBundleReport> for TrustVcNativeTrustIrBundleReport {
    type Error = String;

    /// The declared rollup must be the fold of the DECLARED request verdicts
    /// (a payload no producer writes is refused), and the decoded rollup is
    /// the fold of the DECODED requests — so a decoded bundle whose discharge
    /// request declared `discharge_refuted` rolls up to `NotJudged`, never to
    /// a verdict read off the wire.
    fn try_from(wire: WireBundleReport) -> Result<Self, Self::Error> {
        let declared_rollup = wire
            .requests
            .iter()
            .map(|request| request.verdict)
            .reduce(TrustVcNativeTrustIrVerdict::worse_of)
            .ok_or_else(|| {
                "a native TrustIr bundle report must carry at least one request".to_string()
            })?;
        if declared_rollup != wire.verdict {
            return Err(format!(
                "native TrustIr bundle report declares verdict {:?} but its requests roll up to \
                 {declared_rollup:?}",
                wire.verdict
            ));
        }
        let requests = wire
            .requests
            .into_iter()
            .map(TrustVcNativeTrustIrRequestReport::try_from)
            .collect::<Result<Vec<_>, _>>()?;
        let verdict = rollup_verdict(&requests).ok_or_else(|| {
            "a native TrustIr bundle report must carry at least one request".to_string()
        })?;
        Ok(Self {
            producer: wire.producer,
            input_kind: wire.input_kind,
            input_digest: wire.input_digest,
            trust_ir_module_digest: wire.trust_ir_module_digest,
            compiler_facts_digest: wire.compiler_facts_digest,
            module_name: wire.module_name,
            requests,
            verdict,
            produced_certificates: wire.produced_certificates,
            produced_evidence_bundles: wire.produced_evidence_bundles,
        })
    }
}

/// Worst-wins fold over request verdicts. `None` for an empty request list:
/// folding from `CertificatesAdmitted` over nothing would manufacture a pass
/// out of nothing, so the empty case is refused by the caller instead.
fn rollup_verdict(
    requests: &[TrustVcNativeTrustIrRequestReport],
) -> Option<TrustVcNativeTrustIrVerdict> {
    requests
        .iter()
        .map(TrustVcNativeTrustIrRequestReport::verdict)
        .reduce(TrustVcNativeTrustIrVerdict::worse_of)
}

impl TrustVcNativeTrustIrBundleReport {
    /// Return the native bundle producer label.
    pub fn producer(&self) -> &str {
        &self.producer
    }

    /// Return the worst verdict across every request in this bundle.
    pub const fn verdict(&self) -> TrustVcNativeTrustIrVerdict {
        self.verdict
    }

    /// Return the kind of input artifact that backs this bundle.
    pub const fn input_kind(&self) -> TrustVcNativeTrustIrInputKind {
        self.input_kind
    }

    /// Return the source input digest when the bundle came from Rust MIR.
    pub fn input_digest(&self) -> Option<&str> {
        self.input_digest.as_deref()
    }

    /// Return the TrustIr module digest bound by the native bundle lineage.
    pub fn trust_ir_module_digest(&self) -> &str {
        &self.trust_ir_module_digest
    }

    /// Return the TrustIr schema-v2 compiler-facts digest bound by this bundle.
    pub fn compiler_facts_digest(&self) -> &str {
        &self.compiler_facts_digest
    }

    /// Return the native TrustIr module name.
    pub fn module_name(&self) -> &str {
        &self.module_name
    }

    /// Return consumed TrustVc request reports.
    pub fn requests(&self) -> &[TrustVcNativeTrustIrRequestReport] {
        &self.requests
    }

    /// Return the proof certificates trust-vc produced on the discharge lane.
    pub fn produced_certificates(&self) -> &[TrustVcNativeTrustIrProducedCertificate] {
        &self.produced_certificates
    }

    /// Return the evidence bundles trust-vc produced on the discharge lane.
    pub fn produced_evidence_bundles(&self) -> &[TrustVcNativeEvidenceBundle] {
        &self.produced_evidence_bundles
    }

    /// Admit every native TrustIr certificate evidence item as a proof artifact.
    ///
    /// Each artifact is bound with the native frontend assertion id carried by
    /// its own TrustIr compiler-fact source mapping. Evidence without that binding
    /// remains present in the returned list, but its artifact admission rejects
    /// fail-closed with `MissingAssertionId`.
    pub fn admit_native_proof_artifacts(&self) -> Vec<TrustVcNativeProofArtifact> {
        self.requests
            .iter()
            .flat_map(TrustVcNativeTrustIrRequestReport::admit_native_proof_artifacts)
            .collect()
    }
}

/// Source input kind for a consumed native TrustIr bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrInputKind {
    RustMir,
    TrustIrModule,
}

/// One consumed native `TrustVcNativeRequest`.
///
/// # `mode`, `verdict`, `discharge` and `advisory_discharge` must agree, at deserialization time
///
/// `verdict` is REQUIRED (it used to default to `CertificatesAdmitted`, which
/// made a key-less report read as a clean pass), and [`TryFrom`] refuses every
/// combination the producer cannot construct: a discharge-mode report with
/// neither lane's answer, or with both; an ADVISORY discharge report carrying
/// certificate evidence or wearing a verdict the advisory lane cannot mint; a
/// `native_discharge` report wearing a verdict that lane cannot mint; and a
/// certificate-mode report carrying either discharge channel or wearing a
/// discharge verdict. Without that, the advisory containment on
/// [`TrustVcNativeTrustIrDischargeAnswer`] guards a label while the field that
/// actually decides success is free. The declared verdict must also be the one
/// the report's own content folds to (`check_verdict_rederives`): an advisory
/// answer must answer exactly the obligations the report names, and its
/// verdict is re-folded from the answer's outcomes.
///
/// A decoded discharge-mode report carries no authority on either channel: it
/// decodes `NotJudged`, and every per-obligation outcome of either lane
/// decodes `NotJudged` (see [`TrustVcNativeTrustIrVerdict::NotJudged`]).
///
/// Two discharge lanes are kept. `discharge` is the per-obligation vector of
/// the serialized-bundle lane ([`crate::native_discharge`], which
/// `consume_native_trust_ir_bundle` routes every validated discharge request
/// to); `advisory_discharge` is the answer of the in-process ADVISORY body lane
/// ([`crate::trust_ir_body`]), reached only through
/// [`TrustVcTrustEngine::discharge_native_trust_ir_request`]. A report carries
/// at most one of them.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "WireRequestReport")]
#[must_use]
pub struct TrustVcNativeTrustIrRequestReport {
    request_id: u32,
    mode: TrustVcNativeTrustIrRequestMode,
    lineage_roots: Vec<u32>,
    /// The proof obligations the request NAMES. REQUIRED on the wire: a
    /// certificate-mode verdict is folded over this set
    /// (`certificate_mode_verdict`), so evidence covering none — or only
    /// some — of them can never read as admitted.
    obligations: Vec<u32>,
    proof_evidence: Vec<TrustVcNativeTrustIrCertificateEvidence>,
    /// What came of this request. REQUIRED on the wire and cross-checked
    /// against `mode`, `discharge` and `advisory_discharge`; see the type doc.
    verdict: TrustVcNativeTrustIrVerdict,
    /// The ADVISORY answer to a `DischargeProofObligations` request.
    ///
    /// A SEPARATE CHANNEL FROM `proof_evidence` ON PURPOSE. `proof_evidence` is
    /// the certificate-admission channel and is the only thing
    /// [`Self::admit_native_proof_artifacts`] reads, so a discharge answer can
    /// never become an admissible native proof artifact by sitting in the same
    /// list. `None` for every certificate mode.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    advisory_discharge: Option<TrustVcNativeTrustIrDischargeAnswer>,
    /// Per-obligation discharge results. Empty for Import/Merge.
    ///
    /// SOUNDNESS: this is the ONLY field a consumer may map to a per-obligation
    /// proof status. See [`TrustVcNativeTrustIrDischargeOutcome`].
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    discharge: Vec<TrustVcNativeTrustIrDischargeOutcome>,
}

/// Deserialization mirror of [`TrustVcNativeTrustIrRequestReport`].
#[derive(Deserialize)]
struct WireRequestReport {
    request_id: u32,
    mode: TrustVcNativeTrustIrRequestMode,
    lineage_roots: Vec<u32>,
    obligations: Vec<u32>,
    proof_evidence: Vec<TrustVcNativeTrustIrCertificateEvidence>,
    #[serde(default)]
    advisory_discharge: Option<TrustVcNativeTrustIrDischargeAnswer>,
    verdict: TrustVcNativeTrustIrVerdict,
    #[serde(default)]
    discharge: Vec<TrustVcNativeTrustIrDischargeOutcome>,
}

impl TryFrom<WireRequestReport> for TrustVcNativeTrustIrRequestReport {
    type Error = String;

    fn try_from(wire: WireRequestReport) -> Result<Self, Self::Error> {
        check_request_report_channels(
            wire.mode,
            wire.verdict,
            wire.advisory_discharge.is_some(),
            !wire.discharge.is_empty(),
            wire.proof_evidence.is_empty(),
        )?;
        check_verdict_rederives(
            wire.mode,
            wire.verdict,
            &wire.obligations,
            &wire.proof_evidence,
            wire.advisory_discharge.as_ref(),
        )?;
        // A DECODED DISCHARGE REPORT CARRIES NO AUTHORITY. Its outcomes are
        // labels with nothing behind them on the wire, so none is read: every
        // outcome of either lane decodes `NotJudged` wherever it is decoded
        // (the erasure is `TrustVcNativeTrustIrDischargeObligation`'s and
        // `TrustVcNativeTrustIrDischargeOutcome`'s own), and so does the
        // report's verdict, whatever the payload declared (see
        // `TrustVcNativeTrustIrVerdict::NotJudged`). The shape checks above
        // still refuse a payload no producer can write; they do not decide
        // what the decoded report says.
        let verdict = match wire.mode {
            TrustVcNativeTrustIrRequestMode::DischargeProofObligations => {
                TrustVcNativeTrustIrVerdict::NotJudged
            }
            TrustVcNativeTrustIrRequestMode::ImportProofCertificates
            | TrustVcNativeTrustIrRequestMode::MergeProofCertificates => wire.verdict,
        };
        Ok(Self {
            request_id: wire.request_id,
            mode: wire.mode,
            lineage_roots: wire.lineage_roots,
            obligations: wire.obligations,
            proof_evidence: wire.proof_evidence,
            advisory_discharge: wire.advisory_discharge,
            verdict,
            discharge: wire.discharge,
        })
    }
}

/// The mode/verdict/channel agreement a produced report always satisfies.
///
/// Stated once, as a predicate, so that the wire cannot express a state the
/// producer cannot reach — in particular a discharge answer wearing
/// `CertificatesAdmitted`, which [`TrustVcNativeTrustIrVerdict::is_ok`] reads
/// as a clean pass.
fn check_request_report_shape(
    mode: TrustVcNativeTrustIrRequestMode,
    verdict: TrustVcNativeTrustIrVerdict,
    has_discharge: bool,
    proof_evidence_empty: bool,
) -> Result<(), String> {
    use TrustVcNativeTrustIrRequestMode as Mode;
    use TrustVcNativeTrustIrVerdict as Verdict;
    match mode {
        Mode::DischargeProofObligations => {
            if !has_discharge {
                return Err(
                    "a discharge-mode native TrustIr request report must carry a discharge answer"
                        .to_string(),
                );
            }
            if !proof_evidence_empty {
                return Err(
                    "a discharge-mode native TrustIr request report must carry no certificate \
                     evidence"
                        .to_string(),
                );
            }
            match verdict {
                // `NotJudged` is what a decoded report re-encodes as.
                Verdict::DischargedAdvisory
                | Verdict::DischargeRefuted
                | Verdict::DischargeNotAnswerable
                | Verdict::NotJudged => Ok(()),
                other => Err(format!(
                    "a discharge-mode native TrustIr request report cannot wear verdict {other:?}"
                )),
            }
        }
        Mode::ImportProofCertificates | Mode::MergeProofCertificates => {
            if has_discharge {
                return Err(format!(
                    "a {mode:?} native TrustIr request report must not carry a discharge answer"
                ));
            }
            match verdict {
                Verdict::CertificatesAdmitted | Verdict::CertificatesRejected => Ok(()),
                other => Err(format!(
                    "a {mode:?} native TrustIr request report cannot wear verdict {other:?}"
                )),
            }
        }
    }
}

/// The full channel agreement for a request report: which discharge channel a
/// report carries decides which verdict family it may wear.
///
/// MERGED 2026-09-23. [`check_request_report_shape`] is upstream's predicate for
/// the ADVISORY in-process lane and the certificate modes, kept verbatim. This
/// adds the serialized [`crate::native_discharge`] lane's shape in front of it:
/// a discharge-mode report whose per-obligation `discharge` vector is
/// non-empty and which carries no advisory answer must wear one of the verdicts
/// that lane mints — `Discharged`, `Refuted`, `DischargeDeclined`, or
/// `DischargeNotAnswerable` for a request refused before the lowering, or the
/// `NotJudged` a decoded report re-encodes as — and may carry the evidence rows
/// of the certificates it produced. Every other shape goes to upstream's
/// predicate, so a certificate-mode report carrying either discharge channel,
/// and a report carrying BOTH, are refused.
fn check_request_report_channels(
    mode: TrustVcNativeTrustIrRequestMode,
    verdict: TrustVcNativeTrustIrVerdict,
    has_advisory: bool,
    has_discharge_outcomes: bool,
    proof_evidence_empty: bool,
) -> Result<(), String> {
    use TrustVcNativeTrustIrRequestMode as Mode;
    use TrustVcNativeTrustIrVerdict as Verdict;
    if has_discharge_outcomes {
        if mode != Mode::DischargeProofObligations {
            return Err(format!(
                "a {mode:?} native TrustIr request report must not carry discharge outcomes"
            ));
        }
        if has_advisory {
            return Err(
                "a discharge-mode native TrustIr request report must not carry both a \
                 native_discharge outcome vector and an advisory answer"
                    .to_string(),
            );
        }
        return match verdict {
            Verdict::Discharged
            | Verdict::Refuted
            | Verdict::DischargeDeclined
            | Verdict::DischargeNotAnswerable
            | Verdict::NotJudged => Ok(()),
            other => Err(format!(
                "a native_discharge request report cannot wear verdict {other:?}"
            )),
        };
    }
    check_request_report_shape(mode, verdict, has_advisory, proof_evidence_empty)
}

/// The certificate-mode verdict: `CertificatesAdmitted` iff the request names
/// at least one obligation, every named obligation has certificate evidence,
/// no evidence item answers an obligation the request does not name, and every
/// evidence item is admissible. The producer and the decoder both fold with
/// THIS function.
///
/// It used to be `proof_evidence.iter().all(admissible)` alone, which is
/// vacuously true over an empty list: a REJECTED report with every request's
/// `proof_evidence` set to `[]` and its verdicts set to
/// `certificates_admitted` decoded as a clean pass (`is_ok() == true`),
/// because the report did not carry the set of obligations the evidence had
/// to cover.
fn certificate_mode_verdict(
    obligations: &[u32],
    proof_evidence: &[TrustVcNativeTrustIrCertificateEvidence],
) -> TrustVcNativeTrustIrVerdict {
    let named = obligations.iter().copied().collect::<BTreeSet<_>>();
    let answered = proof_evidence
        .iter()
        .map(TrustVcNativeTrustIrCertificateEvidence::obligation_id)
        .collect::<BTreeSet<_>>();
    let admitted = !named.is_empty()
        && named == answered
        && proof_evidence
            .iter()
            .all(|evidence| evidence.release_admission().is_admissible());
    if admitted {
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted
    } else {
        TrustVcNativeTrustIrVerdict::CertificatesRejected
    }
}

/// A request's verdict is RE-DERIVED on the way in, by the producer's own fold
/// over the content the report carries, and a payload whose declared verdict
/// differs is refused:
///
/// * certificate mode — [`certificate_mode_verdict`] over the obligations the
///   report names and the certificates' DECODED admissions, which are never
///   admissible (see [`TrustVcNativeTrustIrCertificateAdmission`]). A payload
///   declaring `CertificatesAdmitted` is therefore refused whatever evidence it
///   carries — including none: it used to decode as a clean pass, including one
///   written before `coverage_established` existed or edited to claim it, and
///   one stripped of every certificate. The admission can only be
///   re-established by consuming the bundle itself.
/// * discharge mode, advisory channel — nothing is re-derived, because
///   nothing on the wire can be: a decoded answer's outcomes are `NotJudged`
///   ([`TrustVcNativeTrustIrDischargeObligation`] erases them), and the
///   decoded report is `NotJudged` whatever it declares (see
///   `TryFrom<WireRequestReport>`). The answer must still answer exactly the
///   obligations the request names (the producer answers one entry per cited
///   obligation). Only
///   [`TrustVcTrustEngine::rejudge_native_trust_ir_discharge_report`] — which
///   holds the module and the request — re-derives a verdict for it. (The
///   declared verdict was once taken as written, then re-folded from the
///   declared outcomes, which a consistent edit of both passed.)
/// * discharge mode, `native_discharge` channel — nothing beyond
///   [`check_request_report_channels`]: the report decodes `NotJudged` and
///   every outcome decodes `NotJudged` ([`TrustVcNativeTrustIrDischargeOutcome`]
///   erases it), so no declared verdict or outcome survives decoding.
///
/// Either mode: a report names each obligation at most once. A request names
/// a set (upstream `validate_requests` refuses a duplicate, and so does
/// [`TrustVcTrustEngine::discharge_native_trust_ir_request`]), so a named list
/// like `[0, 0]` is no report any producer writes.
fn check_verdict_rederives(
    mode: TrustVcNativeTrustIrRequestMode,
    declared: TrustVcNativeTrustIrVerdict,
    obligations: &[u32],
    proof_evidence: &[TrustVcNativeTrustIrCertificateEvidence],
    advisory_discharge: Option<&TrustVcNativeTrustIrDischargeAnswer>,
) -> Result<(), String> {
    use TrustVcNativeTrustIrRequestMode as Mode;
    if let Some(duplicate) = first_duplicate(obligations) {
        return Err(format!(
            "a native TrustIr request report names obligation {duplicate} more than once: a \
             request names each obligation at most once"
        ));
    }
    match mode {
        Mode::DischargeProofObligations => {
            // No advisory answer: a `native_discharge` report, whose shape
            // `check_request_report_channels` already required.
            let Some(answer) = advisory_discharge else {
                return Ok(());
            };
            let named = obligations.iter().copied().collect::<BTreeSet<_>>();
            let answered = answer
                .obligations
                .iter()
                .map(TrustVcNativeTrustIrDischargeObligation::obligation_id)
                .collect::<BTreeSet<_>>();
            if named != answered || answered.len() != answer.obligations.len() {
                return Err(format!(
                    "a discharge-mode native TrustIr request report names obligation(s) \
                     {named:?}, but its discharge answer answers {:?}: the answer must answer \
                     each named obligation exactly once",
                    answer
                        .obligations
                        .iter()
                        .map(TrustVcNativeTrustIrDischargeObligation::obligation_id)
                        .collect::<Vec<_>>()
                ));
            }
            // Nothing to re-fold: a decoded answer's outcomes are `NotJudged`
            // (the wire outcome is never read), so the declared verdict is
            // checked for its SHAPE only (`check_request_report_shape`) and the
            // decoded report is `NotJudged`. Re-folding the DECLARED outcomes
            // (a9edcdd4) let a consistent edit of outcomes and verdict decode
            // with authority.
            Ok(())
        }
        Mode::ImportProofCertificates | Mode::MergeProofCertificates => {
            let rederived = certificate_mode_verdict(obligations, proof_evidence);
            if rederived == declared {
                Ok(())
            } else {
                Err(format!(
                    "a {mode:?} native TrustIr request report declares verdict {declared:?}, but \
                     its certificates' admissions over the {} obligation(s) it names, re-derived \
                     on decode, fold to {rederived:?}: coverage is judged only against the bundle \
                     a certificate cites, which a report does not carry — consume the bundle to \
                     re-establish it",
                    obligations.len()
                ))
            }
        }
    }
}

/// The first id that occurs twice in `ids`, if any.
fn first_duplicate(ids: &[u32]) -> Option<u32> {
    let mut seen = BTreeSet::new();
    ids.iter().copied().find(|id| !seen.insert(*id))
}

impl TrustVcNativeTrustIrRequestReport {
    /// Return the native bundle request id.
    pub const fn request_id(&self) -> u32 {
        self.request_id
    }

    /// Return the requested TrustVc native operation.
    pub const fn mode(&self) -> TrustVcNativeTrustIrRequestMode {
        self.mode
    }

    /// Return what came of this request.
    pub const fn verdict(&self) -> TrustVcNativeTrustIrVerdict {
        self.verdict
    }

    /// Return lineage roots bound to this request.
    pub fn lineage_roots(&self) -> &[u32] {
        &self.lineage_roots
    }

    /// Return accepted proof-certificate evidence.
    pub fn proof_evidence(&self) -> &[TrustVcNativeTrustIrCertificateEvidence] {
        &self.proof_evidence
    }

    /// Return the per-obligation discharge results for this request.
    ///
    /// SOUNDNESS: this is the ONLY thing a consumer may read as a proof result.
    pub fn discharge(&self) -> &[TrustVcNativeTrustIrDischargeOutcome] {
        &self.discharge
    }

    /// Return the ADVISORY discharge answer, when this was a discharge request.
    ///
    /// `None` for `ImportProofCertificates` and `MergeProofCertificates`.
    pub const fn advisory_discharge(&self) -> Option<&TrustVcNativeTrustIrDischargeAnswer> {
        self.advisory_discharge.as_ref()
    }

    /// Admit this request's proof-certificate evidence as native proof artifacts.
    ///
    /// Artifact order matches [`Self::proof_evidence`], preserving per-assertion
    /// diagnostics for multi-assertion native TrustIr requests.
    pub fn admit_native_proof_artifacts(&self) -> Vec<TrustVcNativeProofArtifact> {
        self.proof_evidence
            .iter()
            .map(TrustVcNativeTrustIrCertificateEvidence::admit_native_proof_artifact)
            .collect()
    }
}

/// What actually came of a native TrustIr TrustVc request.
///
/// EXISTS BECAUSE SILENCE READ AS SUCCESS. Neither report struct carried any
/// outcome, and `report_exit_code` returned EXIT_OK for every native-bundle
/// report — so a request that discharged nothing was indistinguishable from one
/// that admitted every certificate. That is the shape of a provable no-op, and
/// it is most dangerous exactly when a discharge lane is half-built.
///
/// IT STAYS LOAD-BEARING NOW THAT THE LANE ANSWERS. The discharge route hands
/// back real verdicts, but ADVISORY ones, so this enum has to distinguish
/// three things a single boolean could not: a certificate import that is a
/// genuine pass, an advisory discharge that is NOT ("no lowering witness
/// exists"), and a refutation. [`Self::is_ok`] and [`Self::exit_class`] are
/// where that distinction is kept, and the only reason the three cannot be
/// collapsed downstream.
///
/// Deliberately NOT `trust_vc_core::VerifyResult`: that type has no `Serialize`,
/// would leak counterexample bindings into a wire report, and has no variant
/// meaning "discharged nothing".
///
/// The three discharge-lane variants are APPEND-ONLY additions (the enum is
/// `#[non_exhaustive]`); `DischargeNotAnswerable` is retained and now means
/// exactly "the request never reached the lowering", never "the lowering said
/// no" — that is `DischargeDeclined`.
///
/// MERGED 2026-09-23: TWO discharge verdict families, one per lane, both kept.
/// The serialized [`crate::native_discharge`] lane mints `Discharged` /
/// `Refuted` / `DischargeDeclined` (and `DischargeNotAnswerable` for a request
/// it refuses before the lowering); the in-process ADVISORY body lane
/// ([`crate::trust_ir_body`], via
/// [`TrustVcTrustEngine::discharge_native_trust_ir_request`]) mints
/// `DischargedAdvisory` / `DischargeRefuted` / `DischargeNotAnswerable`. The
/// families never mix inside one request (see
/// [`TrustVcNativeTrustIrRequestReport`]'s wire check). `NotJudged` is what a
/// decoded discharge report of either family becomes. The fold ranks all nine
/// on one scale that is monotone in [`Self::exit_class`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrVerdict {
    /// Every cited certificate was admitted at release grade.
    CertificatesAdmitted,
    /// The request was structurally valid, but at least one certificate was
    /// refused release grade (e.g. it carries trusted evidence).
    CertificatesRejected,
    /// The request asked trust-vc to DISCHARGE obligations and never reached the
    /// lowering: no `function`, no obligations, or a shape refused at the
    /// request level. Reported explicitly rather than as an empty success.
    DischargeNotAnswerable,
    /// Every requested obligation was DISCHARGED by trust-vc's own engine, and
    /// (under the `proof-certificates` feature and a release-admissible policy)
    /// carries a kernel-checked proof artifact.
    ///
    /// READ THE PREMISE VECTOR WITH IT. `Discharged` means "proved under the
    /// premises this outcome records", not "proved outright", and two of those
    /// premises are PRODUCER CLAIMS trust-vc did not check:
    /// [`TrustVcNativeTrustIrPremiseKind::BodyAssume`] (an `Inst::Assume` in the
    /// body) and [`TrustVcNativeTrustIrPremiseKind::CalleeContract`] (a callee
    /// read through its published `ensures`). Either one, if FALSE, can prove
    /// the row by itself — an assume that cannot hold kills the path carrying
    /// the counterexample, and a callee contract its own body contradicts hands
    /// the caller a fact the program never establishes. Both are the documented
    /// design at this pin, not defects, and the callee's own contract row
    /// refutes separately; but a consumer that reads this verdict WITHOUT the
    /// premises is reading a trusted assertion as a proof.
    Discharged,
    /// At least one requested obligation was REFUTED — the solver produced a
    /// counterexample, or answered a model-less non-proof. Strictly worse than
    /// a decline: the obligation is false, not unmodelled.
    Refuted,
    /// At least one requested obligation could not be answered: an unmodelled
    /// trust-ir construct, an unmodelled formula node, or a solver `Unknown`
    /// (including an ay certification-funnel refusal). NEVER a pass.
    DischargeDeclined,
    /// Every obligation of a `DischargeProofObligations` request came back
    /// discharged by the in-process body lane — ADVISORY, and deliberately
    /// NOT a pass.
    ///
    /// [`Self::is_ok`] is FALSE for this variant, and that is the containment,
    /// not an oversight: nothing re-checks that the lowered query is the
    /// trust-ir site's meaning ([`crate::trust_ir_body::LoweringWitness::None`]),
    /// so an advisory answer must never reach a consumer as a clean bundle. The
    /// details, including the word "advisory" in its own required type, are on
    /// [`TrustVcNativeTrustIrRequestReport::advisory_discharge`].
    DischargedAdvisory,
    /// At least one obligation of a `DischargeProofObligations` request was
    /// REFUTED by the advisory body lane: a solver counterexample that
    /// trust-ir's own reference interpreter replays as a failing site.
    DischargeRefuted,
    /// A `DischargeProofObligations` request report that was DECODED, not
    /// produced: nothing in this process judged its obligations.
    ///
    /// Never produced in process. A discharge answer's per-obligation outcomes
    /// are labels a producer wrote, and the wire report carries no evidence a
    /// decoder could re-check them against — witness bindings deliberately
    /// stay in the in-process report, and the lane's answer is advisory with
    /// no lowering witness. So decoding reads no verdict off the wire: every
    /// decoded discharge report is `NotJudged`, whatever verdict and outcomes
    /// it declares, and its outcomes decode as
    /// [`TrustVcNativeTrustIrAdvisoryOutcome::NotJudged`] (advisory channel)
    /// or [`TrustVcNativeTrustIrDischargeStatus::NotJudged`] (`native_discharge`
    /// channel). The declared
    /// verdict used to be re-folded from the declared outcomes, which only
    /// caught INCONSISTENT edits: a refuted report whose outcomes and verdict
    /// were both edited to `discharged_advisory` (or `not_answerable`) decoded
    /// with its exit class moved from `Refuted` to `Unknown`, and an advisory
    /// report edited to `refuted` decoded as a FABRICATED refutation
    /// (`Unknown` → `Refuted`). An authoritative verdict for a decoded report
    /// is re-derived from the module and the request it answers:
    /// [`TrustVcTrustEngine::rejudge_native_trust_ir_discharge_report`].
    ///
    /// Exit class [`TrustVcNativeTrustIrExitClass::Unknown`]: a report nobody
    /// judged is neither a pass nor a refutation.
    NotJudged,
}

/// What a bundle verdict means for a process exit code.
///
/// Lives here, not in the runner, so that ADDING a verdict variant is a
/// compile error in this exhaustive match rather than a silent fall-through to
/// a success exit in a downstream `_ =>` arm. Deliberately NOT `non_exhaustive`:
/// the runner must be able to match it exhaustively.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustVcNativeTrustIrExitClass {
    /// Exit successfully.
    Ok,
    /// Exit as a refutation.
    Refuted,
    /// Exit as "could not answer".
    Unknown,
    /// Exit as "consumed, but a certificate is not release grade".
    ///
    /// The bundle was well-formed and every certificate was graded, but at
    /// least one was refused release admission (pending/failed/trusted
    /// obligation, trusted payload, missing identity or source mapping, or
    /// coverage not established as `Unbounded`). That is not a pass: nothing
    /// the bundle claims has been established at release grade.
    Rejected,
}

impl TrustVcNativeTrustIrVerdict {
    /// Is this verdict a clean pass?
    ///
    /// Used for the bundle rollup and the process exit code, so the two can
    /// never disagree about what counts as success.
    ///
    /// `CertificatesAdmitted` and the `native_discharge` lane's `Discharged`
    /// qualify. [`Self::DischargedAdvisory`] does not: an advisory answer with
    /// no lowering witness is not an authoritative pass, and the one place that
    /// distinction could quietly be lost is exactly here.
    pub const fn is_ok(self) -> bool {
        matches!(self, Self::CertificatesAdmitted | Self::Discharged)
    }

    /// Exit classification, exhaustive over the verdict enum.
    ///
    /// ONLY `CertificatesAdmitted` is `Ok`. `CertificatesRejected` used to be
    /// `Ok` too ("release admission is a grading result"), which made
    /// [`TrustVcTrustEngine::validate_native_trust_ir_bundle`] — documented as
    /// "`Ok(())` means the rollup is a clean pass" — answer `Ok(())` for a
    /// bundle none of whose certificates was admitted, and the runner exit 0
    /// for it. It is now [`TrustVcNativeTrustIrExitClass::Rejected`]: the
    /// report still says which certificates are non-release and why; the exit
    /// no longer says that nothing is wrong.
    pub const fn exit_class(self) -> TrustVcNativeTrustIrExitClass {
        match self {
            Self::CertificatesAdmitted | Self::Discharged => TrustVcNativeTrustIrExitClass::Ok,
            Self::CertificatesRejected => TrustVcNativeTrustIrExitClass::Rejected,
            Self::Refuted | Self::DischargeRefuted => TrustVcNativeTrustIrExitClass::Refuted,
            // An advisory discharge is NOT a pass; see `is_ok`. A decoded
            // discharge report was judged by nobody here.
            Self::DischargeNotAnswerable
            | Self::DischargeDeclined
            | Self::DischargedAdvisory
            | Self::NotJudged => TrustVcNativeTrustIrExitClass::Unknown,
        }
    }

    /// Rank for the worst-wins fold; higher is worse.
    ///
    /// A total order rather than the pairwise match this replaced, so the fold
    /// is obviously commutative and associative however many variants exist.
    ///
    /// # The ranking must never improve an exit class
    ///
    /// The runner's exit code reads [`Self::exit_class`] of the FOLDED verdict
    /// and nothing else, so this ranking is only sound if it is monotone in
    /// `exit_class`: every verdict with a non-`Ok` exit class must outrank
    /// every verdict with an `Ok` one. It briefly was not —
    /// `DischargedAdvisory` (exit class `Unknown`) ranked BELOW
    /// `CertificatesRejected` (then exit class `Ok`), so a bundle pairing an
    /// advisory discharge with one rejected certificate folded to
    /// `CertificatesRejected` and the runner exited 0, laundering the advisory
    /// answer away. `the_fold_never_improves_an_exit_class` pins the property
    /// over every ordered pair; keep this ranking grouped by exit class, in
    /// the order `Ok` < `Rejected` < `Unknown` < `Refuted`.
    ///
    /// The `native_discharge` lane's pairwise fold ranked not-answerable ABOVE
    /// refuted, which is not monotone in exit class (a refutation exits
    /// `Refuted`, a not-answerable `Unknown`); on this scale both refutations
    /// outrank every `Unknown`. Its other two rules survive unchanged: declined
    /// outranks rejected, and `Discharged` survives only as the unanimous
    /// answer — it ranks below `CertificatesAdmitted`, so a bundle that mixes an
    /// import with a discharge rolls up to the import label rather than
    /// claiming the whole bundle was discharged.
    const fn severity(self) -> u8 {
        match self {
            // --- exit class Ok ---
            Self::Discharged => 0,
            Self::CertificatesAdmitted => 1,
            // --- exit class Rejected ---
            Self::CertificatesRejected => 2,
            // --- exit class Unknown ---
            // Answered, but advisory: never a pass. It must outrank every
            // Ok-exiting verdict or the fold would erase it.
            Self::DischargedAdvisory => 3,
            Self::DischargeDeclined => 4,
            Self::DischargeNotAnswerable => 5,
            // Decoded, judged by nobody: the least informative Unknown.
            Self::NotJudged => 6,
            // --- exit class Refuted ---
            Self::Refuted => 7,
            Self::DischargeRefuted => 8,
        }
    }

    /// Worst-wins fold, so one bad request cannot be averaged away by good ones.
    ///
    /// NOTE this fold CANNOT enforce the mode/verdict pairing (an import request
    /// must never answer `Discharged`). That is enforced structurally at the
    /// mode match in `build_request_report`, which is the only place a verdict
    /// is minted, and re-checked on the wire by the request report's `TryFrom`.
    const fn worse_of(self, other: Self) -> Self {
        if other.severity() > self.severity() {
            other
        } else {
            self
        }
    }
}

/// Native TrustVc operation requested by TrustIr.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrRequestMode {
    ImportProofCertificates,
    MergeProofCertificates,
    /// TrustIr asked trust-vc to DISCHARGE the request's obligations itself,
    /// rather than check certificates produced elsewhere.
    ///
    /// ANSWERABLE for the scalar fragment. The request is routed to
    /// `native_discharge`, which lowers the named `function`'s trust-ir body and
    /// each obligation's typed `trust-types.Formula@1` payload into trust-vc's
    /// own IR and runs the real engine. Everything outside that fragment
    /// DECLINES by name — see [`TrustVcNativeTrustIrVerdict::DischargeDeclined`].
    ///
    /// The two adapter-side certificate guards are mode-conditional for exactly
    /// this reason: a discharge request PRODUCES the certificate and the
    /// evidence bundle that an import request must CARRY. They are still
    /// enforced verbatim for Import/Merge. What replaced them is not silence:
    /// every report carries a verdict, the per-obligation `discharge` vector is
    /// the only thing a consumer may read as a proof result, and the runner maps
    /// a non-pass verdict to a non-zero exit.
    ///
    /// A SECOND, ADVISORY answer exists for an in-memory module (merged
    /// 2026-09-23): [`TrustVcTrustEngine::discharge_native_trust_ir_request`]
    /// routes one request to the in-process body lane ([`crate::trust_ir_body`]),
    /// which lowers the named `trust_ir::Function` and answers the `Assert` sites
    /// of the cited obligations. That answer lands on
    /// [`TrustVcNativeTrustIrRequestReport::advisory_discharge`] and NEVER on
    /// `proof_evidence`, so it cannot be admitted as a native proof artifact; see
    /// [`TrustVcNativeTrustIrDischargeAnswer`] for why it cannot be read as
    /// authority. It was written at trust-ir 0.11, where upstream's validator
    /// refused every certificate-less discharge request, so it reached its answer
    /// only in process; at this pin the serialized path is open and is routed to
    /// `native_discharge` above, not to the advisory lane.
    ///
    /// Mirrors `trust_ir::request::TrustVcVerificationMode::DischargeProofObligations`.
    /// The seam spelling differs by design: upstream serializes as
    /// `DischargeProofObligations`, this enum as `discharge_proof_obligations`
    /// via `rename_all = "snake_case"`.
    DischargeProofObligations,
}

impl From<TrustVcVerificationMode> for TrustVcNativeTrustIrRequestMode {
    fn from(value: TrustVcVerificationMode) -> Self {
        match value {
            TrustVcVerificationMode::ImportProofCertificates => Self::ImportProofCertificates,
            TrustVcVerificationMode::MergeProofCertificates => Self::MergeProofCertificates,
            TrustVcVerificationMode::DischargeProofObligations => Self::DischargeProofObligations,
        }
    }
}

/// One obligation's result on the DISCHARGE lane.
///
/// THIS VECTOR IS THE ONLY PROOF RESULT A CONSUMER MAY READ. The artifact list
/// (`proof_evidence`) says which certificates exist; it does not say which
/// obligations held. A bridge that maps artifacts to "proved" reports a refuted
/// request as a pass the moment one sibling obligation happens to carry
/// evidence. Map `outcome` and nothing else.
///
/// DECODED, its outcome is always
/// [`TrustVcNativeTrustIrDischargeStatus::NotJudged`]: the wire carries a
/// status with no evidence behind it, and this type — not the report that may
/// contain it — erases it, so no decode path can read one back. Only an
/// outcome produced in process carries a status.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "WireDischargeOutcome")]
#[must_use]
pub struct TrustVcNativeTrustIrDischargeOutcome {
    obligation_id: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    public_obligation_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    semantic_digest: Option<String>,
    /// `sha256(ProofFormula.payload)` for the formula this outcome is ABOUT.
    ///
    /// Soundness checklist item A: neither `Module::stable_digest` nor
    /// `write_native_request_stable` covers an obligation's formula, so an
    /// outcome that names only an obligation id would replay against a re-lowered
    /// obligation with an edited `ensures`. This binds the bytes that were
    /// actually solved.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    formula_payload_sha256: Option<String>,
    outcome: TrustVcNativeTrustIrDischargeStatus,
    /// Everything this outcome RESTS ON that trust-vc did not itself prove:
    /// `Inst::Assume` nodes folded into the unit, callee contracts used in place
    /// of callee bodies, monomorphization facts. A premise never disappears into
    /// a certified verdict — it is a `(Trusted, None)` assumption on the row.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    premises: Vec<TrustVcNativeTrustIrPremise>,
    message: String,
}

impl TrustVcNativeTrustIrDischargeOutcome {
    /// Build an outcome for one obligation, binding its public identity and the
    /// digest of the formula bytes this run actually saw.
    ///
    /// SOUNDNESS (checklist item A): the public identity and
    /// `sha256(ProofFormula.payload)` are read from the bundle here, at the
    /// point the obligation is decided — never reconstructed later from an id.
    /// Neither `Module::stable_digest` nor `write_native_request_stable` covers
    /// an obligation's formula, so an outcome that named only `obligation_id`
    /// would replay unchanged against a re-lowered obligation with an edited
    /// `ensures`.
    ///
    /// The two digests have DIFFERENT authorities, and a reader must not
    /// conflate them. `formula_payload_sha256` is computed HERE, over the bytes
    /// this run actually decided, so it is trust-vc's own claim. The
    /// `semantic_digest` is the PRODUCER's claim, copied verbatim off
    /// `PublicObligationIdentity`: it is `canonical_obligation_context_digest_sha256`
    /// over the api row's kind, description, metadata and contract, none of
    /// which reach this crate, so nothing here can recompute it and a bundle
    /// whose `semantic_digest` disagrees with its own formula is not detectable
    /// on this side. It is re-checked where it is checkable, on import. Bind to
    /// `formula_payload_sha256` for "which predicate was decided".
    pub(crate) fn new(
        inputs: &RequestReportInputs<'_>,
        obligation_id: ProofId,
        outcome: TrustVcNativeTrustIrDischargeStatus,
        premises: Vec<TrustVcNativeTrustIrPremise>,
        message: impl Into<String>,
    ) -> Self {
        let obligation = inputs.obligations.get(&obligation_id).copied();
        let public = obligation
            .and_then(|obligation| obligation.source.as_ref())
            .and_then(|source| source.public.as_ref());
        Self {
            obligation_id: obligation_id.index(),
            public_obligation_id: public.map(|public| public.obligation_id.clone()),
            semantic_digest: public.map(|public| public.semantic_digest.to_string()),
            formula_payload_sha256: obligation
                .and_then(|obligation| obligation.formula.as_ref())
                .map(|formula| sha256_hex(formula.payload.as_bytes())),
            outcome,
            premises,
            message: message.into(),
        }
    }

    /// Build a `Declined` outcome naming the construct trust-vc refused.
    pub(crate) fn declined(
        inputs: &RequestReportInputs<'_>,
        obligation_id: ProofId,
        reason: impl Into<String>,
    ) -> Self {
        let reason = reason.into();
        Self::new(
            inputs,
            obligation_id,
            TrustVcNativeTrustIrDischargeStatus::Declined {
                reason: reason.clone(),
            },
            Vec::new(),
            reason,
        )
    }

    /// Return the TrustIr proof-obligation id this outcome is about.
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }

    /// Return the public `vc:<def_path>:<kind>:<i>` identity, when the bundle
    /// carried one.
    pub fn public_obligation_id(&self) -> Option<&str> {
        self.public_obligation_id.as_deref()
    }

    /// Return the public obligation's semantic digest, when carried.
    ///
    /// The PRODUCER's claim, copied verbatim and not recomputable here (see
    /// [`Self::new`]). [`Self::formula_payload_sha256`] is the digest trust-vc
    /// itself computed over the predicate it decided.
    pub fn semantic_digest(&self) -> Option<&str> {
        self.semantic_digest.as_deref()
    }

    /// Return `sha256(ProofFormula.payload)` for the solved formula.
    pub fn formula_payload_sha256(&self) -> Option<&str> {
        self.formula_payload_sha256.as_deref()
    }

    /// Return what came of this obligation.
    pub const fn outcome(&self) -> &TrustVcNativeTrustIrDischargeStatus {
        &self.outcome
    }

    /// Return the trusted premises this outcome rests on.
    pub fn premises(&self) -> &[TrustVcNativeTrustIrPremise] {
        &self.premises
    }

    /// Return the human-readable explanation for this outcome.
    pub fn message(&self) -> &str {
        &self.message
    }

    /// The verdict this single outcome forces on its request.
    const fn verdict(&self) -> TrustVcNativeTrustIrVerdict {
        match &self.outcome {
            TrustVcNativeTrustIrDischargeStatus::Verified => {
                TrustVcNativeTrustIrVerdict::Discharged
            }
            TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
            | TrustVcNativeTrustIrDischargeStatus::NotProved => {
                TrustVcNativeTrustIrVerdict::Refuted
            }
            // An `Unknown` is a NON-PROOF, so it folds with the declines. It is
            // deliberately NOT `Discharged`: an ay certification-funnel refusal
            // (`ConfirmationDisagree` / self-check-rejected) arrives here, and
            // publishing it as a pass would bypass the funnel this engine exists
            // to respect. The distinction survives in `outcome`.
            TrustVcNativeTrustIrDischargeStatus::Unknown { .. }
            | TrustVcNativeTrustIrDischargeStatus::Declined { .. } => {
                TrustVcNativeTrustIrVerdict::DischargeDeclined
            }
            TrustVcNativeTrustIrDischargeStatus::NotJudged => {
                TrustVcNativeTrustIrVerdict::NotJudged
            }
        }
    }
}

/// Deserialization mirror of [`TrustVcNativeTrustIrDischargeOutcome`]. The
/// outcome must be present and well-formed, and is never read.
#[derive(Deserialize)]
struct WireDischargeOutcome {
    obligation_id: u32,
    #[serde(default)]
    public_obligation_id: Option<String>,
    #[serde(default)]
    semantic_digest: Option<String>,
    #[serde(default)]
    formula_payload_sha256: Option<String>,
    #[serde(rename = "outcome")]
    _declared_outcome: TrustVcNativeTrustIrDischargeStatus,
    #[serde(default)]
    premises: Vec<TrustVcNativeTrustIrPremise>,
    message: String,
}

impl From<WireDischargeOutcome> for TrustVcNativeTrustIrDischargeOutcome {
    fn from(wire: WireDischargeOutcome) -> Self {
        Self {
            obligation_id: wire.obligation_id,
            public_obligation_id: wire.public_obligation_id,
            semantic_digest: wire.semantic_digest,
            formula_payload_sha256: wire.formula_payload_sha256,
            outcome: TrustVcNativeTrustIrDischargeStatus::NotJudged,
            premises: wire.premises,
            message: wire.message,
        }
    }
}

/// What came of one obligation on the discharge lane.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrDischargeStatus {
    /// trust-vc's engine proved the obligation.
    Verified,
    /// The solver found a concrete model in which the obligation is FALSE.
    Counterexample {
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        bindings: Vec<TrustCounterexampleBinding>,
    },
    /// A model-less non-proof: the obligation did not hold up, but no
    /// counterexample was recovered.
    NotProved,
    /// The solver could neither prove nor refute — including an ay
    /// certification-funnel refusal of an UNSAT it found.
    Unknown { reason: String, category: String },
    /// trust-vc REFUSED to model this obligation: an unmodelled trust-ir
    /// construct, type, or formula node. The reason names the construct.
    Declined { reason: String },
    /// DECODED from the wire: whatever status the payload declared, nothing in
    /// this process judged it (see [`TrustVcNativeTrustIrVerdict::NotJudged`]).
    /// Never produced in process.
    NotJudged,
}

/// A fact a discharge outcome RESTS ON but did not prove.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrPremise {
    kind: TrustVcNativeTrustIrPremiseKind,
    detail: String,
}

impl TrustVcNativeTrustIrPremise {
    /// Record one trusted premise.
    pub fn new(kind: TrustVcNativeTrustIrPremiseKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Return the premise class.
    pub const fn kind(&self) -> TrustVcNativeTrustIrPremiseKind {
        self.kind
    }

    /// Return what exactly was assumed.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

/// Classes of trusted premise a discharge outcome can rest on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrPremiseKind {
    /// An `Inst::Assume` node in the body was folded in as an assumption.
    ///
    /// The producer asserted it; trust-vc did not prove it. An assume that is
    /// FALSE on some path removes that path from the model entirely — and a
    /// path-local one does not trip the engine's `VacuousTruth` detector, which
    /// fires only on a globally contradictory assumption set. So an outcome
    /// carrying this premise can be `Discharged` on the strength of the assume
    /// alone, with no counterexample and no `Unknown` to signal it. That is the
    /// intended reading of an assume, and it is exactly why the premise is
    /// recorded rather than folded in silently.
    BodyAssume,
    /// A callee's contract (`ensures`) was assumed in place of its body.
    ///
    /// At this trust-ir pin there is no opacity marker, so a callee is read
    /// contract-only (see the `native_discharge` module docs) — which is the
    /// right reading for `external_body` and the only available one here. The
    /// consequence to state plainly: if the callee's published `ensures` is
    /// false about its own body, the caller's row is proved from a fact the
    /// program never establishes, and a contract that is CONTRADICTORY kills the
    /// call's path the way a false `BodyAssume` does. The callee's own contract
    /// row refutes separately — that is where the defect surfaces — so this
    /// premise is the pointer to the row a consumer must also read.
    CalleeContract,
    /// A callee's body was used definitionally (unified compilation).
    InlinedCalleeBody,
    /// A callee produced no usable fact at all: its result is unconstrained.
    HavockedCallee,
    /// A callee published obligation rows this lane deliberately did NOT import.
    ///
    /// Recorded so that "the lane did not use it" is visible rather than silent.
    /// Every omission is an explicit rule in
    /// `native_discharge::body::Builder::callee_contract_facts` and only
    /// WEAKENS the unit; a row that could impose an obligation on the call site
    /// (any `Precondition`), or whose kind this build has no rule for, declines
    /// the call instead. Adversarial review round 6 found the opposite shape —
    /// a filter that silently dropped a callee `requires` carrying an
    /// `ObligationSite` — and this premise is the audit trail that makes the
    /// same class visible next time.
    UnimportedCalleeObligation,
    /// The function's own def-site `requires` was ASSUMED at its definition.
    ///
    /// That is what a `requires` MEANS, and its `ProofStatus` is deliberately not
    /// read (assuming your own precondition at your own definition site does not
    /// depend on whether the call sites established it). But it is still pure
    /// PRODUCER content folded into the unit's assumptions with no proof and no
    /// satisfiability check of its own, exactly like an `Inst::Assume` — and a
    /// reader of a `Discharged` outcome could not previously see which `requires`
    /// rows the proof rested on. Adversarial review round 7 named the asymmetry;
    /// this premise removes it. A GLOBALLY contradictory `requires` is still
    /// caught by the engine's `VacuousTruth` detector, so this is disclosure, not
    /// a soundness patch.
    DefSiteRequires,
    /// A monomorphization fact the compiler supplied rather than trust-vc derived.
    Monomorphization,
    /// Fixed-width arithmetic decided at the declared machine width.
    ///
    /// MEASURED, and the reason this premise exists: a contract clause's `x + 1`
    /// denotes MATHEMATICAL addition on the wire (the clause parser emits
    /// `Formula::Add` at `Sort::Int` and renders it `(+ a b)`), while this lane
    /// decides it at the value's declared width. The two readings agree exactly
    /// when the operation does not overflow — and the no-overflow claim is a
    /// PANIC-FREEDOM obligation, a separate row with its own suite, which this
    /// lane neither decides nor assumes away. So an outcome over machine
    /// arithmetic rests on that other row, and says so here rather than leaving
    /// a reader to infer the whole-program claim from a postcondition alone.
    MachineArithmetic,
}

/// A proof certificate trust-vc PRODUCED on the discharge lane.
///
/// Deliberately not `trust_ir::ProofCertificate` in the serialized report:
/// that type is `PartialEq` but not `Eq` (its `GammaCrownBound` variant carries
/// floats), and the report is `Eq`. [`Self::to_trust_ir_certificate`] mints the
/// real upstream value for a caller that folds it back into a bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrProducedCertificate {
    request_id: u32,
    obligation_id: u32,
    prover: String,
    /// The verification unit (and therefore the assertion) this proof refutes
    /// the negation of.
    unit_id: String,
    /// The Alethe proof text ay produced and `trust-vc-kernel` re-checked.
    alethe: String,
    kernel_verified: bool,
    strict_verified: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    semantic_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    formula_payload_sha256: Option<String>,
}

impl TrustVcNativeTrustIrProducedCertificate {
    /// Mint a certificate row for an obligation trust-vc just proved.
    ///
    /// SOUNDNESS (checklist item A): the row binds the public semantic digest
    /// AND `sha256(ProofFormula.payload)`. A certificate that named only an
    /// obligation id would replay against a re-lowered obligation with an edited
    /// `ensures`, because neither `Module::stable_digest` nor
    /// `write_native_request_stable` covers a formula.
    ///
    /// The two digests have DIFFERENT authorities, and a reader must not
    /// conflate them. `formula_payload_sha256` is computed HERE, over the bytes
    /// this run actually decided, so it is trust-vc's own claim. The
    /// `semantic_digest` is the PRODUCER's claim, copied verbatim off
    /// `PublicObligationIdentity`: it is `canonical_obligation_context_digest_sha256`
    /// over the api row's kind, description, metadata and contract, none of
    /// which reach this crate, so nothing here can recompute it and a bundle
    /// whose `semantic_digest` disagrees with its own formula is not detectable
    /// on this side. It is re-checked where it is checkable, on import. Bind to
    /// `formula_payload_sha256` for "which predicate was decided".
    pub(crate) fn new(
        inputs: &RequestReportInputs<'_>,
        obligation_id: ProofId,
        unit_id: &str,
        alethe: String,
        kernel_verified: bool,
        strict_verified: bool,
    ) -> Self {
        let obligation = inputs.obligations.get(&obligation_id).copied();
        let public = obligation
            .and_then(|obligation| obligation.source.as_ref())
            .and_then(|source| source.public.as_ref());
        Self {
            request_id: inputs.request.id.index(),
            obligation_id: obligation_id.index(),
            prover: TRUST_VC_DISCHARGE_PROVER.to_string(),
            unit_id: unit_id.to_string(),
            alethe,
            kernel_verified,
            strict_verified,
            semantic_digest: public.map(|public| public.semantic_digest.to_string()),
            formula_payload_sha256: obligation
                .and_then(|obligation| obligation.formula.as_ref())
                .map(|formula| sha256_hex(formula.payload.as_bytes())),
        }
    }

    /// The evidence row for this produced certificate.
    ///
    /// Deliberately the SAME row type an imported certificate produces, and it
    /// goes through the same `from_native_parts` release-admission rules — so a
    /// certificate this lane minted is graded by the rules it would be graded by
    /// on the way back in, not by a private standard.
    ///
    /// `obligation_status` is `Discharged` because that is what trust-vc
    /// concluded, and this row is only built for an outcome that verified. The
    /// module's own status is the PRODUCER's claim about a proof that did not
    /// exist yet; quoting it here would reject trust-vc's own result.
    ///
    /// ROUND 9's minor: this used to DEFAULT when the module carried no
    /// obligation for the produced certificate — publishing
    /// `obligation_kind = Postcondition` and an empty description for a row
    /// nothing described. That is the move the round-8 blocker's own remedy
    /// forbade ("where a rendering is absent, say what that means and fail
    /// closed rather than defaulting"), sitting beside the field that remedy had
    /// just made fail-closed. It is unreachable today — a produced certificate's
    /// obligation id is taken from the module — so the repair is a REFUSAL, not
    /// a fallback value.
    pub(crate) fn evidence_row(
        &self,
        inputs: &RequestReportInputs<'_>,
    ) -> Result<TrustVcNativeTrustIrCertificateEvidence, TrustEngineError> {
        let obligation_id = ProofId::new(self.obligation_id);
        let Some(obligation) = inputs.obligations.get(&obligation_id).copied() else {
            return Err(
                TrustEngineError::NativeTrustIrProducedCertificateUnknownObligation {
                    module: inputs.module.name.clone(),
                    obligation_id: self.obligation_id,
                    unit_id: self.unit_id.clone(),
                },
            );
        };
        // The same refusal an imported certificate meets: a spec-attributed
        // obligation, or a kind with no faithful native label, is not stated
        // under a guessed kind.
        let obligation_kind = importable_obligation_kind(inputs.request.id.index(), obligation)?;
        let obligation = Some(obligation);
        let source = inputs.compiler_fact_sources.get(&obligation_id).copied();
        // THE EXPORT SEAM. The compiler-fact `assertion_id` is published only
        // when the discharge request carries exactly one `Assertion` replay atom
        // for this obligation, stating the same id.
        let (renderings, corroboration) = crate::native_assertion_id::corroboration_for(
            inputs.obligations,
            inputs.compiler_fact_sources,
            inputs.assertion_ids,
            obligation_id,
            &inputs.request.provenance.replay_context,
        );
        let assertion_id = corroboration.licensed(&renderings);
        let independent_assertion_id = corroboration.independent(&renderings);
        let alethe_digest = sha256_hex(self.alethe.as_bytes());
        let suite_identity = TrustVcNativeVerifierSuiteIdentity::new(
            TrustVcNativeVerifierSuite::TrustVc,
            TRUST_VC_DISCHARGE_PROVER,
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
        );
        let solver_identity = TrustVcNativeSolverIdentity::new(TRUST_VC_DISCHARGE_PROVER)
            .with_solver(TrustVcNativeToolIdentity::new("ay"))
            .with_replay_identity(
                TRUST_VC_DISCHARGE_REPLAY_ENGINE,
                format!("trust-vc discharge {}", self.unit_id),
                Some(alethe_digest.clone()),
            );
        let compiler_facts_binding =
            compiler_facts_binding(inputs.compiler_facts_digest, self.obligation_id, source);
        let certificate = self.to_trust_ir_certificate();
        let release_admission =
            TrustVcNativeTrustIrCertificateAdmission::from_native_parts(AdmissionParts {
                assertion_id,
                trust_ir_obligation_id: self.obligation_id,
                status: TrustVcNativeArtifactObligationStatus::Discharged,
                certificate: &certificate,
                suite_identity: &suite_identity,
                solver_identity: &solver_identity,
                compiler_facts_binding: &compiler_facts_binding,
                coverage: inputs.coverage,
            });
        Ok(TrustVcNativeTrustIrCertificateEvidence {
            obligation_id: self.obligation_id,
            assertion_id,
            independent_assertion_id,
            trust_ir_module_digest: inputs.trust_ir_module_digest.to_string(),
            request_digest: inputs.request_digest.to_string(),
            obligation_kind,
            obligation_status: TrustVcNativeArtifactObligationStatus::Discharged,
            description: obligation
                .map(|obligation| obligation.description.clone())
                .unwrap_or_default(),
            formula_schema: obligation
                .and_then(|obligation| obligation.formula.as_ref())
                .map(|formula| formula.schema.clone()),
            formula_sort: obligation
                .and_then(|obligation| obligation.formula.as_ref())
                .and_then(|formula| formula.sort.clone()),
            prover: self.prover.clone(),
            evidence_digest: alethe_digest,
            certificate_digest: certificate.stable_digest().to_string(),
            suite_identity,
            solver_identity,
            replay_metadata: None,
            compiler_facts_binding,
            evidence_kind: TrustVcNativeTrustIrEvidenceKind::SmtProof,
            trusted: false,
            release_admission,
        })
    }

    /// Return the unit id (the public `vc:` identity where the bundle has one)
    /// this certificate was produced under.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the native request this certificate was produced for.
    pub const fn request_id(&self) -> u32 {
        self.request_id
    }

    /// Return the TrustIr obligation this certificate discharges.
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }

    /// Return the prover label stamped on the certificate.
    pub fn prover(&self) -> &str {
        &self.prover
    }

    /// Return the rendered Alethe proof text.
    pub fn alethe(&self) -> &str {
        &self.alethe
    }

    /// Return whether `trust-vc-kernel` independently re-checked the proof.
    pub const fn kernel_verified(&self) -> bool {
        self.kernel_verified
    }

    /// Return whether ay's strict proof checker accepted the proof.
    pub const fn strict_verified(&self) -> bool {
        self.strict_verified
    }

    /// Return the public obligation's semantic digest, when carried.
    ///
    /// The PRODUCER's claim, copied verbatim and not recomputable here (see
    /// [`Self::new`]). [`Self::formula_payload_sha256`] is the digest trust-vc
    /// itself computed over the predicate it proved.
    pub fn semantic_digest(&self) -> Option<&str> {
        self.semantic_digest.as_deref()
    }

    /// Return `sha256(ProofFormula.payload)` for the formula this certificate
    /// refutes the negation of.
    pub fn formula_payload_sha256(&self) -> Option<&str> {
        self.formula_payload_sha256.as_deref()
    }

    /// Mint the upstream `trust_ir::ProofCertificate` for this row.
    ///
    /// `assurance` is `None` (NOT RECORDED): trust-ir-build establishes a
    /// coverage bound only from the cited request's own fields, and a TrustVc
    /// request states none, so any bound recorded here would be the
    /// producer's word alone. Release admission therefore refuses this
    /// certificate's coverage as unrecorded.
    pub fn to_trust_ir_certificate(&self) -> ProofCertificate {
        ProofCertificate {
            obligation: ProofId::new(self.obligation_id),
            prover: self.prover.clone(),
            evidence: ProofEvidence::SmtProof(self.alethe.clone().into_bytes()),
            assurance: None,
        }
    }
}

/// The ADVISORY answer to one `DischargeProofObligations` request.
///
/// # This is not authority, and the type is what says so
///
/// Five properties keep a body-lane answer out of the authoritative channel,
/// and every one of them is structural rather than a policy a caller could
/// forget to apply:
///
/// 1. [`Self::authority`] is [`TrustVcNativeTrustIrDischargeAuthority`], which
///    has exactly ONE variant, `Advisory`. It is a REQUIRED serde field with
///    no `default`, so a report from which the label was stripped does not
///    deserialize at all, and no other value can be spelled.
/// 2. [`Self::lowering_witness`] is
///    [`TrustVcNativeTrustIrLoweringWitness`], which has exactly one variant,
///    `None`. Nothing re-checks that the lowered solver query is the trust-ir
///    site's meaning, and the type states it rather than leaving it to a doc.
/// 3. It never reaches `proof_evidence`, the only list
///    [`TrustVcNativeTrustIrRequestReport::admit_native_proof_artifacts`]
///    reads, so no [`crate::TrustVcNativeProofArtifact`] can be minted from it.
/// 4. It carries no `trust_ir::ProofStatus`, no `trust_ir::ProofCertificate`
///    and no proof formula — only obligation ids, outcome labels and
///    human-readable detail. Producer claims the lane SAW are recorded as
///    [`Self::ignored_inputs`], present and deliberately unread.
/// 5. Its request verdict is [`TrustVcNativeTrustIrVerdict::DischargedAdvisory`],
///    whose [`TrustVcNativeTrustIrVerdict::is_ok`] is FALSE and whose
///    [`TrustVcNativeTrustIrVerdict::exit_class`] is
///    [`TrustVcNativeTrustIrExitClass::Unknown`], so a bundle answered this way
///    cannot exit 0. That verdict is REQUIRED on the wire and cross-checked
///    against the mode (see
///    [`TrustVcNativeTrustIrRequestReport`]) — it used to be `serde(default)`ed
///    to the permissive verdict, which made properties 1-4 guard a label while
///    the only field that decides success was free to be omitted.
///
/// A sixth property is about what the answer does NOT hide rather than what it
/// cannot claim: [`Self::unexamined_asserts`] discloses the `Assert` sites in
/// the same function that no cited obligation covers, so "every cited
/// obligation discharged" can never be read as "this function is clean".
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrDischargeAnswer {
    /// Always `Advisory`. Required, defaultless, single-valued: see the type doc.
    authority: TrustVcNativeTrustIrDischargeAuthority,
    /// Always `None`. Required, defaultless, single-valued: see the type doc.
    lowering_witness: TrustVcNativeTrustIrLoweringWitness,
    /// Schema of the body lane that produced this answer.
    lane_schema: String,
    /// Stable digest of the `NativeVerificationRequest` this answers.
    ///
    /// Present so a consumer holding only this report can check WHICH request
    /// it answers. Not authority: it binds the answer to a question, not the
    /// lowering to a meaning.
    request_digest: String,
    /// Stable digest of the `trust_ir::Module` the lane actually read.
    ///
    /// The in-process entry
    /// ([`crate::TrustVcTrustEngine::discharge_native_trust_ir_request`])
    /// performs no upstream bundle validation, so nothing else checks that the
    /// request was minted against this module. Recording the digest is what
    /// makes a mix-up detectable rather than silent.
    trust_ir_module_digest: String,
    /// The `trust_ir::FuncId` index the request named.
    function: u32,
    /// The body lane's provisional semantic digest of that function.
    semantic_digest: String,
    /// Set when the body is outside the lane's v0 fragment; every obligation
    /// is then `NotAnswerable` for this reason.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    function_refusal: Option<String>,
    /// Present iff some obligation below was decided under the havoc reading
    /// of `Inst::Undef`; see `crate::trust_ir_body`'s module doc.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    havoc_instantiation_note: Option<String>,
    /// `Assert` sites in the named function that NO cited obligation covers,
    /// and which the lane therefore did not examine.
    ///
    /// A discharge answer that says nothing about these would let a consumer
    /// read "every cited obligation discharged" as "this function is clean".
    /// Empty for a body with no unobligated asserts, and for a refused body.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    unexamined_asserts: Vec<TrustVcNativeTrustIrUnexaminedAssert>,
    /// One entry per cited obligation, in `ProofId` order.
    obligations: Vec<TrustVcNativeTrustIrDischargeObligation>,
    /// What the lane saw and deliberately did not read as fact.
    ignored_inputs: TrustVcNativeTrustIrDischargeIgnoredInputs,
}

impl TrustVcNativeTrustIrDischargeAnswer {
    /// Always [`TrustVcNativeTrustIrDischargeAuthority::Advisory`].
    pub const fn authority(&self) -> TrustVcNativeTrustIrDischargeAuthority {
        self.authority
    }

    /// Always [`TrustVcNativeTrustIrLoweringWitness::None`].
    pub const fn lowering_witness(&self) -> TrustVcNativeTrustIrLoweringWitness {
        self.lowering_witness
    }

    /// Return the body lane schema that produced this answer.
    pub fn lane_schema(&self) -> &str {
        &self.lane_schema
    }

    /// Return the stable digest of the request this answers.
    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    /// Return the stable digest of the module the lane read.
    pub fn trust_ir_module_digest(&self) -> &str {
        &self.trust_ir_module_digest
    }

    /// Return the `Assert` sites in the named function that no cited
    /// obligation covers, and which the lane therefore did not examine.
    pub fn unexamined_asserts(&self) -> &[TrustVcNativeTrustIrUnexaminedAssert] {
        &self.unexamined_asserts
    }

    /// Return the `trust_ir::FuncId` index the request named.
    pub const fn function(&self) -> u32 {
        self.function
    }

    /// Return the body lane's provisional semantic digest of that function.
    pub fn semantic_digest(&self) -> &str {
        &self.semantic_digest
    }

    /// Return why the whole body was refused, when it was.
    pub fn function_refusal(&self) -> Option<&str> {
        self.function_refusal.as_deref()
    }

    /// Return the havoc-reading disclosure, when some verdict here carries it.
    pub fn havoc_instantiation_note(&self) -> Option<&str> {
        self.havoc_instantiation_note.as_deref()
    }

    /// Return the per-obligation answers, in `ProofId` order.
    pub fn obligations(&self) -> &[TrustVcNativeTrustIrDischargeObligation] {
        &self.obligations
    }

    /// Return what the lane saw and did not read as fact.
    pub const fn ignored_inputs(&self) -> &TrustVcNativeTrustIrDischargeIgnoredInputs {
        &self.ignored_inputs
    }
}

/// An `Assert` the advisory lane did not examine, because no cited obligation
/// covers it.
///
/// Mirrors `crate::trust_ir_body::AssertPosition` onto the wire, carrying
/// [`crate::trust_ir_body::UNOBLIGATED_ASSERT_LABEL`] verbatim so the report
/// says what it means without the reader needing this doc.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrUnexaminedAssert {
    /// `trust_ir::BlockId` index of the block holding the assert.
    pub block: u32,
    /// Instruction index within that block.
    pub inst_index: u32,
    /// Always [`crate::trust_ir_body::UNOBLIGATED_ASSERT_LABEL`].
    pub label: String,
}

/// Authority of a discharge answer. One variant, on purpose.
///
/// NOT `non_exhaustive`, and NOT defaultable in serde: a second variant would
/// be a breaking change that has to be argued for, which is the point.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustVcNativeTrustIrDischargeAuthority {
    /// Advisory only: see [`TrustVcNativeTrustIrDischargeAnswer`].
    Advisory,
}

/// Evidence that the lowering matches trust-ir semantics. None exists yet.
///
/// Mirrors [`crate::trust_ir_body::LoweringWitness`] onto the wire.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustVcNativeTrustIrLoweringWitness {
    /// No independent re-check of the lowering exists.
    None,
}

/// Which semantics one obligation's answer is about.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrBodyReading {
    /// The module as written; trust-ir's pinned interpreter executes it unchanged.
    PinnedInterpreter,
    /// An `Inst::Undef` reached on the way to the site was read as a fresh
    /// unconstrained value; see
    /// [`TrustVcNativeTrustIrDischargeAnswer::havoc_instantiation_note`].
    HavocInstantiatedUndef,
}

impl From<BodyReading> for TrustVcNativeTrustIrBodyReading {
    fn from(value: BodyReading) -> Self {
        match value {
            BodyReading::PinnedInterpreter => Self::PinnedInterpreter,
            BodyReading::HavocInstantiatedUndef => Self::HavocInstantiatedUndef,
        }
    }
}

/// What came of one cited obligation on the advisory body lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrAdvisoryOutcome {
    /// The site holds under its premises, per the solver, with the premises
    /// witnessed satisfiable by interpreter replay. ADVISORY.
    DischargedAdvisory,
    /// A solver counterexample that replays as a failing site.
    Refuted,
    /// A solver counterexample that fails the site, but where an earlier
    /// (deliberately not assumed) `Assert` fails first.
    RefutedIgnoringPriorAsserts,
    /// The solver did not decide it.
    Unknown,
    /// The lane declined the function, the site, or the obligation kind. The
    /// reason is on [`TrustVcNativeTrustIrDischargeObligation::detail`].
    NotAnswerable,
    /// DECODED from the wire: whatever outcome the payload declared, nothing in
    /// this process judged it, and the wire carries no evidence to re-check
    /// (see [`TrustVcNativeTrustIrVerdict::NotJudged`]). Never produced in
    /// process.
    NotJudged,
}

/// One cited obligation's advisory answer.
///
/// DECODED, its outcome is always
/// [`TrustVcNativeTrustIrAdvisoryOutcome::NotJudged`]: the wire carries a
/// label with no evidence behind it, and this type — not the report that may
/// contain it — erases it, so no decode path can read one back (a standalone
/// [`TrustVcNativeTrustIrDischargeAnswer`] decoded with every outcome edited to
/// `refuted` used to keep `Refuted`, readable through
/// [`Self::outcome`]). Only an answer produced in process carries outcomes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "WireDischargeObligation")]
#[must_use]
pub struct TrustVcNativeTrustIrDischargeObligation {
    obligation_id: u32,
    outcome: TrustVcNativeTrustIrAdvisoryOutcome,
    reading: TrustVcNativeTrustIrBodyReading,
    /// Why, for every outcome that has a why. Never a counterexample: witness
    /// bindings stay in the in-process report and out of the wire report.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    detail: Option<String>,
}

/// Deserialization mirror of [`TrustVcNativeTrustIrDischargeObligation`]. The
/// outcome must be present and well-formed, and is never read.
#[derive(Deserialize)]
struct WireDischargeObligation {
    obligation_id: u32,
    #[serde(rename = "outcome")]
    _declared_outcome: TrustVcNativeTrustIrAdvisoryOutcome,
    reading: TrustVcNativeTrustIrBodyReading,
    #[serde(default)]
    detail: Option<String>,
}

impl From<WireDischargeObligation> for TrustVcNativeTrustIrDischargeObligation {
    fn from(wire: WireDischargeObligation) -> Self {
        Self {
            obligation_id: wire.obligation_id,
            outcome: TrustVcNativeTrustIrAdvisoryOutcome::NotJudged,
            reading: wire.reading,
            detail: wire.detail,
        }
    }
}

impl TrustVcNativeTrustIrDischargeObligation {
    /// Return the TrustIr proof-obligation id.
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }

    /// Return what came of this obligation.
    pub const fn outcome(&self) -> TrustVcNativeTrustIrAdvisoryOutcome {
        self.outcome
    }

    /// Return which semantics this answer is about.
    pub const fn reading(&self) -> TrustVcNativeTrustIrBodyReading {
        self.reading
    }

    /// Return the refusal or unknown reason, when there is one.
    pub fn detail(&self) -> Option<&str> {
        self.detail.as_deref()
    }
}

/// Producer claims the advisory lane saw and deliberately did not use as facts.
///
/// This is the report's own record that NO STATUS WAS WRITTEN BACK: an
/// obligation whose `statuses` flag is set arrived already labelled, and the
/// lane answered it from the body anyway.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrDischargeIgnoredInputs {
    /// Some reported obligation carried a status other than `Pending`.
    pub statuses: bool,
    /// The module carried proof certificates.
    pub certificates: bool,
    /// Some reported obligation carried a formula payload.
    pub formulas: bool,
    /// The function or one of its nodes carried proof annotations.
    pub annotations: bool,
    /// The function summary carried `requires` clauses.
    pub summary_requires: bool,
}

/// One proof certificate accepted from a native TrustIr TrustVc request.
///
/// Decoding re-derives `release_admission` from the decoded binding (see
/// [`TrustVcNativeTrustIrCertificateAdmission`]): the identity checks are
/// re-run over the payload's own fields and its coverage is never judged, so
/// a decoded evidence item is never admissible and never yields an accepted
/// artifact, whatever its `release_admission` says.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "WireCertificateEvidence")]
#[must_use]
pub struct TrustVcNativeTrustIrCertificateEvidence {
    obligation_id: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    assertion_id: Option<u32>,
    /// The INDEPENDENT numeric rendering of the same assertion identity — the
    /// `assertion_id` of the `Assertion` replay atom that the request citing
    /// this certificate carries for its obligation, not the compiler-fact side
    /// table `assertion_id` above. The request digest (`request_digest`) covers
    /// it.
    ///
    /// With both fields taken from the ONE compiler-fact field,
    /// `TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch` would
    /// compare a value against itself. The artifact is stamped only when THIS
    /// rendering agrees, so that check compares two independently sourced
    /// values and fires even with the bundle-level gates
    /// (`native_assertion_id::validate_request_assertion_atoms`) neutralized.
    /// `None` means the citing request carried no single atom stating the id,
    /// and then the row publishes NO assertion id at all. See
    /// [`crate::native_assertion_id::AssertionIdCorroboration`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    independent_assertion_id: Option<u32>,
    #[serde(alias = "tmir_module_digest")]
    trust_ir_module_digest: String,
    #[serde(default)]
    request_digest: String,
    obligation_kind: TrustVcNativeTrustIrObligationKind,
    obligation_status: TrustVcNativeArtifactObligationStatus,
    description: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    formula_schema: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    formula_sort: Option<String>,
    prover: String,
    evidence_digest: String,
    certificate_digest: String,
    #[serde(default)]
    suite_identity: TrustVcNativeVerifierSuiteIdentity,
    #[serde(default)]
    solver_identity: TrustVcNativeSolverIdentity,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    replay_metadata: Option<TrustVcNativeTrustIrReplayMetadata>,
    compiler_facts_binding: TrustVcNativeCompilerFactsBinding,
    evidence_kind: TrustVcNativeTrustIrEvidenceKind,
    trusted: bool,
    #[serde(default)]
    release_admission: TrustVcNativeTrustIrCertificateAdmission,
}

/// Deserialization mirror of [`TrustVcNativeTrustIrCertificateEvidence`].
#[derive(Deserialize)]
struct WireCertificateEvidence {
    obligation_id: u32,
    #[serde(default)]
    assertion_id: Option<u32>,
    #[serde(default)]
    independent_assertion_id: Option<u32>,
    #[serde(alias = "tmir_module_digest")]
    trust_ir_module_digest: String,
    #[serde(default)]
    request_digest: String,
    obligation_kind: TrustVcNativeTrustIrObligationKind,
    obligation_status: TrustVcNativeArtifactObligationStatus,
    description: String,
    #[serde(default)]
    formula_schema: Option<String>,
    #[serde(default)]
    formula_sort: Option<String>,
    prover: String,
    evidence_digest: String,
    certificate_digest: String,
    #[serde(default)]
    suite_identity: TrustVcNativeVerifierSuiteIdentity,
    #[serde(default)]
    solver_identity: TrustVcNativeSolverIdentity,
    #[serde(default)]
    replay_metadata: Option<TrustVcNativeTrustIrReplayMetadata>,
    compiler_facts_binding: TrustVcNativeCompilerFactsBinding,
    evidence_kind: TrustVcNativeTrustIrEvidenceKind,
    trusted: bool,
    #[serde(default)]
    release_admission: TrustVcNativeTrustIrCertificateAdmission,
}

impl From<WireCertificateEvidence> for TrustVcNativeTrustIrCertificateEvidence {
    fn from(wire: WireCertificateEvidence) -> Self {
        let identity = identity_rejections(IdentityParts {
            assertion_id: wire.assertion_id,
            trust_ir_obligation_id: wire.obligation_id,
            status: wire.obligation_status,
            trusted: wire.trusted,
            suite_identity: &wire.suite_identity,
            solver_identity: &wire.solver_identity,
            compiler_facts_binding: &wire.compiler_facts_binding,
        });
        // `wire.release_admission` has itself been decoded (never admissible);
        // only its coverage refusals are carried over.
        let release_admission = TrustVcNativeTrustIrCertificateAdmission::decoded(
            identity,
            wire.release_admission.rejection_reasons(),
        );
        Self {
            obligation_id: wire.obligation_id,
            assertion_id: wire.assertion_id,
            independent_assertion_id: wire.independent_assertion_id,
            trust_ir_module_digest: wire.trust_ir_module_digest,
            request_digest: wire.request_digest,
            obligation_kind: wire.obligation_kind,
            obligation_status: wire.obligation_status,
            description: wire.description,
            formula_schema: wire.formula_schema,
            formula_sort: wire.formula_sort,
            prover: wire.prover,
            evidence_digest: wire.evidence_digest,
            certificate_digest: wire.certificate_digest,
            suite_identity: wire.suite_identity,
            solver_identity: wire.solver_identity,
            replay_metadata: wire.replay_metadata,
            compiler_facts_binding: wire.compiler_facts_binding,
            evidence_kind: wire.evidence_kind,
            trusted: wire.trusted,
            release_admission,
        }
    }
}

impl TrustVcNativeTrustIrCertificateEvidence {
    /// Return the TrustIr proof-obligation id.
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }

    /// Return the native frontend assertion id carried by TrustIr, if present.
    pub const fn native_assertion_id(&self) -> Option<u32> {
        self.assertion_id
    }

    /// Return the assertion id as the citing request's `Assertion` replay atom
    /// renders it, if the request carried exactly one such atom stating it.
    ///
    /// This is the value an artifact is stamped from (see
    /// [`Self::admit_native_proof_artifact`]); [`Self::native_assertion_id`] is
    /// the compiler-fact side table's rendering of the same identity.
    pub const fn independent_assertion_id(&self) -> Option<u32> {
        self.independent_assertion_id
    }

    /// Return the TrustIr module digest bound to this certificate evidence.
    pub fn trust_ir_module_digest(&self) -> &str {
        &self.trust_ir_module_digest
    }

    /// Return the stable native request digest covering the replay assertion
    /// formula used by this certificate import.
    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    /// Return the TrustIr obligation kind label.
    pub fn obligation_kind(&self) -> &str {
        self.obligation_kind.label()
    }

    /// Return the typed TrustIr obligation kind.
    pub const fn typed_obligation_kind(&self) -> TrustVcNativeTrustIrObligationKind {
        self.obligation_kind
    }

    /// Return the TrustIr obligation status label.
    pub fn obligation_status(&self) -> &str {
        self.obligation_status.label()
    }

    /// Return the typed TrustIr obligation status.
    pub const fn typed_obligation_status(&self) -> TrustVcNativeArtifactObligationStatus {
        self.obligation_status
    }

    /// Return the TrustIr obligation description.
    pub fn description(&self) -> &str {
        &self.description
    }

    /// Return the formula schema carried by the obligation, if any.
    pub fn formula_schema(&self) -> Option<&str> {
        self.formula_schema.as_deref()
    }

    /// Return the formula sort carried by the obligation, if any.
    pub fn formula_sort(&self) -> Option<&str> {
        self.formula_sort.as_deref()
    }

    /// Return the prover label from the proof certificate.
    pub fn prover(&self) -> &str {
        &self.prover
    }

    /// Return the TrustIr evidence digest referenced by the request.
    pub fn evidence_digest(&self) -> &str {
        &self.evidence_digest
    }

    /// Return the full TrustIr proof-certificate digest.
    pub fn certificate_digest(&self) -> &str {
        &self.certificate_digest
    }

    /// Return the typed verifier-suite identity for this native artifact.
    pub const fn suite_identity(&self) -> &TrustVcNativeVerifierSuiteIdentity {
        &self.suite_identity
    }

    /// Return the solver/prover identity for this native artifact.
    pub const fn solver_identity(&self) -> &TrustVcNativeSolverIdentity {
        &self.solver_identity
    }

    /// Return explicit replay/check metadata bound into this native report.
    pub const fn replay_metadata(&self) -> Option<&TrustVcNativeTrustIrReplayMetadata> {
        self.replay_metadata.as_ref()
    }

    /// Return the compiler-fact source binding for this obligation.
    pub const fn compiler_facts_binding(&self) -> &TrustVcNativeCompilerFactsBinding {
        &self.compiler_facts_binding
    }

    /// Return the native evidence payload class.
    pub const fn evidence_kind(&self) -> TrustVcNativeTrustIrEvidenceKind {
        self.evidence_kind
    }

    /// Return whether the imported certificate is explicitly trusted evidence.
    pub const fn trusted(&self) -> bool {
        self.trusted
    }

    /// Return release-grade admission details for this native TrustIr certificate.
    pub const fn release_admission(&self) -> &TrustVcNativeTrustIrCertificateAdmission {
        &self.release_admission
    }

    /// Admit this native certificate evidence with the assertion id carried by TrustIr.
    ///
    /// If the source bundle does not carry `NativeObligationSource.assertion_id`
    /// for this obligation, the returned proof artifact is rejected fail-closed
    /// with `MissingAssertionId`.
    ///
    /// The certificate's COVERAGE judgement travels with it (see
    /// [`Self::admit_proof_artifact`]): an artifact is never accepted for a
    /// certificate whose release admission did not establish `Unbounded`
    /// coverage.
    ///
    /// ROUND 9, THE BLOCKER — WHAT THE LANE PUBLISHES IS ALSO TWO RENDERINGS.
    /// This row carries the assertion identity THREE times: the compiler-fact
    /// side table's `assertion_id`, the formula payload's own
    /// `independent_assertion_id`, and the republished
    /// `compiler_facts_binding.assertion_id`. Round 8 made the stamp come from
    /// the second instead of the first, so that
    /// `TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch` stopped
    /// comparing one field against itself — and left the row's own `assertion_id`
    /// compared against nothing. A consumer deserializing a trust-runner report
    /// could then hold ONE JSON object that reports assertion 1, grades assertion
    /// 1 admissible, and mints an artifact stamped assertion 0 (probe R9-P9).
    ///
    /// The rule now has no preferred rendering to attack. What is published is
    /// the id this row REPORTS — the one its own `release_admission` graded and
    /// the one a reader of the report sees — and it is published only when every
    /// other rendering the row carries agrees with it. A disagreement publishes
    /// NO id, with `AssertionIdRenderingsDisagree` beside the resulting
    /// `MissingAssertionId`; a row that reports no id publishes none, and no
    /// other rendering is promoted into one. Fail closed rather than pick a
    /// winner — picking a winner is what round 8 did, and it is what round 9
    /// exploited.
    ///
    /// Agreement among renderings is only worth something when at least one of
    /// them is INDEPENDENT. Where [`Self::independent_assertion_id`] is `None`,
    /// the "renderings" are `assertion_id` and
    /// `compiler_facts_binding.assertion_id` — TWO COPIES OF ONE FIELD, which
    /// always agree. A row that carries no independent rendering (the citing
    /// request's `Assertion` replay atom) therefore publishes NO assertion id,
    /// whatever it reports. See [`crate::native_assertion_id`].
    pub fn admit_native_proof_artifact(&self) -> TrustVcNativeProofArtifact {
        if self.assertion_id.is_none() {
            // The row reports NO assertion id — either the bundle carried none,
            // or the export seam declined to license one (nothing corroborated
            // it, or the number is shared by two identities). The other
            // renderings may still carry a value; they are NOT promoted into one,
            // because the absence here is a decision, not an omission. Nothing is
            // published, which is `MissingAssertionId`.
            return TrustVcNativeProofArtifact::new(self.artifact_input(String::new()));
        }
        let renderings = self.assertion_id_renderings();
        // ROUND 11. Without an independent rendering there is nothing here but
        // copies of the compiler fact, and agreement among copies is not
        // corroboration. Publish no id.
        //
        // ROUND 12 CORRECTS WHAT THIS COMMENT USED TO CLAIM. It said the
        // renderings are "still attached, so a reader of the artifact can see
        // what the row held". They are not: `TrustVcNativeProofArtifactInput`
        // carries them, `corroborated_assertion_id` consumes them at
        // construction, and `TrustVcNativeProofArtifact` has no renderings
        // field — a reader of the published artifact sees `assertion_id: ""`
        // and `MissingAssertionId`, nothing more. The renderings are still
        // passed because they DECIDE the admission; where a reader sees what
        // the row held is the evidence row in the report, which serializes
        // `assertion_id`, `independent_assertion_id` and
        // `compiler_facts_binding`.
        //
        // Every rendering this row carries must agree with the one it REPORTS.
        // Where they do not, publish nothing at all rather than pick a winner —
        // picking a winner is what round 8 did, and it is what round 9 exploited.
        // Both rules live in `licensed_assertion_id`, which the caller-named
        // path (`admit_proof_artifact`) goes through too.
        let stamped = self
            .licensed_assertion_id()
            .map(|licensed| licensed.to_string())
            .unwrap_or_default();
        self.artifact_with_renderings(stamped, renderings)
    }

    /// THE ONE ID THIS ROW LICENSES, if any: what
    /// [`Self::admit_native_proof_artifact`] stamps, and the only id
    /// [`Self::admit_proof_artifact`] accepts.
    ///
    /// `Some` only when the row REPORTS an id (the export seam licensed it: the
    /// citing request carries exactly one `Assertion` atom for the obligation,
    /// its id equals the compiler fact's, and no other obligation in the bundle
    /// carries the number under another identity), records the atom's id
    /// beside it as [`Self::independent_assertion_id`], carries the
    /// compiler-fact binding's copy, and every one of those renderings says the
    /// same number. A row missing any of them licenses nothing.
    fn licensed_assertion_id(&self) -> Option<u32> {
        let reported = self.assertion_id?;
        let independent = self.independent_assertion_id?;
        let binding = self.compiler_facts_binding.assertion_id()?;
        match crate::native_artifact::corroborated_assertion_id(&self.assertion_id_renderings()) {
            Ok(Some(corroborated))
                if corroborated == reported && independent == reported && binding == reported =>
            {
                Some(reported)
            }
            _ => None,
        }
    }

    /// The artifact for this row stamped `assertion_id`, carrying every
    /// rendering the row holds so the admission cross-checks the stamp against
    /// each of them.
    fn artifact_with_renderings(
        &self,
        assertion_id: String,
        renderings: Vec<TrustVcNativeAssertionIdRendering>,
    ) -> TrustVcNativeProofArtifact {
        let mut input = self.artifact_input(assertion_id);
        for rendering in renderings {
            input = input.with_assertion_id_rendering(rendering.source, rendering.value);
        }
        TrustVcNativeProofArtifact::new(input)
    }

    /// Every numeric rendering of this row's assertion identity, labelled,
    /// INCLUDING the one it reports.
    ///
    /// Two of the three are independent of each other by provenance: the
    /// compiler-fact side table and the citing request's replay atom. The
    /// third (`compiler_facts_binding.assertion_id`) is the compiler-fact
    /// rendering republished on the binding — it is included because an editor
    /// who moves one of the two copies of the compiler-fact rendering and not
    /// the other is exactly as caught as one who moves the payload's. The
    /// reported one is included so the admission's check is TOTAL: what is
    /// stamped is compared against every rendering, itself included.
    fn assertion_id_renderings(&self) -> Vec<TrustVcNativeAssertionIdRendering> {
        [
            (
                "row `assertion_id` (compiler-fact side table)",
                self.assertion_id,
            ),
            (
                "row `independent_assertion_id` (citing request's `Assertion` replay atom `assertion_id`)",
                self.independent_assertion_id,
            ),
            (
                "row `compiler_facts_binding.assertion_id`",
                self.compiler_facts_binding.assertion_id(),
            ),
        ]
        .into_iter()
        .filter_map(|(source, value)| {
            value.map(|value| TrustVcNativeAssertionIdRendering::new(source, value))
        })
        .collect()
    }

    /// The artifact input for this row, bound to one stamped assertion id.
    fn artifact_input(&self, assertion_id: String) -> TrustVcNativeProofArtifactInput {
        TrustVcNativeProofArtifactInput::new(
            assertion_id,
            self.obligation_id,
            self.evidence_digest.clone(),
            self.certificate_digest.clone(),
        )
        .with_trust_ir_module_digest(self.trust_ir_module_digest.clone())
        .with_request_digest(self.request_digest.clone())
        .with_suite_identity(self.suite_identity.clone())
        .with_solver_identity(self.solver_identity.clone())
        .with_obligation_status(self.obligation_status)
        .with_trusted(self.trusted)
        .with_compiler_facts_binding(self.compiler_facts_binding.clone())
        .with_coverage(self.release_admission.artifact_coverage())
    }

    /// Bind this native certificate evidence to an assertion id the CALLER
    /// names, checked against the one id the row licenses.
    ///
    /// ROUND 13. A caller-named id goes through the same rule as the evidence
    /// row: the id must be the one the citing request's single `Assertion`
    /// replay atom states, equal to the compiler fact's, and unambiguous in the
    /// bundle. This method used to compare it with the compiler fact alone, so
    /// a row the export seam had refused `MissingAssertionId` (no atom, two
    /// atoms, a number another obligation shares, an id only a payload renders)
    /// still minted an accepted artifact for whatever id the caller named from
    /// its own side table. A side table cannot license what the bundle does
    /// not. So:
    ///
    /// * the canonical decimal spelling of the id the row licenses returns
    ///   exactly [`Self::admit_native_proof_artifact`];
    /// * any id on a row that licenses NONE returns that same artifact, which
    ///   publishes no id: `MissingAssertionId`, whatever the caller named;
    /// * another spelling of the licensed number (`"01"`, `"+1"`) publishes no
    ///   id either, rather than stamp a second string for one assertion;
    /// * another number is stamped as named and refused
    ///   `CompilerFactAssertionIdMismatch`: a licensed row's compiler-fact
    ///   binding always carries the licensed number.
    ///
    /// Every coverage refusal in [`Self::release_admission`] — bounded,
    /// undetermined, established only for a sibling certificate, or refused
    /// for the bundle — is a rejection of the
    /// returned artifact under the same name, and an admission that never
    /// established coverage (a default or pre-field payload) rejects it as
    /// [`crate::TrustVcNativeArtifactRejection::CertificateCoverageNotJudged`].
    /// The artifact path used to skip coverage entirely, so a certificate its
    /// own release admission refused still yielded an `accepted` artifact.
    pub fn admit_proof_artifact(
        &self,
        assertion_id: impl Into<String>,
    ) -> TrustVcNativeProofArtifact {
        let named = assertion_id.into();
        let Some(licensed) = self.licensed_assertion_id() else {
            // The row licenses no id, so none is published, whatever the
            // caller named.
            return self.admit_native_proof_artifact();
        };
        if named == licensed.to_string() {
            return self.admit_native_proof_artifact();
        }
        if named.parse::<u32>() == Ok(licensed) {
            // The licensed number, spelled another way: publish none.
            return self.artifact_with_renderings(String::new(), self.assertion_id_renderings());
        }
        // Another number. The binding carries `licensed`, so the admission
        // refuses this stamp as `CompilerFactAssertionIdMismatch`.
        TrustVcNativeProofArtifact::new(self.artifact_input(named))
    }
}

/// Typed TrustIr proof-obligation kind exposed by TrustVc native evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrObligationKind {
    Precondition,
    Postcondition,
    LoopInvariant,
    TypeInvariant,
    RefinementType,
    TranslationValidation,
    MemorySafety,
    PanicFreedom,
}

impl TrustVcNativeTrustIrObligationKind {
    /// Return the stable wire label for this obligation kind.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Precondition => "precondition",
            Self::Postcondition => "postcondition",
            Self::LoopInvariant => "loop_invariant",
            Self::TypeInvariant => "type_invariant",
            Self::RefinementType => "refinement_type",
            Self::TranslationValidation => "translation_validation",
            Self::MemorySafety => "memory_safety",
            Self::PanicFreedom => "panic_freedom",
        }
    }
}

/// Native TrustIr proof-certificate evidence payload class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrEvidenceKind {
    SmtProof,
    LeanProof,
    KaniHarness,
    GammaCrownBound,
    TranslationValidation,
    /// A kernel-recheckable CIC proof term (`ProofEvidence::CleanCic`).
    ///
    /// Distinct from `Trusted` DELIBERATELY, and the distinction is the point:
    /// `Trusted` is a manual audit justification taken on faith, while this is
    /// backed by a term a kernel can re-check. Collapsing the two — as this
    /// enum did before, mapping CleanCic onto `Trusted` as an "unmapped strong
    /// evidence" placeholder — made the report UNDERSTATE its own evidence and
    /// made `trusted()` answer true for a kernel-checked proof.
    CleanCic,
    Trusted,
}

/// Replay/check metadata exposed directly in native TrustIr certificate reports.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrReplayMetadata {
    source: TrustVcNativeTrustIrReplayMetadataSource,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    lineage_node_id: Option<u32>,
    engine: String,
    invocation: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    transcript_digest: Option<String>,
}

impl TrustVcNativeTrustIrReplayMetadata {
    fn from_lineage_node(node: &ProofLineageNode) -> Option<Self> {
        let replay = node.replay.as_ref()?;
        Some(Self::from_parts(
            TrustVcNativeTrustIrReplayMetadataSource::LineageNode,
            Some(node.id.index()),
            replay,
        ))
    }

    fn from_request_provenance(provenance: &NativeRequestProvenance) -> Option<Self> {
        let replay = provenance.replay.as_ref()?;
        Some(Self::from_parts(
            TrustVcNativeTrustIrReplayMetadataSource::RequestProvenance,
            None,
            replay,
        ))
    }

    fn from_parts(
        source: TrustVcNativeTrustIrReplayMetadataSource,
        lineage_node_id: Option<u32>,
        replay: &trust_ir::ProofReplayIdentity,
    ) -> Self {
        Self {
            source,
            lineage_node_id,
            engine: replay.engine.clone(),
            invocation: replay.invocation.clone(),
            transcript_digest: replay.transcript_digest.map(|digest| digest.to_string()),
        }
    }

    /// Return where TrustVc found this replay/check metadata.
    pub const fn source(&self) -> TrustVcNativeTrustIrReplayMetadataSource {
        self.source
    }

    /// Return the proof-lineage node id when metadata came from lineage.
    pub const fn lineage_node_id(&self) -> Option<u32> {
        self.lineage_node_id
    }

    /// Return the replay/check engine name.
    pub fn engine(&self) -> &str {
        &self.engine
    }

    /// Return the replay/check invocation.
    pub fn invocation(&self) -> &str {
        &self.invocation
    }

    /// Return the transcript digest that binds replay output, when supplied.
    pub fn transcript_digest(&self) -> Option<&str> {
        self.transcript_digest.as_deref()
    }
}

/// Source of replay/check metadata in a native TrustIr certificate report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrReplayMetadataSource {
    LineageNode,
    RequestProvenance,
}

/// Release-admission verdict for native TrustIr certificate imports.
///
/// # Decoding never yields an admission
///
/// Admission is a JUDGEMENT made against the bundle a certificate cites: its
/// coverage is derived by trust-ir-build's `coverage_establishment_report`
/// over that bundle (basis K, see [`crate::native_coverage`]), which no
/// serialized admission, evidence item or report carries. Deserializing one
/// therefore re-derives what the payload's own fields can support and never
/// reads the wire's verdict: the status is `Rejected`, `coverage_established`
/// is `false`, the basis and detail are dropped, the payload's coverage
/// refusals are kept (a refusal only rejects more), and a payload that names
/// none is refused as
/// [`TrustVcNativeTrustIrCertificateRejection::CertificateCoverageNotJudged`].
/// It used to be a plain derive, so `{"status": "admissible",
/// "coverage_established": true}` decoded as an admissible, established
/// certificate and its artifact was accepted.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "WireCertificateAdmission")]
#[must_use]
pub struct TrustVcNativeTrustIrCertificateAdmission {
    #[serde(default)]
    status: TrustVcNativeTrustIrCertificateAdmissionStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    rejection_reasons: Vec<TrustVcNativeTrustIrCertificateRejection>,
    /// The certificate's coverage was ESTABLISHED as `Unbounded` against the
    /// bundle it cites — exactly when `coverage_basis` is `Some`.
    ///
    /// A positive fact of its own, not "no coverage reason in
    /// `rejection_reasons`": a payload that predates this field (or any
    /// default-constructed admission) carries no reasons at all, and reading
    /// that silence as established coverage is exactly the fail-open the
    /// native-artifact path had. Defaults to `false`.
    #[serde(default)]
    coverage_established: bool,
    /// WHAT established the coverage: the kernel replay of this very
    /// certificate (basis K). `None` unless established; never decoded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    coverage_basis: Option<TrustVcNativeCoverageBasis>,
    /// trust-ir-build's own words for a coverage refusal (its refusals, or
    /// why nothing was established). For a report reader; never decoded and
    /// never read as evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    coverage_detail: Option<String>,
}

impl Default for TrustVcNativeTrustIrCertificateAdmission {
    fn default() -> Self {
        Self {
            status: TrustVcNativeTrustIrCertificateAdmissionStatus::Unspecified,
            rejection_reasons: Vec::new(),
            coverage_established: false,
            coverage_basis: None,
            coverage_detail: None,
        }
    }
}

/// Deserialization mirror of [`TrustVcNativeTrustIrCertificateAdmission`]:
/// everything a payload may say, none of which is believed (see the type doc).
/// `coverage_basis` and `coverage_detail` are not even read.
#[derive(Deserialize)]
struct WireCertificateAdmission {
    #[serde(default, rename = "status")]
    _status: TrustVcNativeTrustIrCertificateAdmissionStatus,
    #[serde(default)]
    rejection_reasons: Vec<TrustVcNativeTrustIrCertificateRejection>,
    #[serde(default, rename = "coverage_established")]
    _coverage_established: bool,
}

impl From<WireCertificateAdmission> for TrustVcNativeTrustIrCertificateAdmission {
    fn from(wire: WireCertificateAdmission) -> Self {
        // A bare admission has no binding to re-derive from: keep every
        // reason it names, and refuse its coverage as not judged.
        Self::decoded(wire.rejection_reasons, &[])
    }
}

impl TrustVcNativeTrustIrCertificateAdmission {
    /// The admission a DECODED payload can support: `identity` (the reasons
    /// re-derived from the payload's own binding, or a bare admission's own
    /// list), plus the payload's coverage refusals `wire`, plus
    /// `CertificateCoverageNotJudged` when no coverage refusal is left — so it
    /// is never admissible and never establishes coverage. A legacy coverage
    /// label decodes as `CertificateCoverageNotJudged` (see the rejection
    /// enum); each reason is kept once.
    fn decoded(
        identity: Vec<TrustVcNativeTrustIrCertificateRejection>,
        wire: &[TrustVcNativeTrustIrCertificateRejection],
    ) -> Self {
        let mut rejection_reasons = Vec::new();
        for reason in identity {
            if !rejection_reasons.contains(&reason) {
                rejection_reasons.push(reason);
            }
        }
        for reason in wire {
            if reason.is_coverage_refusal() && !rejection_reasons.contains(reason) {
                rejection_reasons.push(*reason);
            }
        }
        if !rejection_reasons
            .iter()
            .any(|reason| reason.is_coverage_refusal())
        {
            rejection_reasons
                .push(TrustVcNativeTrustIrCertificateRejection::CertificateCoverageNotJudged);
        }
        Self {
            status: TrustVcNativeTrustIrCertificateAdmissionStatus::Rejected,
            rejection_reasons,
            coverage_established: false,
            coverage_basis: None,
            coverage_detail: None,
        }
    }

    fn from_native_parts(parts: AdmissionParts<'_>) -> Self {
        let AdmissionParts {
            assertion_id,
            trust_ir_obligation_id,
            status,
            certificate,
            suite_identity,
            solver_identity,
            compiler_facts_binding,
            coverage,
        } = parts;
        let mut rejection_reasons = identity_rejections(IdentityParts {
            assertion_id,
            trust_ir_obligation_id,
            status,
            trusted: certificate.uses_trusted_evidence(),
            suite_identity,
            solver_identity,
            compiler_facts_binding,
        });
        // The certificate's OWN coverage verdict, by its lineage reference
        // (which excludes `assurance`: the in-module row is never read).
        let judgement = coverage.judge(&certificate.lineage_ref());
        let coverage_established = judgement.basis.is_some() && judgement.rejections.is_empty();
        rejection_reasons.extend(judgement.rejections);

        Self {
            status: if rejection_reasons.is_empty() {
                TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
            } else {
                TrustVcNativeTrustIrCertificateAdmissionStatus::Rejected
            },
            rejection_reasons,
            coverage_established,
            coverage_basis: judgement.basis.filter(|_| coverage_established),
            coverage_detail: judgement.detail,
        }
    }
}

/// The release-admission checks that read only a certificate's own binding —
/// every check but coverage. The bundle path runs them beside the coverage
/// judgement ([`crate::native_coverage`]); decoding re-runs them over the
/// decoded fields.
struct IdentityParts<'a> {
    assertion_id: Option<u32>,
    trust_ir_obligation_id: u32,
    status: TrustVcNativeArtifactObligationStatus,
    trusted: bool,
    suite_identity: &'a TrustVcNativeVerifierSuiteIdentity,
    solver_identity: &'a TrustVcNativeSolverIdentity,
    compiler_facts_binding: &'a TrustVcNativeCompilerFactsBinding,
}

fn identity_rejections(parts: IdentityParts<'_>) -> Vec<TrustVcNativeTrustIrCertificateRejection> {
    let IdentityParts {
        assertion_id,
        trust_ir_obligation_id,
        status,
        trusted,
        suite_identity,
        solver_identity,
        compiler_facts_binding,
    } = parts;
    {
        let mut rejection_reasons = Vec::new();
        if assertion_id.is_none() {
            rejection_reasons.push(TrustVcNativeTrustIrCertificateRejection::MissingAssertionId);
        }
        if !suite_identity.is_reported() {
            rejection_reasons.push(TrustVcNativeTrustIrCertificateRejection::MissingSuiteIdentity);
        }
        if !solver_identity.has_reported_solver_identities() {
            rejection_reasons.push(TrustVcNativeTrustIrCertificateRejection::MissingSolverIdentity);
        }
        if solver_identity
            .transcript_digest()
            .is_none_or(|value| value.is_empty())
        {
            rejection_reasons
                .push(TrustVcNativeTrustIrCertificateRejection::MissingReplayTranscriptDigest);
        }
        if compiler_facts_binding.compiler_facts_digest().is_empty()
            || compiler_facts_binding.obligation_source_digest().is_empty()
            || compiler_facts_binding.obligation_id() != trust_ir_obligation_id
        {
            rejection_reasons
                .push(TrustVcNativeTrustIrCertificateRejection::MissingCompilerFactSource);
        }
        if compiler_facts_binding.fact_refs().is_empty() {
            rejection_reasons
                .push(TrustVcNativeTrustIrCertificateRejection::MissingCompilerFactReferences);
        }
        match status {
            // `Certified` is judged on the replay, not on the label: it is
            // admissible here exactly like `Discharged`, and release admission
            // still needs this certificate's OWN kernel replay to establish
            // its coverage (basis K) — which is what `Certified` asserts.
            TrustVcNativeArtifactObligationStatus::Discharged
            | TrustVcNativeArtifactObligationStatus::Certified => {}
            TrustVcNativeArtifactObligationStatus::Pending
            | TrustVcNativeArtifactObligationStatus::Unspecified => {
                rejection_reasons.push(TrustVcNativeTrustIrCertificateRejection::ObligationPending);
            }
            TrustVcNativeArtifactObligationStatus::Failed => {
                rejection_reasons.push(TrustVcNativeTrustIrCertificateRejection::ObligationFailed);
            }
            TrustVcNativeArtifactObligationStatus::Trusted => {
                rejection_reasons.push(TrustVcNativeTrustIrCertificateRejection::ObligationTrusted);
            }
        }
        if trusted {
            rejection_reasons
                .push(TrustVcNativeTrustIrCertificateRejection::CertificateUsesTrustedEvidence);
        }
        rejection_reasons
    }
}

impl TrustVcNativeTrustIrCertificateAdmission {
    /// Whether the certificate's coverage was established as `Unbounded`
    /// against the bundle it cites — by trust-ir-build's
    /// `coverage_establishment_report` on basis K (the kernel replay of this
    /// very certificate), see the crate README.
    ///
    /// `false` for an admission that never judged coverage, including one
    /// deserialized from a payload without the field.
    pub const fn coverage_established(&self) -> bool {
        self.coverage_established
    }

    /// What established the coverage, when it was: the kernel replay of this
    /// very certificate and the classified family of the replayed claim.
    /// `None` for every admission that did not establish coverage, and for
    /// every decoded one.
    pub const fn coverage_basis(&self) -> Option<&TrustVcNativeCoverageBasis> {
        self.coverage_basis.as_ref()
    }

    /// trust-ir-build's own words for why coverage was NOT established (its
    /// refusals, or its undetermined reason), for a report reader. `None`
    /// when coverage was established, and for every decoded admission.
    pub fn coverage_detail(&self) -> Option<&str> {
        self.coverage_detail.as_deref()
    }

    /// The coverage judgement a native proof artifact built from this
    /// certificate must carry into its OWN admission.
    ///
    /// The artifact path used to rebuild admission from the obligation status,
    /// trust flag and identities alone, so a certificate refused here for its
    /// coverage still produced an artifact whose admission was `accepted`.
    /// Every coverage refusal is carried over by name; an established
    /// judgement carries its BASIS (the artifact fingerprint binds it); an
    /// admission that never established coverage and names no refusal (a
    /// default or decoded payload) carries
    /// [`crate::TrustVcNativeArtifactRejection::CertificateCoverageNotJudged`].
    pub(crate) fn artifact_coverage(&self) -> NativeArtifactCoverage {
        let refusals = self
            .rejection_reasons
            .iter()
            .filter_map(|reason| reason.coverage_artifact_rejection())
            .collect::<Vec<_>>();
        match &self.coverage_basis {
            Some(basis) if self.coverage_established && refusals.is_empty() => {
                NativeArtifactCoverage::Established(basis.clone())
            }
            _ if refusals.is_empty() => NativeArtifactCoverage::NotJudged,
            _ => NativeArtifactCoverage::Refused(refusals),
        }
    }

    /// Return the release-admission status.
    pub const fn status(&self) -> TrustVcNativeTrustIrCertificateAdmissionStatus {
        self.status
    }

    /// Return whether this native TrustIr certificate is admissible for release gates.
    pub const fn is_admissible(&self) -> bool {
        matches!(
            self.status,
            TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
        )
    }

    /// Return reasons this certificate is not release-admissible.
    pub fn rejection_reasons(&self) -> &[TrustVcNativeTrustIrCertificateRejection] {
        &self.rejection_reasons
    }
}

/// Release-admission status for native TrustIr certificate imports.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrCertificateAdmissionStatus {
    /// Missing admission status from an older serialized payload.
    #[default]
    Unspecified,
    /// The imported native TrustIr certificate satisfies TrustVc release-gate policy.
    Admissible,
    /// The imported native TrustIr certificate is present but not release-admissible.
    Rejected,
}

/// Reasons an imported native TrustIr certificate is not release-admissible.
///
/// # Legacy coverage labels decode as `certificate_coverage_not_judged`
///
/// Before coverage was derived by the consumer (basis K), admission judged a
/// producer-written `ProofCertificate::assurance` row and could refuse it as
/// `certificate_coverage_unrecorded`, `_request_unknown`,
/// `_obligation_not_requested`, `_bound_mismatch`, `_contested` or
/// `_not_established_for_module`. Those judgements are no longer made and the
/// variants are gone; their labels still DECODE — as
/// [`Self::CertificateCoverageNotJudged`], which is what a decoded coverage
/// refusal is worth — so a payload written by the previous rule stays
/// readable (and rejected) for one cohort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrCertificateRejection {
    /// The native request lacks a frontend assertion id for artifact binding.
    MissingAssertionId,
    /// The native request lacks a typed verifier-suite identity.
    MissingSuiteIdentity,
    /// The native request lacks typed solver/prover identities.
    MissingSolverIdentity,
    /// The native proof lineage lacks a replay transcript digest.
    MissingReplayTranscriptDigest,
    /// The native request lacks a per-obligation compiler-fact source mapping.
    MissingCompilerFactSource,
    /// The native request lacks typed compiler fact references.
    MissingCompilerFactReferences,
    /// The referenced TrustIr obligation is still pending.
    ObligationPending,
    /// The referenced TrustIr obligation failed upstream.
    ObligationFailed,
    /// The referenced TrustIr obligation is marked trusted rather than discharged.
    ObligationTrusted,
    /// The certificate payload is explicitly trusted evidence.
    CertificateUsesTrustedEvidence,
    /// trust-ir-build ESTABLISHED a coverage bound for this very certificate,
    /// but not `Unbounded`: it did not discharge the obligation for every
    /// input. `CoverageBound` is `#[non_exhaustive]`; anything but `Unbounded`
    /// lands here.
    CertificateCoverageBounded,
    /// trust-ir-build established NO coverage for this certificate: it was not
    /// kernel-replayed (no basis), its replayed claim's family is unclassified,
    /// the build has no kernel, or the report was unchecked. Never read as
    /// `Unbounded`; the in-module `assurance` row is never consulted.
    CertificateCoverageUndetermined,
    /// A SIBLING certificate on the same obligation was kernel-replayed, not
    /// this one. Basis K is per certificate: an SMT or `Trusted` certificate
    /// gains nothing from a `CleanCic` sibling's replay.
    CertificateCoverageBasisNotThisCertificate,
    /// trust-ir-build REFUSED something in the bundle — a producer stated
    /// something false, e.g. an in-module `assurance` row claiming more than
    /// its certificate's derived bound. Fatal for EVERY certificate of the
    /// bundle, whichever certificate the refusal is about; the admission's
    /// `coverage_detail` carries trust-ir-build's own words.
    CertificateCoverageRefused,
    /// No coverage judgement: the admission was DECODED. Coverage is
    /// established only against the bundle the certificate cites, which a
    /// serialized admission, evidence item or report does not carry, so a
    /// decoded admission never establishes it (see
    /// [`TrustVcNativeTrustIrCertificateAdmission`]). The retired coverage
    /// labels decode here too (see the type doc).
    #[serde(
        alias = "certificate_coverage_unrecorded",
        alias = "certificate_coverage_request_unknown",
        alias = "certificate_coverage_obligation_not_requested",
        alias = "certificate_coverage_bound_mismatch",
        alias = "certificate_coverage_contested",
        alias = "certificate_coverage_not_established_for_module"
    )]
    CertificateCoverageNotJudged,
}

impl TrustVcNativeTrustIrCertificateRejection {
    /// Whether this is a COVERAGE refusal (one that travels onto the artifact).
    const fn is_coverage_refusal(self) -> bool {
        self.coverage_artifact_rejection().is_some()
    }

    /// The native-artifact rejection that carries this refusal onto a
    /// [`TrustVcNativeProofArtifact`], when it is a COVERAGE refusal.
    ///
    /// `None` for every other reason: the artifact path re-derives those
    /// (assertion id, identities, compiler facts, obligation status, trusted
    /// payload) from the artifact's own binding. Exhaustive with no wildcard,
    /// so a coverage refusal added above must decide here whether it travels.
    const fn coverage_artifact_rejection(self) -> Option<TrustVcNativeArtifactRejection> {
        match self {
            Self::MissingAssertionId
            | Self::MissingSuiteIdentity
            | Self::MissingSolverIdentity
            | Self::MissingReplayTranscriptDigest
            | Self::MissingCompilerFactSource
            | Self::MissingCompilerFactReferences
            | Self::ObligationPending
            | Self::ObligationFailed
            | Self::ObligationTrusted
            | Self::CertificateUsesTrustedEvidence => None,
            Self::CertificateCoverageBounded => {
                Some(TrustVcNativeArtifactRejection::CertificateCoverageBounded)
            }
            Self::CertificateCoverageUndetermined => {
                Some(TrustVcNativeArtifactRejection::CertificateCoverageUndetermined)
            }
            Self::CertificateCoverageBasisNotThisCertificate => {
                Some(TrustVcNativeArtifactRejection::CertificateCoverageBasisNotThisCertificate)
            }
            Self::CertificateCoverageRefused => {
                Some(TrustVcNativeArtifactRejection::CertificateCoverageRefused)
            }
            Self::CertificateCoverageNotJudged => {
                Some(TrustVcNativeArtifactRejection::CertificateCoverageNotJudged)
            }
        }
    }
}

/// The inputs of [`TrustVcNativeTrustIrCertificateAdmission::from_native_parts`],
/// grouped.
struct AdmissionParts<'a> {
    assertion_id: Option<u32>,
    trust_ir_obligation_id: u32,
    status: TrustVcNativeArtifactObligationStatus,
    certificate: &'a ProofCertificate,
    suite_identity: &'a TrustVcNativeVerifierSuiteIdentity,
    solver_identity: &'a TrustVcNativeSolverIdentity,
    compiler_facts_binding: &'a TrustVcNativeCompilerFactsBinding,
    coverage: &'a CoverageJudge,
}

/// One request of the bundle being consumed, paired with its `stable_digest`
/// RECOMPUTED from the request (never read from a field that merely copies
/// it, such as `NativeEvidenceBundle::request_digest`).
type BundleRequest<'a> = (ProofDigest, &'a NativeVerificationRequest);

impl TrustVcTrustEngine {
    /// Answer one `DischargeProofObligations` request against an in-memory
    /// module, ADVISORY.
    ///
    /// This is the routing the adjudication's TEST 1 asks for: a request that
    /// names a function and cites obligations inside it is handed to the
    /// in-process body lane ([`crate::trust_ir_body`]), each cited obligation
    /// gets that lane's verdict, and an obligation the lane declines comes back
    /// [`TrustVcNativeTrustIrAdvisoryOutcome::NotAnswerable`] naming the
    /// reason. It is called directly by a Trust-side bridge that already holds
    /// the module. (MERGED 2026-09-23: it is NOT the route
    /// [`Self::consume_native_trust_ir_bundle`] takes. At this crate's trust-ir
    /// pin the serialized path is open, and every validated discharge request
    /// in a bundle goes to the [`crate::native_discharge`] lane, whose verdicts
    /// and certificates are its own; this entry stays the advisory in-process
    /// answer.)
    ///
    /// # This answer is advisory, and nothing here can promote it
    ///
    /// No upstream bundle validation runs on this entry — no lineage, no
    /// provenance, no replay identity — and that is sound precisely BECAUSE
    /// the answer is not authority: it mints no `trust_ir::ProofCertificate`,
    /// writes back no `trust_ir::ProofStatus`, produces no
    /// [`crate::TrustVcNativeProofArtifact`] (the returned report's
    /// `proof_evidence` is empty, and that is the only list
    /// [`TrustVcNativeTrustIrRequestReport::admit_native_proof_artifacts`]
    /// reads), and its verdict can never satisfy
    /// [`TrustVcNativeTrustIrVerdict::is_ok`]. See
    /// [`TrustVcNativeTrustIrDischargeAnswer`] for the five structural
    /// properties, each a type rather than a policy.
    ///
    /// # Refusals
    ///
    /// Fail-closed, all four before the lane is entered:
    ///
    /// * a request in any other mode —
    ///   `NativeTrustIrDischargeRequestWrongMode`;
    /// * `function: None` —
    ///   `NativeTrustIrDischargeRequestMissingFunction`. This is the
    ///   load-bearing one: naming a function is what makes obligation scoping
    ///   checkable at all;
    /// * any attached certificate —
    ///   `NativeTrustIrDischargeRequestCarriesCertificate`. A discharge request
    ///   asks trust-vc to PRODUCE, so it must not smuggle in an import;
    /// * no obligations, an obligation the module does not declare, an
    ///   obligation not SITED in the named function (including one with no
    ///   site at all), or one whose declared `function` disagrees with the
    ///   function it is sited in —
    ///   `NativeTrustIrDischargeRequestWithoutObligations`,
    ///   `NativeTrustIrTrustVcRequestUnknownObligation`,
    ///   `NativeTrustIrDischargeRequestObligationOutsideFunction`,
    ///   `NativeTrustIrDischargeRequestObligationFunctionDisagrees`. This gate
    ///   is a CONJUNCTION and is narrower than the body lane's own scoping
    ///   disjunction on purpose; see the comment at the check.
    ///
    /// These are a SECOND gate. On the serialized path trust-ir's own
    /// validator refuses the same shapes first (and, at trust-vc's pinned
    /// trust-ir, refuses every certificate-less discharge request outright);
    /// the gates here also cover the direct in-process call, which has no
    /// upstream validator in front of it.
    pub fn discharge_native_trust_ir_request(
        &self,
        module: &Module,
        request: &TrustVcNativeRequest,
    ) -> Result<TrustVcNativeTrustIrRequestReport, TrustEngineError> {
        let request_id = request.id.index();
        if request.mode != TrustVcVerificationMode::DischargeProofObligations {
            return Err(TrustEngineError::NativeTrustIrDischargeRequestWrongMode {
                request_id,
                mode: format!("{:?}", request.mode),
            });
        }
        let Some(function) = request.function else {
            return Err(
                TrustEngineError::NativeTrustIrDischargeRequestMissingFunction { request_id },
            );
        };
        if let Some(certificate) = request.certificates.first() {
            return Err(
                TrustEngineError::NativeTrustIrDischargeRequestCarriesCertificate {
                    request_id,
                    obligation_id: certificate.obligation.index(),
                    prover: certificate.prover.clone(),
                },
            );
        }
        let cited = request.obligations.iter().copied().collect::<BTreeSet<_>>();
        if cited.is_empty() {
            return Err(
                TrustEngineError::NativeTrustIrDischargeRequestWithoutObligations { request_id },
            );
        }
        // A request names a SET: the report records the request's list, and a
        // decoder refuses a list naming one obligation twice.
        let named = request
            .obligations
            .iter()
            .map(|obligation| obligation.index())
            .collect::<Vec<_>>();
        if let Some(obligation_id) = first_duplicate(&named) {
            return Err(
                TrustEngineError::NativeTrustIrDischargeRequestDuplicateObligation {
                    request_id,
                    obligation_id,
                },
            );
        }
        // The answer is bound to the WHOLE module's digest below, and the lane
        // hashes the function's image; both panic on a construct the binary
        // writer cannot encode, wherever in the module it sits.
        refuse_module_without_wire_identity(module)?;

        let declared = module
            .proof_obligations
            .iter()
            .map(|obligation| (obligation.id, obligation))
            .collect::<BTreeMap<_, _>>();
        for proof_id in &cited {
            let Some(obligation) = declared.get(proof_id) else {
                return Err(
                    TrustEngineError::NativeTrustIrTrustVcRequestUnknownObligation {
                        request_id,
                        obligation_id: proof_id.index(),
                    },
                );
            };
            // NARROWER THAN THE BODY LANE, ON PURPOSE.
            //
            // The lane scopes by the DISJUNCTION
            // `obligation.function == Some(f) || obligation.site.function == f`
            // because it is reporting on everything that could belong to the
            // function. A request gate is a different question: it decides
            // what trust-vc will ANSWER for, so it takes the conjunction.
            //
            // `site.function` is the load-bearing half: the lane proves the
            // `Assert` AT THE SITE, so an obligation with no site in `f` is
            // not an obligation about `f`'s body whatever `function` claims.
            // `obligation.function` is a second, independent producer claim;
            // when it is set it must agree, and a disagreement is refused
            // rather than resolved in either direction.
            //
            // The disjunction admitted two shapes upstream would never have
            // sanctioned — `function: Some(f)` with the site in another
            // function, and the mirror — which the lane then answered
            // `NotAnswerable` one layer down. Both are now refused at the gate.
            if obligation.site.map(|site| site.function) != Some(function) {
                return Err(
                    TrustEngineError::NativeTrustIrDischargeRequestObligationOutsideFunction {
                        request_id,
                        obligation_id: proof_id.index(),
                        function_id: function.index(),
                    },
                );
            }
            if matches!(obligation.function, Some(declared) if declared != function) {
                let declared = obligation.function.expect("matched Some above");
                return Err(
                    TrustEngineError::NativeTrustIrDischargeRequestObligationFunctionDisagrees {
                        request_id,
                        obligation_id: proof_id.index(),
                        declared_function_id: declared.index(),
                        function_id: function.index(),
                    },
                );
            }
        }

        // EvidenceOnly on purpose: the lane's own provisional certificate is
        // not a trust-ir certificate and has no place on a wire report that a
        // consumer might mistake for one.
        let body = self
            .discharge_trust_ir_function(module, function, &TrustIrBodyOptions::default())
            .map_err(
                |error| TrustEngineError::NativeTrustIrDischargeLaneRefusedRequest {
                    request_id,
                    detail: error.to_string(),
                },
            )?;
        // BIND THE ANSWER TO WHAT IT ANSWERS. This entry performs no upstream
        // bundle validation, so nothing else checks that `request` was minted
        // against `module`. Recording both digests does not make the answer
        // authority — it makes a mix-up DETECTABLE by a consumer holding only
        // the report, which it previously was not: the answer named a bare
        // `FuncId` index and a digest the lane computed for itself.
        let request_digest = NativeVerificationRequest::TrustVc(request.clone())
            .stable_digest()
            .to_string();
        let module_digest = module.stable_digest().to_string();
        let answer = discharge_answer(DischargeAnswerInput {
            request_id,
            request_digest,
            trust_ir_module_digest: module_digest,
            function,
            body: &body,
            cited: &cited,
        });

        Ok(TrustVcNativeTrustIrRequestReport {
            request_id,
            mode: TrustVcNativeTrustIrRequestMode::DischargeProofObligations,
            lineage_roots: request
                .lineage_roots
                .iter()
                .map(|root| root.index())
                .collect(),
            obligations: request
                .obligations
                .iter()
                .map(|obligation| obligation.index())
                .collect(),
            // EMPTY, ALWAYS. This is the certificate-admission channel; a
            // discharge answer never enters it.
            proof_evidence: Vec::new(),
            verdict: discharge_verdict(&answer.obligations),
            advisory_discharge: Some(answer),
            discharge: Vec::new(),
        })
    }

    /// Re-derive a verdict for a DECODED discharge-mode request report from
    /// the module and the request it claims to answer.
    ///
    /// A decoded discharge report is
    /// [`TrustVcNativeTrustIrVerdict::NotJudged`]: its outcomes are labels the
    /// wire carries no evidence for. This is where a verdict comes back, and
    /// it comes back from nothing the report says. The report must be BOUND
    /// to `request` against `module`, all of which the caller holds:
    ///
    /// * its mode is `DischargeProofObligations` and its request id is the
    ///   request's;
    /// * its answer's `request_digest` is the request's stable digest and its
    ///   `trust_ir_module_digest` is `module`'s, and it names the request's
    ///   function;
    /// * the obligations it names are EXACTLY the request's obligation list,
    ///   and its answer answers each of them exactly once — so a consistently
    ///   renamed id (`0` → `4242` in both lists), a dropped one, or a
    ///   duplicated one (`[0, 0]`) is refused, not re-judged.
    ///
    /// Then the request is discharged afresh in this process
    /// ([`Self::discharge_native_trust_ir_request`]) and THAT report is
    /// returned. The decoded report's claims are never consulted.
    pub fn rejudge_native_trust_ir_discharge_report(
        &self,
        module: &Module,
        request: &TrustVcNativeRequest,
        report: &TrustVcNativeTrustIrRequestReport,
    ) -> Result<TrustVcNativeTrustIrRequestReport, TrustEngineError> {
        let request_id = request.id.index();
        let not_bound = |detail: String| TrustEngineError::NativeTrustIrDischargeReportNotBound {
            request_id,
            detail,
        };
        if report.mode != TrustVcNativeTrustIrRequestMode::DischargeProofObligations {
            return Err(not_bound(format!(
                "the report is a {:?} report, not a discharge report",
                report.mode
            )));
        }
        if report.request_id != request_id {
            return Err(not_bound(format!(
                "the report answers request {}",
                report.request_id
            )));
        }
        let answer = report.advisory_discharge.as_ref().ok_or_else(|| {
            not_bound("the report carries no advisory discharge answer".to_string())
        })?;
        let request_digest = NativeVerificationRequest::TrustVc(request.clone())
            .stable_digest()
            .to_string();
        if answer.request_digest != request_digest {
            return Err(not_bound(format!(
                "the answer names request digest {}, the request's is {request_digest}",
                answer.request_digest
            )));
        }
        refuse_module_without_wire_identity(module)?;
        let module_digest = module.stable_digest().to_string();
        if answer.trust_ir_module_digest != module_digest {
            return Err(not_bound(format!(
                "the answer names module digest {}, this module's is {module_digest}",
                answer.trust_ir_module_digest
            )));
        }
        if Some(answer.function) != request.function.map(|function| function.index()) {
            return Err(not_bound(format!(
                "the answer names function {}, the request names {:?}",
                answer.function,
                request.function.map(|function| function.index())
            )));
        }
        let requested = request
            .obligations
            .iter()
            .map(|obligation| obligation.index())
            .collect::<Vec<_>>();
        if report.obligations != requested {
            return Err(not_bound(format!(
                "the report names obligation(s) {:?}, the request names {requested:?}",
                report.obligations
            )));
        }
        let mut answered = answer
            .obligations
            .iter()
            .map(TrustVcNativeTrustIrDischargeObligation::obligation_id)
            .collect::<Vec<_>>();
        answered.sort_unstable();
        let mut expected = requested;
        expected.sort_unstable();
        if answered != expected {
            return Err(not_bound(format!(
                "the answer answers obligation(s) {answered:?}, the request names {expected:?}"
            )));
        }
        self.discharge_native_trust_ir_request(module, request)
    }

    /// Validate a native TrustIr bundle and ensure it contains consumable TrustVc requests.
    ///
    /// # `Ok(())` means the rollup is a clean pass, not merely that consuming
    /// did not error
    ///
    /// This used to be `consume_native_trust_ir_bundle(..).map(|_| ())`, which
    /// discarded the report and its verdict. That was harmless while every
    /// non-`Err` outcome was a certificate import; it is not harmless now that
    /// a bundle carrying a discharge request can come back `DischargeRefuted`
    /// — a genuine counterexample — through an API called `validate_`. A
    /// non-`Ok` [`TrustVcNativeTrustIrExitClass`] is an `Err` here — and that
    /// includes a `CertificatesRejected` rollup (exit class
    /// [`TrustVcNativeTrustIrExitClass::Rejected`]), which used to come back
    /// `Ok(())` because its exit class was `Ok`.
    ///
    /// Callers that want the refutation itself, rather than the fact of it,
    /// should call [`Self::consume_native_trust_ir_bundle`] and read the
    /// report.
    pub fn validate_native_trust_ir_bundle(
        &self,
        bundle: &NativeVerificationBundle,
    ) -> Result<(), TrustEngineError> {
        check_bundle_report_is_clean(&self.consume_native_trust_ir_bundle(bundle)?)
    }

    /// Consume typed native Tmir (Trust MIR) TrustVc requests directly from a
    /// native bundle.
    ///
    /// Tmir is the current public name for the same typed TrustIr bundle
    /// surface; this forwarder exists so tRust-side bridges can call into the
    /// engine using the Tmir naming.
    pub fn consume_native_tmir_bundle(
        &self,
        bundle: &NativeVerificationBundle,
    ) -> Result<TrustVcNativeTrustIrBundleReport, TrustEngineError> {
        self.consume_native_trust_ir_bundle(bundle)
    }

    /// Consume typed native TrustIr TrustVc requests directly from a native bundle.
    ///
    /// This validates the upstream TrustIr bundle, requires release evidence for
    /// every `NativeVerificationRequest::TrustVc` entry, and imports the
    /// requested proof-certificate references as native certificate evidence.
    pub fn consume_native_trust_ir_bundle(
        &self,
        bundle: &NativeVerificationBundle,
    ) -> Result<TrustVcNativeTrustIrBundleReport, TrustEngineError> {
        refuse_module_without_wire_identity(&bundle.module)?;
        validate_producer_module(&bundle.module)?;
        validate_upstream_bundle(bundle)?;
        validate_trust_vc_release_evidence_bundles(bundle)?;
        refuse_discharge_lineage_certifying_own_obligations(bundle)?;
        // THE EXPORT SEAM's input gates. Every rendering of an assertion
        // identity in this bundle must agree with every other, and every TrustVc
        // request's replay atoms must state their obligation's own formula and
        // number; a bundle that breaks either is refused rather than published
        // from. See `crate::native_assertion_id`.
        crate::native_assertion_id::validate_assertion_id_renderings(
            &bundle.module,
            &bundle.compiler_facts,
        )?;
        crate::native_assertion_id::validate_request_assertion_atoms(
            &bundle.module,
            &bundle.compiler_facts,
            &bundle.requests,
        )?;
        // ROUND 9: the same rule for the obligation KIND, whose second rendering
        // (the compiler fact's `cause`) this crate republishes on every artifact
        // binding without ever comparing it to the kind the lane decides with.
        crate::native_assertion_id::validate_obligation_kind_renderings(
            &bundle.module,
            &bundle.compiler_facts,
        )?;

        let obligations = bundle
            .module
            .proof_obligations
            .iter()
            .map(|obligation| (obligation.id, obligation))
            .collect::<BTreeMap<_, _>>();
        let certificates = bundle
            .module
            .proof_certificates
            .iter()
            .map(|certificate| (certificate.lineage_ref(), certificate))
            .collect::<BTreeMap<_, _>>();
        let trust_ir_module_digest = bundle.trust_ir_module_digest.to_string();
        let compiler_facts_digest = bundle.compiler_facts.stable_digest().to_string();
        let compiler_fact_sources = bundle
            .compiler_facts
            .obligation_sources
            .iter()
            .map(|source| (source.obligation, source))
            .collect::<BTreeMap<_, _>>();
        let assertion_ids = crate::native_assertion_id::AssertionIdIndex::of(
            &bundle.module,
            &bundle.compiler_facts,
            &bundle.requests,
        );

        // Every request's digest, recomputed once: each TrustVc report binds
        // its own.
        let bundle_requests = bundle
            .requests
            .iter()
            .map(|request| (request.stable_digest(), request))
            .collect::<Vec<BundleRequest<'_>>>();
        // Coverage is DERIVED here, once per bundle, from evidence this
        // process re-checks (basis K: the kernel replay of each certificate);
        // no producer-written `assurance` row is read.
        let coverage = CoverageJudge::for_bundle(bundle);

        let mut requests = Vec::new();
        let mut produced_certificates = Vec::new();
        let mut produced_evidence_bundles = Vec::new();
        for (request_digest_raw, request) in &bundle_requests {
            let request_digest = request_digest_raw.to_string();
            if let NativeVerificationRequest::TrustVc(trust_vc_request) = request {
                let outcome = build_request_report(RequestReportInputs {
                    request: trust_vc_request,
                    request_digest: &request_digest,
                    module: &bundle.module,
                    trust_ir_module_digest_raw: bundle.trust_ir_module_digest,
                    request_digest_raw: *request_digest_raw,
                    obligations: &obligations,
                    certificates: &certificates,
                    trust_ir_module_digest: &trust_ir_module_digest,
                    compiler_facts_digest: &compiler_facts_digest,
                    compiler_fact_sources: &compiler_fact_sources,
                    assertion_ids: &assertion_ids,
                    lineage_nodes: &bundle.lineage.nodes,
                    coverage: &coverage,
                })?;
                requests.push(outcome.report);
                produced_certificates.extend(outcome.produced_certificates);
                produced_evidence_bundles.extend(outcome.produced_evidence_bundle);
            }
        }

        if requests.is_empty() {
            return Err(TrustEngineError::NativeTrustIrBundleHasNoTrustVcRequests {
                module: bundle.module.name.clone(),
            });
        }

        let (input_kind, input_digest) = native_input_parts(bundle.input);
        Ok(TrustVcNativeTrustIrBundleReport {
            producer: producer_label(bundle.producer).to_string(),
            input_kind,
            input_digest,
            trust_ir_module_digest,
            compiler_facts_digest,
            module_name: bundle.module.name.clone(),
            // Worst-wins, via the same `rollup_verdict` the deserializer
            // re-checks a wire report against, so a produced report and an
            // accepted one can never disagree about the fold. An empty request
            // list cannot reach here — the no-TrustVc-request case is refused
            // above — and `rollup_verdict` returns `None` for it rather than
            // manufacturing a pass out of nothing. Unreachable or not, fail
            // closed on `DischargeNotAnswerable` rather than panic.
            verdict: rollup_verdict(&requests)
                .unwrap_or(TrustVcNativeTrustIrVerdict::DischargeNotAnswerable),
            requests,
            produced_certificates,
            produced_evidence_bundles,
        })
    }
}

/// The gate [`TrustVcTrustEngine::validate_native_trust_ir_bundle`] applies to
/// the report it just consumed.
///
/// A free function so it is testable against a hand-built report. (Written at
/// trust-ir 0.11, where no bundle could reach a non-`Ok` verdict through
/// `consume_native_trust_ir_bundle`; at this pin a serialized discharge request
/// can come back `Refuted` or `DischargeDeclined` from the `native_discharge`
/// lane, and this gate refuses those too.)
fn check_bundle_report_is_clean(
    report: &TrustVcNativeTrustIrBundleReport,
) -> Result<(), TrustEngineError> {
    if report.verdict().exit_class() != TrustVcNativeTrustIrExitClass::Ok {
        return Err(TrustEngineError::NativeTrustIrBundleVerdictNotClean {
            module: report.module_name().to_string(),
            verdict: format!("{:?}", report.verdict()),
        });
    }
    Ok(())
}

/// THE INPUT GATE: run the PRODUCER's own validator on the incoming module and
/// refuse anything it rejects.
///
/// # Why the producer's validator and not another hand-written gate
///
/// Four rounds of adversarial review found a false `Discharged` each time, and
/// every single shape was one `trust-ir-build::validate_module` ALREADY rejects:
/// a `ValueId` defined twice, a constant outside its declared width, a use before
/// its definition, a repeated switch case, a signature that disagrees with its
/// entry block (`validate.rs:1812`), two proof obligations sharing one `ProofId`
/// (`validate.rs:1819`). Gating them one at a time is whack-a-mole over a CLASS:
/// the lane's soundness argument silently assumed module well-formedness that
/// nothing established. This runs the authority that defines it.
///
/// # Which entry point, and why
///
/// [`trust_ir_build::validate_module`] — i.e. `validate_module_report` under
/// [`trust_ir::proof::RejectingModuleProofAuthority`]. The alternatives, and why
/// not:
///
/// * `validate_module_with_authority` takes a capability that may turn a
///   `Discharged` row's certificate into proof authority "by re-establishing its
///   claim in this process". This lane re-establishes NOTHING it is handed: it
///   proves the obligation from the body with its own encoder. Supplying an
///   authority would be claiming a replay that does not happen, and the
///   validator's own doc notes such a capability widens the refs consulted by
///   `validate_proof_contexts`, the `InheritedFromCallee` chain and lineage
///   closure — i.e. a capability admitted here is admitted EVERYWHERE. Fail
///   closed: hand it the rejecting authority.
/// * `validate_module_with_dialect_schemas` requires a
///   `DialectSchemaRegistry` this crate does not have and cannot invent; without
///   the real registry it is not a stronger check, it is a different one.
/// * `validate_module_for_codegen` does not exist at the pinned trust-ir rev
///   (`6713d9ed`); it is a sibling-working-tree addition. Its contract is a
///   codegen body LICENSE, which is not this consumer's question.
///
/// # The ONE verdict this deliberately does NOT treat as a module defect
///
/// [`trust_ir_build::ValidationError::DischargedWithoutCertificate`] is the
/// rejecting authority's own capability verdict — "the format build cannot run a
/// solver or a kernel and must not pretend otherwise", in its words. It is
/// AUTHORITY-DEPENDENT: at the pinned rev it is minted by a function that takes
/// the authority set as an argument and reports every `Discharged` row with no
/// certificate that set admits, so a replay-capable consumer would not see it at
/// all. It says nothing about whether the module is WELL-FORMED. This crate
/// decides certificate admission itself
/// ([`TrustVcNativeTrustIrCertificateRejection`], and the kernel/strict policy
/// behind the `proof-certificates` feature), and the discharge lane trusts no
/// incoming certificate at all — it proves the obligation from the body. So it
/// is carried past this gate and left to the admission path that actually owns
/// it.
///
/// MEASURED: relaxing exactly this one is what the checked-in import fixture
/// needs at its admission baseline (`native_request_trust_bundle.json`,
/// normalized to a `Discharged` obligation 0). No other checked-in bundle
/// produces any validator error at all. Every other variant — every
/// structural, type, CFG, SSA, proof-integrity and ABI arm — refuses the
/// bundle.
///
/// # Why `CertifiedCleanCicKernelRecheckFailed` is NOT carried past (round 5)
///
/// It used to be, on the same "capability verdict" rationale, and that rationale
/// was false for that variant. At the pinned rev it is minted by
/// `validate_certified_evidence_with_catalog`, which takes NO authority
/// argument, so no capability a consumer could supply removes it; upstream's own
/// doc calls it "the kernel re-checker's rejection ... Rejected, never
/// faith-accepted (fail-closed: a re-check that cannot be run is a re-check that
/// did not pass)", covering a proof term that does not have its declared type and
/// a rooted audit that finds a trust/provenance issue. It is also the only real
/// kernel recheck on this side — the import lane's own admission is
/// metadata-only. So it refuses.
///
/// The corpus fixture `native_request_trust_bundle.json` ships obligation 0 at
/// `Certified` with a directive-less contract `CleanCic` term. With
/// `trust-ir-build`'s default `clean-tv-anchor` feature the re-checker
/// re-derives that contract goal and the term re-checks, so the verbatim
/// fixture passes this gate.
/// `runner_refuses_the_corpus_bundle_whose_certified_claim_fails_its_kernel_recheck`
/// pins the refusal on the same bundle with its term corrupted.
fn validate_producer_module(module: &trust_ir::Module) -> Result<(), TrustEngineError> {
    let errors = trust_ir_build::validate_module(module)
        .into_iter()
        .filter(|error| !is_proof_replay_capability_verdict(error))
        .map(|error| error.to_string())
        .collect::<Vec<_>>();
    if errors.is_empty() {
        return Ok(());
    }
    Err(
        TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator {
            module: module.name.clone(),
            errors: errors.join("; "),
        },
    )
}

/// Is this error the rejecting proof authority declining to REPLAY a
/// certificate, rather than a statement that the module is malformed?
///
/// Deliberately a positive, exhaustive-by-name list of ONE, and the test that
/// pins it asserts the exact variant rather than a set. `ValidationError` is
/// `#[non_exhaustive]`, so a new variant added upstream lands in the REFUSING
/// branch by default, which is the direction a fail-closed gate must default in.
///
/// # SCOPE (adversarial review round 6, blocker 1) — what carrying it past MEANS
///
/// It means exactly one thing: **this crate grades certificates itself, so it
/// does not want the format build's capability verdict about them.** It does
/// NOT mean a `Discharged` row is established, and nothing downstream may read
/// it that way. At the pinned rev `validate_discharged_authority` raises this
/// verdict for EVERY `Discharged` obligation with no authority-admitted
/// certificate, and under `RejectingModuleProofAuthority` that authority set
/// only ever holds `Certified` rows whose `CleanCic` term the kernel re-checked
/// — so it fires for every `Discharged` row UNCONDITIONALLY. A module carrying a
/// `Discharged` row backed by nothing at all therefore passes this gate, by
/// design.
///
/// Round 5 then had `native_discharge::body`'s `lower_call` read that bare label
/// as ESTABLISHED and assume the callee's `ensures` as fact, which is precisely
/// what this error's own text forbids: "status is Discharged but no exact
/// certificate was replayed by this validator — opaque evidence and status
/// labels are not proof authority". The probe: `g` is the identity, publishes
/// `ensures result >= 100` at `Discharged` with no certificate, and
/// `caller(x) { g(x) }` claiming the same came back `Discharged` with a
/// release-admissible kernel-checked certificate. False at `x = 0`.
///
/// The carve-out was NOT deleted — the CLI acceptance fixture
/// (`kernel_grounded_native_bundle_json`) moves obligation 0 to `Discharged`,
/// and grading an IMPORT is a different job from discharging. It was SCOPED:
/// `Builder::established_callee_ensures` now requires `Certified` plus a
/// lineage-bound `CleanCic` certificate, and the enumeration of every point
/// where a producer claim can influence a verdict lives at
/// `Builder::callee_contract_facts`.
fn is_proof_replay_capability_verdict(error: &trust_ir_build::ValidationError) -> bool {
    matches!(
        error,
        trust_ir_build::ValidationError::DischargedWithoutCertificate { .. }
    )
}

/// Refuse a module that has no canonical binary image BEFORE anything hashes
/// it. Upstream `NativeVerificationBundle::validate` and this crate both take
/// `Module::stable_digest`, which panics on such a module.
fn refuse_module_without_wire_identity(module: &Module) -> Result<(), TrustEngineError> {
    match wire_identity_gap(module) {
        Some(gap) => Err(TrustEngineError::NativeTrustIrModuleHasNoWireIdentity {
            location: gap.location,
            construct: gap.construct,
        }),
        None => Ok(()),
    }
}

fn validate_upstream_bundle(bundle: &NativeVerificationBundle) -> Result<(), TrustEngineError> {
    refuse_module_without_wire_identity(&bundle.module)?;
    let Err(errors) = bundle.validate() else {
        return Ok(());
    };

    let errors = errors
        .into_iter()
        .filter(|error| !is_discharge_mode_certificate_rule(bundle, error))
        .map(|error| error.to_string())
        .collect::<Vec<_>>();
    if errors.is_empty() {
        return Ok(());
    }

    Err(TrustEngineError::InvalidNativeTrustIrBundle {
        errors: errors.join("; "),
    })
}

/// The ONE upstream rule this lane relaxes, and only for a discharge request's
/// own obligations.
///
/// MEASURED at the pinned trust-ir (0.14.0, binary VERSION 40):
/// `validate_trust_vc_request` requires a certificate reference for every
/// obligation of every `NativeVerificationRequest::TrustVc`, and it does NOT
/// look at the request's mode. Combined with its sibling rule — a referenced
/// certificate must belong to an obligation that is already
/// `Discharged`/`Certified` AND was replayed by the Clean kernel in this
/// process — the wire schema admits a TrustVc request only when what it asks
/// about has ALREADY been proved. A discharge request is by definition a
/// request for a proof that does not exist yet, so under the unrelaxed rule the
/// mode is not merely unanswered, it is UNEXPRESSIBLE.
///
/// WHAT IS RELAXED, EXACTLY: `MissingTrustVcEvidenceForObligation` for an
/// obligation that a DISCHARGE-mode request itself lists. Nothing else. Every
/// other rule — module digest, lineage roots and their target module,
/// per-obligation source spans and assertion ids, the certificate-status rule
/// when a discharge request DOES cite a certificate, and this same
/// missing-evidence rule on every Import/Merge request — stays fatal, and any
/// error variant this build does not recognize stays fatal.
///
/// WHY IT IS NOT A SOUNDNESS HOLE: the relaxed rule is about the request's
/// INPUT evidence. It says nothing about the answer. The discharge lane derives
/// its verdict from the trust-ir body and the obligation's own formula through
/// trust-vc's encoder and ay, publishes it in the per-obligation `discharge`
/// vector, and mints a certificate only from a kernel-checked artifact. A
/// discharge request that carried no evidence and was refused here produced no
/// answer at all; one that is admitted still cannot produce `Discharged`
/// without a real proof.
///
/// REMOVE THIS the moment trust-ir makes the rule mode-conditional (the
/// additive-schema step of the fusion plan). It is keyed on the upstream error
/// variant precisely so that a schema that stops emitting it needs no further
/// change here.
fn is_discharge_mode_certificate_rule(
    bundle: &NativeVerificationBundle,
    error: &NativeVerificationBundleError,
) -> bool {
    let NativeVerificationBundleError::MissingTrustVcEvidenceForObligation {
        request,
        obligation,
    } = error
    else {
        return false;
    };
    bundle.requests.iter().any(|candidate| {
        let NativeVerificationRequest::TrustVc(candidate) = candidate else {
            return false;
        };
        candidate.id == *request
            && candidate.mode == TrustVcVerificationMode::DischargeProofObligations
            && candidate.obligations.contains(obligation)
    })
}

fn validate_trust_vc_release_evidence_bundles(
    bundle: &NativeVerificationBundle,
) -> Result<(), TrustEngineError> {
    let trust_vc_evidence_requests = bundle
        .evidence_bundles
        .iter()
        .filter(|evidence| evidence.verifier_suite() == NativeVerifierSuite::TrustVc)
        .map(|evidence| evidence.request())
        .collect::<BTreeSet<_>>();
    let missing_evidence = bundle
        .requests
        .iter()
        .filter_map(|request| {
            let NativeVerificationRequest::TrustVc(request) = request else {
                return None;
            };
            // MODE-CONDITIONAL, and this is the whole point of the discharge
            // lane: an Import/Merge request CARRIES its evidence bundle, a
            // Discharge request PRODUCES one. Demanding the output on input
            // refused every discharge request before it started. Import/Merge
            // keep the rule verbatim.
            if request.mode == TrustVcVerificationMode::DischargeProofObligations {
                return None;
            }
            (!trust_vc_evidence_requests.contains(&request.id)).then_some(request.id)
        })
        .collect::<Vec<_>>();

    if missing_evidence.is_empty() {
        return Ok(());
    }

    Err(TrustEngineError::InvalidNativeTrustIrBundle {
        errors: missing_evidence
            .iter()
            .map(|request| {
                format!(
                    "native verification request {} requires a TrustVc native evidence bundle",
                    request.index()
                )
            })
            .collect::<Vec<_>>()
            .join("; "),
    })
}

/// Refuse a discharge request whose lineage closure already certifies one of
/// the obligations it asks trust-vc to discharge.
///
/// A discharge request asks for proofs that do not exist yet, so upstream
/// refuses one that carries a certificate for its own obligations
/// (`TrustVcDischargeRequestCarriesCertificate`). The same certificate reached
/// through the request's lineage closure (every node reachable from its
/// `lineage_roots` along `depends_on`) is refused too: the request would hold
/// both an imported account and a discharge of one obligation, which upstream
/// also refuses across requests (`TrustVcObligationBothImportedAndDischarged`).
fn refuse_discharge_lineage_certifying_own_obligations(
    bundle: &NativeVerificationBundle,
) -> Result<(), TrustEngineError> {
    let nodes = bundle
        .lineage
        .nodes
        .iter()
        .map(|node| (node.id, node))
        .collect::<BTreeMap<_, _>>();
    let mut errors = Vec::new();
    for request in &bundle.requests {
        let NativeVerificationRequest::TrustVc(request) = request else {
            continue;
        };
        if request.mode != TrustVcVerificationMode::DischargeProofObligations {
            continue;
        }
        let own = request.obligations.iter().copied().collect::<BTreeSet<_>>();
        let mut stack = request.lineage_roots.clone();
        let mut visited = BTreeSet::new();
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            let Some(node) = nodes.get(&id) else {
                continue;
            };
            for certificate in node
                .certificates
                .iter()
                .filter(|certificate| own.contains(&certificate.obligation))
            {
                errors.push(format!(
                    "discharge request {} asks for obligation {} but its lineage node {} \
                     already carries a certificate for it from prover `{}`",
                    request.id.index(),
                    certificate.obligation.index(),
                    node.id,
                    certificate.prover,
                ));
            }
            stack.extend(node.depends_on.iter().copied());
        }
    }
    if errors.is_empty() {
        return Ok(());
    }
    Err(TrustEngineError::InvalidNativeTrustIrBundle {
        errors: errors.join("; "),
    })
}

/// The prover label trust-vc stamps on a certificate it produced itself.
///
/// DISTINCT from the `trust_vc` label an imported certificate may carry: a
/// reader must be able to tell a proof this lane derived from one it merely
/// checked.
pub(crate) const TRUST_VC_DISCHARGE_PROVER: &str = "trust-vc/ay (discharge)";

/// The replay engine name for a produced certificate.
pub(crate) const TRUST_VC_DISCHARGE_REPLAY_ENGINE: &str = "trust-vc-trust-engine";

/// The evidence bundle a discharge request PRODUCES.
///
/// This is the output half of the per-request evidence rule that Import/Merge
/// require on input: a discharge request arrives without one (upstream refuses
/// an evidence bundle whose mode disagrees with its request's) and leaves with
/// one describing what trust-vc proved.
///
/// `None` when nothing was proved — an evidence bundle for zero artifacts would
/// assert that a request was answered when it was not.
pub(crate) fn produced_evidence_bundle(
    inputs: &RequestReportInputs<'_>,
    report: &DischargeReport,
) -> Option<TrustVcNativeEvidenceBundle> {
    if report.produced_certificates.is_empty() {
        return None;
    }
    let artifacts = report
        .produced_certificates
        .iter()
        .map(|certificate| {
            NativeEvidenceArtifact::new(
                format!("trust-vc discharge {}", certificate.unit_id()),
                // Deliberately NOT `TrustVcCertificateImport`: nothing was
                // imported. There is no discharge-specific kind on the pinned
                // schema, and mislabelling the artifact would be the one piece
                // of this row a reader would take at face value.
                NativeEvidenceArtifactKind::Other,
                digest_of(certificate.alethe().as_bytes()),
            )
        })
        .collect::<Vec<_>>();
    let transcript = report
        .produced_certificates
        .iter()
        .map(TrustVcNativeTrustIrProducedCertificate::alethe)
        .collect::<Vec<_>>()
        .join("\n");
    Some(TrustVcNativeEvidenceBundle {
        request: inputs.request.id,
        mode: TrustVcVerificationMode::DischargeProofObligations,
        obligations: report
            .produced_certificates
            .iter()
            .map(|certificate| ProofId::new(certificate.obligation_id()))
            .collect(),
        verifier: NativeToolIdentity::new(env!("CARGO_PKG_NAME"))
            .with_version(env!("CARGO_PKG_VERSION")),
        solvers: vec![NativeToolIdentity::new("ay")],
        replay: trust_ir::ProofReplayIdentity {
            engine: TRUST_VC_DISCHARGE_REPLAY_ENGINE.to_string(),
            invocation: format!("trust-vc discharge request {}", inputs.request.id.index()),
            transcript_digest: Some(digest_of(transcript.as_bytes())),
        },
        trust_ir_module_digest: inputs.trust_ir_module_digest_raw,
        request_digest: inputs.request_digest_raw,
        artifacts,
    })
}

/// A typed SHA-256 `ProofDigest` over `bytes`.
fn digest_of(bytes: &[u8]) -> trust_ir::ProofDigest {
    trust_ir::ProofDigest::sha256(Sha256::digest(bytes).into())
}

/// Lowercase hex SHA-256 of `bytes`.
///
/// Used to bind a discharge outcome to the exact `ProofFormula.payload` bytes it
/// was decided from (soundness checklist item A).
pub(crate) fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest.iter().fold(String::new(), |mut out, byte| {
        let _ = write!(out, "{byte:02x}");
        out
    })
}

fn native_input_parts(
    input: NativeAdapterInput,
) -> (TrustVcNativeTrustIrInputKind, Option<String>) {
    match input {
        NativeAdapterInput::RustMir { body_digest } => (
            TrustVcNativeTrustIrInputKind::RustMir,
            Some(body_digest.to_string()),
        ),
        NativeAdapterInput::TrustIrModule => (TrustVcNativeTrustIrInputKind::TrustIrModule, None),
    }
}

fn producer_label(producer: NativeBundleProducer) -> &'static str {
    match producer {
        NativeBundleProducer::TRust => "tRust",
        NativeBundleProducer::TSwift => "tSwift",
        NativeBundleProducer::TC => "tC",
        NativeBundleProducer::TrustIr => "TrustIr",
        NativeBundleProducer::Clean => "Clean",
    }
}

/// The inputs of [`build_request_report`], grouped.
///
/// One bundle's digests and lookup tables are computed once and reused for
/// every request in it; passing them as a record keeps the call site readable
/// (and `clippy::too_many_arguments` satisfied) without changing what any of
/// them mean.
#[derive(Clone, Copy)]
pub(crate) struct RequestReportInputs<'a> {
    pub(crate) request: &'a TrustVcNativeRequest,
    pub(crate) request_digest: &'a str,
    /// The whole trust-ir module. The discharge lane reads `functions`,
    /// `func_types`, `target_info`, `proof_obligations` and
    /// `proof_certificates` from it; the import/merge lanes read
    /// `proof_obligations` and `proof_certificates` only.
    ///
    /// CORRECTED, round 8: this doc said `structs`/`enums` were read, and the
    /// DERIVED scan in [`crate::producer_fields`] says they are not — every
    /// aggregate type declines in `TypeDecoder::sort` long before a struct
    /// definition is needed. Exactly the kind of hand-maintained claim the
    /// derived table exists to stop.
    pub(crate) module: &'a Module,
    pub(crate) obligations: &'a BTreeMap<ProofId, &'a ProofObligation>,
    certificates: &'a BTreeMap<ProofCertificateRef, &'a ProofCertificate>,
    pub(crate) trust_ir_module_digest: &'a str,
    /// The same module digest, typed, for anything this lane PRODUCES.
    pub(crate) trust_ir_module_digest_raw: trust_ir::ProofDigest,
    /// The request's stable digest, typed, for the produced evidence bundle.
    pub(crate) request_digest_raw: trust_ir::ProofDigest,
    compiler_facts_digest: &'a str,
    pub(crate) compiler_fact_sources: &'a BTreeMap<ProofId, &'a NativeObligationSource>,
    /// Bundle-wide: which numeric assertion ids are carried by more than one
    /// identity, and so name none of them. Built once per bundle beside the
    /// input gate; see [`crate::native_assertion_id::AssertionIdIndex`].
    pub(crate) assertion_ids: &'a crate::native_assertion_id::AssertionIdIndex,
    lineage_nodes: &'a [ProofLineageNode],
    coverage: &'a CoverageJudge,
}

/// What one request contributed to the bundle report.
struct RequestReportOutcome {
    report: TrustVcNativeTrustIrRequestReport,
    produced_certificates: Vec<TrustVcNativeTrustIrProducedCertificate>,
    produced_evidence_bundle: Option<TrustVcNativeEvidenceBundle>,
}

fn build_request_report(
    inputs: RequestReportInputs<'_>,
) -> Result<RequestReportOutcome, TrustEngineError> {
    let RequestReportInputs {
        request,
        request_digest,
        module: _,
        trust_ir_module_digest_raw: _,
        request_digest_raw: _,
        obligations,
        certificates,
        trust_ir_module_digest,
        compiler_facts_digest,
        compiler_fact_sources,
        assertion_ids,
        lineage_nodes,
        coverage,
    } = inputs;
    let request_id = request.id.index();
    let requested_obligations = request.obligations.iter().copied().collect::<BTreeSet<_>>();
    let certified_obligations = request
        .certificates
        .iter()
        .map(|certificate| certificate.obligation)
        .collect::<BTreeSet<_>>();

    // MODE-CONDITIONAL, same reason as the evidence-bundle guard above: a
    // discharge request is asking trust-vc to MINT the certificate, so
    // requiring one per obligation on input refused it before it started.
    // Import/Merge keep the rule verbatim. Nothing is lost for Discharge:
    // upstream's own `NativeVerificationBundle::validate()` (run first, in
    // `validate_upstream_bundle`) still rejects a certificate reference for an
    // unrequested obligation, a missing module certificate, and a certificate
    // outside the request's lineage roots.
    let is_discharge = request.mode == TrustVcVerificationMode::DischargeProofObligations;
    if !is_discharge {
        for obligation in &request.obligations {
            if !certified_obligations.contains(obligation) {
                return Err(
                    TrustEngineError::NativeTrustIrTrustVcRequestMissingCertificate {
                        request_id,
                        obligation_id: obligation.index(),
                    },
                );
            }
        }
    }

    let mut proof_evidence: Vec<TrustVcNativeTrustIrCertificateEvidence> = Vec::new();
    // On the discharge lane the request's INPUT certificates are not evidence
    // of anything trust-vc did; publishing them as `proof_evidence` would let a
    // consumer read someone else's certificate as this run's result. The
    // discharge lane's evidence is what it produced, in `produced_certificates`.
    for certificate_ref in request.certificates.iter().filter(|_| !is_discharge) {
        if !requested_obligations.contains(&certificate_ref.obligation) {
            return Err(
                TrustEngineError::NativeTrustIrTrustVcRequestUnexpectedCertificate {
                    request_id,
                    obligation_id: certificate_ref.obligation.index(),
                    prover: certificate_ref.prover.clone(),
                },
            );
        }
        let obligation = obligations
            .get(&certificate_ref.obligation)
            .ok_or_else(
                || TrustEngineError::NativeTrustIrTrustVcRequestUnknownObligation {
                    request_id,
                    obligation_id: certificate_ref.obligation.index(),
                },
            )?;
        let certificate = certificates.get(certificate_ref).ok_or_else(|| {
            TrustEngineError::NativeTrustIrCertificateMissing {
                request_id,
                obligation_id: certificate_ref.obligation.index(),
                prover: certificate_ref.prover.clone(),
            }
        })?;
        let obligation_kind = importable_obligation_kind(request_id, obligation)?;
        let lineage_node =
            lineage_node_for_certificate(lineage_nodes, &request.lineage_roots, certificate_ref);
        proof_evidence.push(build_certificate_evidence(CertificateEvidenceInput {
            certificate_ref,
            certificate,
            obligation,
            obligation_kind,
            lineage_node,
            request_provenance: &request.provenance,
            trust_ir_module_digest,
            request_digest,
            compiler_facts_digest,
            obligation_source: compiler_fact_sources.get(&obligation.id).copied(),
            assertion_ids,
            coverage,
        }));
    }

    let named_obligations = request
        .obligations
        .iter()
        .map(|obligation| obligation.index())
        .collect::<Vec<_>>();
    let mut discharged = DischargeReport::default();
    // THE ONLY PLACE A VERDICT IS MINTED, and the only place that can enforce
    // the mode/verdict pairing: the Import/Merge arm cannot reach `Discharged`
    // and the Discharge arm cannot reach `CertificatesAdmitted`, because each
    // arm names its own outcomes. `worse_of` cannot enforce this — it folds
    // verdicts that already exist.
    let (verdict, discharge) = match request.mode {
        TrustVcVerificationMode::DischargeProofObligations => {
            discharged = discharge_request(inputs);
            let verdict = if discharged.request_refusal.is_some() {
                // Refused at the REQUEST level — the lowering never ran.
                TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
            } else {
                discharged
                    .outcomes
                    .iter()
                    .map(TrustVcNativeTrustIrDischargeOutcome::verdict)
                    .reduce(TrustVcNativeTrustIrVerdict::worse_of)
                    // An empty outcome vector is "answered nothing", not
                    // "nothing was wrong" — fail closed on the worst verdict.
                    .unwrap_or(TrustVcNativeTrustIrVerdict::DischargeNotAnswerable)
            };
            (verdict, std::mem::take(&mut discharged.outcomes))
        }
        TrustVcVerificationMode::ImportProofCertificates
        | TrustVcVerificationMode::MergeProofCertificates => (
            certificate_mode_verdict(&named_obligations, &proof_evidence),
            Vec::new(),
        ),
    };

    // On the discharge lane the evidence rows are what this run PRODUCED. They
    // are built here, from the certificates minted above, so the existing
    // artifact-admission path (`admit_native_proof_artifacts`) and the bridge's
    // import lane work over a produced certificate unchanged.
    if is_discharge {
        proof_evidence = discharged
            .produced_certificates
            .iter()
            .map(|certificate| certificate.evidence_row(&inputs))
            .collect::<Result<Vec<_>, _>>()?;
    }

    Ok(RequestReportOutcome {
        report: TrustVcNativeTrustIrRequestReport {
            request_id,
            mode: request.mode.into(),
            lineage_roots: request
                .lineage_roots
                .iter()
                .map(|root| root.index())
                .collect(),
            obligations: named_obligations,
            proof_evidence,
            verdict,
            advisory_discharge: None,
            discharge,
        },
        produced_certificates: discharged.produced_certificates,
        produced_evidence_bundle: discharged.produced_evidence_bundle,
    })
}

/// Render a body-lane refusal as the wire `detail` string.
///
/// Written out rather than `{:?}` so the strings a consumer reads are chosen
/// deliberately and keep naming the block, index and instruction the lane
/// declined.
fn render_refusal(refusal: &TrustIrBodyRefusal) -> String {
    match refusal {
        TrustIrBodyRefusal::ControlFlow {
            block,
            inst_index,
            detail,
        } => match inst_index {
            Some(index) => format!(
                "control flow outside the lane at block {}, instruction {index}: {detail}",
                block.index()
            ),
            None => format!(
                "control flow outside the lane at block {}: {detail}",
                block.index()
            ),
        },
        TrustIrBodyRefusal::UnsupportedInstruction {
            block,
            inst_index,
            inst,
            detail,
        } => format!(
            "unsupported instruction {inst} at block {}, instruction {inst_index}: {detail}",
            block.index()
        ),
        TrustIrBodyRefusal::UnsupportedType {
            block,
            inst_index,
            ty,
        } => match (block, inst_index) {
            (Some(block), Some(index)) => format!(
                "unsupported type {ty} at block {}, instruction {index}",
                block.index()
            ),
            (Some(block), None) => {
                format!("unsupported type {ty} at block {}", block.index())
            }
            _ => format!("unsupported type {ty}"),
        },
        TrustIrBodyRefusal::IllTyped {
            block,
            inst_index,
            detail,
        } => format!(
            "ill-typed at block {}, instruction {inst_index}: {detail}",
            block.index()
        ),
        TrustIrBodyRefusal::Malformed { detail } => format!("malformed function: {detail}"),
        TrustIrBodyRefusal::UnsupportedModuleTable { table, detail } => {
            format!("unsupported module table {table}: {detail}")
        }
        TrustIrBodyRefusal::FunctionScopeMissing => {
            "the obligation names no function scope".to_string()
        }
        TrustIrBodyRefusal::SiteMissing => "the obligation names no site".to_string(),
        TrustIrBodyRefusal::SiteFunctionMismatch { site_function } => format!(
            "the obligation's site is in function #{}, not the requested one",
            site_function.index()
        ),
        TrustIrBodyRefusal::SiteBlockMissing { block } => format!(
            "the obligation's site names block {}, which the function does not have",
            block.index()
        ),
        TrustIrBodyRefusal::SiteIndexOutOfRange { block, inst_index } => format!(
            "the obligation's site names instruction {inst_index} of block {}, which is out of range",
            block.index()
        ),
        TrustIrBodyRefusal::SiteNotAssert { found } => {
            format!("the obligation's site is a {found}, not an Assert")
        }
        TrustIrBodyRefusal::UnsupportedObligationKind(kind) => {
            format!("obligation kind {kind} is outside the lane")
        }
        TrustIrBodyRefusal::TemporalPropertyAttributed { machine, temporal } => format!(
            "the obligation names temporal property {temporal} of machine {machine}; \
             an Assert-site discharge cannot back that attribution"
        ),
        TrustIrBodyRefusal::VacuousPremises => {
            "the premises before the site are unsatisfiable, so no claim is made".to_string()
        }
    }
}

/// Map one body-lane obligation report onto its wire answer.
fn discharge_obligation_answer(
    report: &TrustIrBodyObligationReport,
) -> TrustVcNativeTrustIrDischargeObligation {
    // WITNESSES DO NOT CROSS. A refutation's `TrustIrBodyWitness` carries
    // concrete parameter values; those stay in the in-process report, for the
    // same reason `TrustVcNativeTrustIrVerdict` is not `VerifyResult` — a wire
    // report is not the place to leak counterexample bindings.
    let (outcome, detail) = match &report.verdict {
        TrustIrBodyVerdict::DischargedAdvisory { .. } => (
            TrustVcNativeTrustIrAdvisoryOutcome::DischargedAdvisory,
            None,
        ),
        TrustIrBodyVerdict::Refuted { .. } => (
            TrustVcNativeTrustIrAdvisoryOutcome::Refuted,
            Some("a solver counterexample replays as a failing site".to_string()),
        ),
        TrustIrBodyVerdict::RefutedIgnoringPriorAsserts { .. } => (
            TrustVcNativeTrustIrAdvisoryOutcome::RefutedIgnoringPriorAsserts,
            Some(
                "a solver counterexample fails the site, but an earlier, not-assumed Assert \
                 fails first"
                    .to_string(),
            ),
        ),
        TrustIrBodyVerdict::Unknown { reason, category } => (
            TrustVcNativeTrustIrAdvisoryOutcome::Unknown,
            Some(format!("{category}: {reason}")),
        ),
        TrustIrBodyVerdict::NotAnswerable(refusal) => (
            TrustVcNativeTrustIrAdvisoryOutcome::NotAnswerable,
            Some(render_refusal(refusal)),
        ),
    };
    TrustVcNativeTrustIrDischargeObligation {
        obligation_id: report.proof_id.index(),
        outcome,
        reading: report.reading.into(),
        detail,
    }
}

/// Fold per-obligation outcomes into the request verdict.
///
/// FAIL-CLOSED BY SHAPE: only an all-discharged, non-empty answer reaches
/// `DischargedAdvisory`; anything else is a refutation or not-answerable.
///
/// # `RefutedIgnoringPriorAsserts` reports at refutation grade, deliberately
///
/// That outcome may be a FALSE ALARM by its own definition
/// ([`TrustVcNativeTrustIrAdvisoryOutcome::RefutedIgnoringPriorAsserts`]): the
/// counterexample fails the site, but an earlier, deliberately-not-assumed
/// `Assert` fails first, so the witness may be unreachable and the site may in
/// truth be fine. Folding it to `DischargeRefuted` therefore erases a
/// distinction the per-obligation outcome keeps.
///
/// It is kept anyway, and the alternative was considered and rejected:
/// demoting it to `DischargeNotAnswerable` would move the request's exit class
/// from `Refuted` to `Unknown`, i.e. would make the seam QUIETER about a
/// possible real defect. This fold may only ever err loud. The distinction is
/// not lost — it is on the obligation's own `outcome` and `detail`, which the
/// wire report carries — it is simply not promoted to the verdict, because the
/// verdict's job is the floor and not the diagnosis.
///
/// A `NotJudged` outcome (a decoded answer) folds to `NotJudged` before
/// anything else: an answer nobody here judged carries no refutation and no
/// discharge.
fn discharge_verdict(
    obligations: &[TrustVcNativeTrustIrDischargeObligation],
) -> TrustVcNativeTrustIrVerdict {
    if obligations
        .iter()
        .any(|obligation| obligation.outcome == TrustVcNativeTrustIrAdvisoryOutcome::NotJudged)
    {
        return TrustVcNativeTrustIrVerdict::NotJudged;
    }
    if obligations.iter().any(|obligation| {
        matches!(
            obligation.outcome,
            TrustVcNativeTrustIrAdvisoryOutcome::Refuted
                | TrustVcNativeTrustIrAdvisoryOutcome::RefutedIgnoringPriorAsserts
        )
    }) {
        return TrustVcNativeTrustIrVerdict::DischargeRefuted;
    }
    if !obligations.is_empty()
        && obligations.iter().all(|obligation| {
            obligation.outcome == TrustVcNativeTrustIrAdvisoryOutcome::DischargedAdvisory
        })
    {
        return TrustVcNativeTrustIrVerdict::DischargedAdvisory;
    }
    TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
}

struct DischargeAnswerInput<'a> {
    request_id: u32,
    request_digest: String,
    trust_ir_module_digest: String,
    function: FuncId,
    body: &'a TrustIrBodyReport,
    cited: &'a BTreeSet<ProofId>,
}

/// Build the advisory answer from a body-lane report, restricted to the
/// obligations the request actually cited.
fn discharge_answer(input: DischargeAnswerInput<'_>) -> TrustVcNativeTrustIrDischargeAnswer {
    let DischargeAnswerInput {
        request_id,
        request_digest,
        trust_ir_module_digest,
        function,
        body,
        cited,
    } = input;
    let obligations = cited
        .iter()
        .map(|proof_id| match body.obligation(*proof_id) {
            Some(report) => discharge_obligation_answer(report),
            // Unreachable: every cited obligation was scope-checked against
            // this function above, and the lane reports exactly those. Fail
            // closed anyway rather than drop the obligation from the answer.
            None => TrustVcNativeTrustIrDischargeObligation {
                obligation_id: proof_id.index(),
                outcome: TrustVcNativeTrustIrAdvisoryOutcome::NotAnswerable,
                reading: TrustVcNativeTrustIrBodyReading::PinnedInterpreter,
                detail: Some(format!(
                    "request {request_id} cited obligation {} but the advisory body lane did not \
                     report it",
                    proof_id.index()
                )),
            },
        })
        .collect::<Vec<_>>();
    let havoc_instantiation_note = obligations
        .iter()
        .any(|obligation| {
            obligation.reading == TrustVcNativeTrustIrBodyReading::HavocInstantiatedUndef
        })
        .then(|| HAVOC_INSTANTIATION_NOTE.to_string());
    // THE LANE'S OWN "I DID NOT LOOK AT THIS" DISCLOSURE, CROSSING THE SEAM.
    // The in-process report has always carried it; it used to be dropped here,
    // so a consumer was told every cited obligation was discharged and told
    // nothing about the `Assert`s in the same function that nobody examined.
    // An advisory answer that knows strictly more than it says is the wrong
    // shape for this seam.
    let unexamined_asserts = body
        .unobligated_asserts
        .iter()
        .map(|position| TrustVcNativeTrustIrUnexaminedAssert {
            block: position.block.index(),
            inst_index: position.inst_index,
            label: UNOBLIGATED_ASSERT_LABEL.to_string(),
        })
        .collect::<Vec<_>>();
    TrustVcNativeTrustIrDischargeAnswer {
        authority: TrustVcNativeTrustIrDischargeAuthority::Advisory,
        lowering_witness: TrustVcNativeTrustIrLoweringWitness::None,
        lane_schema: TRUST_IR_BODY_LANE_SCHEMA.to_string(),
        request_digest,
        trust_ir_module_digest,
        function: function.index(),
        semantic_digest: body.semantic_digest.clone(),
        function_refusal: body.function_refusal.as_ref().map(render_refusal),
        havoc_instantiation_note,
        unexamined_asserts,
        obligations,
        ignored_inputs: TrustVcNativeTrustIrDischargeIgnoredInputs {
            statuses: body.ignored_inputs.statuses,
            certificates: body.ignored_inputs.certificates,
            formulas: body.ignored_inputs.formulas,
            annotations: body.ignored_inputs.annotations,
            summary_requires: body.ignored_inputs.summary_requires,
        },
    }
}

struct CertificateEvidenceInput<'a> {
    certificate_ref: &'a ProofCertificateRef,
    certificate: &'a ProofCertificate,
    obligation: &'a ProofObligation,
    /// `obligation.kind`, already known to be representable
    /// ([`importable_obligation_kind`]).
    obligation_kind: TrustVcNativeTrustIrObligationKind,
    lineage_node: Option<&'a ProofLineageNode>,
    request_provenance: &'a NativeRequestProvenance,
    trust_ir_module_digest: &'a str,
    request_digest: &'a str,
    compiler_facts_digest: &'a str,
    obligation_source: Option<&'a NativeObligationSource>,
    /// Which numeric assertion ids this bundle cannot use as identities; see
    /// [`crate::native_assertion_id::AssertionIdIndex`].
    assertion_ids: &'a crate::native_assertion_id::AssertionIdIndex,
    coverage: &'a CoverageJudge,
}

fn build_certificate_evidence(
    input: CertificateEvidenceInput<'_>,
) -> TrustVcNativeTrustIrCertificateEvidence {
    // THE EXPORT SEAM — the SAME rule as the discharge lane's `evidence_row`,
    // because an imported certificate is stamped onto an artifact by the same
    // `admit_native_proof_artifact` and joined by the same fleet coverage join.
    // Rendering E is read from the request that cites this certificate.
    let renderings = crate::native_assertion_id::AssertionIdRenderings::cited_by(
        input.obligation,
        input.obligation_source,
        &input.request_provenance.replay_context,
    );
    let corroboration =
        crate::native_assertion_id::AssertionIdCorroboration::of(&renderings, input.assertion_ids);
    let assertion_id = corroboration.licensed(&renderings);
    let independent_assertion_id = corroboration.independent(&renderings);
    let formula = input.obligation.formula.as_ref();
    let trusted = input.certificate.uses_trusted_evidence();
    let obligation_status = proof_status(input.obligation.status);
    let solver_identity = solver_identity(
        input.certificate,
        input.request_provenance,
        input.lineage_node,
    );
    let replay_metadata = input
        .lineage_node
        .and_then(TrustVcNativeTrustIrReplayMetadata::from_lineage_node)
        .or_else(|| {
            TrustVcNativeTrustIrReplayMetadata::from_request_provenance(input.request_provenance)
        });
    let suite_identity = suite_identity(input.request_provenance);
    let compiler_facts_binding = compiler_facts_binding(
        input.compiler_facts_digest,
        input.obligation.id.index(),
        input.obligation_source,
    );
    let release_admission =
        TrustVcNativeTrustIrCertificateAdmission::from_native_parts(AdmissionParts {
            assertion_id,
            trust_ir_obligation_id: input.obligation.id.index(),
            status: obligation_status,
            certificate: input.certificate,
            suite_identity: &suite_identity,
            solver_identity: &solver_identity,
            compiler_facts_binding: &compiler_facts_binding,
            coverage: input.coverage,
        });
    TrustVcNativeTrustIrCertificateEvidence {
        obligation_id: input.obligation.id.index(),
        assertion_id,
        independent_assertion_id,
        trust_ir_module_digest: input.trust_ir_module_digest.to_string(),
        request_digest: input.request_digest.to_string(),
        obligation_kind: input.obligation_kind,
        obligation_status,
        description: input.obligation.description.clone(),
        formula_schema: formula.map(|formula| formula.schema.clone()),
        formula_sort: formula.and_then(|formula| formula.sort.clone()),
        prover: input.certificate.prover.clone(),
        evidence_digest: input.certificate_ref.evidence_digest.to_string(),
        certificate_digest: input.certificate.stable_digest().to_string(),
        suite_identity,
        solver_identity,
        replay_metadata,
        compiler_facts_binding,
        evidence_kind: evidence_kind(&input.certificate.evidence),
        trusted,
        release_admission,
    }
}

fn lineage_node_for_certificate<'a>(
    lineage_nodes: &'a [ProofLineageNode],
    roots: &[ProofLineageId],
    certificate_ref: &ProofCertificateRef,
) -> Option<&'a ProofLineageNode> {
    let nodes = lineage_nodes
        .iter()
        .map(|node| (node.id, node))
        .collect::<BTreeMap<_, _>>();
    let mut stack = roots.to_vec();
    let mut visited = BTreeSet::new();
    while let Some(id) = stack.pop() {
        if !visited.insert(id) {
            continue;
        }
        let Some(node) = nodes.get(&id).copied() else {
            continue;
        };
        if node.certificates.iter().any(|cert| cert == certificate_ref) {
            return Some(node);
        }
        stack.extend(node.depends_on.iter().copied());
    }
    None
}

fn solver_identity(
    certificate: &ProofCertificate,
    request_provenance: &NativeRequestProvenance,
    lineage_node: Option<&ProofLineageNode>,
) -> TrustVcNativeSolverIdentity {
    let mut identity = TrustVcNativeSolverIdentity::new(certificate.prover.clone()).with_solvers(
        request_provenance
            .solver_identities()
            .iter()
            .map(native_tool_identity)
            .collect(),
    );
    if let Some(replay) = lineage_node
        .and_then(|node| node.replay.as_ref())
        .or(request_provenance.replay.as_ref())
    {
        identity = identity.with_replay_identity(
            replay.engine.clone(),
            replay.invocation.clone(),
            replay.transcript_digest.map(|digest| digest.to_string()),
        );
    }
    identity
}

fn suite_identity(
    request_provenance: &NativeRequestProvenance,
) -> TrustVcNativeVerifierSuiteIdentity {
    let expected = request_provenance.expected_verifier();
    let identity = TrustVcNativeVerifierSuiteIdentity::new(
        native_verifier_suite(request_provenance.verifier_suite()),
        expected.name.clone(),
        expected
            .revision
            .clone()
            .unwrap_or_else(|| "unreported".to_string()),
        expected
            .version
            .clone()
            .unwrap_or_else(|| "unreported".to_string()),
    );
    if let Some(digest) = expected.digest {
        identity.with_tool_digest(digest.to_string())
    } else {
        identity
    }
}

fn native_tool_identity(tool: &NativeToolIdentity) -> TrustVcNativeToolIdentity {
    let mut identity = TrustVcNativeToolIdentity::new(tool.name.clone());
    if let Some(version) = &tool.version {
        identity = identity.with_version(version.clone());
    }
    if let Some(revision) = &tool.revision {
        identity = identity.with_revision(revision.clone());
    }
    if let Some(digest) = tool.digest {
        identity = identity.with_digest(digest.to_string());
    }
    identity
}

fn native_verifier_suite(suite: NativeVerifierSuite) -> TrustVcNativeVerifierSuite {
    match suite {
        NativeVerifierSuite::Unknown => TrustVcNativeVerifierSuite::Unknown,
        NativeVerifierSuite::TrustVc => TrustVcNativeVerifierSuite::TrustVc,
        NativeVerifierSuite::TrustMc => TrustVcNativeVerifierSuite::TrustMc,
        NativeVerifierSuite::TrustWp => TrustVcNativeVerifierSuite::TrustWp,
        NativeVerifierSuite::AY => TrustVcNativeVerifierSuite::AY,
        NativeVerifierSuite::TRust => TrustVcNativeVerifierSuite::TRust,
        NativeVerifierSuite::TrustIr => TrustVcNativeVerifierSuite::TrustIr,
        NativeVerifierSuite::Other => TrustVcNativeVerifierSuite::Other,
    }
}

fn compiler_facts_binding(
    compiler_facts_digest: &str,
    obligation_id: u32,
    source: Option<&NativeObligationSource>,
) -> TrustVcNativeCompilerFactsBinding {
    let Some(source) = source else {
        return TrustVcNativeCompilerFactsBinding::default();
    };
    debug_assert_eq!(source.obligation.index(), obligation_id);

    TrustVcNativeCompilerFactsBinding::new(
        compiler_facts_digest,
        source.obligation.index(),
        source.function.map(|function| function.index()),
        source.span.map(native_source_span),
        obligation_cause(source.cause),
        source
            .monomorphization
            .map(|monomorphization| monomorphization.index()),
        source
            .facts
            .iter()
            .copied()
            .map(compiler_fact_ref)
            .collect(),
    )
    .with_assertion_id(source.assertion_id.map(|assertion_id| assertion_id.index()))
}

fn compiler_fact_ref(fact: NativeCompilerFactRef) -> TrustVcNativeCompilerFactRef {
    match fact {
        NativeCompilerFactRef::AdtLayout(id) => {
            TrustVcNativeCompilerFactRef::adt_layout(id.index())
        }
        NativeCompilerFactRef::FatPointer(id) => {
            TrustVcNativeCompilerFactRef::fat_pointer(id.index())
        }
        NativeCompilerFactRef::TraitObjectMetadata(id) => {
            TrustVcNativeCompilerFactRef::trait_object_metadata(id.index())
        }
        NativeCompilerFactRef::PointerOffset(id) => {
            TrustVcNativeCompilerFactRef::pointer_offset(id.index())
        }
        NativeCompilerFactRef::Cast(id) => TrustVcNativeCompilerFactRef::cast(id.index()),
        NativeCompilerFactRef::Monomorphization(id) => {
            TrustVcNativeCompilerFactRef::monomorphization(id.index())
        }
    }
}

fn native_source_span(span: SourceSpan) -> TrustVcNativeSourceSpan {
    TrustVcNativeSourceSpan::new(span.file, span.line, span.col)
}

fn obligation_cause(cause: NativeObligationCause) -> TrustVcNativeObligationCause {
    match cause {
        NativeObligationCause::Precondition => TrustVcNativeObligationCause::Precondition,
        NativeObligationCause::Postcondition => TrustVcNativeObligationCause::Postcondition,
        NativeObligationCause::Assert => TrustVcNativeObligationCause::Assert,
        NativeObligationCause::BoundsCheck => TrustVcNativeObligationCause::BoundsCheck,
        NativeObligationCause::OverflowCheck => TrustVcNativeObligationCause::OverflowCheck,
        NativeObligationCause::LayoutCheck => TrustVcNativeObligationCause::LayoutCheck,
        NativeObligationCause::CastCheck => TrustVcNativeObligationCause::CastCheck,
        NativeObligationCause::PointerOffset => TrustVcNativeObligationCause::PointerOffset,
        NativeObligationCause::BorrowCheck => TrustVcNativeObligationCause::BorrowCheck,
        NativeObligationCause::Translation => TrustVcNativeObligationCause::Translation,
        NativeObligationCause::Panic => TrustVcNativeObligationCause::Panic,
        NativeObligationCause::Other => TrustVcNativeObligationCause::Other,
        NativeObligationCause::Temporal => TrustVcNativeObligationCause::Other,
    }
}

/// The obligation kind an IMPORTED certificate is reported under, or a named
/// refusal when the import cannot state the obligation faithfully.
///
/// The body lane already refuses a spec-carrying obligation
/// (`TrustIrBodyRefusal::TemporalPropertyAttributed`) and every kind outside
/// its panic class; the Import/Merge certificate path used to do neither. It
/// filed `TemporalSafety`, `Liveness` and — through a `_` arm — every kind the
/// pinned trust-ir had grown since (`GiveBackRefinement`, `Termination`,
/// `Ownership`, `Custom`) as `PanicFreedom`, and then admitted the
/// certificate: a report that a liveness property was proved read as a
/// panic-freedom import. Refused here instead, before any evidence is built:
///
/// * a `spec` reference (trust-ir v46) names a temporal property this
///   certificate would be attributed to; nothing in an import report can
///   carry that attribution, so it would be dropped silently —
///   [`TrustEngineError::NativeTrustIrImportObligationAttributesTemporalProperty`];
/// * a kind with no faithful [`TrustVcNativeTrustIrObligationKind`] —
///   [`TrustEngineError::NativeTrustIrImportObligationKindUnrepresentable`].
fn importable_obligation_kind(
    request_id: u32,
    obligation: &ProofObligation,
) -> Result<TrustVcNativeTrustIrObligationKind, TrustEngineError> {
    if let Some(spec) = &obligation.spec {
        return Err(
            TrustEngineError::NativeTrustIrImportObligationAttributesTemporalProperty {
                request_id,
                obligation_id: obligation.id.index(),
                machine: spec.machine.clone(),
                temporal: spec.temporal.clone(),
            },
        );
    }
    obligation_kind(&obligation.kind).ok_or_else(|| {
        TrustEngineError::NativeTrustIrImportObligationKindUnrepresentable {
            request_id,
            obligation_id: obligation.id.index(),
            kind: obligation.kind.to_string(),
        }
    })
}

/// `None` = this kind has no faithful native label; the caller refuses it.
fn obligation_kind(kind: &ObligationKind) -> Option<TrustVcNativeTrustIrObligationKind> {
    match kind {
        ObligationKind::Precondition => Some(TrustVcNativeTrustIrObligationKind::Precondition),
        ObligationKind::Postcondition => Some(TrustVcNativeTrustIrObligationKind::Postcondition),
        ObligationKind::LoopInvariant => Some(TrustVcNativeTrustIrObligationKind::LoopInvariant),
        ObligationKind::TypeInvariant => Some(TrustVcNativeTrustIrObligationKind::TypeInvariant),
        ObligationKind::RefinementType => Some(TrustVcNativeTrustIrObligationKind::RefinementType),
        ObligationKind::TranslationValidation => {
            Some(TrustVcNativeTrustIrObligationKind::TranslationValidation)
        }
        ObligationKind::MemorySafety => Some(TrustVcNativeTrustIrObligationKind::MemorySafety),
        ObligationKind::PanicFreedom => Some(TrustVcNativeTrustIrObligationKind::PanicFreedom),
        // trust-ir defines both as panic-class obligations that "route
        // identically to `PanicFreedom`" (it *is* a panic-freedom obligation;
        // proof/obligations.rs at 4f09dab8). Filing them under their own
        // class loses the arithmetic-vs-bounds detail, not the claim.
        ObligationKind::ArithmeticSafety | ObligationKind::BoundsCheck => {
            Some(TrustVcNativeTrustIrObligationKind::PanicFreedom)
        }
        // Not panic-class, and no native label for any of them: a temporal
        // or liveness property, a give-back refinement, termination,
        // ownership/aliasing discipline, a producer-namespaced kind.
        ObligationKind::TemporalSafety
        | ObligationKind::Liveness
        | ObligationKind::GiveBackRefinement
        | ObligationKind::Termination
        | ObligationKind::Ownership
        | ObligationKind::Custom { .. } => None,
        // `ObligationKind` is `#[non_exhaustive]` in trust-ir, so this arm is
        // required. A kind trust-ir adds later is unrepresentable until
        // someone classifies it above — never panic-freedom by default.
        _ => None,
    }
}

fn proof_status(status: ProofStatus) -> TrustVcNativeArtifactObligationStatus {
    match status {
        ProofStatus::Pending => TrustVcNativeArtifactObligationStatus::Pending,
        ProofStatus::Discharged => TrustVcNativeArtifactObligationStatus::Discharged,
        ProofStatus::Failed => TrustVcNativeArtifactObligationStatus::Failed,
        ProofStatus::Trusted => TrustVcNativeArtifactObligationStatus::Trusted,
        // `Certified` is the kernel-checkable CIC tier: trust-ir says the
        // status is backed by a `ProofEvidence::CleanCic` payload a kernel can
        // re-check. It used to be filed as `Trusted` (a manual audit taken on
        // faith), which refused every Certified certificate as
        // `obligation_trusted` whatever its evidence. It is now its own status
        // and is judged ON ITS REPLAY: identity admission treats it like
        // `Discharged`, and release admission additionally needs THIS
        // certificate's own coverage to be established by trust-ir-build's
        // basis K — the in-process kernel replay of exactly this certificate
        // against the claim re-derived from its obligation, which upstream
        // runs for `Certified` and `Discharged` alike. The label alone admits
        // nothing: an SMT or `Trusted` certificate on a `Certified` obligation
        // is refused `certificate_coverage_basis_not_this_certificate`.
        ProofStatus::Certified => TrustVcNativeArtifactObligationStatus::Certified,
    }
}

fn evidence_kind(evidence: &ProofEvidence) -> TrustVcNativeTrustIrEvidenceKind {
    match evidence {
        ProofEvidence::SmtProof(_) => TrustVcNativeTrustIrEvidenceKind::SmtProof,
        ProofEvidence::LeanProof(_) => TrustVcNativeTrustIrEvidenceKind::LeanProof,
        ProofEvidence::KaniHarness(_) => TrustVcNativeTrustIrEvidenceKind::KaniHarness,
        ProofEvidence::GammaCrownBound { .. } => TrustVcNativeTrustIrEvidenceKind::GammaCrownBound,
        ProofEvidence::TranslationValidation { .. } => {
            TrustVcNativeTrustIrEvidenceKind::TranslationValidation
        }
        ProofEvidence::Trusted(_) => TrustVcNativeTrustIrEvidenceKind::Trusted,
        // Sibling trust-ir added `InheritedFromCallee` (cross-language proof
        // composition) after this crate's last sync. It is not self-justifying
        // ground evidence; surface it as `Trusted` until a dedicated native kind
        // is added. (Integration-verifier cross-crate seam fix.)
        ProofEvidence::InheritedFromCallee { .. } => TrustVcNativeTrustIrEvidenceKind::Trusted,
        // Sibling trust-ir added `CleanCic` (a kernel-checkable CIC proof term)
        // after this crate's last sync. There is no dedicated native CIC
        ProofEvidence::CleanCic { .. } => TrustVcNativeTrustIrEvidenceKind::CleanCic,
    }
}

/// The Import/Merge obligation gate, pinned directly.
///
/// Through [`TrustVcTrustEngine::consume_native_trust_ir_bundle`] this gate is
/// SECOND: at trust-ir 4f09dab8 upstream admits an imported TrustVc
/// certificate for a `Discharged` obligation only when a CleanCic term was
/// kernel-replayed for it, and the kernel grounder certifies only the four
/// contract kinds — so a temporal, liveness, termination, ownership or
/// panic-class obligation is refused upstream before this crate runs (see
/// `tests/native_trust_ir_bundle.rs`). The gate still has to hold on its own
/// the day upstream grows another authority, which is what these pin.
#[cfg(test)]
mod import_obligation_tests {
    use super::*;
    use trust_ir::proof::SpecObligationRef;

    fn obligation(kind: ObligationKind) -> ProofObligation {
        ProofObligation {
            id: ProofId::new(7),
            kind,
            status: ProofStatus::Discharged,
            description: "import gate".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
            spec: None,
        }
    }

    #[test]
    fn kinds_without_a_faithful_label_are_refused_by_name() {
        for kind in [
            ObligationKind::TemporalSafety,
            ObligationKind::Liveness,
            ObligationKind::GiveBackRefinement,
            ObligationKind::Termination,
            ObligationKind::Ownership,
            ObligationKind::Custom {
                namespace: "trust.concurrency".to_string(),
                name: "deadlock_freedom".to_string(),
            },
        ] {
            let label = kind.to_string();
            assert_eq!(
                importable_obligation_kind(3, &obligation(kind)),
                Err(
                    TrustEngineError::NativeTrustIrImportObligationKindUnrepresentable {
                        request_id: 3,
                        obligation_id: 7,
                        kind: label.clone(),
                    }
                ),
                "{label}"
            );
        }
    }

    #[test]
    fn representable_kinds_keep_their_label_and_panic_class_kinds_file_as_panic_freedom() {
        for (kind, expected) in [
            (
                ObligationKind::Precondition,
                TrustVcNativeTrustIrObligationKind::Precondition,
            ),
            (
                ObligationKind::Postcondition,
                TrustVcNativeTrustIrObligationKind::Postcondition,
            ),
            (
                ObligationKind::LoopInvariant,
                TrustVcNativeTrustIrObligationKind::LoopInvariant,
            ),
            (
                ObligationKind::TypeInvariant,
                TrustVcNativeTrustIrObligationKind::TypeInvariant,
            ),
            (
                ObligationKind::RefinementType,
                TrustVcNativeTrustIrObligationKind::RefinementType,
            ),
            (
                ObligationKind::TranslationValidation,
                TrustVcNativeTrustIrObligationKind::TranslationValidation,
            ),
            (
                ObligationKind::MemorySafety,
                TrustVcNativeTrustIrObligationKind::MemorySafety,
            ),
            (
                ObligationKind::PanicFreedom,
                TrustVcNativeTrustIrObligationKind::PanicFreedom,
            ),
            (
                ObligationKind::ArithmeticSafety,
                TrustVcNativeTrustIrObligationKind::PanicFreedom,
            ),
            (
                ObligationKind::BoundsCheck,
                TrustVcNativeTrustIrObligationKind::PanicFreedom,
            ),
        ] {
            let label = kind.to_string();
            assert_eq!(
                importable_obligation_kind(0, &obligation(kind)),
                Ok(expected),
                "{label}"
            );
        }
    }

    /// `spec` is refused before the kind is looked at: on a temporal kind,
    /// and on a kind the import could otherwise state.
    #[test]
    fn a_temporal_property_attribution_is_refused_whatever_the_kind() {
        for kind in [
            ObligationKind::Liveness,
            ObligationKind::TemporalSafety,
            ObligationKind::Postcondition,
        ] {
            let label = kind.to_string();
            let mut attributed = obligation(kind);
            attributed.spec = Some(SpecObligationRef::new("Mutex", "EventuallyReleased"));
            assert_eq!(
                importable_obligation_kind(1, &attributed),
                Err(
                    TrustEngineError::NativeTrustIrImportObligationAttributesTemporalProperty {
                        request_id: 1,
                        obligation_id: 7,
                        machine: "Mutex".to_string(),
                        temporal: "EventuallyReleased".to_string(),
                    }
                ),
                "{label}"
            );
        }
    }
}

#[cfg(test)]
mod verdict_tests {
    use super::*;

    /// Every verdict, worst-first. The fold must be total, and the two
    /// discharge-mode verdicts that DO carry news — a refutation and an
    /// advisory discharge — must sit on the right side of "clean pass".
    ///
    /// `DischargedAdvisory` sits ABOVE `CertificatesRejected` here, and that
    /// ordering is not cosmetic: see
    /// `the_fold_never_improves_an_exit_class`, which is the property this
    /// list has to satisfy and which the previous order violated.
    const WORST_FIRST: [TrustVcNativeTrustIrVerdict; 6] = [
        TrustVcNativeTrustIrVerdict::DischargeRefuted,
        TrustVcNativeTrustIrVerdict::NotJudged,
        TrustVcNativeTrustIrVerdict::DischargeNotAnswerable,
        TrustVcNativeTrustIrVerdict::DischargedAdvisory,
        TrustVcNativeTrustIrVerdict::CertificatesRejected,
        TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
    ];

    /// Rank of an exit class, worse is higher. The runner reads only the
    /// FOLDED verdict's exit class, so this is the scale that actually decides
    /// the process exit code.
    const fn exit_rank(class: TrustVcNativeTrustIrExitClass) -> u8 {
        match class {
            TrustVcNativeTrustIrExitClass::Ok => 0,
            TrustVcNativeTrustIrExitClass::Rejected => 1,
            TrustVcNativeTrustIrExitClass::Unknown => 2,
            TrustVcNativeTrustIrExitClass::Refuted => 3,
        }
    }

    /// THE PROPERTY THE RUNNER DEPENDS ON, which the severity ranking alone
    /// does not state: folding two verdicts must never produce a BETTER exit
    /// class than either input.
    ///
    /// The ranking violated this exactly once, and it was reachable: with
    /// `DischargedAdvisory` ranked below `CertificatesRejected`, a bundle
    /// pairing one advisory discharge (exit class `Unknown`) with one
    /// rejected certificate (then exit class `Ok`) folded to
    /// `CertificatesRejected` and `trust_vc-trust-runner` exited **0** — an
    /// advisory answer with no lowering witness laundered into a successful
    /// process exit. `the_rollup_is_worst_wins_and_order_independent` could
    /// not catch it, because it checks the fold against the same ranking it is
    /// testing.
    #[test]
    fn the_fold_never_improves_an_exit_class() {
        for left in WORST_FIRST {
            for right in WORST_FIRST {
                let folded = left.worse_of(right);
                let floor = exit_rank(left.exit_class()).max(exit_rank(right.exit_class()));
                assert!(
                    exit_rank(folded.exit_class()) >= floor,
                    "{left:?} ({:?}) folded with {right:?} ({:?}) gave {folded:?} ({:?}), \
                     which exits better than both",
                    left.exit_class(),
                    right.exit_class(),
                    folded.exit_class(),
                );
            }
        }
    }

    /// MERGED 2026-09-23: the same property over EVERY variant, including the
    /// `native_discharge` lane's three. `WORST_FIRST` above is the advisory
    /// lane's list and does not name them, so without this the monotonicity
    /// that the runner's exit code depends on would be unchecked for half the
    /// enum.
    #[test]
    fn the_fold_never_improves_an_exit_class_over_every_variant() {
        const ALL: [TrustVcNativeTrustIrVerdict; 8] = [
            TrustVcNativeTrustIrVerdict::Discharged,
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
            TrustVcNativeTrustIrVerdict::CertificatesRejected,
            TrustVcNativeTrustIrVerdict::DischargedAdvisory,
            TrustVcNativeTrustIrVerdict::DischargeDeclined,
            TrustVcNativeTrustIrVerdict::DischargeNotAnswerable,
            TrustVcNativeTrustIrVerdict::Refuted,
            TrustVcNativeTrustIrVerdict::DischargeRefuted,
        ];
        for left in ALL {
            for right in ALL {
                let folded = left.worse_of(right);
                assert_eq!(folded, right.worse_of(left), "{left:?} vs {right:?}");
                let floor = exit_rank(left.exit_class()).max(exit_rank(right.exit_class()));
                assert!(
                    exit_rank(folded.exit_class()) >= floor,
                    "{left:?} folded with {right:?} gave {folded:?}, which exits better than both"
                );
            }
        }
        // The native_discharge lane's own rules, kept across the merge.
        use TrustVcNativeTrustIrVerdict as V;
        assert_eq!(V::Discharged.worse_of(V::Discharged), V::Discharged);
        assert_eq!(
            V::Discharged.worse_of(V::CertificatesAdmitted),
            V::CertificatesAdmitted
        );
        assert_eq!(
            V::DischargeDeclined.worse_of(V::CertificatesRejected),
            V::DischargeDeclined
        );
        assert_eq!(V::Refuted.worse_of(V::DischargeDeclined), V::Refuted);
    }

    /// THE EXACT PAIR that laundered to exit 0 before the ranking was fixed.
    /// Named on its own so a regression says what broke, not just that a
    /// property failed.
    #[test]
    fn an_advisory_discharge_beside_a_rejected_certificate_does_not_exit_zero() {
        for pair in [
            [
                TrustVcNativeTrustIrVerdict::CertificatesRejected,
                TrustVcNativeTrustIrVerdict::DischargedAdvisory,
            ],
            [
                TrustVcNativeTrustIrVerdict::DischargedAdvisory,
                TrustVcNativeTrustIrVerdict::CertificatesRejected,
            ],
        ] {
            let folded = pair[0].worse_of(pair[1]);
            assert_eq!(
                folded,
                TrustVcNativeTrustIrVerdict::DischargedAdvisory,
                "{pair:?}"
            );
            assert_eq!(
                folded.exit_class(),
                TrustVcNativeTrustIrExitClass::Unknown,
                "the runner must not exit 0 for {pair:?}"
            );
        }
    }

    /// The rollup is worst-wins over EVERY pair, in both argument orders.
    ///
    /// The pairwise match this replaced had to be re-reasoned each time a
    /// variant was added, and adding two at once is exactly when that goes
    /// wrong.
    #[test]
    fn the_rollup_is_worst_wins_and_order_independent() {
        for (left_rank, left) in WORST_FIRST.iter().enumerate() {
            for (right_rank, right) in WORST_FIRST.iter().enumerate() {
                let expected = WORST_FIRST[left_rank.min(right_rank)];
                assert_eq!(left.worse_of(*right), expected, "{left:?} vs {right:?}");
                assert_eq!(right.worse_of(*left), expected, "{right:?} vs {left:?}");
            }
        }
    }

    /// ONE advisory discharge among any number of admitted certificates still
    /// drags the bundle off a clean pass. This is the containment on the
    /// rollup: an advisory answer cannot be averaged away.
    #[test]
    fn an_advisory_discharge_cannot_be_averaged_into_a_pass() {
        let rollup = [
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
            TrustVcNativeTrustIrVerdict::DischargedAdvisory,
        ]
        .into_iter()
        .fold(
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
            TrustVcNativeTrustIrVerdict::worse_of,
        );
        assert_eq!(rollup, TrustVcNativeTrustIrVerdict::DischargedAdvisory);
        assert!(!rollup.is_ok());
        assert_eq!(rollup.exit_class(), TrustVcNativeTrustIrExitClass::Unknown);
    }

    /// A discharge answer with no obligations, or a mixed one, fails closed.
    #[test]
    fn the_discharge_fold_fails_closed() {
        fn obligation(
            outcome: TrustVcNativeTrustIrAdvisoryOutcome,
        ) -> TrustVcNativeTrustIrDischargeObligation {
            TrustVcNativeTrustIrDischargeObligation {
                obligation_id: 0,
                outcome,
                reading: TrustVcNativeTrustIrBodyReading::PinnedInterpreter,
                detail: None,
            }
        }
        use TrustVcNativeTrustIrAdvisoryOutcome as Outcome;

        // Empty is NOT a vacuous pass.
        assert_eq!(
            discharge_verdict(&[]),
            TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
        );
        // An unknown among discharges is not a discharge.
        assert_eq!(
            discharge_verdict(&[
                obligation(Outcome::DischargedAdvisory),
                obligation(Outcome::Unknown),
            ]),
            TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
        );
        // A refutation dominates, even alongside discharges and refusals.
        assert_eq!(
            discharge_verdict(&[
                obligation(Outcome::DischargedAdvisory),
                obligation(Outcome::NotAnswerable),
                obligation(Outcome::RefutedIgnoringPriorAsserts),
            ]),
            TrustVcNativeTrustIrVerdict::DischargeRefuted
        );
        // All-discharged is the ONLY route to the advisory verdict.
        assert_eq!(
            discharge_verdict(&[
                obligation(Outcome::DischargedAdvisory),
                obligation(Outcome::DischargedAdvisory),
            ]),
            TrustVcNativeTrustIrVerdict::DischargedAdvisory
        );
        // A decoded (not judged) outcome dominates even a claimed refutation:
        // nobody here judged the answer.
        assert_eq!(
            discharge_verdict(&[obligation(Outcome::Refuted), obligation(Outcome::NotJudged),]),
            TrustVcNativeTrustIrVerdict::NotJudged
        );
    }
}

#[cfg(test)]
mod wire_shape_tests {
    use super::*;

    /// The shape predicate the deserializer enforces, stated directly.
    ///
    /// `verdict` used to be `#[serde(default)]`ed to `CertificatesAdmitted`,
    /// so a report that merely OMITTED the key read as a clean pass — and a
    /// discharge-mode report with its advisory answer intact could carry that
    /// pass. `authority` was required and defaultless, but `authority` gates
    /// nothing; `is_ok()` and `exit_class()` read `verdict`.
    #[test]
    fn a_discharge_report_cannot_wear_a_certificate_mode_verdict() {
        use TrustVcNativeTrustIrRequestMode as Mode;
        use TrustVcNativeTrustIrVerdict as Verdict;

        // Accepted: the three shapes the producer actually builds, and the
        // `NotJudged` a decoded report re-encodes as.
        for verdict in [
            Verdict::DischargedAdvisory,
            Verdict::DischargeRefuted,
            Verdict::DischargeNotAnswerable,
            Verdict::NotJudged,
        ] {
            check_request_report_shape(Mode::DischargeProofObligations, verdict, true, true)
                .unwrap_or_else(|error| panic!("{verdict:?} must be admissible: {error}"));
        }
        for verdict in [Verdict::CertificatesAdmitted, Verdict::CertificatesRejected] {
            check_request_report_shape(Mode::ImportProofCertificates, verdict, false, true)
                .unwrap_or_else(|error| panic!("{verdict:?} must be admissible: {error}"));
            check_request_report_shape(Mode::MergeProofCertificates, verdict, false, false)
                .unwrap_or_else(|error| panic!("{verdict:?} must be admissible: {error}"));
        }

        // Refused: a discharge report wearing either certificate-mode verdict.
        for verdict in [Verdict::CertificatesAdmitted, Verdict::CertificatesRejected] {
            check_request_report_shape(Mode::DischargeProofObligations, verdict, true, true)
                .expect_err("a discharge report must not wear a certificate-mode verdict");
        }
        // Refused: a certificate report wearing a discharge verdict.
        for verdict in [
            Verdict::DischargedAdvisory,
            Verdict::DischargeRefuted,
            Verdict::DischargeNotAnswerable,
            Verdict::NotJudged,
        ] {
            check_request_report_shape(Mode::ImportProofCertificates, verdict, false, true)
                .expect_err("a certificate report must not wear a discharge verdict");
        }
        // Refused: a discharge report with no answer, or carrying evidence.
        check_request_report_shape(
            Mode::DischargeProofObligations,
            Verdict::DischargedAdvisory,
            false,
            true,
        )
        .expect_err("a discharge report must carry its answer");
        check_request_report_shape(
            Mode::DischargeProofObligations,
            Verdict::DischargedAdvisory,
            true,
            false,
        )
        .expect_err("a discharge report must carry no certificate evidence");
        // Refused: a certificate report carrying a discharge answer.
        check_request_report_shape(
            Mode::ImportProofCertificates,
            Verdict::CertificatesAdmitted,
            true,
            true,
        )
        .expect_err("a certificate report must not carry a discharge answer");
    }

    fn bundle_report(verdict: TrustVcNativeTrustIrVerdict) -> TrustVcNativeTrustIrBundleReport {
        TrustVcNativeTrustIrBundleReport {
            producer: "Trust".to_string(),
            input_kind: TrustVcNativeTrustIrInputKind::TrustIrModule,
            input_digest: None,
            trust_ir_module_digest: "sha256:00".to_string(),
            compiler_facts_digest: "sha256:01".to_string(),
            module_name: "demo".to_string(),
            requests: Vec::new(),
            verdict,
            produced_certificates: Vec::new(),
            produced_evidence_bundles: Vec::new(),
        }
    }

    /// A FUNCTION CALLED `validate_` MUST NOT ANSWER `Ok(())` FOR A REFUTATION.
    ///
    /// `validate_native_trust_ir_bundle` used to be
    /// `consume_native_trust_ir_bundle(..).map(|_| ())`, discarding the whole
    /// report. That was harmless while every non-`Err` outcome was a
    /// certificate import; a bundle whose discharge request comes back
    /// `DischargeRefuted` — a genuine counterexample — would have validated.
    ///
    /// Nor for a REJECTED rollup: `CertificatesRejected` used to validate
    /// (its exit class was `Ok`), so a bundle none of whose certificates was
    /// release grade came back `Ok(())` from a function whose own doc says
    /// that means a clean pass.
    #[test]
    fn only_an_ok_exit_class_validates() {
        check_bundle_report_is_clean(&bundle_report(
            TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
        ))
        .unwrap_or_else(|error| panic!("CertificatesAdmitted must still validate: {error}"));
        for verdict in [
            TrustVcNativeTrustIrVerdict::CertificatesRejected,
            TrustVcNativeTrustIrVerdict::DischargeRefuted,
            TrustVcNativeTrustIrVerdict::DischargedAdvisory,
            TrustVcNativeTrustIrVerdict::DischargeNotAnswerable,
            TrustVcNativeTrustIrVerdict::NotJudged,
        ] {
            match check_bundle_report_is_clean(&bundle_report(verdict)) {
                Err(TrustEngineError::NativeTrustIrBundleVerdictNotClean { module, .. }) => {
                    assert_eq!(module, "demo");
                }
                other => panic!("{verdict:?} must not validate, got {other:?}"),
            }
        }
    }

    /// The rollup is RE-DERIVED on the way in, so a hand-written bundle report
    /// cannot declare a verdict its own requests do not support.
    #[test]
    fn a_bundle_report_cannot_declare_a_verdict_its_requests_do_not_support() {
        let request = |verdict| TrustVcNativeTrustIrRequestReport {
            request_id: 0,
            mode: TrustVcNativeTrustIrRequestMode::DischargeProofObligations,
            lineage_roots: Vec::new(),
            obligations: Vec::new(),
            proof_evidence: Vec::new(),
            advisory_discharge: None,
            verdict,
            discharge: Vec::new(),
        };
        // Empty is not a vacuous pass; it has no rollup at all.
        assert_eq!(rollup_verdict(&[]), None);
        assert_eq!(
            rollup_verdict(&[
                request(TrustVcNativeTrustIrVerdict::CertificatesAdmitted),
                request(TrustVcNativeTrustIrVerdict::DischargedAdvisory),
            ]),
            Some(TrustVcNativeTrustIrVerdict::DischargedAdvisory)
        );
        assert_eq!(
            rollup_verdict(&[
                request(TrustVcNativeTrustIrVerdict::CertificatesRejected),
                request(TrustVcNativeTrustIrVerdict::DischargedAdvisory),
            ]),
            Some(TrustVcNativeTrustIrVerdict::DischargedAdvisory),
            "the pair that used to fold to an Ok-exiting verdict"
        );
    }
}
