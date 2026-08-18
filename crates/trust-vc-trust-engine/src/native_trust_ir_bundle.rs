//! Direct consumer for upstream `trust_ir::NativeVerificationBundle` requests.
//!
//! This module handles the typed `NativeVerificationRequest::TrustVc` variant
//! directly. It does not route through adapter-name strings or source-text
//! verifier payloads.

use crate::{
    TrustEngineError, TrustVcNativeArtifactObligationStatus, TrustVcNativeCompilerFactRef,
    TrustVcNativeCompilerFactsBinding, TrustVcNativeObligationCause, TrustVcNativeProofArtifact,
    TrustVcNativeProofArtifactInput, TrustVcNativeSolverIdentity, TrustVcNativeSourceSpan,
    TrustVcNativeToolIdentity, TrustVcNativeVerifierSuite, TrustVcNativeVerifierSuiteIdentity,
    TrustVcTrustEngine,
};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::{
    ObligationKind, ProofCertificate, ProofCertificateRef, ProofEvidence, ProofId, ProofLineageId,
    ProofLineageNode, ProofObligation, ProofStatus, SourceSpan,
};
// The `Native*` / `TrustVc*` request-bundle types live in `trust_ir::request`;
// their crate-root re-exports are gated behind trust-ir's default-on
// `request-reexports` feature (audit #55), which trust-vc builds with disabled —
// so import them via the always-available canonical `request::` path.
use trust_ir::request::{
    NativeAdapterInput, NativeBundleProducer, NativeCompilerFactRef, NativeObligationCause,
    NativeObligationSource, NativeRequestProvenance, NativeToolIdentity, NativeVerificationBundle,
    NativeVerificationRequest, NativeVerifierSuite, TrustVcNativeRequest, TrustVcVerificationMode,
};

/// Report produced after TrustVc consumes native TrustIr TrustVc requests.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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
    /// Worst-wins rollup over `requests`.
    #[serde(default = "default_verdict")]
    verdict: TrustVcNativeTrustIrVerdict,
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
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrRequestReport {
    request_id: u32,
    mode: TrustVcNativeTrustIrRequestMode,
    lineage_roots: Vec<u32>,
    proof_evidence: Vec<TrustVcNativeTrustIrCertificateEvidence>,
    /// `serde(default)` so a report written before this field existed still
    /// deserializes; the default is the permissive verdict, which is safe only
    /// because it is never used for a report this crate PRODUCES.
    #[serde(default = "default_verdict")]
    verdict: TrustVcNativeTrustIrVerdict,
}

const fn default_verdict() -> TrustVcNativeTrustIrVerdict {
    TrustVcNativeTrustIrVerdict::CertificatesAdmitted
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
/// it is most dangerous exactly when a discharge lane is half-built: the mode is
/// expressible today and NOT answerable, so without this the honest answer
/// ("trust-vc cannot do this yet") would have been reported as a pass.
///
/// Deliberately NOT `trust_vc_core::VerifyResult`: that type has no `Serialize`,
/// would leak counterexample bindings into a wire report, and has no variant
/// meaning "discharged nothing".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeTrustIrVerdict {
    /// Every cited certificate was admitted at release grade.
    CertificatesAdmitted,
    /// The request was structurally valid, but at least one certificate was
    /// refused release grade (e.g. it carries trusted evidence).
    CertificatesRejected,
    /// The request asked trust-vc to DISCHARGE obligations, which it cannot yet
    /// do. Reported explicitly rather than as an empty success.
    DischargeNotAnswerable,
}

impl TrustVcNativeTrustIrVerdict {
    /// Is this verdict a clean pass?
    ///
    /// Used for the bundle rollup and the process exit code, so the two can
    /// never disagree about what counts as success.
    pub const fn is_ok(self) -> bool {
        matches!(self, Self::CertificatesAdmitted)
    }

    /// Worst-wins fold, so one bad request cannot be averaged away by good ones.
    /// Order of severity: not-answerable > rejected > admitted.
    fn worse_of(self, other: Self) -> Self {
        match (self, other) {
            (Self::DischargeNotAnswerable, _) | (_, Self::DischargeNotAnswerable) => {
                Self::DischargeNotAnswerable
            }
            (Self::CertificatesRejected, _) | (_, Self::CertificatesRejected) => {
                Self::CertificatesRejected
            }
            _ => Self::CertificatesAdmitted,
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
    /// NOT YET ANSWERABLE. Nothing in this crate lowers a trust-ir function body
    /// to trust-vc's IR, so a discharge request currently fails LOUDLY on the
    /// existing certificate requirements — which is the correct behaviour until
    /// a discharge engine and a verdict channel exist. Do not relax
    /// `build_request_report`'s missing-certificate check to accommodate it: the
    /// report structs carry no verdict field and `report_exit_code` returns
    /// EXIT_OK unconditionally, so a silently-accepted discharge request would
    /// read as SUCCESS.
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

/// One proof certificate accepted from a native TrustIr TrustVc request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrCertificateEvidence {
    obligation_id: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    assertion_id: Option<u32>,
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

impl TrustVcNativeTrustIrCertificateEvidence {
    /// Return the TrustIr proof-obligation id.
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }

    /// Return the native frontend assertion id carried by TrustIr, if present.
    pub const fn native_assertion_id(&self) -> Option<u32> {
        self.assertion_id
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
    pub fn admit_native_proof_artifact(&self) -> TrustVcNativeProofArtifact {
        self.admit_proof_artifact(
            self.assertion_id
                .map(|assertion_id| assertion_id.to_string())
                .unwrap_or_default(),
        )
    }

    /// Bind this native certificate evidence to an explicit assertion id.
    ///
    /// This remains available for older native bundles and callers that keep a
    /// separate assertion-id side table. Prefer [`Self::admit_native_proof_artifact`]
    /// when the TrustIr source mapping carries `NativeObligationSource.assertion_id`.
    pub fn admit_proof_artifact(
        &self,
        assertion_id: impl Into<String>,
    ) -> TrustVcNativeProofArtifact {
        TrustVcNativeProofArtifact::new(
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
            .with_compiler_facts_binding(self.compiler_facts_binding.clone()),
        )
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
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeTrustIrCertificateAdmission {
    #[serde(default)]
    status: TrustVcNativeTrustIrCertificateAdmissionStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    rejection_reasons: Vec<TrustVcNativeTrustIrCertificateRejection>,
}

impl Default for TrustVcNativeTrustIrCertificateAdmission {
    fn default() -> Self {
        Self {
            status: TrustVcNativeTrustIrCertificateAdmissionStatus::Unspecified,
            rejection_reasons: Vec::new(),
        }
    }
}

impl TrustVcNativeTrustIrCertificateAdmission {
    fn from_native_parts(
        assertion_id: Option<u32>,
        trust_ir_obligation_id: u32,
        status: TrustVcNativeArtifactObligationStatus,
        trusted: bool,
        suite_identity: &TrustVcNativeVerifierSuiteIdentity,
        solver_identity: &TrustVcNativeSolverIdentity,
        compiler_facts_binding: &TrustVcNativeCompilerFactsBinding,
    ) -> Self {
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
            TrustVcNativeArtifactObligationStatus::Discharged => {}
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

        Self {
            status: if rejection_reasons.is_empty() {
                TrustVcNativeTrustIrCertificateAdmissionStatus::Admissible
            } else {
                TrustVcNativeTrustIrCertificateAdmissionStatus::Rejected
            },
            rejection_reasons,
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
}

impl TrustVcTrustEngine {
    /// Validate a native TrustIr bundle and ensure it contains consumable TrustVc requests.
    pub fn validate_native_trust_ir_bundle(
        &self,
        bundle: &NativeVerificationBundle,
    ) -> Result<(), TrustEngineError> {
        self.consume_native_trust_ir_bundle(bundle).map(|_| ())
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
        validate_upstream_bundle(bundle)?;
        validate_trust_vc_release_evidence_bundles(bundle)?;

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

        let mut requests = Vec::new();
        for request in &bundle.requests {
            let request_digest = request.stable_digest().to_string();
            if let NativeVerificationRequest::TrustVc(trust_vc_request) = request {
                requests.push(build_request_report(
                    trust_vc_request,
                    &request_digest,
                    &obligations,
                    &certificates,
                    &trust_ir_module_digest,
                    &compiler_facts_digest,
                    &compiler_fact_sources,
                    &bundle.lineage.nodes,
                )?);
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
            // Worst-wins. An empty request list cannot reach here — the
            // no-TrustVc-request case is refused above — so folding from
            // `CertificatesAdmitted` cannot manufacture a pass out of nothing.
            verdict: requests
                .iter()
                .map(TrustVcNativeTrustIrRequestReport::verdict)
                .fold(
                    TrustVcNativeTrustIrVerdict::CertificatesAdmitted,
                    TrustVcNativeTrustIrVerdict::worse_of,
                ),
            requests,
        })
    }
}

fn validate_upstream_bundle(bundle: &NativeVerificationBundle) -> Result<(), TrustEngineError> {
    bundle
        .validate()
        .map_err(|errors| TrustEngineError::InvalidNativeTrustIrBundle {
            errors: errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("; "),
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
    }
}

fn build_request_report(
    request: &TrustVcNativeRequest,
    request_digest: &str,
    obligations: &BTreeMap<ProofId, &ProofObligation>,
    certificates: &BTreeMap<ProofCertificateRef, &ProofCertificate>,
    trust_ir_module_digest: &str,
    compiler_facts_digest: &str,
    compiler_fact_sources: &BTreeMap<ProofId, &NativeObligationSource>,
    lineage_nodes: &[ProofLineageNode],
) -> Result<TrustVcNativeTrustIrRequestReport, TrustEngineError> {
    let request_id = request.id.index();
    let requested_obligations = request.obligations.iter().copied().collect::<BTreeSet<_>>();
    let certified_obligations = request
        .certificates
        .iter()
        .map(|certificate| certificate.obligation)
        .collect::<BTreeSet<_>>();

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

    let mut proof_evidence = Vec::new();
    for certificate_ref in &request.certificates {
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
        let lineage_node =
            lineage_node_for_certificate(lineage_nodes, &request.lineage_roots, certificate_ref);
        proof_evidence.push(build_certificate_evidence(CertificateEvidenceInput {
            certificate_ref,
            certificate,
            obligation,
            lineage_node,
            request_provenance: &request.provenance,
            trust_ir_module_digest,
            request_digest,
            compiler_facts_digest,
            obligation_source: compiler_fact_sources.get(&obligation.id).copied(),
        }));
    }

    // Discharge is unconditionally not-answerable: nothing in this crate lowers
    // a trust-ir function body, so an empty evidence list means "could not", not
    // "nothing to do". Import/Merge fold their certificates' release admission.
    let verdict = match request.mode {
        TrustVcVerificationMode::DischargeProofObligations => {
            TrustVcNativeTrustIrVerdict::DischargeNotAnswerable
        }
        TrustVcVerificationMode::ImportProofCertificates
        | TrustVcVerificationMode::MergeProofCertificates => {
            if proof_evidence
                .iter()
                .all(|evidence| evidence.release_admission().is_admissible())
            {
                TrustVcNativeTrustIrVerdict::CertificatesAdmitted
            } else {
                TrustVcNativeTrustIrVerdict::CertificatesRejected
            }
        }
    };

    Ok(TrustVcNativeTrustIrRequestReport {
        request_id,
        mode: request.mode.into(),
        lineage_roots: request
            .lineage_roots
            .iter()
            .map(|root| root.index())
            .collect(),
        proof_evidence,
        verdict,
    })
}

struct CertificateEvidenceInput<'a> {
    certificate_ref: &'a ProofCertificateRef,
    certificate: &'a ProofCertificate,
    obligation: &'a ProofObligation,
    lineage_node: Option<&'a ProofLineageNode>,
    request_provenance: &'a NativeRequestProvenance,
    trust_ir_module_digest: &'a str,
    request_digest: &'a str,
    compiler_facts_digest: &'a str,
    obligation_source: Option<&'a NativeObligationSource>,
}

fn build_certificate_evidence(
    input: CertificateEvidenceInput<'_>,
) -> TrustVcNativeTrustIrCertificateEvidence {
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
    let release_admission = TrustVcNativeTrustIrCertificateAdmission::from_native_parts(
        input
            .obligation_source
            .and_then(|source| source.assertion_id.map(|assertion_id| assertion_id.index())),
        input.obligation.id.index(),
        obligation_status,
        trusted,
        &suite_identity,
        &solver_identity,
        &compiler_facts_binding,
    );
    TrustVcNativeTrustIrCertificateEvidence {
        obligation_id: input.obligation.id.index(),
        assertion_id: input
            .obligation_source
            .and_then(|source| source.assertion_id.map(|assertion_id| assertion_id.index())),
        trust_ir_module_digest: input.trust_ir_module_digest.to_string(),
        request_digest: input.request_digest.to_string(),
        obligation_kind: obligation_kind(&input.obligation.kind),
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

fn obligation_kind(kind: &ObligationKind) -> TrustVcNativeTrustIrObligationKind {
    match kind {
        ObligationKind::Precondition => TrustVcNativeTrustIrObligationKind::Precondition,
        ObligationKind::Postcondition => TrustVcNativeTrustIrObligationKind::Postcondition,
        ObligationKind::LoopInvariant => TrustVcNativeTrustIrObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant => TrustVcNativeTrustIrObligationKind::TypeInvariant,
        ObligationKind::RefinementType => TrustVcNativeTrustIrObligationKind::RefinementType,
        ObligationKind::TranslationValidation => {
            TrustVcNativeTrustIrObligationKind::TranslationValidation
        }
        ObligationKind::MemorySafety => TrustVcNativeTrustIrObligationKind::MemorySafety,
        // Trust (trust-ir-spine item T1): the routing-grade panic-class kinds
        // `ArithmeticSafety`/`BoundsCheck` are panic-freedom obligations. They
        // exist only in the Trust superproject's trust-ir (added on an unmerged
        // branch, commits d435468/1c26b9c) and NOT in the published
        // `alabsystems/trust-ir` main that this crate pins, so naming them
        // here breaks the standalone build. `ObligationKind` is
        // `#[non_exhaustive]`, and the catch-all below maps any unrecognized
        // kind (including these two, when the superproject trust-ir provides
        // them) to `PanicFreedom` identically — so behavior is unchanged in
        // both the standalone and superproject builds.
        ObligationKind::PanicFreedom => TrustVcNativeTrustIrObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety | ObligationKind::Liveness => {
            TrustVcNativeTrustIrObligationKind::PanicFreedom
        }
        // In the superproject's trust-ir, `ObligationKind` is `#[non_exhaustive]`,
        // so this wildcard is required and reachable there — it absorbs
        // `ArithmeticSafety`/`BoundsCheck` and any future kind onto panic-freedom.
        // Against the pinned public trust-ir main the explicit arms above are
        // exhaustive, making this wildcard unreachable in the standalone build;
        // allow the lint so standalone stays warning-clean without dropping the
        // wildcard the superproject build requires.
        #[allow(unreachable_patterns)]
        _ => TrustVcNativeTrustIrObligationKind::PanicFreedom,
    }
}

fn proof_status(status: ProofStatus) -> TrustVcNativeArtifactObligationStatus {
    match status {
        ProofStatus::Pending => TrustVcNativeArtifactObligationStatus::Pending,
        ProofStatus::Discharged => TrustVcNativeArtifactObligationStatus::Discharged,
        ProofStatus::Failed => TrustVcNativeArtifactObligationStatus::Failed,
        ProofStatus::Trusted => TrustVcNativeArtifactObligationStatus::Trusted,
        // Sibling trust-ir added `Certified` (the kernel-checkable CIC proof
        // tier, strictly stronger than `Trusted`) after this crate's last sync.
        // The native status enum has no `Certified` tier yet; surface it as the
        // strongest available accepted status (`Trusted`). Sound because
        // `Certified` is at least as strong as `Trusted`, so this never
        // over-claims an obligation's proof strength.
        ProofStatus::Certified => TrustVcNativeArtifactObligationStatus::Trusted,
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
