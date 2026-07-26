// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed native proof-artifact admission shared by TrustIr bundle consumers.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fmt::Write as _;

/// Schema version for native verifier proof-object fingerprints.
pub const TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION: u32 = 6;

/// Native verifier suite that produced a proof artifact.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeVerifierSuite {
    /// Missing suite identity from an older serialized payload.
    #[default]
    Unknown,
    /// TrustVc/Trust proof engine.
    #[serde(alias = "trust-vc")]
    TrustVc,
    /// TrustIr-native proof producer.
    #[serde(alias = "trust-ir")]
    TrustIr,
    /// TrustMc verifier suite.
    #[serde(alias = "trust-mc")]
    TrustMc,
    /// TrustWp verifier suite.
    #[serde(alias = "trust-wp")]
    TrustWp,
    /// ay SMT solver or proof checker.
    #[serde(rename = "ay")]
    AY,
    /// tRust native verifier or producer suite.
    #[serde(rename = "tRust", alias = "t_rust")]
    TRust,
    /// Other typed native suite.
    Other,
}

/// Stable suite identity bound into a native proof object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeVerifierSuiteIdentity {
    suite: TrustVcNativeVerifierSuite,
    name: String,
    producer: String,
    version: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    tool_digest: Option<String>,
}

impl Default for TrustVcNativeVerifierSuiteIdentity {
    fn default() -> Self {
        Self {
            suite: TrustVcNativeVerifierSuite::Unknown,
            name: "unknown".to_string(),
            producer: "unknown".to_string(),
            version: "unknown".to_string(),
            tool_digest: None,
        }
    }
}

impl TrustVcNativeVerifierSuiteIdentity {
    /// Build a typed verifier-suite identity.
    pub fn new(
        suite: TrustVcNativeVerifierSuite,
        name: impl Into<String>,
        producer: impl Into<String>,
        version: impl Into<String>,
    ) -> Self {
        Self {
            suite,
            name: name.into(),
            producer: producer.into(),
            version: version.into(),
            tool_digest: None,
        }
    }

    /// Infer a known suite from a native prover or replay-engine name.
    pub fn from_native_names(
        prover: &str,
        replay_engine: Option<&str>,
        producer: impl Into<String>,
        version: impl Into<String>,
    ) -> Self {
        Self::new(
            native_suite_from_names(prover, replay_engine),
            prover,
            producer,
            version,
        )
    }

    /// Attach the verifier tool digest reported by native request provenance.
    pub fn with_tool_digest(mut self, tool_digest: impl Into<String>) -> Self {
        self.tool_digest = Some(tool_digest.into());
        self
    }

    /// Return the typed verifier suite.
    pub const fn suite(&self) -> TrustVcNativeVerifierSuite {
        self.suite
    }

    /// Return the suite/prover name included in the native certificate.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the producer recorded by proof lineage.
    pub fn producer(&self) -> &str {
        &self.producer
    }

    /// Return the suite or transform version recorded by proof lineage.
    pub fn version(&self) -> &str {
        &self.version
    }

    /// Return the verifier tool digest reported by native provenance, if present.
    pub fn tool_digest(&self) -> Option<&str> {
        self.tool_digest.as_deref()
    }

    /// Return a stable fingerprint for this verifier-suite identity.
    pub fn fingerprint(&self) -> String {
        native_suite_identity_fingerprint(self)
    }
}

fn native_suite_from_names(
    prover: &str,
    replay_engine: Option<&str>,
) -> TrustVcNativeVerifierSuite {
    let prover = prover.to_ascii_lowercase();
    let replay_engine = replay_engine.unwrap_or_default().to_ascii_lowercase();
    if prover.contains("trust_vc")
        || replay_engine.contains("trust_vc")
        || replay_engine.contains("trust")
    {
        TrustVcNativeVerifierSuite::TrustVc
    } else if prover.contains("trust_mc") || replay_engine.contains("trust_mc") {
        TrustVcNativeVerifierSuite::TrustMc
    } else if prover.contains("trust_wp") || replay_engine.contains("trust_wp") {
        TrustVcNativeVerifierSuite::TrustWp
    } else if prover.contains("ay") || replay_engine.contains("ay") {
        TrustVcNativeVerifierSuite::AY
    } else if prover.contains("trust") || replay_engine.contains("trust") {
        TrustVcNativeVerifierSuite::TRust
    } else if prover.contains("trust_ir") || replay_engine.contains("trust_ir") {
        TrustVcNativeVerifierSuite::TrustIr
    } else {
        TrustVcNativeVerifierSuite::Unknown
    }
}

/// Stable identity for a native solver/prover binary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeToolIdentity {
    name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    version: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    revision: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    digest: Option<String>,
}

impl Default for TrustVcNativeToolIdentity {
    fn default() -> Self {
        Self::new("unknown")
    }
}

impl TrustVcNativeToolIdentity {
    /// Build a native solver/prover tool identity.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: None,
            revision: None,
            digest: None,
        }
    }

    /// Attach a tool version.
    pub fn with_version(mut self, version: impl Into<String>) -> Self {
        self.version = Some(version.into());
        self
    }

    /// Attach a source revision or build id.
    pub fn with_revision(mut self, revision: impl Into<String>) -> Self {
        self.revision = Some(revision.into());
        self
    }

    /// Attach a stable tool digest.
    pub fn with_digest(mut self, digest: impl Into<String>) -> Self {
        self.digest = Some(digest.into());
        self
    }

    /// Return the solver/prover tool name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the reported tool version.
    pub fn version(&self) -> Option<&str> {
        self.version.as_deref()
    }

    /// Return the reported tool revision.
    pub fn revision(&self) -> Option<&str> {
        self.revision.as_deref()
    }

    /// Return the reported stable tool digest.
    pub fn digest(&self) -> Option<&str> {
        self.digest.as_deref()
    }

    /// Return whether this tool identity is specific enough for admission.
    pub fn is_reported(&self) -> bool {
        !self.name.is_empty()
            && self.name != "unknown"
            && self
                .version
                .as_deref()
                .is_none_or(|value| !value.is_empty())
            && self
                .revision
                .as_deref()
                .is_none_or(|value| !value.is_empty())
            && self.digest.as_deref().is_none_or(|value| !value.is_empty())
    }

    /// Return a stable fingerprint for this tool identity.
    pub fn fingerprint(&self) -> String {
        native_tool_identity_fingerprint(self)
    }
}

/// Solver/prover identity bound into a native proof object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeSolverIdentity {
    prover: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    solvers: Vec<TrustVcNativeToolIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    replay_engine: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    replay_invocation: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    transcript_digest: Option<String>,
}

impl Default for TrustVcNativeSolverIdentity {
    fn default() -> Self {
        Self::new("unknown")
    }
}

impl TrustVcNativeSolverIdentity {
    /// Build a solver identity from a native certificate prover.
    pub fn new(prover: impl Into<String>) -> Self {
        Self {
            prover: prover.into(),
            solvers: Vec::new(),
            replay_engine: None,
            replay_invocation: None,
            transcript_digest: None,
        }
    }

    /// Attach one typed solver/prover identity from native request provenance.
    pub fn with_solver(mut self, solver: TrustVcNativeToolIdentity) -> Self {
        self.solvers.push(solver);
        self
    }

    /// Attach all typed solver/prover identities from native request provenance.
    pub fn with_solvers(mut self, solvers: Vec<TrustVcNativeToolIdentity>) -> Self {
        self.solvers = solvers;
        self
    }

    /// Attach replay identity from native proof lineage.
    pub fn with_replay_identity(
        mut self,
        replay_engine: impl Into<String>,
        replay_invocation: impl Into<String>,
        transcript_digest: Option<String>,
    ) -> Self {
        self.replay_engine = Some(replay_engine.into());
        self.replay_invocation = Some(replay_invocation.into());
        self.transcript_digest = transcript_digest;
        self
    }

    /// Return the prover label from the native certificate.
    pub fn prover(&self) -> &str {
        &self.prover
    }

    /// Return typed solver/prover identities reported by native provenance.
    pub fn solvers(&self) -> &[TrustVcNativeToolIdentity] {
        &self.solvers
    }

    /// Return the replay engine, when native lineage supplied one.
    pub fn replay_engine(&self) -> Option<&str> {
        self.replay_engine.as_deref()
    }

    /// Return the replay invocation, when native lineage supplied one.
    pub fn replay_invocation(&self) -> Option<&str> {
        self.replay_invocation.as_deref()
    }

    /// Return the replay transcript digest, when native lineage supplied one.
    pub fn transcript_digest(&self) -> Option<&str> {
        self.transcript_digest.as_deref()
    }

    /// Return whether the identity has enough data for fail-closed replay admission.
    pub fn is_replayable(&self) -> bool {
        self.replay_engine
            .as_ref()
            .is_some_and(|value| !value.is_empty())
            && self
                .replay_invocation
                .as_ref()
                .is_some_and(|value| !value.is_empty())
            && self
                .transcript_digest
                .as_ref()
                .is_some_and(|value| !value.is_empty())
    }

    /// Return whether native provenance supplied specific typed solver identities.
    pub fn has_reported_solver_identities(&self) -> bool {
        !self.solvers.is_empty()
            && self
                .solvers
                .iter()
                .all(TrustVcNativeToolIdentity::is_reported)
    }

    /// Return a stable fingerprint for this solver/prover identity binding.
    pub fn fingerprint(&self) -> String {
        native_solver_identity_fingerprint(self)
    }
}

impl TrustVcNativeVerifierSuiteIdentity {
    /// Return whether the identity has enough data for fail-closed admission.
    pub fn is_reported(&self) -> bool {
        !matches!(self.suite, TrustVcNativeVerifierSuite::Unknown)
            && !self.name.is_empty()
            && self.name != "unknown"
            && !self.producer.is_empty()
            && self.producer != "unknown"
            && !self.version.is_empty()
            && self.version != "unknown"
            && self.version != "unreported"
            && self
                .tool_digest
                .as_deref()
                .is_none_or(|value| !value.is_empty())
    }
}

/// Typed compiler fact class referenced by a native proof object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeCompilerFactKind {
    AdtLayout,
    FatPointer,
    TraitObjectMetadata,
    PointerOffset,
    Cast,
    Monomorphization,
}

/// Typed reference to one compiler-originated fact in a TrustIr schema-v2 bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeCompilerFactRef {
    kind: TrustVcNativeCompilerFactKind,
    id: u32,
}

impl TrustVcNativeCompilerFactRef {
    /// Build a typed compiler fact reference.
    pub const fn new(kind: TrustVcNativeCompilerFactKind, id: u32) -> Self {
        Self { kind, id }
    }

    /// Build an ADT layout fact reference.
    pub const fn adt_layout(id: u32) -> Self {
        Self::new(TrustVcNativeCompilerFactKind::AdtLayout, id)
    }

    /// Build a fat-pointer metadata fact reference.
    pub const fn fat_pointer(id: u32) -> Self {
        Self::new(TrustVcNativeCompilerFactKind::FatPointer, id)
    }

    /// Build a trait-object metadata fact reference.
    pub const fn trait_object_metadata(id: u32) -> Self {
        Self::new(TrustVcNativeCompilerFactKind::TraitObjectMetadata, id)
    }

    /// Build a pointer-offset fact reference.
    pub const fn pointer_offset(id: u32) -> Self {
        Self::new(TrustVcNativeCompilerFactKind::PointerOffset, id)
    }

    /// Build a cast/transmute layout fact reference.
    pub const fn cast(id: u32) -> Self {
        Self::new(TrustVcNativeCompilerFactKind::Cast, id)
    }

    /// Build a monomorphization identity fact reference.
    pub const fn monomorphization(id: u32) -> Self {
        Self::new(TrustVcNativeCompilerFactKind::Monomorphization, id)
    }

    /// Return the typed fact class.
    pub const fn kind(&self) -> TrustVcNativeCompilerFactKind {
        self.kind
    }

    /// Return the TrustIr compiler fact id.
    pub const fn id(&self) -> u32 {
        self.id
    }
}

/// Source span associated with a native compiler-fact obligation source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeSourceSpan {
    file_id: u32,
    line: u32,
    column: u32,
}

impl TrustVcNativeSourceSpan {
    /// Build a source span from TrustIr source-map coordinates.
    pub const fn new(file_id: u32, line: u32, column: u32) -> Self {
        Self {
            file_id,
            line,
            column,
        }
    }

    /// Return the TrustIr source file id.
    pub const fn file_id(&self) -> u32 {
        self.file_id
    }

    /// Return the source line.
    pub const fn line(&self) -> u32 {
        self.line
    }

    /// Return the source column.
    pub const fn column(&self) -> u32 {
        self.column
    }
}

/// Compiler-side reason a native proof obligation was emitted.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeObligationCause {
    Precondition,
    Postcondition,
    Assert,
    BoundsCheck,
    OverflowCheck,
    LayoutCheck,
    CastCheck,
    PointerOffset,
    BorrowCheck,
    Translation,
    Panic,
    #[default]
    Other,
}

/// Typed compiler-fact source binding for a native proof object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeCompilerFactsBinding {
    compiler_facts_digest: String,
    obligation_source_digest: String,
    obligation_id: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    function_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source_span: Option<TrustVcNativeSourceSpan>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    assertion_id: Option<u32>,
    cause: TrustVcNativeObligationCause,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    monomorphization_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    fact_refs: Vec<TrustVcNativeCompilerFactRef>,
}

impl Default for TrustVcNativeCompilerFactsBinding {
    fn default() -> Self {
        Self {
            compiler_facts_digest: String::new(),
            obligation_source_digest: String::new(),
            obligation_id: u32::MAX,
            function_id: None,
            source_span: None,
            assertion_id: None,
            cause: TrustVcNativeObligationCause::Other,
            monomorphization_id: None,
            fact_refs: Vec::new(),
        }
    }
}

impl TrustVcNativeCompilerFactsBinding {
    /// Build a compiler-fact binding for one TrustIr obligation source.
    pub fn new(
        compiler_facts_digest: impl Into<String>,
        obligation_id: u32,
        function_id: Option<u32>,
        source_span: Option<TrustVcNativeSourceSpan>,
        cause: TrustVcNativeObligationCause,
        monomorphization_id: Option<u32>,
        fact_refs: Vec<TrustVcNativeCompilerFactRef>,
    ) -> Self {
        let compiler_facts_digest = compiler_facts_digest.into();
        let obligation_source_digest = compiler_fact_source_digest(CompilerFactSourceDigestParts {
            compiler_facts_digest: &compiler_facts_digest,
            obligation_id,
            function_id,
            source_span,
            assertion_id: None,
            cause,
            monomorphization_id,
            fact_refs: &fact_refs,
        });
        Self {
            compiler_facts_digest,
            obligation_source_digest,
            obligation_id,
            function_id,
            source_span,
            assertion_id: None,
            cause,
            monomorphization_id,
            fact_refs,
        }
    }

    /// Attach the native frontend assertion id carried by the source mapping.
    pub fn with_assertion_id(mut self, assertion_id: Option<u32>) -> Self {
        self.assertion_id = assertion_id;
        self.obligation_source_digest =
            compiler_fact_source_digest(CompilerFactSourceDigestParts {
                compiler_facts_digest: &self.compiler_facts_digest,
                obligation_id: self.obligation_id,
                function_id: self.function_id,
                source_span: self.source_span,
                assertion_id: self.assertion_id,
                cause: self.cause,
                monomorphization_id: self.monomorphization_id,
                fact_refs: &self.fact_refs,
            });
        self
    }

    /// Return the digest of the whole TrustIr `NativeCompilerFacts` payload.
    pub fn compiler_facts_digest(&self) -> &str {
        &self.compiler_facts_digest
    }

    /// Return the digest of this obligation's compiler-fact source mapping.
    pub fn obligation_source_digest(&self) -> &str {
        &self.obligation_source_digest
    }

    /// Return the TrustIr proof-obligation id bound by this source mapping.
    pub const fn obligation_id(&self) -> u32 {
        self.obligation_id
    }

    /// Return the TrustIr function id responsible for this obligation, when known.
    pub const fn function_id(&self) -> Option<u32> {
        self.function_id
    }

    /// Return the source span responsible for this obligation, when known.
    pub const fn source_span(&self) -> Option<TrustVcNativeSourceSpan> {
        self.source_span
    }

    /// Return the native frontend assertion id for this obligation, when known.
    pub const fn assertion_id(&self) -> Option<u32> {
        self.assertion_id
    }

    /// Return the compiler-side obligation cause.
    pub const fn cause(&self) -> TrustVcNativeObligationCause {
        self.cause
    }

    /// Return the monomorphization id responsible for this obligation, when known.
    pub const fn monomorphization_id(&self) -> Option<u32> {
        self.monomorphization_id
    }

    /// Return the typed compiler fact references bound to this obligation.
    pub fn fact_refs(&self) -> &[TrustVcNativeCompilerFactRef] {
        &self.fact_refs
    }
}

/// Typed TrustIr proof-obligation status used for native artifact admission.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeArtifactObligationStatus {
    /// Missing status from an older serialized payload.
    #[default]
    Unspecified,
    /// The upstream obligation is not discharged yet.
    Pending,
    /// The upstream obligation is discharged.
    Discharged,
    /// The upstream obligation failed.
    Failed,
    /// The upstream obligation was marked trusted rather than proved.
    Trusted,
}

impl TrustVcNativeArtifactObligationStatus {
    /// Return the stable wire label for this status.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Unspecified => "unspecified",
            Self::Pending => "pending",
            Self::Discharged => "discharged",
            Self::Failed => "failed",
            Self::Trusted => "trusted",
        }
    }
}

/// Replay verdict for a native proof object.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeArtifactReplayStatus {
    /// Missing replay status from an older serialized payload.
    #[default]
    Unspecified,
    /// Native lineage carries a replay engine, invocation, and transcript digest.
    Replayable,
    /// Native lineage is not replayable enough for first-class admission.
    Rejected,
}

/// Admission verdict for a first-class native proof object.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeArtifactAdmissionStatus {
    /// Missing admission status from an older serialized payload.
    #[default]
    Unspecified,
    /// The artifact binding is accepted for the requested obligation/assertion.
    Accepted,
    /// The artifact binding is present but rejected fail-closed.
    Rejected,
}

/// Reasons a native proof object was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVcNativeArtifactRejection {
    /// Caller did not provide a stable assertion id.
    MissingAssertionId,
    /// Native proof object lacks the TrustIr module digest it was proved against.
    MissingTrustIrModuleDigest,
    /// Native proof object lacks the stable request digest authenticating its
    /// replay formula.
    MissingRequestDigest,
    /// Native proof object lacks a verifier-suite identity.
    MissingSuiteIdentity,
    /// Native proof object lacks a solver/prover identity.
    MissingSolverIdentity,
    /// Native proof lineage lacks a replay engine or invocation.
    MissingReplayIdentity,
    /// Native proof lineage lacks a replay transcript digest.
    MissingReplayTranscriptDigest,
    /// Native proof object lacks a per-obligation compiler-fact source mapping.
    MissingCompilerFactSource,
    /// Native proof object lacks typed compiler fact references.
    MissingCompilerFactReferences,
    /// The referenced TrustIr obligation is still pending.
    ObligationPending,
    /// The referenced TrustIr obligation failed upstream.
    ObligationFailed,
    /// The referenced TrustIr obligation is marked trusted rather than discharged.
    ObligationTrusted,
    /// The certificate payload is explicitly trusted evidence.
    CertificateUsesTrustedEvidence,
    /// The proof object is bound to a different assertion id.
    AssertionIdMismatch,
    /// The proof object assertion id disagrees with its compiler-fact source assertion id.
    CompilerFactAssertionIdMismatch,
    /// The proof object is bound to a different TrustIr obligation id.
    TrustIrObligationIdMismatch,
    /// The proof object is bound to a different TrustIr module digest.
    TrustIrModuleDigestMismatch,
    /// The proof object is bound to a different native request/replay digest.
    RequestDigestMismatch,
    /// The proof object is bound to a different verifier suite.
    SuiteIdentityMismatch,
    /// The proof object is bound to a different solver/prover identity.
    SolverIdentityMismatch,
    /// The proof object carries a stale evidence digest.
    EvidenceDigestMismatch,
    /// The proof object carries a stale certificate digest.
    CertificateDigestMismatch,
    /// The proof object carries a stale compiler-facts digest.
    CompilerFactsDigestMismatch,
    /// The proof object is bound to a different compiler-fact source mapping.
    CompilerFactSourceMismatch,
    /// The proof object is bound to different typed compiler fact references.
    CompilerFactReferencesMismatch,
    /// The proof object fingerprint does not match the expected binding.
    ArtifactFingerprintMismatch,
}

/// Fail-closed replay and admission status for a native proof object.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeArtifactAdmission {
    #[serde(default)]
    replay_status: TrustVcNativeArtifactReplayStatus,
    #[serde(default)]
    status: TrustVcNativeArtifactAdmissionStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    rejection_reasons: Vec<TrustVcNativeArtifactRejection>,
}

impl Default for TrustVcNativeArtifactAdmission {
    fn default() -> Self {
        Self {
            replay_status: TrustVcNativeArtifactReplayStatus::Unspecified,
            status: TrustVcNativeArtifactAdmissionStatus::Unspecified,
            rejection_reasons: Vec::new(),
        }
    }
}

struct NativeAdmissionParts<'a> {
    assertion_id: &'a str,
    trust_ir_module_digest: &'a str,
    request_digest: Option<&'a str>,
    trust_ir_obligation_id: u32,
    suite_identity: &'a TrustVcNativeVerifierSuiteIdentity,
    obligation_status: TrustVcNativeArtifactObligationStatus,
    trusted: bool,
    solver_identity: &'a TrustVcNativeSolverIdentity,
    compiler_facts_binding: &'a TrustVcNativeCompilerFactsBinding,
}

impl TrustVcNativeArtifactAdmission {
    /// Build admission from native obligation, replay, and trust metadata.
    pub fn from_native_parts(
        assertion_id: &str,
        obligation_status: TrustVcNativeArtifactObligationStatus,
        trusted: bool,
        solver_identity: &TrustVcNativeSolverIdentity,
    ) -> Self {
        Self::from_native_binding_parts(
            assertion_id,
            u32::MAX,
            &TrustVcNativeVerifierSuiteIdentity::default(),
            obligation_status,
            trusted,
            solver_identity,
            &TrustVcNativeCompilerFactsBinding::default(),
        )
    }

    /// Build admission from native obligation, replay, trust, and compiler-fact metadata.
    pub fn from_native_binding_parts(
        assertion_id: &str,
        trust_ir_obligation_id: u32,
        suite_identity: &TrustVcNativeVerifierSuiteIdentity,
        obligation_status: TrustVcNativeArtifactObligationStatus,
        trusted: bool,
        solver_identity: &TrustVcNativeSolverIdentity,
        compiler_facts_binding: &TrustVcNativeCompilerFactsBinding,
    ) -> Self {
        Self::from_native_admission_parts(NativeAdmissionParts {
            assertion_id,
            trust_ir_module_digest: "",
            request_digest: None,
            trust_ir_obligation_id,
            suite_identity,
            obligation_status,
            trusted,
            solver_identity,
            compiler_facts_binding,
        })
    }

    fn from_native_admission_parts(parts: NativeAdmissionParts<'_>) -> Self {
        let mut rejection_reasons = Vec::new();
        if parts.assertion_id.is_empty() {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingAssertionId);
        }
        if parts
            .compiler_facts_binding
            .assertion_id()
            .is_some_and(|assertion_id| parts.assertion_id.parse::<u32>() != Ok(assertion_id))
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::CompilerFactAssertionIdMismatch);
        }
        if parts.trust_ir_module_digest.is_empty() {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingTrustIrModuleDigest);
        }
        if parts.request_digest.is_some_and(str::is_empty) {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingRequestDigest);
        }
        if !parts.suite_identity.is_reported() {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingSuiteIdentity);
        }
        if parts.solver_identity.prover().is_empty()
            || parts.solver_identity.prover() == "unknown"
            || !parts.solver_identity.has_reported_solver_identities()
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingSolverIdentity);
        }
        if parts
            .solver_identity
            .replay_engine()
            .is_none_or(|value| value.is_empty())
            || parts
                .solver_identity
                .replay_invocation()
                .is_none_or(|value| value.is_empty())
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingReplayIdentity);
        }
        if parts
            .solver_identity
            .transcript_digest()
            .is_none_or(|value| value.is_empty())
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingReplayTranscriptDigest);
        }
        if parts
            .compiler_facts_binding
            .compiler_facts_digest()
            .is_empty()
            || parts
                .compiler_facts_binding
                .obligation_source_digest()
                .is_empty()
            || parts.compiler_facts_binding.obligation_id() != parts.trust_ir_obligation_id
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingCompilerFactSource);
        }
        if parts.compiler_facts_binding.fact_refs().is_empty() {
            rejection_reasons.push(TrustVcNativeArtifactRejection::MissingCompilerFactReferences);
        }
        match parts.obligation_status {
            TrustVcNativeArtifactObligationStatus::Discharged => {}
            TrustVcNativeArtifactObligationStatus::Pending
            | TrustVcNativeArtifactObligationStatus::Unspecified => {
                rejection_reasons.push(TrustVcNativeArtifactRejection::ObligationPending);
            }
            TrustVcNativeArtifactObligationStatus::Failed => {
                rejection_reasons.push(TrustVcNativeArtifactRejection::ObligationFailed);
            }
            TrustVcNativeArtifactObligationStatus::Trusted => {
                rejection_reasons.push(TrustVcNativeArtifactRejection::ObligationTrusted);
            }
        }
        if parts.trusted {
            rejection_reasons.push(TrustVcNativeArtifactRejection::CertificateUsesTrustedEvidence);
        }
        Self::from_rejections(rejection_reasons)
    }

    fn from_rejections(rejection_reasons: Vec<TrustVcNativeArtifactRejection>) -> Self {
        Self {
            replay_status: if rejection_reasons.iter().any(|reason| {
                matches!(
                    reason,
                    TrustVcNativeArtifactRejection::MissingReplayIdentity
                        | TrustVcNativeArtifactRejection::MissingReplayTranscriptDigest
                )
            }) {
                TrustVcNativeArtifactReplayStatus::Rejected
            } else {
                TrustVcNativeArtifactReplayStatus::Replayable
            },
            status: if rejection_reasons.is_empty() {
                TrustVcNativeArtifactAdmissionStatus::Accepted
            } else {
                TrustVcNativeArtifactAdmissionStatus::Rejected
            },
            rejection_reasons,
        }
    }

    /// Return replay status.
    pub const fn replay_status(&self) -> TrustVcNativeArtifactReplayStatus {
        self.replay_status
    }

    /// Return admission status.
    pub const fn status(&self) -> TrustVcNativeArtifactAdmissionStatus {
        self.status
    }

    /// Return whether the artifact is accepted.
    pub const fn is_accepted(&self) -> bool {
        matches!(self.status, TrustVcNativeArtifactAdmissionStatus::Accepted)
    }

    /// Return rejection reasons.
    pub fn rejection_reasons(&self) -> &[TrustVcNativeArtifactRejection] {
        &self.rejection_reasons
    }
}

/// Expected native proof-object binding supplied by a caller such as tRust.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeArtifactExpectation {
    assertion_id: String,
    #[serde(alias = "tmir_obligation_id")]
    trust_ir_obligation_id: u32,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        alias = "tmir_module_digest"
    )]
    trust_ir_module_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    request_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    suite_identity: Option<TrustVcNativeVerifierSuiteIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    solver_identity: Option<TrustVcNativeSolverIdentity>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    evidence_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    certificate_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    compiler_facts_binding: Option<TrustVcNativeCompilerFactsBinding>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    artifact_fingerprint: Option<String>,
}

impl TrustVcNativeArtifactExpectation {
    /// Build a minimal assertion/TrustIr-obligation expectation.
    pub fn new(assertion_id: impl Into<String>, trust_ir_obligation_id: u32) -> Self {
        Self {
            assertion_id: assertion_id.into(),
            trust_ir_obligation_id,
            trust_ir_module_digest: None,
            request_digest: None,
            suite_identity: None,
            solver_identity: None,
            evidence_digest: None,
            certificate_digest: None,
            compiler_facts_binding: None,
            artifact_fingerprint: None,
        }
    }

    /// Require an exact TrustIr module digest.
    pub fn with_trust_ir_module_digest(
        mut self,
        trust_ir_module_digest: impl Into<String>,
    ) -> Self {
        self.trust_ir_module_digest = Some(trust_ir_module_digest.into());
        self
    }

    /// Require the stable digest of the native request and replay context.
    pub fn with_request_digest(mut self, request_digest: impl Into<String>) -> Self {
        self.request_digest = Some(request_digest.into());
        self
    }

    /// Require an exact verifier-suite identity.
    pub fn with_suite_identity(
        mut self,
        suite_identity: TrustVcNativeVerifierSuiteIdentity,
    ) -> Self {
        self.suite_identity = Some(suite_identity);
        self
    }

    /// Require an exact solver/prover identity.
    pub fn with_solver_identity(mut self, solver_identity: TrustVcNativeSolverIdentity) -> Self {
        self.solver_identity = Some(solver_identity);
        self
    }

    /// Require an exact evidence digest.
    pub fn with_evidence_digest(mut self, evidence_digest: impl Into<String>) -> Self {
        self.evidence_digest = Some(evidence_digest.into());
        self
    }

    /// Require an exact certificate digest.
    pub fn with_certificate_digest(mut self, certificate_digest: impl Into<String>) -> Self {
        self.certificate_digest = Some(certificate_digest.into());
        self
    }

    /// Require an exact compiler-facts binding.
    pub fn with_compiler_facts_binding(
        mut self,
        compiler_facts_binding: TrustVcNativeCompilerFactsBinding,
    ) -> Self {
        self.compiler_facts_binding = Some(compiler_facts_binding);
        self
    }

    /// Require an exact full binding fingerprint.
    pub fn with_artifact_fingerprint(mut self, artifact_fingerprint: impl Into<String>) -> Self {
        self.artifact_fingerprint = Some(artifact_fingerprint.into());
        self
    }
}

/// First-class native proof object bound to one assertion and TrustIr obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeProofArtifactInput {
    assertion_id: String,
    #[serde(alias = "tmir_module_digest")]
    trust_ir_module_digest: String,
    #[serde(default)]
    request_digest: String,
    #[serde(alias = "tmir_obligation_id")]
    trust_ir_obligation_id: u32,
    suite_identity: TrustVcNativeVerifierSuiteIdentity,
    solver_identity: TrustVcNativeSolverIdentity,
    obligation_status: TrustVcNativeArtifactObligationStatus,
    trusted: bool,
    evidence_digest: String,
    certificate_digest: String,
    compiler_facts_binding: TrustVcNativeCompilerFactsBinding,
}

impl TrustVcNativeProofArtifactInput {
    /// Build native proof-artifact input for an assertion and TrustIr obligation.
    pub fn new(
        assertion_id: impl Into<String>,
        trust_ir_obligation_id: u32,
        evidence_digest: impl Into<String>,
        certificate_digest: impl Into<String>,
    ) -> Self {
        Self {
            assertion_id: assertion_id.into(),
            trust_ir_module_digest: String::new(),
            request_digest: String::new(),
            trust_ir_obligation_id,
            suite_identity: TrustVcNativeVerifierSuiteIdentity::default(),
            solver_identity: TrustVcNativeSolverIdentity::default(),
            obligation_status: TrustVcNativeArtifactObligationStatus::Unspecified,
            trusted: false,
            evidence_digest: evidence_digest.into(),
            certificate_digest: certificate_digest.into(),
            compiler_facts_binding: TrustVcNativeCompilerFactsBinding::default(),
        }
    }

    /// Attach the TrustIr module digest that produced this proof obligation.
    pub fn with_trust_ir_module_digest(
        mut self,
        trust_ir_module_digest: impl Into<String>,
    ) -> Self {
        self.trust_ir_module_digest = trust_ir_module_digest.into();
        self
    }

    /// Attach the stable digest of the native request whose replay assertion
    /// carries this proof's formula.
    pub fn with_request_digest(mut self, request_digest: impl Into<String>) -> Self {
        self.request_digest = request_digest.into();
        self
    }

    /// Attach verifier-suite identity.
    pub fn with_suite_identity(
        mut self,
        suite_identity: TrustVcNativeVerifierSuiteIdentity,
    ) -> Self {
        self.suite_identity = suite_identity;
        self
    }

    /// Attach solver/prover identity.
    pub fn with_solver_identity(mut self, solver_identity: TrustVcNativeSolverIdentity) -> Self {
        self.solver_identity = solver_identity;
        self
    }

    /// Attach the upstream TrustIr obligation status.
    pub const fn with_obligation_status(
        mut self,
        obligation_status: TrustVcNativeArtifactObligationStatus,
    ) -> Self {
        self.obligation_status = obligation_status;
        self
    }

    /// Record whether the native certificate uses trusted evidence.
    pub const fn with_trusted(mut self, trusted: bool) -> Self {
        self.trusted = trusted;
        self
    }

    /// Attach the compiler-fact source binding for this TrustIr obligation.
    pub fn with_compiler_facts_binding(
        mut self,
        compiler_facts_binding: TrustVcNativeCompilerFactsBinding,
    ) -> Self {
        self.compiler_facts_binding = compiler_facts_binding;
        self
    }
}

/// First-class native proof object bound to one assertion and TrustIr obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVcNativeProofArtifact {
    schema_version: u32,
    assertion_id: String,
    #[serde(alias = "tmir_module_digest")]
    trust_ir_module_digest: String,
    #[serde(default)]
    request_digest: String,
    #[serde(alias = "tmir_obligation_id")]
    trust_ir_obligation_id: u32,
    suite_identity: TrustVcNativeVerifierSuiteIdentity,
    solver_identity: TrustVcNativeSolverIdentity,
    evidence_digest: String,
    certificate_digest: String,
    #[serde(default)]
    compiler_facts_binding: TrustVcNativeCompilerFactsBinding,
    artifact_fingerprint: String,
    admission: TrustVcNativeArtifactAdmission,
}

impl TrustVcNativeProofArtifact {
    /// Build and admit a native proof object from typed binding parts.
    pub fn new(input: TrustVcNativeProofArtifactInput) -> Self {
        let fingerprint_payload = NativeArtifactFingerprintPayload {
            schema_version: TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
            assertion_id: &input.assertion_id,
            trust_ir_module_digest: &input.trust_ir_module_digest,
            request_digest: &input.request_digest,
            trust_ir_obligation_id: input.trust_ir_obligation_id,
            suite_identity: &input.suite_identity,
            solver_identity: &input.solver_identity,
            evidence_digest: &input.evidence_digest,
            certificate_digest: &input.certificate_digest,
            compiler_facts_binding: &input.compiler_facts_binding,
        };
        let artifact_fingerprint = native_artifact_fingerprint(&fingerprint_payload);
        let admission =
            TrustVcNativeArtifactAdmission::from_native_admission_parts(NativeAdmissionParts {
                assertion_id: &input.assertion_id,
                trust_ir_module_digest: &input.trust_ir_module_digest,
                request_digest: Some(&input.request_digest),
                trust_ir_obligation_id: input.trust_ir_obligation_id,
                suite_identity: &input.suite_identity,
                obligation_status: input.obligation_status,
                trusted: input.trusted,
                solver_identity: &input.solver_identity,
                compiler_facts_binding: &input.compiler_facts_binding,
            });

        Self {
            schema_version: TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
            assertion_id: input.assertion_id,
            trust_ir_module_digest: input.trust_ir_module_digest,
            request_digest: input.request_digest,
            trust_ir_obligation_id: input.trust_ir_obligation_id,
            suite_identity: input.suite_identity,
            solver_identity: input.solver_identity,
            evidence_digest: input.evidence_digest,
            certificate_digest: input.certificate_digest,
            compiler_facts_binding: input.compiler_facts_binding,
            artifact_fingerprint,
            admission,
        }
    }

    /// Return the schema version used for this binding.
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    /// Return the caller-supplied assertion id.
    pub fn assertion_id(&self) -> &str {
        &self.assertion_id
    }

    /// Return the TrustIr module digest this proof object is bound to.
    pub fn trust_ir_module_digest(&self) -> &str {
        &self.trust_ir_module_digest
    }

    /// Return the stable digest of the native request/replay context bound into
    /// this artifact fingerprint.
    pub fn request_digest(&self) -> &str {
        &self.request_digest
    }

    /// Return the Tmir (Trust MIR) module digest this proof object is bound to.
    ///
    /// Tmir is the current public name for the same typed TrustIr module
    /// digest; this accessor forwards to [`Self::trust_ir_module_digest`].
    pub fn tmir_module_digest(&self) -> &str {
        self.trust_ir_module_digest()
    }

    /// Return the TrustIr proof-obligation id.
    pub const fn trust_ir_obligation_id(&self) -> u32 {
        self.trust_ir_obligation_id
    }

    /// Return the Tmir (Trust MIR) proof-obligation id.
    ///
    /// Tmir is the current public name for the typed TrustIr proof obligation
    /// id; this accessor forwards to [`Self::trust_ir_obligation_id`].
    pub const fn tmir_obligation_id(&self) -> u32 {
        self.trust_ir_obligation_id()
    }

    /// Return the verifier-suite identity.
    pub const fn suite_identity(&self) -> &TrustVcNativeVerifierSuiteIdentity {
        &self.suite_identity
    }

    /// Return the solver/prover identity.
    pub const fn solver_identity(&self) -> &TrustVcNativeSolverIdentity {
        &self.solver_identity
    }

    /// Return the native evidence digest.
    pub fn evidence_digest(&self) -> &str {
        &self.evidence_digest
    }

    /// Return the full native certificate digest.
    pub fn certificate_digest(&self) -> &str {
        &self.certificate_digest
    }

    /// Return the compiler-fact source binding.
    pub const fn compiler_facts_binding(&self) -> &TrustVcNativeCompilerFactsBinding {
        &self.compiler_facts_binding
    }

    /// Return the full proof-object binding fingerprint.
    pub fn artifact_fingerprint(&self) -> &str {
        &self.artifact_fingerprint
    }

    /// Return fail-closed admission details.
    pub const fn admission(&self) -> &TrustVcNativeArtifactAdmission {
        &self.admission
    }

    /// Check this artifact against caller expectations.
    pub fn admission_against(
        &self,
        expected: &TrustVcNativeArtifactExpectation,
    ) -> TrustVcNativeArtifactAdmission {
        let mut rejection_reasons = self.admission.rejection_reasons().to_vec();
        if self.assertion_id != expected.assertion_id {
            rejection_reasons.push(TrustVcNativeArtifactRejection::AssertionIdMismatch);
        }
        if self.trust_ir_obligation_id != expected.trust_ir_obligation_id {
            rejection_reasons.push(TrustVcNativeArtifactRejection::TrustIrObligationIdMismatch);
        }
        if expected
            .trust_ir_module_digest
            .as_ref()
            .is_some_and(|expected| expected != &self.trust_ir_module_digest)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::TrustIrModuleDigestMismatch);
        }
        if expected
            .request_digest
            .as_ref()
            .is_some_and(|expected| expected != &self.request_digest)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::RequestDigestMismatch);
        }
        if expected
            .suite_identity
            .as_ref()
            .is_some_and(|expected| expected != &self.suite_identity)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::SuiteIdentityMismatch);
        }
        if expected
            .solver_identity
            .as_ref()
            .is_some_and(|expected| expected != &self.solver_identity)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::SolverIdentityMismatch);
        }
        if expected
            .evidence_digest
            .as_ref()
            .is_some_and(|expected| expected != &self.evidence_digest)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::EvidenceDigestMismatch);
        }
        if expected
            .certificate_digest
            .as_ref()
            .is_some_and(|expected| expected != &self.certificate_digest)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::CertificateDigestMismatch);
        }
        if expected
            .compiler_facts_binding
            .as_ref()
            .is_some_and(|expected| {
                expected.compiler_facts_digest()
                    != self.compiler_facts_binding.compiler_facts_digest()
            })
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::CompilerFactsDigestMismatch);
        }
        if expected
            .compiler_facts_binding
            .as_ref()
            .is_some_and(|expected| {
                expected.obligation_source_digest()
                    != self.compiler_facts_binding.obligation_source_digest()
            })
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::CompilerFactSourceMismatch);
        }
        if expected
            .compiler_facts_binding
            .as_ref()
            .is_some_and(|expected| expected.fact_refs() != self.compiler_facts_binding.fact_refs())
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::CompilerFactReferencesMismatch);
        }
        if expected
            .artifact_fingerprint
            .as_ref()
            .is_some_and(|expected| expected != &self.artifact_fingerprint)
        {
            rejection_reasons.push(TrustVcNativeArtifactRejection::ArtifactFingerprintMismatch);
        }
        TrustVcNativeArtifactAdmission::from_rejections(rejection_reasons)
    }
}

#[derive(Serialize)]
struct NativeArtifactFingerprintPayload<'a> {
    schema_version: u32,
    assertion_id: &'a str,
    trust_ir_module_digest: &'a str,
    request_digest: &'a str,
    trust_ir_obligation_id: u32,
    suite_identity: &'a TrustVcNativeVerifierSuiteIdentity,
    solver_identity: &'a TrustVcNativeSolverIdentity,
    evidence_digest: &'a str,
    certificate_digest: &'a str,
    compiler_facts_binding: &'a TrustVcNativeCompilerFactsBinding,
}

fn native_artifact_fingerprint(payload: &NativeArtifactFingerprintPayload<'_>) -> String {
    sha256_json(payload, "native proof-object payload")
}

#[derive(Serialize)]
struct NativeSuiteIdentityFingerprintPayload<'a> {
    schema_version: u32,
    suite_identity: &'a TrustVcNativeVerifierSuiteIdentity,
}

fn native_suite_identity_fingerprint(identity: &TrustVcNativeVerifierSuiteIdentity) -> String {
    let payload = NativeSuiteIdentityFingerprintPayload {
        schema_version: TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
        suite_identity: identity,
    };
    sha256_json(&payload, "native verifier-suite identity payload")
}

#[derive(Serialize)]
struct NativeToolIdentityFingerprintPayload<'a> {
    schema_version: u32,
    tool_identity: &'a TrustVcNativeToolIdentity,
}

fn native_tool_identity_fingerprint(identity: &TrustVcNativeToolIdentity) -> String {
    let payload = NativeToolIdentityFingerprintPayload {
        schema_version: TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
        tool_identity: identity,
    };
    sha256_json(&payload, "native tool identity payload")
}

#[derive(Serialize)]
struct NativeSolverIdentityFingerprintPayload<'a> {
    schema_version: u32,
    solver_identity: &'a TrustVcNativeSolverIdentity,
}

fn native_solver_identity_fingerprint(identity: &TrustVcNativeSolverIdentity) -> String {
    let payload = NativeSolverIdentityFingerprintPayload {
        schema_version: TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
        solver_identity: identity,
    };
    sha256_json(&payload, "native solver identity payload")
}

#[derive(Serialize)]
struct NativeCompilerFactsBindingDigestPayload<'a> {
    schema_version: u32,
    compiler_facts_digest: &'a str,
    obligation_id: u32,
    function_id: Option<u32>,
    source_span: Option<TrustVcNativeSourceSpan>,
    assertion_id: Option<u32>,
    cause: TrustVcNativeObligationCause,
    monomorphization_id: Option<u32>,
    fact_refs: &'a [TrustVcNativeCompilerFactRef],
}

struct CompilerFactSourceDigestParts<'a> {
    compiler_facts_digest: &'a str,
    obligation_id: u32,
    function_id: Option<u32>,
    source_span: Option<TrustVcNativeSourceSpan>,
    assertion_id: Option<u32>,
    cause: TrustVcNativeObligationCause,
    monomorphization_id: Option<u32>,
    fact_refs: &'a [TrustVcNativeCompilerFactRef],
}

fn compiler_fact_source_digest(parts: CompilerFactSourceDigestParts<'_>) -> String {
    let payload = NativeCompilerFactsBindingDigestPayload {
        schema_version: TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
        compiler_facts_digest: parts.compiler_facts_digest,
        obligation_id: parts.obligation_id,
        function_id: parts.function_id,
        source_span: parts.source_span,
        assertion_id: parts.assertion_id,
        cause: parts.cause,
        monomorphization_id: parts.monomorphization_id,
        fact_refs: parts.fact_refs,
    };
    sha256_json(&payload, "native compiler-fact source payload")
}

fn sha256_json(payload: &impl Serialize, context: &str) -> String {
    let encoded = serde_json::to_vec(payload)
        .unwrap_or_else(|err| format!("trust-vc:serialization-error:{context}:{err}").into_bytes());
    let digest = Sha256::digest(encoded);
    let mut out = String::from("sha256:");
    for byte in digest {
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}
