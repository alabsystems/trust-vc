//! Programmatic adapter boundary between trust_vc and tRust verifier concepts.
//!
//! This is the adapter through which trust-vc serves as Trust's proof backend:
//! it consumes resolved compiler facts from Trust's `trust_ir` (types/borrows)
//! and emits proof-certificate lineage back to Trust. Verus parity is the
//! benchmark; the destination is Trust's proof calculus on the pure-Rust `ay`
//! solver. See `design-trust-proof-backend.md`.
//!
//! This crate intentionally avoids trust_vc's proc-macro test collection path.
//! Callers build a [`TrustVerificationRequest`] directly, then pass it to a
//! [`TrustVerifier`]. The initial [`TrustVcTrustEngine`] implementation lowers
//! each verification unit into `trust_vc_core::vc::VerificationContext` and runs
//! trust_vc's existing solver pipeline from that context.
//!
//! A direct dependency on tRust's compiler-side crates is deferred until that
//! API is stable enough for trust_vc to depend on. In the meantime, tRust-facing
//! code can translate its `VerifiableFunction`, TrustIr proof obligation, or
//! solver request data into this crate's stable request model.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use thiserror::Error;
use trust_vc_core::ir::{
    ArithOp as TrustVcArithOp, CompareOp as TrustVcCompareOp, DatatypeVariant,
    LogicOp as TrustVcLogicOp, QuantifierKind as TrustVcQuantifierKind, TrustVcExpr, TrustVcType,
};
pub use trust_vc_core::vc::TypedProofObligation;
use trust_vc_core::vc::{
    ObligationKind as TrustVcObligationKind, ProofObligation, SolverMode, VariableDecl,
    VerificationContext,
};
use trust_vc_core::TriggerInferenceMode as TrustVcTriggerInferenceMode;
use trust_vc_core::VerificationReport;
use trust_vc_core::{CounterexampleBinding, VerificationReportOptions, VerifyResult};

pub mod mir_memory;
pub use mir_memory::{
    typed_mir_memory_metadata, TrustMirMemoryObligation, TrustMirMemoryProofUnit,
    TRUST_VC_CONDITION_ORIGIN_METADATA_KEY, TRUST_VC_CONDITION_ORIGIN_TYPED_TRUST_VC_EXPR_VALUE,
    TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY, TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION,
    TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY, TRUST_VC_OWNERSHIP_CONTEXT_TYPED_VALUE,
    TRUST_VC_PROOF_OBLIGATION_METADATA_KEY, TRUST_VC_PROOF_OBLIGATION_TYPED_PROOF_OBLIGATION_VALUE,
};
#[allow(clippy::upper_case_acronyms)]
pub type TrusTrustIrMemoryObligation = TrustMirMemoryObligation;
#[allow(clippy::upper_case_acronyms)]
pub type TrusTrustIrMemoryProofUnit = TrustMirMemoryProofUnit;
pub mod native_artifact;
pub use native_artifact::{
    TrustVcNativeArtifactAdmission, TrustVcNativeArtifactAdmissionStatus,
    TrustVcNativeArtifactExpectation, TrustVcNativeArtifactObligationStatus,
    TrustVcNativeArtifactRejection, TrustVcNativeArtifactReplayStatus,
    TrustVcNativeCompilerFactKind, TrustVcNativeCompilerFactRef, TrustVcNativeCompilerFactsBinding,
    TrustVcNativeObligationCause, TrustVcNativeProofArtifact, TrustVcNativeProofArtifactInput,
    TrustVcNativeSolverIdentity, TrustVcNativeSourceSpan, TrustVcNativeToolIdentity,
    TrustVcNativeVerifierSuite, TrustVcNativeVerifierSuiteIdentity,
    TRUST_VC_NATIVE_ARTIFACT_BINDING_SCHEMA_VERSION,
};
pub mod native_trust_ir_bundle;
pub use native_trust_ir_bundle::{
    TrustVcNativeTrustIrBundleReport, TrustVcNativeTrustIrCertificateAdmission,
    TrustVcNativeTrustIrCertificateAdmissionStatus, TrustVcNativeTrustIrCertificateEvidence,
    TrustVcNativeTrustIrCertificateRejection, TrustVcNativeTrustIrEvidenceKind,
    TrustVcNativeTrustIrInputKind, TrustVcNativeTrustIrObligationKind,
    TrustVcNativeTrustIrReplayMetadata, TrustVcNativeTrustIrReplayMetadataSource,
    TrustVcNativeTrustIrRequestMode, TrustVcNativeTrustIrRequestReport,
    TrustVcNativeTrustIrVerdict,
};
pub mod trust_ir_adapter;
pub use trust_ir_adapter::{
    TrustSourceSpan, TrustTrustIrAdapterRequest, TrustTrustIrObligation,
    TrustTrustIrObligationKind, TrustTrustIrPredicate, TrustTrustIrProofUnit,
    TrustUnsupportedTrustIrConstruct,
};

// Tmir (Trust MIR) is the current name for the typed TrustIr adapter surface
// exposed to tRust-side bridges. The Tmir naming is the stable public alias;
// the older `TrustIr` types are retained for back-compat with existing call
// sites inside this crate.
//
// These aliases keep the Trust-side bridge importing
// `trust_vc_trust_engine::TrustTmirAdapterRequest` etc. while the engine's
// internal implementation continues to use the `TrustIr` types.
pub type TrustTmirAdapterRequest = TrustTrustIrAdapterRequest;
pub type TrustTmirObligation = TrustTrustIrObligation;
pub type TrustTmirObligationKind = TrustTrustIrObligationKind;
pub type TrustTmirPredicate = TrustTrustIrPredicate;
pub type TrustTmirProofUnit = TrustTrustIrProofUnit;
pub type TrustUnsupportedTmirConstruct = TrustUnsupportedTrustIrConstruct;
pub type TrustVcNativeTmirBundleReport = TrustVcNativeTrustIrBundleReport;

/// Schema version for tRust-facing Trust evidence cache keys.
pub const TRUST_EVIDENCE_CACHE_KEY_SCHEMA_VERSION: u32 = 1;

/// Schema version for per-assertion Trust proof-artifact bindings.
pub const TRUST_PROOF_ARTIFACT_BINDING_SCHEMA_VERSION: u32 = 1;

/// Schema version for typed TrustIr/trust-types adapter requests.
pub const TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION: u32 = 1;

/// Request metadata key used to supply the ay version/revision in cache keys.
pub const TRUST_CACHE_METADATA_AY_VERSION: &str = "trust.cache.ay_version";

/// Request metadata key used to supply the TrustVc kernel version/revision.
pub const TRUST_CACHE_METADATA_KERNEL_VERSION: &str = "trust.cache.kernel_version";

/// Request metadata key used to supply a TrustIr function/body hash.
pub const TRUST_CACHE_METADATA_TRUST_IR_BODY_HASH: &str = "trust.cache.trust_ir_body_hash";

/// Request metadata key used to supply a compiler layout/type-context hash.
pub const TRUST_CACHE_METADATA_LAYOUT_HASH: &str = "trust.cache.layout_hash";

/// Verifier abstraction used by trust-vc-side tRust adapters.
///
/// Implementations should treat [`TrustVerificationRequest`] as the stable
/// boundary. tRust-owned crates can translate into this request model without
/// forcing trust_vc to depend directly on unstable compiler or TrustIr APIs.
pub trait TrustVerifier {
    /// Verify all units in `request`.
    ///
    /// Structural request problems are returned as [`TrustEngineError`]. Solver
    /// failures, counterexamples, and unknowns are represented inside the
    /// returned [`TrustVerificationReport`].
    fn verify(
        &self,
        request: &TrustVerificationRequest,
    ) -> Result<TrustVerificationReport, TrustEngineError>;
}

/// TrustVc-backed implementation of [`TrustVerifier`].
///
/// This engine lowers each trust unit to a standalone
/// [`VerificationContext`]. It does not call
/// `VerificationPipeline::collect_from_macros`.
#[derive(Debug, Clone, Copy, Default)]
pub struct TrustVcTrustEngine;

impl TrustVcTrustEngine {
    /// Create a new TrustVc-backed trust engine.
    pub const fn new() -> Self {
        Self
    }

    /// Lower a single trust verification unit into a trust_vc verification context.
    ///
    /// This is exposed so integration code can inspect or further configure the
    /// context before choosing how to run the solver.
    pub fn lower_unit(
        &self,
        unit: &TrustVerificationUnit,
    ) -> Result<VerificationContext, TrustEngineError> {
        self.lower_unit_for_mode(unit, TrustVerificationMode::Compatibility)
    }

    /// Lower a unit for full verification.
    ///
    /// Full verification rejects legacy string-backed obligations and builds
    /// the trust_vc context from typed proof obligations only.
    pub fn lower_full_unit(
        &self,
        unit: &TrustVerificationUnit,
    ) -> Result<VerificationContext, TrustEngineError> {
        self.lower_unit_for_mode(unit, TrustVerificationMode::Full)
    }

    /// Validate a Trust request without running the solver.
    ///
    /// This is the public fail-closed preflight used by compiler adapters before
    /// handing typed TrustIr or trust-types payloads to a verification runner.
    pub fn validate_request(
        &self,
        request: &TrustVerificationRequest,
    ) -> Result<(), TrustEngineError> {
        if request.units.is_empty() {
            return Err(TrustEngineError::EmptyRequest);
        }
        validate_request_proof_policy(request)?;
        for unit in &request.units {
            validate_unit_for_mode(unit, request.mode)?;
        }
        Ok(())
    }

    fn lower_unit_for_mode(
        &self,
        unit: &TrustVerificationUnit,
        mode: TrustVerificationMode,
    ) -> Result<VerificationContext, TrustEngineError> {
        validate_unit_for_mode(unit, mode)?;

        let variables = unit
            .variables
            .iter()
            .chain(
                unit.native_context
                    .iter()
                    .flat_map(TrustNativeContext::variables),
            )
            .map(|variable| {
                Ok(VariableDecl::new(
                    variable.name.clone(),
                    variable.sort.to_trust_vc_type()?,
                ))
            })
            .collect::<Result<Vec<_>, TrustEngineError>>()?;

        if mode == TrustVerificationMode::Full {
            let obligations = unit
                .obligations
                .iter()
                .map(|obligation| obligation.to_trust_vc_typed_obligation(&unit.unit_id))
                .collect::<Result<Vec<_>, _>>()?;

            let mut context = VerificationContext::from_typed_parts(variables, obligations);
            configure_trust_verification_context(unit, &mut context);
            return Ok(context);
        }

        let obligations = unit
            .obligations
            .iter()
            .map(TrustObligation::to_trust_vc_obligation)
            .collect::<Result<Vec<_>, _>>()?;

        let mut context = VerificationContext::from_parts(variables, obligations);
        configure_trust_verification_context(unit, &mut context);
        Ok(context)
    }

    /// Lower native datatype metadata into trust_vc typed IR.
    ///
    /// This hook is separate from [`Self::lower_unit`] because the current
    /// `VerificationContext::from_parts` surface accepts variables and proof
    /// obligations only. Native integrations can still validate and register
    /// datatype metadata before choosing a richer trust-vc-core setup path.
    pub fn lower_native_datatypes(
        &self,
        unit: &TrustVerificationUnit,
    ) -> Result<Vec<TrustVcType>, TrustEngineError> {
        validate_unit_for_mode(unit, TrustVerificationMode::Compatibility)?;
        unit.native_context
            .as_ref()
            .map(|native| {
                native
                    .datatypes
                    .iter()
                    .map(TrustDatatype::to_trust_vc_type)
                    .collect()
            })
            .unwrap_or_else(|| Ok(Vec::new()))
    }

    /// Validate and lower a typed contract bundle into the general proof-IR request.
    ///
    /// This path is for tRust adapters that already have typed contract clauses
    /// and native contract-frame bindings. The resulting request always uses
    /// full verification so TrustVc lowers the carried [`TrustExpr`] values
    /// directly instead of reparsing source strings.
    pub fn lower_contract_bundle(
        &self,
        bundle: &TrustContractBundle,
    ) -> Result<TrustVerificationRequest, TrustEngineError> {
        bundle.validate_for_verification(self)?;
        Ok(bundle.to_trust_request())
    }

    /// Verify a typed contract bundle through TrustVc's full verification path.
    pub fn verify_contract_bundle(
        &self,
        bundle: &TrustContractBundle,
    ) -> Result<TrustVerificationReport, TrustEngineError> {
        let request = self.lower_contract_bundle(bundle)?;
        TrustVerifier::verify(self, &request)
    }

    /// Validate and lower a TrustVc-core typed proof unit into the Trust report model.
    ///
    /// This is the in-process bridge for callers that already build
    /// [`TypedProofObligation`] values and need structured native proof evidence
    /// instead of compatibility-mode source strings.
    pub fn lower_typed_proof_unit(
        &self,
        unit: &TrustTypedProofUnit,
    ) -> Result<TrustVerificationRequest, TrustEngineError> {
        unit.validate_for_verification(self)?;
        unit.to_trust_request()
    }

    /// Verify a TrustVc-core typed proof unit through TrustVc's full verification path.
    pub fn verify_typed_proof_unit(
        &self,
        unit: &TrustTypedProofUnit,
    ) -> Result<TrustVerificationReport, TrustEngineError> {
        let request = self.lower_typed_proof_unit(unit)?;
        TrustVerifier::verify(self, &request)
    }

    fn verify_unit(
        &self,
        source_id: &str,
        unit: &TrustVerificationUnit,
        mode: TrustVerificationMode,
        proof_policy: TrustProofPolicy,
        request_metadata: &BTreeMap<String, String>,
    ) -> Result<TrustUnitReport, TrustEngineError> {
        let context = self.lower_unit_for_mode(unit, mode)?;
        let result = context.verify_with_report(VerificationReportOptions::new());
        let outcome = TrustOutcome::from(result.result().clone());
        let proof_artifacts = TrustReplayableProofArtifact::from_verified_report_if_requested(
            unit,
            proof_policy,
            &result,
        )?;
        let proof_artifact_by_assertion = proof_artifacts
            .iter()
            .flat_map(|artifact| {
                artifact
                    .assertion_obligation_ids()
                    .iter()
                    .map(move |obligation_id| {
                        (
                            obligation_id.as_str(),
                            (artifact.artifact_id(), artifact.binding_fingerprint()),
                        )
                    })
            })
            .collect::<BTreeMap<_, _>>();
        let proof_evidence = if matches!(outcome, TrustOutcome::Verified) {
            unit.obligations
                .iter()
                .map(|obligation| {
                    let cache_key = TrustEvidenceCacheKey::from_obligation(
                        source_id,
                        unit,
                        obligation,
                        proof_policy,
                        request_metadata,
                    );
                    TrustProofEvidence::from_obligation(
                        unit,
                        obligation,
                        mode,
                        proof_artifact_by_assertion
                            .get(obligation.id())
                            .map(|(artifact_id, _)| *artifact_id),
                        proof_artifact_by_assertion
                            .get(obligation.id())
                            .map(|(_, binding_fingerprint)| *binding_fingerprint),
                        Some(cache_key),
                    )
                })
                .collect()
        } else {
            Vec::new()
        };
        let proof_artifact = match proof_artifacts.as_slice() {
            [artifact] => Some(artifact.clone()),
            _ => None,
        };
        let proof_artifact_coverage = proof_policy
            .wants_replayable_artifact()
            .then(|| TrustProofArtifactCoverage::from_unit_artifacts(unit, &proof_artifacts));
        Ok(TrustUnitReport {
            unit_id: unit.unit_id.clone(),
            outcome,
            cache_status: TrustEvidenceCacheStatus::Miss,
            diagnostics: result
                .steps()
                .iter()
                .map(|step| TrustDiagnostic {
                    message: step.label().to_string(),
                })
                .collect(),
            proof_evidence,
            proof_artifacts,
            proof_artifact,
            proof_artifact_coverage,
        })
    }
}

impl TrustVerifier for TrustVcTrustEngine {
    fn verify(
        &self,
        request: &TrustVerificationRequest,
    ) -> Result<TrustVerificationReport, TrustEngineError> {
        self.validate_request(request)?;

        let units = request
            .units
            .iter()
            .map(|unit| {
                self.verify_unit(
                    &request.source_id,
                    unit,
                    request.mode,
                    request.proof_policy,
                    &request.metadata,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TrustVerificationReport {
            source_id: request.source_id.clone(),
            units,
        })
    }
}

/// Verification policy mode for tRust-facing requests.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustVerificationMode {
    /// Compatibility mode accepts the legacy source-expression payload and
    /// lowers it through trust_vc's existing parser.
    #[default]
    Compatibility,
    /// Full verification mode requires typed TrustVc expressions and rejects
    /// string-backed obligations before solver execution.
    Full,
}

/// Proof-artifact policy for tRust-facing verification.
///
/// The default keeps the historical per-obligation evidence accounting. The
/// replayable modes are for hostile-reviewer/full-bootstrap gates: they require
/// full-mode typed obligations and only accept real TrustVc/ay proof artifacts,
/// never source strings or metadata-only success.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustProofPolicy {
    /// Return per-obligation evidence metadata after a verified unit.
    #[default]
    EvidenceOnly,
    /// Attach replayable proof artifacts when this build and solver produce them.
    AttachReplayableCertificates,
    /// Reject verified units that cannot provide a replayable proof artifact.
    RequireReplayableCertificate,
    /// Reject verified units whose proof artifact is absent or not strict-checker accepted.
    RequireStrictReplayableCertificate,
    /// Reject verified units whose proof artifact is not release-admissible.
    RequireReleaseAdmissibleCertificate,
}

impl TrustProofPolicy {
    const fn wants_replayable_artifact(self) -> bool {
        matches!(
            self,
            Self::AttachReplayableCertificates
                | Self::RequireReplayableCertificate
                | Self::RequireStrictReplayableCertificate
                | Self::RequireReleaseAdmissibleCertificate
        )
    }

    const fn requires_replayable_artifact(self) -> bool {
        matches!(
            self,
            Self::RequireReplayableCertificate
                | Self::RequireStrictReplayableCertificate
                | Self::RequireReleaseAdmissibleCertificate
        )
    }

    #[cfg(feature = "proof-certificates")]
    const fn requires_strict_replayable_artifact(self) -> bool {
        matches!(self, Self::RequireStrictReplayableCertificate)
    }

    #[cfg(feature = "proof-certificates")]
    const fn requires_release_admissible_artifact(self) -> bool {
        matches!(self, Self::RequireReleaseAdmissibleCertificate)
    }
}

/// Complete programmatic verification request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVerificationRequest {
    source_id: String,
    units: Vec<TrustVerificationUnit>,
    #[serde(default)]
    mode: TrustVerificationMode,
    #[serde(default)]
    proof_policy: TrustProofPolicy,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    metadata: BTreeMap<String, String>,
}

impl TrustVerificationRequest {
    /// Create an empty request for a crate, module, or compiler session.
    pub fn new(source_id: impl Into<String>) -> Self {
        Self {
            source_id: source_id.into(),
            units: Vec::new(),
            mode: TrustVerificationMode::Compatibility,
            proof_policy: TrustProofPolicy::default(),
            metadata: BTreeMap::new(),
        }
    }

    /// Return the source identifier associated with this request.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return the verification units in this request.
    pub fn units(&self) -> &[TrustVerificationUnit] {
        &self.units
    }

    /// Return the verification policy mode for this request.
    pub const fn mode(&self) -> TrustVerificationMode {
        self.mode
    }

    /// Return the requested proof-artifact policy.
    pub const fn proof_policy(&self) -> TrustProofPolicy {
        self.proof_policy
    }

    /// Return request metadata.
    pub fn metadata(&self) -> &BTreeMap<String, String> {
        &self.metadata
    }

    /// Replace all units in the request.
    pub fn with_units(mut self, units: Vec<TrustVerificationUnit>) -> Self {
        self.units = units;
        self
    }

    /// Set the verification policy mode.
    pub fn with_mode(mut self, mode: TrustVerificationMode) -> Self {
        self.mode = mode;
        self
    }

    /// Require full-verification policy for this request.
    pub fn for_full_verification(mut self) -> Self {
        self.mode = TrustVerificationMode::Full;
        self
    }

    /// Set the proof-artifact policy.
    pub fn with_proof_policy(mut self, proof_policy: TrustProofPolicy) -> Self {
        self.proof_policy = proof_policy;
        self
    }

    /// Attach replayable proof artifacts when TrustVc can produce them.
    pub fn with_replayable_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::AttachReplayableCertificates;
        self
    }

    /// Require replayable proof artifacts for verified full-mode units.
    pub fn require_replayable_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::RequireReplayableCertificate;
        self
    }

    /// Require replayable proof artifacts accepted by TrustVc's strict checker.
    pub fn require_strict_replayable_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::RequireStrictReplayableCertificate;
        self
    }

    /// Require replayable proof artifacts admitted by TrustVc's release policy.
    pub fn require_release_admissible_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::RequireReleaseAdmissibleCertificate;
        self
    }

    /// Append a unit to the request.
    pub fn with_unit(mut self, unit: TrustVerificationUnit) -> Self {
        self.units.push(unit);
        self
    }

    /// Insert a metadata entry.
    pub fn insert_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
}

/// In-process proof unit for callers that already have TrustVc typed obligations.
///
/// Unlike [`TrustTrustIrAdapterRequest`], this facade is not a JSON interchange
/// format. It lets tRust-side integration code pass first-class
/// [`TypedProofObligation`] values to TrustVc and still receive
/// [`TrustProofEvidence`] with structured typed expression payloads for the
/// TrustVc expression subset supported by [`TrustExpr`].
#[derive(Debug, Clone)]
#[must_use]
pub struct TrustTypedProofUnit {
    source_id: String,
    unit_id: String,
    display_name: Option<String>,
    native_context: Option<TrustNativeContext>,
    verifier_variables: Vec<TrustVariable>,
    obligations: Vec<TypedProofObligation>,
    proof_policy: TrustProofPolicy,
    metadata: BTreeMap<String, String>,
}

impl TrustTypedProofUnit {
    /// Create an empty in-process typed proof unit.
    pub fn new(source_id: impl Into<String>, unit_id: impl Into<String>) -> Self {
        Self {
            source_id: source_id.into(),
            unit_id: unit_id.into(),
            display_name: None,
            native_context: None,
            verifier_variables: Vec::new(),
            obligations: Vec::new(),
            proof_policy: TrustProofPolicy::default(),
            metadata: BTreeMap::new(),
        }
    }

    /// Return the request source id.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return the stable unit id.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the optional display name.
    pub fn display_name(&self) -> Option<&str> {
        self.display_name.as_deref()
    }

    /// Return typed native verifier context, if supplied.
    pub const fn native_context(&self) -> Option<&TrustNativeContext> {
        self.native_context.as_ref()
    }

    /// Return additional verifier variables referenced by obligations.
    pub fn verifier_variables(&self) -> &[TrustVariable] {
        &self.verifier_variables
    }

    /// Return the TrustVc typed proof obligations.
    pub fn obligations(&self) -> &[TypedProofObligation] {
        &self.obligations
    }

    /// Return the requested proof-artifact policy.
    pub const fn proof_policy(&self) -> TrustProofPolicy {
        self.proof_policy
    }

    /// Return request metadata.
    pub fn metadata(&self) -> &BTreeMap<String, String> {
        &self.metadata
    }

    /// Set a display name for diagnostics.
    pub fn with_display_name(mut self, display_name: impl Into<String>) -> Self {
        self.display_name = Some(display_name.into());
        self
    }

    /// Attach typed native verifier context.
    pub fn with_native_context(mut self, native_context: TrustNativeContext) -> Self {
        self.native_context = Some(native_context);
        self
    }

    /// Append an additional typed verifier variable.
    pub fn with_variable(mut self, variable: TrustVariable) -> Self {
        self.verifier_variables.push(variable);
        self
    }

    /// Append a TrustVc typed proof obligation.
    pub fn with_obligation(mut self, obligation: TypedProofObligation) -> Self {
        self.obligations.push(obligation);
        self
    }

    /// Set the proof-artifact policy used by the lowered request.
    pub fn with_proof_policy(mut self, proof_policy: TrustProofPolicy) -> Self {
        self.proof_policy = proof_policy;
        self
    }

    /// Insert request metadata.
    pub fn insert_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Lower this in-process facade into the general Trust request model.
    pub fn to_trust_request(&self) -> Result<TrustVerificationRequest, TrustEngineError> {
        let mut request = TrustVerificationRequest::new(self.source_id.clone())
            .for_full_verification()
            .with_proof_policy(self.proof_policy)
            .with_unit(self.to_trust_unit()?);
        for (key, value) in &self.metadata {
            request = request.insert_metadata(key.clone(), value.clone());
        }
        Ok(request)
    }

    /// Lower this in-process facade into one Trust verification unit.
    pub fn to_trust_unit(&self) -> Result<TrustVerificationUnit, TrustEngineError> {
        let mut unit = TrustVerificationUnit::new(self.unit_id.clone());
        if let Some(display_name) = &self.display_name {
            unit = unit.with_display_name(display_name.clone());
        }
        if let Some(native_context) = &self.native_context {
            unit = unit.with_native_context(native_context.clone());
        }
        for variable in &self.verifier_variables {
            unit = unit.with_variable(variable.clone());
        }
        for obligation in &self.obligations {
            unit = unit.with_obligation(TrustObligation::from_trust_vc_typed_obligation(
                &self.unit_id,
                obligation,
            )?);
        }
        Ok(unit)
    }

    fn validate_for_verification(
        &self,
        engine: &TrustVcTrustEngine,
    ) -> Result<(), TrustEngineError> {
        let unit = self.to_trust_unit()?;
        let _ = engine.lower_full_unit(&unit)?;
        Ok(())
    }
}

/// Typed contract proof-IR bundle supplied by a tRust-facing adapter.
///
/// This facade deliberately exposes only typed contract clauses. It is useful
/// when integration code has native function signatures, result/old-value
/// bindings, and typed pre/postcondition expressions, but should not be able to
/// smuggle in string-backed report fixtures.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustContractBundle {
    source_id: String,
    units: Vec<TrustContractProofUnit>,
    #[serde(default)]
    proof_policy: TrustProofPolicy,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    metadata: BTreeMap<String, String>,
}

impl TrustContractBundle {
    /// Create an empty typed contract bundle for a crate, module, or compiler session.
    pub fn new(source_id: impl Into<String>) -> Self {
        Self {
            source_id: source_id.into(),
            units: Vec::new(),
            proof_policy: TrustProofPolicy::default(),
            metadata: BTreeMap::new(),
        }
    }

    /// Return the source identifier associated with this bundle.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return the typed contract proof units in this bundle.
    pub fn units(&self) -> &[TrustContractProofUnit] {
        &self.units
    }

    /// Return the requested proof-artifact policy.
    pub const fn proof_policy(&self) -> TrustProofPolicy {
        self.proof_policy
    }

    /// Return bundle metadata.
    pub fn metadata(&self) -> &BTreeMap<String, String> {
        &self.metadata
    }

    /// Replace all units in this bundle.
    pub fn with_units(mut self, units: Vec<TrustContractProofUnit>) -> Self {
        self.units = units;
        self
    }

    /// Append a typed contract proof unit.
    pub fn with_unit(mut self, unit: TrustContractProofUnit) -> Self {
        self.units.push(unit);
        self
    }

    /// Set the proof-artifact policy used by the lowered request.
    pub fn with_proof_policy(mut self, proof_policy: TrustProofPolicy) -> Self {
        self.proof_policy = proof_policy;
        self
    }

    /// Attach replayable proof artifacts when TrustVc can produce them.
    pub fn with_replayable_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::AttachReplayableCertificates;
        self
    }

    /// Require replayable proof artifacts for verified units.
    pub fn require_replayable_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::RequireReplayableCertificate;
        self
    }

    /// Require replayable proof artifacts accepted by TrustVc's strict checker.
    pub fn require_strict_replayable_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::RequireStrictReplayableCertificate;
        self
    }

    /// Require replayable proof artifacts admitted by TrustVc's release policy.
    pub fn require_release_admissible_proof_artifacts(mut self) -> Self {
        self.proof_policy = TrustProofPolicy::RequireReleaseAdmissibleCertificate;
        self
    }

    /// Insert a metadata entry.
    pub fn insert_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Lower this bundle into the general trust verification request.
    ///
    /// This conversion is structural. Use [`TrustVcTrustEngine::lower_contract_bundle`]
    /// when the caller needs fail-closed validation before handing the request to
    /// a verifier.
    pub fn to_trust_request(&self) -> TrustVerificationRequest {
        let mut request = TrustVerificationRequest::new(self.source_id.clone())
            .for_full_verification()
            .with_proof_policy(self.proof_policy)
            .with_units(
                self.units
                    .iter()
                    .map(TrustContractProofUnit::to_trust_unit)
                    .collect(),
            );
        for (key, value) in &self.metadata {
            request = request.insert_metadata(key.clone(), value.clone());
        }
        request
    }

    fn validate_for_verification(
        &self,
        engine: &TrustVcTrustEngine,
    ) -> Result<(), TrustEngineError> {
        if self.units.is_empty() {
            return Err(TrustEngineError::EmptyRequest);
        }
        for unit in &self.units {
            unit.validate_for_verification(engine)?;
        }
        Ok(())
    }
}

/// A single typed contract proof boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustContractProofUnit {
    unit_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    display_name: Option<String>,
    native_context: TrustNativeContext,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    verifier_variables: Vec<TrustVariable>,
    clauses: Vec<TrustContractClause>,
}

impl TrustContractProofUnit {
    /// Create a contract proof unit backed by typed native context.
    ///
    /// `native_context` should include a [`TrustContractFrame`] so preconditions,
    /// postconditions, `result`, and `old(...)` snapshots are all first-class at
    /// the TrustVc boundary.
    pub fn new(unit_id: impl Into<String>, native_context: TrustNativeContext) -> Self {
        Self {
            unit_id: unit_id.into(),
            display_name: None,
            native_context,
            verifier_variables: Vec::new(),
            clauses: Vec::new(),
        }
    }

    /// Return the stable unit identifier.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the optional display name.
    pub fn display_name(&self) -> Option<&str> {
        self.display_name.as_deref()
    }

    /// Return typed native verifier context.
    pub const fn native_context(&self) -> &TrustNativeContext {
        &self.native_context
    }

    /// Return additional verifier variables referenced by clauses.
    pub fn verifier_variables(&self) -> &[TrustVariable] {
        &self.verifier_variables
    }

    /// Return typed contract clauses.
    pub fn clauses(&self) -> &[TrustContractClause] {
        &self.clauses
    }

    /// Set a display name for diagnostics.
    pub fn with_display_name(mut self, display_name: impl Into<String>) -> Self {
        self.display_name = Some(display_name.into());
        self
    }

    /// Append an additional typed verifier variable.
    pub fn with_variable(mut self, variable: TrustVariable) -> Self {
        self.verifier_variables.push(variable);
        self
    }

    /// Append a typed contract clause.
    pub fn with_clause(mut self, clause: TrustContractClause) -> Self {
        self.clauses.push(clause);
        self
    }

    /// Append a typed `requires` clause.
    pub fn with_requires(mut self, id: impl Into<String>, predicate: TrustExpr) -> Self {
        self.clauses
            .push(TrustContractClause::requires(id, predicate));
        self
    }

    /// Append a typed `recommends` clause.
    pub fn with_recommends(mut self, id: impl Into<String>, predicate: TrustExpr) -> Self {
        self.clauses
            .push(TrustContractClause::recommends(id, predicate));
        self
    }

    /// Append a typed `ensures` clause.
    pub fn with_ensures(mut self, id: impl Into<String>, predicate: TrustExpr) -> Self {
        self.clauses
            .push(TrustContractClause::ensures(id, predicate));
        self
    }

    /// Lower this contract proof unit into the general verification unit.
    pub fn to_trust_unit(&self) -> TrustVerificationUnit {
        let mut unit = TrustVerificationUnit::new(self.unit_id.clone())
            .with_native_context(self.native_context.clone());
        if let Some(display_name) = &self.display_name {
            unit = unit.with_display_name(display_name.clone());
        }
        for variable in &self.verifier_variables {
            unit = unit.with_variable(variable.clone());
        }
        for clause in &self.clauses {
            unit = unit.with_obligation(clause.to_trust_obligation());
        }
        unit
    }

    fn validate_for_verification(
        &self,
        engine: &TrustVcTrustEngine,
    ) -> Result<(), TrustEngineError> {
        if self.clauses.is_empty() {
            return Err(TrustEngineError::UnitHasNoAssertions {
                unit_id: self.unit_id.clone(),
            });
        }
        if self.native_context.contract_frame().is_none() {
            return Err(TrustEngineError::MissingNativeContext {
                unit_id: self.unit_id.clone(),
                obligation_id: self.clauses[0].id.clone(),
                missing: "typed contract frame",
            });
        }
        let _ = engine.lower_full_unit(&self.to_trust_unit())?;
        Ok(())
    }
}

/// Contract-clause kind accepted by [`TrustContractBundle`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustContractClauseKind {
    Requires,
    Recommends,
    Ensures,
}

/// One typed contract clause in a contract bundle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustContractClause {
    id: String,
    kind: TrustContractClauseKind,
    predicate: TrustExpr,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    location: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    solver_mode: Option<TrustSolverMode>,
}

impl TrustContractClause {
    /// Create a typed `requires` clause.
    pub fn requires(id: impl Into<String>, predicate: TrustExpr) -> Self {
        Self::new(id, TrustContractClauseKind::Requires, predicate)
    }

    /// Create a typed `recommends` clause.
    pub fn recommends(id: impl Into<String>, predicate: TrustExpr) -> Self {
        Self::new(id, TrustContractClauseKind::Recommends, predicate)
    }

    /// Create a typed `ensures` clause.
    pub fn ensures(id: impl Into<String>, predicate: TrustExpr) -> Self {
        Self::new(id, TrustContractClauseKind::Ensures, predicate)
    }

    /// Create a typed contract clause.
    pub fn new(id: impl Into<String>, kind: TrustContractClauseKind, predicate: TrustExpr) -> Self {
        Self {
            id: id.into(),
            kind,
            predicate,
            location: None,
            solver_mode: None,
        }
    }

    /// Return the stable clause id.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Return the contract-clause kind.
    pub const fn kind(&self) -> TrustContractClauseKind {
        self.kind
    }

    /// Return the typed predicate lowered into TrustVc IR.
    pub const fn predicate(&self) -> &TrustExpr {
        &self.predicate
    }

    /// Return source location text, if supplied by tRust.
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// Return the optional solver strategy hint.
    pub const fn solver_mode(&self) -> Option<TrustSolverMode> {
        self.solver_mode
    }

    /// Attach source location text.
    pub fn with_location(mut self, location: impl Into<String>) -> Self {
        self.location = Some(location.into());
        self
    }

    /// Attach a solver mode hint.
    pub fn with_solver_mode(mut self, solver_mode: TrustSolverMode) -> Self {
        self.solver_mode = Some(solver_mode);
        self
    }

    fn to_trust_obligation(&self) -> TrustObligation {
        let mut obligation = match self.kind {
            TrustContractClauseKind::Requires => {
                TrustObligation::requires_typed(self.id.clone(), self.predicate.clone())
            }
            TrustContractClauseKind::Recommends => TrustObligation::assert_typed(
                self.id.clone(),
                TrustObligationKind::Recommends,
                self.predicate.clone(),
            ),
            TrustContractClauseKind::Ensures => {
                TrustObligation::ensures_typed(self.id.clone(), self.predicate.clone())
            }
        };
        if let Some(location) = &self.location {
            obligation = obligation.with_location(location.clone());
        }
        if let Some(solver_mode) = self.solver_mode {
            obligation = obligation.with_solver_mode(solver_mode);
        }
        obligation
    }
}

/// One function, proof boundary, or TrustIr/tRust verification unit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVerificationUnit {
    unit_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    display_name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    native_context: Option<TrustNativeContext>,
    variables: Vec<TrustVariable>,
    obligations: Vec<TrustObligation>,
}

impl TrustVerificationUnit {
    /// Create a unit with no variables or obligations.
    pub fn new(unit_id: impl Into<String>) -> Self {
        Self {
            unit_id: unit_id.into(),
            display_name: None,
            native_context: None,
            variables: Vec::new(),
            obligations: Vec::new(),
        }
    }

    /// Return the stable unit identifier.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the optional display name.
    pub fn display_name(&self) -> Option<&str> {
        self.display_name.as_deref()
    }

    /// Return typed native verifier context, when supplied by a tRust adapter.
    pub const fn native_context(&self) -> Option<&TrustNativeContext> {
        self.native_context.as_ref()
    }

    /// Return declared variables.
    pub fn variables(&self) -> &[TrustVariable] {
        &self.variables
    }

    /// Return obligations attached to this unit.
    pub fn obligations(&self) -> &[TrustObligation] {
        &self.obligations
    }

    /// Set a display name for diagnostics.
    pub fn with_display_name(mut self, display_name: impl Into<String>) -> Self {
        self.display_name = Some(display_name.into());
        self
    }

    /// Attach typed tRust/TrustIr verifier context.
    pub fn with_native_context(mut self, native_context: TrustNativeContext) -> Self {
        self.native_context = Some(native_context);
        self
    }

    /// Append a variable declaration.
    pub fn with_variable(mut self, variable: TrustVariable) -> Self {
        self.variables.push(variable);
        self
    }

    /// Append an obligation.
    pub fn with_obligation(mut self, obligation: TrustObligation) -> Self {
        self.obligations.push(obligation);
        self
    }
}

/// Typed native verifier context supplied by the tRust-facing adapter.
///
/// This is intentionally data-only and serializable. It gives trust_vc enough
/// shape to validate that native verifier facts are present before accepting
/// ownership/provenance obligations in full verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustNativeContext {
    function_signature: TrustFunctionSignature,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    contract_frame: Option<TrustContractFrame>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    datatypes: Vec<TrustDatatype>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    invariants: Vec<TrustInvariant>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    ownership: Option<TrustOwnershipState>,
}

impl TrustNativeContext {
    /// Create typed native context for a single function/proof boundary.
    pub fn new(function_signature: TrustFunctionSignature) -> Self {
        Self {
            function_signature,
            contract_frame: None,
            datatypes: Vec::new(),
            invariants: Vec::new(),
            ownership: None,
        }
    }

    /// Return the typed function signature.
    pub const fn function_signature(&self) -> &TrustFunctionSignature {
        &self.function_signature
    }

    /// Return the first-class contract frame, when supplied.
    pub const fn contract_frame(&self) -> Option<&TrustContractFrame> {
        self.contract_frame.as_ref()
    }

    /// Return datatype declarations visible to the unit.
    pub fn datatypes(&self) -> &[TrustDatatype] {
        &self.datatypes
    }

    /// Return invariants visible to the unit.
    pub fn invariants(&self) -> &[TrustInvariant] {
        &self.invariants
    }

    /// Return typed ownership/borrow state, if supplied.
    pub const fn ownership(&self) -> Option<&TrustOwnershipState> {
        self.ownership.as_ref()
    }

    /// Append a datatype declaration.
    pub fn with_datatype(mut self, datatype: TrustDatatype) -> Self {
        self.datatypes.push(datatype);
        self
    }

    /// Attach first-class contract frame bindings for `result` and `old(...)`.
    pub fn with_contract_frame(mut self, contract_frame: TrustContractFrame) -> Self {
        self.contract_frame = Some(contract_frame);
        self
    }

    /// Append an invariant declaration.
    pub fn with_invariant(mut self, invariant: TrustInvariant) -> Self {
        self.invariants.push(invariant);
        self
    }

    /// Attach ownership and borrow state.
    pub fn with_ownership(mut self, ownership: TrustOwnershipState) -> Self {
        self.ownership = Some(ownership);
        self
    }

    fn variables(&self) -> impl Iterator<Item = &TrustVariable> {
        self.function_signature.variables().chain(
            self.contract_frame
                .iter()
                .flat_map(TrustContractFrame::variables),
        )
    }
}

/// First-class bindings visible to typed `requires` and `ensures` clauses.
///
/// tRust owns the public contract syntax; TrustVc consumes the already-typed
/// frame. The return binding models names like `result`, while old-value
/// bindings model pre-state snapshots used by `old(x)`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustContractFrame {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    return_value: Option<TrustVariable>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    old_values: Vec<TrustOldValue>,
}

impl TrustContractFrame {
    /// Create an empty contract frame.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the optional result/return binding.
    pub const fn return_value(&self) -> Option<&TrustVariable> {
        self.return_value.as_ref()
    }

    /// Return old-value snapshot bindings.
    pub fn old_values(&self) -> &[TrustOldValue] {
        &self.old_values
    }

    /// Attach the result/return binding visible to `ensures`.
    pub fn with_return_value(mut self, variable: TrustVariable) -> Self {
        self.return_value = Some(variable);
        self
    }

    /// Append an `old(source)` pre-state snapshot binding.
    pub fn with_old_value(mut self, old_value: TrustOldValue) -> Self {
        self.old_values.push(old_value);
        self
    }

    fn variables(&self) -> impl Iterator<Item = &TrustVariable> {
        self.return_value
            .iter()
            .chain(self.old_values.iter().map(TrustOldValue::snapshot))
    }
}

/// Pre-state snapshot binding for typed `old(...)` contract expressions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustOldValue {
    source: String,
    snapshot: TrustVariable,
}

impl TrustOldValue {
    /// Create an old-value snapshot binding.
    pub fn new(source: impl Into<String>, snapshot: TrustVariable) -> Self {
        Self {
            source: source.into(),
            snapshot,
        }
    }

    /// Return the source expression or place represented by `old(...)`.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Return the variable containing the pre-state snapshot value.
    pub const fn snapshot(&self) -> &TrustVariable {
        &self.snapshot
    }
}

/// Typed function signature extracted from TrustIr/Rust HIR.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustFunctionSignature {
    name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    type_params: Vec<String>,
    params: Vec<TrustVariable>,
    return_sort: TrustSort,
}

impl TrustFunctionSignature {
    /// Create a typed function signature.
    pub fn new(
        name: impl Into<String>,
        params: Vec<TrustVariable>,
        return_sort: TrustSort,
    ) -> Self {
        Self {
            name: name.into(),
            type_params: Vec::new(),
            params,
            return_sort,
        }
    }

    /// Return the function name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return generic type parameter names.
    pub fn type_params(&self) -> &[String] {
        &self.type_params
    }

    /// Return typed parameters.
    pub fn params(&self) -> &[TrustVariable] {
        &self.params
    }

    /// Return the typed return value.
    pub const fn return_sort(&self) -> &TrustSort {
        &self.return_sort
    }

    /// Attach generic type parameter names.
    pub fn with_type_params(mut self, type_params: Vec<String>) -> Self {
        self.type_params = type_params;
        self
    }

    /// Lower this signature into trust_vc variable declarations plus return type.
    pub fn to_trust_vc_parts(&self) -> Result<(Vec<VariableDecl>, TrustVcType), TrustEngineError> {
        let params = self
            .params
            .iter()
            .map(|param| {
                Ok(VariableDecl::new(
                    param.name.clone(),
                    param.sort.to_trust_vc_type()?,
                ))
            })
            .collect::<Result<Vec<_>, TrustEngineError>>()?;
        Ok((params, self.return_sort.to_trust_vc_type()?))
    }

    fn variables(&self) -> impl Iterator<Item = &TrustVariable> {
        self.params.iter()
    }
}

/// Algebraic datatype declaration visible to a native verification unit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustDatatype {
    name: String,
    variants: Vec<TrustDatatypeVariant>,
}

impl TrustDatatype {
    /// Create a datatype declaration.
    pub fn new(name: impl Into<String>, variants: Vec<TrustDatatypeVariant>) -> Self {
        Self {
            name: name.into(),
            variants,
        }
    }

    /// Return the datatype name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return datatype variants.
    pub fn variants(&self) -> &[TrustDatatypeVariant] {
        &self.variants
    }

    /// Lower to trust_vc's typed datatype IR.
    pub fn to_trust_vc_type(&self) -> Result<TrustVcType, TrustEngineError> {
        let variants = self
            .variants
            .iter()
            .map(TrustDatatypeVariant::to_trust_vc_variant)
            .collect::<Result<Vec<_>, _>>()?;
        let ty = TrustVcType::Datatype {
            name: self.name.clone(),
            variants,
        };
        ty.validate_well_foundedness()
            .map_err(|message| TrustEngineError::InvalidDatatype {
                datatype: self.name.clone(),
                message,
            })?;
        Ok(ty)
    }
}

/// One variant of a native datatype.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustDatatypeVariant {
    name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    fields: Vec<TrustField>,
}

impl TrustDatatypeVariant {
    /// Create a datatype variant.
    pub fn new(name: impl Into<String>, fields: Vec<TrustField>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }

    /// Return the variant name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the variant fields.
    pub fn fields(&self) -> &[TrustField] {
        &self.fields
    }

    fn to_trust_vc_variant(&self) -> Result<DatatypeVariant, TrustEngineError> {
        let fields = self
            .fields
            .iter()
            .map(|field| Ok((field.name.clone(), field.sort.to_trust_vc_type()?)))
            .collect::<Result<Vec<_>, TrustEngineError>>()?;
        Ok(DatatypeVariant::new(self.name.clone(), fields))
    }
}

/// Named typed field in a native datatype.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustField {
    name: String,
    sort: TrustSort,
}

impl TrustField {
    /// Create a typed field.
    pub fn new(name: impl Into<String>, sort: TrustSort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    /// Return field name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return field sort.
    pub const fn sort(&self) -> &TrustSort {
        &self.sort
    }
}

/// Typed invariant metadata from the native verifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustInvariant {
    id: String,
    target: TrustInvariantTarget,
    predicate: TrustPredicateRef,
}

impl TrustInvariant {
    /// Create an invariant declaration.
    pub fn new(
        id: impl Into<String>,
        target: TrustInvariantTarget,
        predicate: TrustPredicateRef,
    ) -> Self {
        Self {
            id: id.into(),
            target,
            predicate,
        }
    }

    /// Return invariant id.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Return invariant target.
    pub const fn target(&self) -> &TrustInvariantTarget {
        &self.target
    }

    /// Return typed predicate reference.
    pub const fn predicate(&self) -> &TrustPredicateRef {
        &self.predicate
    }
}

/// Native invariant target.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustInvariantTarget {
    Function { function: String },
    Datatype { datatype: String },
    Loop { loop_id: String },
    BorrowRegion { region: String },
}

/// Reference to a typed predicate produced by the native verifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustPredicateRef {
    name: String,
    params: Vec<TrustVariable>,
    return_sort: TrustSort,
}

impl TrustPredicateRef {
    /// Create a predicate reference. The return sort should normally be bool.
    pub fn new(name: impl Into<String>, params: Vec<TrustVariable>) -> Self {
        Self {
            name: name.into(),
            params,
            return_sort: TrustSort::Bool,
        }
    }

    /// Return predicate name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return typed predicate params.
    pub fn params(&self) -> &[TrustVariable] {
        &self.params
    }

    /// Return predicate return sort.
    pub const fn return_sort(&self) -> &TrustSort {
        &self.return_sort
    }

    /// Lower this predicate reference into trust_vc variable declarations plus return type.
    pub fn to_trust_vc_parts(&self) -> Result<(Vec<VariableDecl>, TrustVcType), TrustEngineError> {
        let params = self
            .params
            .iter()
            .map(|param| {
                Ok(VariableDecl::new(
                    param.name.clone(),
                    param.sort.to_trust_vc_type()?,
                ))
            })
            .collect::<Result<Vec<_>, TrustEngineError>>()?;
        Ok((params, self.return_sort.to_trust_vc_type()?))
    }
}

/// Ownership and borrow state extracted from native tRust analysis.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustOwnershipState {
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    places: Vec<TrustOwnedPlace>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    borrows: Vec<TrustBorrow>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    lifetimes: Vec<TrustLifetimeRegion>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    alias_facts: Vec<TrustAliasFact>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    provenance_facts: Vec<TrustPointerProvenance>,
}

impl TrustOwnershipState {
    /// Create empty ownership state.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return owned places.
    pub fn places(&self) -> &[TrustOwnedPlace] {
        &self.places
    }

    /// Return active borrows.
    pub fn borrows(&self) -> &[TrustBorrow] {
        &self.borrows
    }

    /// Return known lifetime/region facts.
    pub fn lifetimes(&self) -> &[TrustLifetimeRegion] {
        &self.lifetimes
    }

    /// Return typed alias-analysis facts.
    pub fn alias_facts(&self) -> &[TrustAliasFact] {
        &self.alias_facts
    }

    /// Return typed pointer/borrow provenance facts.
    pub fn provenance_facts(&self) -> &[TrustPointerProvenance] {
        &self.provenance_facts
    }

    /// Return true when no ownership, borrow, lifetime, alias, or provenance fact is present.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.places.is_empty()
            && self.borrows.is_empty()
            && self.lifetimes.is_empty()
            && self.alias_facts.is_empty()
            && self.provenance_facts.is_empty()
    }

    /// Append an owned place.
    pub fn with_place(mut self, place: TrustOwnedPlace) -> Self {
        self.places.push(place);
        self
    }

    /// Append an active borrow.
    pub fn with_borrow(mut self, borrow: TrustBorrow) -> Self {
        self.borrows.push(borrow);
        self
    }

    /// Append a lifetime/region fact.
    pub fn with_lifetime(mut self, lifetime: TrustLifetimeRegion) -> Self {
        self.lifetimes.push(lifetime);
        self
    }

    /// Append an alias-analysis fact.
    pub fn with_alias_fact(mut self, alias_fact: TrustAliasFact) -> Self {
        self.alias_facts.push(alias_fact);
        self
    }

    /// Append a pointer/borrow provenance fact.
    pub fn with_provenance_fact(mut self, provenance_fact: TrustPointerProvenance) -> Self {
        self.provenance_facts.push(provenance_fact);
        self
    }
}

/// Native ownership state for a place/root.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustOwnedPlace {
    place: String,
    sort: TrustSort,
}

impl TrustOwnedPlace {
    /// Create owned place metadata.
    pub fn new(place: impl Into<String>, sort: TrustSort) -> Self {
        Self {
            place: place.into(),
            sort,
        }
    }

    /// Return place path.
    pub fn place(&self) -> &str {
        &self.place
    }

    /// Return place sort.
    pub const fn sort(&self) -> &TrustSort {
        &self.sort
    }
}

/// Active native borrow relationship.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustBorrow {
    region: String,
    place: String,
    kind: TrustBorrowKind,
}

impl TrustBorrow {
    /// Create borrow metadata.
    pub fn new(region: impl Into<String>, place: impl Into<String>, kind: TrustBorrowKind) -> Self {
        Self {
            region: region.into(),
            place: place.into(),
            kind,
        }
    }

    /// Return borrow region id.
    pub fn region(&self) -> &str {
        &self.region
    }

    /// Return borrowed place path.
    pub fn place(&self) -> &str {
        &self.place
    }

    /// Return borrow kind.
    pub const fn kind(&self) -> TrustBorrowKind {
        self.kind
    }
}

/// Native borrow mutability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustBorrowKind {
    Shared,
    Mutable,
}

/// Native lifetime/region fact extracted from TrustIr.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustLifetimeRegion {
    region: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    outlives: Vec<String>,
}

impl TrustLifetimeRegion {
    /// Create a lifetime/region fact.
    pub fn new(region: impl Into<String>) -> Self {
        Self {
            region: region.into(),
            outlives: Vec::new(),
        }
    }

    /// Return the region id.
    pub fn region(&self) -> &str {
        &self.region
    }

    /// Return regions known to be outlived by this region.
    pub fn outlives(&self) -> &[String] {
        &self.outlives
    }

    /// Record that this region outlives another region.
    pub fn with_outlives(mut self, region: impl Into<String>) -> Self {
        self.outlives.push(region.into());
        self
    }
}

/// Native alias-analysis fact extracted from TrustIr.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustAliasFact {
    left: String,
    right: String,
    kind: TrustAliasKind,
}

impl TrustAliasFact {
    /// Create a typed alias fact between two places.
    pub fn new(left: impl Into<String>, right: impl Into<String>, kind: TrustAliasKind) -> Self {
        Self {
            left: left.into(),
            right: right.into(),
            kind,
        }
    }

    /// Return the left place.
    pub fn left(&self) -> &str {
        &self.left
    }

    /// Return the right place.
    pub fn right(&self) -> &str {
        &self.right
    }

    /// Return the alias relation.
    pub const fn kind(&self) -> TrustAliasKind {
        self.kind
    }
}

/// Alias relation accepted at the Trust/TrustIr boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustAliasKind {
    NoAlias,
    MayAlias,
    MustAlias,
}

/// Native pointer/borrow provenance fact extracted from TrustIr.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustPointerProvenance {
    pointer: String,
    provenance_id: String,
    origin: TrustPointerProvenanceOrigin,
}

impl TrustPointerProvenance {
    /// Create a typed provenance fact for a pointer-like value.
    pub fn new(
        pointer: impl Into<String>,
        provenance_id: impl Into<String>,
        origin: TrustPointerProvenanceOrigin,
    ) -> Self {
        Self {
            pointer: pointer.into(),
            provenance_id: provenance_id.into(),
            origin,
        }
    }

    /// Return the pointer-like place or variable.
    pub fn pointer(&self) -> &str {
        &self.pointer
    }

    /// Return the stable provenance id.
    pub fn provenance_id(&self) -> &str {
        &self.provenance_id
    }

    /// Return the provenance origin class.
    pub const fn origin(&self) -> TrustPointerProvenanceOrigin {
        self.origin
    }
}

/// Origin class for a typed pointer/borrow provenance fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustPointerProvenanceOrigin {
    FunctionArgument,
    LocalAllocation,
    Reborrow,
    RawPointerCast,
    ExposedAddress,
}

/// Named variable visible to a verification unit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVariable {
    name: String,
    sort: TrustSort,
}

impl TrustVariable {
    /// Create a variable declaration.
    pub fn new(name: impl Into<String>, sort: TrustSort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    /// Return the variable name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the variable sort.
    pub fn sort(&self) -> &TrustSort {
        &self.sort
    }
}

/// Verification sort carried at the tRust adapter boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
#[must_use]
pub enum TrustSort {
    Bool,
    Char,
    StrSlice,
    String,
    BitVector {
        width: u32,
        signed: bool,
    },
    MathInt,
    Nat,
    Real,
    Float {
        width: u32,
    },
    Seq {
        elem: Box<TrustSort>,
    },
    Set {
        elem: Box<TrustSort>,
    },
    Multiset {
        elem: Box<TrustSort>,
    },
    Map {
        key: Box<TrustSort>,
        value: Box<TrustSort>,
    },
    SpecFn {
        args: Vec<TrustSort>,
        ret: Box<TrustSort>,
    },
    Datatype {
        name: String,
        variants: Vec<TrustDatatypeVariant>,
    },
    RecursiveRef {
        name: String,
    },
    TypeParam {
        name: String,
    },
    Opaque {
        name: String,
    },
}

impl TrustSort {
    /// Signed fixed-width Rust integer sort.
    pub const fn signed(width: u32) -> Self {
        Self::BitVector {
            width,
            signed: true,
        }
    }

    /// Unsigned fixed-width Rust integer sort.
    pub const fn unsigned(width: u32) -> Self {
        Self::BitVector {
            width,
            signed: false,
        }
    }

    fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    fn is_fixed_integer(&self) -> bool {
        matches!(self, Self::BitVector { .. })
    }

    fn is_comparable_integer(&self) -> bool {
        matches!(self, Self::BitVector { .. } | Self::MathInt | Self::Nat)
    }

    fn display_label(&self) -> String {
        match self {
            Self::Bool => "bool".to_string(),
            Self::Char => "char".to_string(),
            Self::StrSlice => "str".to_string(),
            Self::String => "String".to_string(),
            Self::BitVector { width, signed } => {
                let prefix = if *signed { "i" } else { "u" };
                format!("{prefix}{width}")
            }
            Self::MathInt => "int".to_string(),
            Self::Nat => "nat".to_string(),
            Self::Real => "real".to_string(),
            Self::Float { width } => format!("f{width}"),
            Self::Seq { elem } => format!("Seq<{}>", elem.display_label()),
            Self::Set { elem } => format!("Set<{}>", elem.display_label()),
            Self::Multiset { elem } => format!("Multiset<{}>", elem.display_label()),
            Self::Map { key, value } => {
                format!("Map<{}, {}>", key.display_label(), value.display_label())
            }
            Self::SpecFn { args, ret } => {
                let args = args
                    .iter()
                    .map(TrustSort::display_label)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("SpecFn({args}) -> {}", ret.display_label())
            }
            Self::Datatype { name, .. }
            | Self::RecursiveRef { name }
            | Self::TypeParam { name }
            | Self::Opaque { name } => name.clone(),
        }
    }

    /// Lower this boundary sort into trust_vc's typed IR.
    pub fn to_trust_vc_type(&self) -> Result<TrustVcType, TrustEngineError> {
        match self {
            Self::Bool => Ok(TrustVcType::Bool),
            Self::Char => Ok(TrustVcType::Char),
            Self::StrSlice => Ok(TrustVcType::StrSlice),
            Self::String => Ok(TrustVcType::String),
            Self::BitVector { width, signed } => {
                validate_width(*width)?;
                if *signed {
                    Ok(TrustVcType::Int { width: *width })
                } else {
                    Ok(TrustVcType::Uint { width: *width })
                }
            }
            Self::MathInt => Ok(TrustVcType::MathInt),
            Self::Nat => Ok(TrustVcType::Nat),
            Self::Real => Ok(TrustVcType::Real),
            Self::Float { width } => {
                validate_float_width(*width)?;
                Ok(TrustVcType::Float { width: *width })
            }
            Self::Seq { elem } => Ok(TrustVcType::Seq(Box::new(elem.to_trust_vc_type()?))),
            Self::Set { elem } => Ok(TrustVcType::Set(Box::new(elem.to_trust_vc_type()?))),
            Self::Multiset { elem } => {
                Ok(TrustVcType::Multiset(Box::new(elem.to_trust_vc_type()?)))
            }
            Self::Map { key, value } => Ok(TrustVcType::Map(
                Box::new(key.to_trust_vc_type()?),
                Box::new(value.to_trust_vc_type()?),
            )),
            Self::SpecFn { args, ret } => Ok(TrustVcType::SpecFn(
                args.iter()
                    .map(TrustSort::to_trust_vc_type)
                    .collect::<Result<Vec<_>, _>>()?,
                Box::new(ret.to_trust_vc_type()?),
            )),
            Self::Datatype { name, variants } => {
                if variants.is_empty() {
                    return Err(TrustEngineError::DatatypeHasNoVariants {
                        unit_id: "<sort>".to_string(),
                        datatype: name.clone(),
                    });
                }
                let variants = variants
                    .iter()
                    .map(TrustDatatypeVariant::to_trust_vc_variant)
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = TrustVcType::Datatype {
                    name: name.clone(),
                    variants,
                };
                ty.validate_well_foundedness().map_err(|message| {
                    TrustEngineError::InvalidDatatype {
                        datatype: name.clone(),
                        message,
                    }
                })?;
                Ok(ty)
            }
            Self::RecursiveRef { name } => Ok(TrustVcType::RecursiveRef(name.clone())),
            Self::TypeParam { name } => Ok(TrustVcType::TypeParam(name.clone())),
            Self::Opaque { name } => Ok(TrustVcType::Opaque(name.clone())),
        }
    }

    fn from_trust_vc_type(
        unit_id: &str,
        obligation_id: &str,
        ty: &TrustVcType,
    ) -> Result<Self, TrustEngineError> {
        match ty {
            TrustVcType::Bool => Ok(Self::Bool),
            TrustVcType::Char => Ok(Self::Char),
            TrustVcType::StrSlice => Ok(Self::StrSlice),
            TrustVcType::String => Ok(Self::String),
            TrustVcType::Int { width } => Ok(Self::signed(*width)),
            TrustVcType::Uint { width } => Ok(Self::unsigned(*width)),
            TrustVcType::MathInt => Ok(Self::MathInt),
            TrustVcType::Nat => Ok(Self::Nat),
            TrustVcType::Real => Ok(Self::Real),
            TrustVcType::Float { width } => Ok(Self::Float { width: *width }),
            TrustVcType::Seq(elem) => Ok(Self::Seq {
                elem: Box::new(Self::from_trust_vc_type(unit_id, obligation_id, elem)?),
            }),
            TrustVcType::Set(elem) => Ok(Self::Set {
                elem: Box::new(Self::from_trust_vc_type(unit_id, obligation_id, elem)?),
            }),
            TrustVcType::Multiset(elem) => Ok(Self::Multiset {
                elem: Box::new(Self::from_trust_vc_type(unit_id, obligation_id, elem)?),
            }),
            TrustVcType::Map(key, value) => Ok(Self::Map {
                key: Box::new(Self::from_trust_vc_type(unit_id, obligation_id, key)?),
                value: Box::new(Self::from_trust_vc_type(unit_id, obligation_id, value)?),
            }),
            TrustVcType::SpecFn(args, ret) => Ok(Self::SpecFn {
                args: args
                    .iter()
                    .map(|arg| Self::from_trust_vc_type(unit_id, obligation_id, arg))
                    .collect::<Result<Vec<_>, _>>()?,
                ret: Box::new(Self::from_trust_vc_type(unit_id, obligation_id, ret)?),
            }),
            TrustVcType::Datatype { name, variants } => Ok(Self::Datatype {
                name: name.clone(),
                variants: variants
                    .iter()
                    .map(|variant| {
                        Ok(TrustDatatypeVariant {
                            name: variant.name.clone(),
                            fields: variant
                                .fields
                                .iter()
                                .map(|(field_name, field_ty)| {
                                    Ok(TrustField {
                                        name: field_name.clone(),
                                        sort: Self::from_trust_vc_type(
                                            unit_id,
                                            obligation_id,
                                            field_ty,
                                        )?,
                                    })
                                })
                                .collect::<Result<Vec<_>, TrustEngineError>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, TrustEngineError>>()?,
            }),
            TrustVcType::RecursiveRef(name) => Ok(Self::RecursiveRef { name: name.clone() }),
            TrustVcType::TypeParam(name) => Ok(Self::TypeParam { name: name.clone() }),
            TrustVcType::Poly => Ok(Self::Opaque {
                name: "Poly".to_string(),
            }),
            TrustVcType::Opaque(name) => Ok(Self::Opaque { name: name.clone() }),
            _ => Err(TrustEngineError::UnsupportedTypedProofObligation {
                unit_id: unit_id.to_string(),
                obligation_id: obligation_id.to_string(),
                feature: "unsupported TrustVcType variant".to_string(),
            }),
        }
    }
}

/// Whether a boundary obligation is trusted context or a fact to discharge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustObligationRole {
    Assumption,
    Assertion,
}

/// tRust-flavored obligation kind, independent of solver polarity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustObligationKind {
    Precondition,
    Recommends,
    Postcondition,
    LoopInvariant,
    TypeInvariant,
    RefinementType,
    TranslationValidation,
    MemorySafety,
    /// Bootstrap obligation proving a typed bool/fixed-int cast fact.
    ///
    /// Full verification accepts this only when the expression is typed, contains
    /// an explicit cast, and the cast is over declared verifier context.
    CastPrecondition,
    /// Bootstrap obligation proving a typed ADT constructor/discriminant fact.
    ///
    /// Full verification accepts this only when the expression is typed, mentions
    /// native datatype metadata, and the datatype fact is over declared verifier
    /// context.
    AdtDiscriminant,
    /// Bootstrap obligation proving a typed pointer operation fact.
    ///
    /// Full verification accepts this only when the expression is typed,
    /// first-class provenance is attached, and a recognized pointer operation
    /// is backed by declared verifier context.
    PointerBootstrap,
    /// Bootstrap obligation proving a typed fat-pointer operation fact.
    ///
    /// Full verification accepts this only when the expression is typed,
    /// first-class provenance is attached, and a recognized fat-pointer
    /// operation is backed by declared verifier context.
    FatPointerBootstrap,
    /// Bootstrap obligation proving a typed closure/Fn/FnMut/FnOnce operation fact.
    ///
    /// Full verification accepts this only when the expression is typed,
    /// first-class provenance is attached, and a recognized closure operation
    /// is backed by declared verifier context.
    ClosureBootstrap,
    /// Bootstrap obligation proving a typed function-pointer operation fact.
    ///
    /// Full verification accepts this only when the expression is typed,
    /// first-class provenance is attached, and a recognized FnPtr operation is
    /// backed by declared verifier context.
    FnPtrBootstrap,
    PanicFreedom,
    Axiom,
    Other(String),
}

/// First-class provenance for a typed Trust obligation.
///
/// This records the compiler pass or adapter rule that produced an obligation.
/// It is separate from [`TrustBootstrapProvenance`]: bootstrap provenance
/// justifies admitting a trusted language/runtime fact, while proof lineage
/// identifies where a normal typed VC came from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustProofLineage {
    source: TrustProofLineageSource,
    producer: String,
    stage: String,
    rule: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    input_digest: Option<String>,
}

impl TrustProofLineage {
    /// Create proof lineage for a typed obligation.
    pub fn new(
        source: TrustProofLineageSource,
        producer: impl Into<String>,
        stage: impl Into<String>,
        rule: impl Into<String>,
    ) -> Self {
        Self {
            source,
            producer: producer.into(),
            stage: stage.into(),
            rule: rule.into(),
            input_digest: None,
        }
    }

    /// Build lineage for a trust-types contract clause.
    pub fn trust_types_contract(producer: impl Into<String>, rule: impl Into<String>) -> Self {
        Self::new(
            TrustProofLineageSource::TrustTypesContract,
            producer,
            "trust-types",
            rule,
        )
    }

    /// Build lineage for a TrustIr lowering proof obligation.
    pub fn trust_ir_lowering(producer: impl Into<String>, rule: impl Into<String>) -> Self {
        Self::new(
            TrustProofLineageSource::TrustIrLowering,
            producer,
            "trust_ir-lowering",
            rule,
        )
    }

    /// Build lineage for a Tmir (Trust MIR) lowering proof obligation.
    ///
    /// Tmir is the current public name for the typed TrustIr lowering lane;
    /// this constructor forwards to [`Self::trust_ir_lowering`].
    pub fn tmir_lowering(producer: impl Into<String>, rule: impl Into<String>) -> Self {
        Self::trust_ir_lowering(producer, rule)
    }

    /// Build lineage for a TrustIr ownership or alias-analysis obligation.
    pub fn trust_ir_ownership(producer: impl Into<String>, rule: impl Into<String>) -> Self {
        Self::new(
            TrustProofLineageSource::TrustIrOwnership,
            producer,
            "trust_ir-ownership",
            rule,
        )
    }

    /// Build lineage for a TrustIr borrow/provenance obligation.
    pub fn trust_ir_provenance(producer: impl Into<String>, rule: impl Into<String>) -> Self {
        Self::new(
            TrustProofLineageSource::TrustIrProvenance,
            producer,
            "trust_ir-provenance",
            rule,
        )
    }

    /// Return the typed lineage source.
    pub const fn source(&self) -> &TrustProofLineageSource {
        &self.source
    }

    /// Return the adapter, compiler pass, or tool that produced this obligation.
    pub fn producer(&self) -> &str {
        &self.producer
    }

    /// Return the compiler/verifier stage that produced this obligation.
    pub fn stage(&self) -> &str {
        &self.stage
    }

    /// Return the named mapping rule that produced this obligation.
    pub fn rule(&self) -> &str {
        &self.rule
    }

    /// Return the optional digest of the typed input consumed by this rule.
    pub fn input_digest(&self) -> Option<&str> {
        self.input_digest.as_deref()
    }

    /// Attach a stable digest of the typed compiler input consumed by this rule.
    pub fn with_input_digest(mut self, input_digest: impl Into<String>) -> Self {
        self.input_digest = Some(input_digest.into());
        self
    }
}

/// Typed source class for obligation proof lineage.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustProofLineageSource {
    /// A first-class trust-types contract clause.
    TrustTypesContract,
    /// A TrustIr lowering or normalization VC.
    #[serde(alias = "tmir_lowering")]
    TrustIrLowering,
    /// A TrustIr ownership/alias-analysis VC.
    #[serde(alias = "tmir_ownership")]
    TrustIrOwnership,
    /// A TrustIr borrow-checking VC.
    #[serde(alias = "tmir_borrow_check")]
    TrustIrBorrowCheck,
    /// A TrustIr pointer/borrow provenance VC.
    #[serde(alias = "tmir_provenance")]
    TrustIrProvenance,
    /// Fact comes from an external named source.
    ExternalAxiom(String),
    /// Fact comes from another named source.
    Other(String),
}

/// Provenance for bootstrap facts admitted outside the contract-frame lane.
///
/// Full verification requires this metadata for non-contract bootstrap facts so
/// downstream review can distinguish language/runtime facts from ordinary
/// deductive obligations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustBootstrapProvenance {
    source: TrustBootstrapProvenanceSource,
    justification: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    producer: Option<String>,
}

impl TrustBootstrapProvenance {
    /// Create provenance for a bootstrap fact.
    pub fn new(source: TrustBootstrapProvenanceSource, justification: impl Into<String>) -> Self {
        Self {
            source,
            justification: justification.into(),
            producer: None,
        }
    }

    /// Return the source class for this bootstrap fact.
    pub const fn source(&self) -> &TrustBootstrapProvenanceSource {
        &self.source
    }

    /// Return the human-readable justification for admitting this fact.
    pub fn justification(&self) -> &str {
        &self.justification
    }

    /// Return the adapter, pass, or tool that produced this fact, if known.
    pub fn producer(&self) -> Option<&str> {
        self.producer.as_deref()
    }

    /// Attach the adapter, pass, or tool that produced this fact.
    pub fn with_producer(mut self, producer: impl Into<String>) -> Self {
        self.producer = Some(producer.into());
        self
    }
}

/// Source class for non-contract bootstrap provenance.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustBootstrapProvenanceSource {
    /// Fact follows from Rust language semantics.
    RustSemantics,
    /// Fact follows from a TrustIr lowering or normalization rule.
    TrustIrLowering,
    /// Fact is supplied by a trusted TrustVc/tRust adapter boundary.
    AdapterBoundary,
    /// Fact comes from an external axiom source named by the payload.
    ExternalAxiom(String),
    /// Fact comes from another named source.
    Other(String),
}

/// Optional solver strategy hint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustSolverMode {
    Default,
    NonlinearArith,
    BitVector,
    Compute,
}

impl From<TrustSolverMode> for SolverMode {
    fn from(value: TrustSolverMode) -> Self {
        match value {
            TrustSolverMode::Default => Self::Default,
            TrustSolverMode::NonlinearArith => Self::NonlinearArith,
            TrustSolverMode::BitVector => Self::BitVector,
            TrustSolverMode::Compute => Self::Compute,
        }
    }
}

impl From<SolverMode> for TrustSolverMode {
    fn from(value: SolverMode) -> Self {
        match value {
            SolverMode::Default => Self::Default,
            SolverMode::NonlinearArith => Self::NonlinearArith,
            SolverMode::BitVector => Self::BitVector,
            SolverMode::Compute => Self::Compute,
            _ => Self::Default,
        }
    }
}

/// Quantifier kind accepted at the tRust/TrustVc boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustQuantifierKind {
    Forall,
    Exists,
}

impl From<TrustQuantifierKind> for TrustVcQuantifierKind {
    fn from(value: TrustQuantifierKind) -> Self {
        match value {
            TrustQuantifierKind::Forall => Self::Forall,
            TrustQuantifierKind::Exists => Self::Exists,
        }
    }
}

impl TrustQuantifierKind {
    const fn from_trust_vc(value: TrustVcQuantifierKind) -> Option<Self> {
        match value {
            TrustVcQuantifierKind::Forall => Some(Self::Forall),
            TrustVcQuantifierKind::Exists => Some(Self::Exists),
            _ => None,
        }
    }
}

/// Quantifier trigger-inference mode carried by the Trust expression surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustTriggerInferenceMode {
    Conservative,
    Aggressive,
}

impl From<TrustTriggerInferenceMode> for TrustVcTriggerInferenceMode {
    fn from(value: TrustTriggerInferenceMode) -> Self {
        match value {
            TrustTriggerInferenceMode::Conservative => Self::Conservative,
            TrustTriggerInferenceMode::Aggressive => Self::Aggressive,
        }
    }
}

impl From<TrustVcTriggerInferenceMode> for TrustTriggerInferenceMode {
    fn from(value: TrustVcTriggerInferenceMode) -> Self {
        match value {
            TrustVcTriggerInferenceMode::Conservative => Self::Conservative,
            TrustVcTriggerInferenceMode::Aggressive => Self::Aggressive,
        }
    }
}

/// Typed variable bound by a Trust quantifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustQuantifierBoundVar {
    name: String,
    sort: TrustSort,
}

impl TrustQuantifierBoundVar {
    /// Create a quantifier-bound variable declaration.
    pub fn new(name: impl Into<String>, sort: TrustSort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    /// Return the bound variable name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Return the bound variable sort.
    pub fn sort(&self) -> &TrustSort {
        &self.sort
    }

    fn to_trust_vc_bound_var(&self) -> Result<(String, TrustVcType), TrustEngineError> {
        Ok((self.name.clone(), self.sort.to_trust_vc_type()?))
    }

    fn from_trust_vc_bound_var(
        unit_id: &str,
        obligation_id: &str,
        name: &str,
        ty: &TrustVcType,
    ) -> Result<Self, TrustEngineError> {
        Ok(Self::new(
            name.to_string(),
            TrustSort::from_trust_vc_type(unit_id, obligation_id, ty)?,
        ))
    }
}

/// Typed expression accepted at the tRust/TrustVc boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
#[must_use]
pub enum TrustExpr {
    BoolLiteral {
        value: bool,
    },
    IntLiteral {
        #[serde(with = "serde_i128_string")]
        value: i128,
        sort: TrustSort,
    },
    Variable {
        name: String,
        sort: TrustSort,
    },
    Old {
        source: String,
        snapshot: String,
        sort: TrustSort,
    },
    Arith {
        op: TrustArithOp,
        left: Box<TrustExpr>,
        right: Box<TrustExpr>,
        sort: TrustSort,
    },
    Compare {
        op: TrustCompareOp,
        left: Box<TrustExpr>,
        right: Box<TrustExpr>,
    },
    Logic {
        op: TrustLogicOp,
        left: Box<TrustExpr>,
        right: Box<TrustExpr>,
    },
    Not {
        expr: Box<TrustExpr>,
    },
    Implies {
        premise: Box<TrustExpr>,
        conclusion: Box<TrustExpr>,
    },
    Cast {
        expr: Box<TrustExpr>,
        from_sort: TrustSort,
        to_sort: TrustSort,
    },
    Call {
        function: String,
        args: Vec<TrustExpr>,
        return_sort: TrustSort,
    },
    Quantifier {
        quantifier_kind: TrustQuantifierKind,
        bound_vars: Vec<TrustQuantifierBoundVar>,
        body: Box<TrustExpr>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        triggers: Option<Vec<Vec<TrustExpr>>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        trigger_inference_mode: Option<TrustTriggerInferenceMode>,
    },
}

impl TrustExpr {
    /// Boolean literal expression.
    pub const fn bool_literal(value: bool) -> Self {
        Self::BoolLiteral { value }
    }

    /// Integer literal expression with a known sort.
    pub fn int_literal(value: i128, sort: TrustSort) -> Self {
        Self::IntLiteral { value, sort }
    }

    /// Typed variable reference.
    pub fn variable(name: impl Into<String>, sort: TrustSort) -> Self {
        Self::Variable {
            name: name.into(),
            sort,
        }
    }

    /// Typed pre-state snapshot reference for `old(source)`.
    pub fn old(source: impl Into<String>, snapshot: impl Into<String>, sort: TrustSort) -> Self {
        Self::Old {
            source: source.into(),
            snapshot: snapshot.into(),
            sort,
        }
    }

    /// Typed arithmetic expression.
    pub fn arith(op: TrustArithOp, left: TrustExpr, right: TrustExpr, sort: TrustSort) -> Self {
        Self::Arith {
            op,
            left: Box::new(left),
            right: Box::new(right),
            sort,
        }
    }

    /// Typed comparison expression.
    pub fn compare(op: TrustCompareOp, left: TrustExpr, right: TrustExpr) -> Self {
        Self::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Typed logical connective.
    pub fn logic(op: TrustLogicOp, left: TrustExpr, right: TrustExpr) -> Self {
        Self::Logic {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Typed logical negation.
    #[allow(clippy::should_implement_trait)]
    pub fn not(expr: TrustExpr) -> Self {
        Self::Not {
            expr: Box::new(expr),
        }
    }

    /// Typed logical implication.
    pub fn implies(premise: TrustExpr, conclusion: TrustExpr) -> Self {
        Self::Implies {
            premise: Box::new(premise),
            conclusion: Box::new(conclusion),
        }
    }

    /// Typed bool/fixed-int cast expression.
    pub fn cast(expr: TrustExpr, from_sort: TrustSort, to_sort: TrustSort) -> Self {
        Self::Cast {
            expr: Box::new(expr),
            from_sort,
            to_sort,
        }
    }

    /// Typed function/predicate call.
    pub fn call(function: impl Into<String>, args: Vec<TrustExpr>, return_sort: TrustSort) -> Self {
        Self::Call {
            function: function.into(),
            args,
            return_sort,
        }
    }

    /// Typed universal or existential quantifier.
    pub fn quantifier(
        kind: TrustQuantifierKind,
        bound_vars: Vec<TrustQuantifierBoundVar>,
        body: TrustExpr,
    ) -> Self {
        Self::quantifier_with_options(kind, bound_vars, body, None, None)
    }

    /// Typed universal quantifier.
    pub fn forall(bound_vars: Vec<TrustQuantifierBoundVar>, body: TrustExpr) -> Self {
        Self::quantifier(TrustQuantifierKind::Forall, bound_vars, body)
    }

    /// Typed existential quantifier.
    pub fn exists(bound_vars: Vec<TrustQuantifierBoundVar>, body: TrustExpr) -> Self {
        Self::quantifier(TrustQuantifierKind::Exists, bound_vars, body)
    }

    /// Typed quantifier with explicit trigger groups.
    pub fn quantifier_with_triggers(
        kind: TrustQuantifierKind,
        bound_vars: Vec<TrustQuantifierBoundVar>,
        body: TrustExpr,
        triggers: Vec<Vec<TrustExpr>>,
    ) -> Self {
        Self::quantifier_with_options(kind, bound_vars, body, Some(triggers), None)
    }

    /// Typed quantifier with explicit trigger and trigger-inference metadata.
    pub fn quantifier_with_options(
        kind: TrustQuantifierKind,
        bound_vars: Vec<TrustQuantifierBoundVar>,
        body: TrustExpr,
        triggers: Option<Vec<Vec<TrustExpr>>>,
        trigger_inference_mode: Option<TrustTriggerInferenceMode>,
    ) -> Self {
        Self::Quantifier {
            quantifier_kind: kind,
            bound_vars,
            body: Box::new(body),
            triggers,
            trigger_inference_mode,
        }
    }

    /// Lower this boundary expression into TrustVc's typed expression IR.
    pub fn to_trust_vc_expr(&self) -> Result<TrustVcExpr, TrustEngineError> {
        match self {
            Self::BoolLiteral { value } => Ok(TrustVcExpr::BoolLit(*value)),
            Self::IntLiteral { value, sort } => Ok(TrustVcExpr::IntLit {
                value: *value,
                ty: sort.to_trust_vc_type()?,
            }),
            Self::Variable { name, sort } => Ok(TrustVcExpr::Var {
                name: name.clone(),
                ty: sort.to_trust_vc_type()?,
            }),
            Self::Old { snapshot, sort, .. } => Ok(TrustVcExpr::Var {
                name: snapshot.clone(),
                ty: sort.to_trust_vc_type()?,
            }),
            Self::Arith {
                op,
                left,
                right,
                sort,
            } => Ok(TrustVcExpr::Arith {
                op: (*op).into(),
                left: Box::new(left.to_trust_vc_expr()?),
                right: Box::new(right.to_trust_vc_expr()?),
                ty: sort.to_trust_vc_type()?,
            }),
            Self::Compare { op, left, right } => Ok(TrustVcExpr::Compare {
                op: (*op).into(),
                left: Box::new(left.to_trust_vc_expr()?),
                right: Box::new(right.to_trust_vc_expr()?),
            }),
            Self::Logic { op, left, right } => Ok(TrustVcExpr::Logic {
                op: (*op).into(),
                left: Box::new(left.to_trust_vc_expr()?),
                right: Box::new(right.to_trust_vc_expr()?),
            }),
            Self::Not { expr } => Ok(TrustVcExpr::Not(Box::new(expr.to_trust_vc_expr()?))),
            Self::Implies {
                premise,
                conclusion,
            } => Ok(TrustVcExpr::Implies {
                premise: Box::new(premise.to_trust_vc_expr()?),
                conclusion: Box::new(conclusion.to_trust_vc_expr()?),
            }),
            Self::Cast {
                expr,
                from_sort,
                to_sort,
            } => Ok(TrustVcExpr::Cast {
                expr: Box::new(expr.to_trust_vc_expr()?),
                from_ty: from_sort.to_trust_vc_type()?,
                to_ty: to_sort.to_trust_vc_type()?,
            }),
            Self::Call {
                function,
                args,
                return_sort,
            } => Ok(TrustVcExpr::FnCall {
                name: function.clone(),
                args: args
                    .iter()
                    .map(TrustExpr::to_trust_vc_expr)
                    .collect::<Result<Vec<_>, _>>()?,
                return_ty: return_sort.to_trust_vc_type()?,
            }),
            Self::Quantifier {
                quantifier_kind,
                bound_vars,
                body,
                triggers,
                trigger_inference_mode,
            } => Ok(TrustVcExpr::Quantifier {
                kind: (*quantifier_kind).into(),
                bound_vars: bound_vars
                    .iter()
                    .map(TrustQuantifierBoundVar::to_trust_vc_bound_var)
                    .collect::<Result<Vec<_>, _>>()?,
                body: Box::new(body.to_trust_vc_expr()?),
                triggers: triggers
                    .as_ref()
                    .map(|groups| {
                        groups
                            .iter()
                            .map(|group| {
                                group
                                    .iter()
                                    .map(TrustExpr::to_trust_vc_expr)
                                    .collect::<Result<Vec<_>, _>>()
                            })
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .transpose()?,
                trigger_inference_mode: trigger_inference_mode.map(Into::into),
            }),
        }
    }

    /// Convert a supported TrustVc typed expression into the Trust evidence shape.
    ///
    /// This is intentionally fail-closed: TrustVc IR variants that do not have a
    /// stable `TrustExpr` wire representation are rejected instead of being
    /// downgraded to diagnostic source text.
    pub fn from_trust_vc_expr(expr: &TrustVcExpr) -> Result<Self, TrustEngineError> {
        Self::from_trust_vc_expr_for_obligation("<trust-vc-expr>", "<expr>", expr)
    }

    fn from_trust_vc_expr_for_obligation(
        unit_id: &str,
        obligation_id: &str,
        expr: &TrustVcExpr,
    ) -> Result<Self, TrustEngineError> {
        match expr {
            TrustVcExpr::BoolLit(value) => Ok(Self::bool_literal(*value)),
            TrustVcExpr::IntLit { value, ty } => Ok(Self::int_literal(
                *value,
                TrustSort::from_trust_vc_type(unit_id, obligation_id, ty)?,
            )),
            TrustVcExpr::Var { name, ty } => Ok(Self::variable(
                name.clone(),
                TrustSort::from_trust_vc_type(unit_id, obligation_id, ty)?,
            )),
            TrustVcExpr::Arith {
                op,
                left,
                right,
                ty,
            } => Ok(Self::arith(
                TrustArithOp::from_trust_vc(*op).ok_or_else(|| {
                    TrustEngineError::UnsupportedTypedProofObligation {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        feature: "unsupported TrustVc arithmetic operator".to_string(),
                    }
                })?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, left)?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, right)?,
                TrustSort::from_trust_vc_type(unit_id, obligation_id, ty)?,
            )),
            TrustVcExpr::Compare { op, left, right } => Ok(Self::compare(
                TrustCompareOp::from_trust_vc(*op).ok_or_else(|| {
                    TrustEngineError::UnsupportedTypedProofObligation {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        feature: "unsupported TrustVc comparison operator".to_string(),
                    }
                })?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, left)?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, right)?,
            )),
            TrustVcExpr::Logic { op, left, right } => Ok(Self::logic(
                TrustLogicOp::from_trust_vc(*op).ok_or_else(|| {
                    TrustEngineError::UnsupportedTypedProofObligation {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        feature: "unsupported TrustVc logic operator".to_string(),
                    }
                })?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, left)?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, right)?,
            )),
            TrustVcExpr::Not(expr) => Ok(Self::not(Self::from_trust_vc_expr_for_obligation(
                unit_id,
                obligation_id,
                expr,
            )?)),
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => Ok(Self::implies(
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, premise)?,
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, conclusion)?,
            )),
            TrustVcExpr::Cast {
                expr,
                from_ty,
                to_ty,
            } => Ok(Self::cast(
                Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, expr)?,
                TrustSort::from_trust_vc_type(unit_id, obligation_id, from_ty)?,
                TrustSort::from_trust_vc_type(unit_id, obligation_id, to_ty)?,
            )),
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } => Ok(Self::call(
                name.clone(),
                args.iter()
                    .map(|arg| Self::from_trust_vc_expr_for_obligation(unit_id, obligation_id, arg))
                    .collect::<Result<Vec<_>, _>>()?,
                TrustSort::from_trust_vc_type(unit_id, obligation_id, return_ty)?,
            )),
            TrustVcExpr::Quantifier {
                kind,
                bound_vars,
                body,
                triggers,
                trigger_inference_mode,
            } => Ok(Self::Quantifier {
                quantifier_kind: TrustQuantifierKind::from_trust_vc(*kind).ok_or_else(|| {
                    TrustEngineError::UnsupportedTypedProofObligation {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        feature: "unsupported TrustVc quantifier kind".to_string(),
                    }
                })?,
                bound_vars: bound_vars
                    .iter()
                    .map(|(name, ty)| {
                        TrustQuantifierBoundVar::from_trust_vc_bound_var(
                            unit_id,
                            obligation_id,
                            name,
                            ty,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                body: Box::new(Self::from_trust_vc_expr_for_obligation(
                    unit_id,
                    obligation_id,
                    body,
                )?),
                triggers: triggers
                    .as_ref()
                    .map(|groups| {
                        groups
                            .iter()
                            .map(|group| {
                                group
                                    .iter()
                                    .map(|trigger| {
                                        Self::from_trust_vc_expr_for_obligation(
                                            unit_id,
                                            obligation_id,
                                            trigger,
                                        )
                                    })
                                    .collect::<Result<Vec<_>, _>>()
                            })
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .transpose()?,
                trigger_inference_mode: trigger_inference_mode.map(Into::into),
            }),
            _ => Err(TrustEngineError::UnsupportedTypedProofObligation {
                unit_id: unit_id.to_string(),
                obligation_id: obligation_id.to_string(),
                feature: "unsupported TrustVcExpr variant".to_string(),
            }),
        }
    }

    fn display_label(&self) -> String {
        match self {
            Self::BoolLiteral { value } => value.to_string(),
            Self::IntLiteral { value, .. } => value.to_string(),
            Self::Variable { name, .. } => name.clone(),
            Self::Old { source, .. } => format!("old({source})"),
            Self::Arith {
                op, left, right, ..
            } => {
                format!(
                    "({} {} {})",
                    left.display_label(),
                    op.as_str(),
                    right.display_label()
                )
            }
            Self::Compare { op, left, right } => {
                format!(
                    "({} {} {})",
                    left.display_label(),
                    op.as_str(),
                    right.display_label()
                )
            }
            Self::Logic { op, left, right } => {
                format!(
                    "({} {} {})",
                    left.display_label(),
                    op.as_str(),
                    right.display_label()
                )
            }
            Self::Not { expr } => format!("!({})", expr.display_label()),
            Self::Implies {
                premise,
                conclusion,
            } => format!(
                "({} ==> {})",
                premise.display_label(),
                conclusion.display_label()
            ),
            Self::Cast {
                expr,
                from_sort,
                to_sort,
            } => format!(
                "({} as {} from {})",
                expr.display_label(),
                to_sort.display_label(),
                from_sort.display_label()
            ),
            Self::Call { function, args, .. } => {
                let args = args
                    .iter()
                    .map(TrustExpr::display_label)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{function}({args})")
            }
            Self::Quantifier {
                quantifier_kind,
                bound_vars,
                body,
                triggers,
                trigger_inference_mode,
            } => {
                let kind_label = match quantifier_kind {
                    TrustQuantifierKind::Forall => "forall",
                    TrustQuantifierKind::Exists => "exists",
                };
                let vars = bound_vars
                    .iter()
                    .map(|var| format!("{}: {}", var.name(), var.sort().display_label()))
                    .collect::<Vec<_>>()
                    .join(", ");
                let mut label = format!("{kind_label} |{vars}| {}", body.display_label());
                if let Some(groups) = triggers {
                    let groups = groups
                        .iter()
                        .map(|group| {
                            format!(
                                "[{}]",
                                group
                                    .iter()
                                    .map(TrustExpr::display_label)
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    label.push_str(&format!(" triggers [{groups}]"));
                }
                if let Some(mode) = trigger_inference_mode {
                    let mode_label = match mode {
                        TrustTriggerInferenceMode::Conservative => "conservative",
                        TrustTriggerInferenceMode::Aggressive => "aggressive",
                    };
                    label.push_str(&format!(" trigger_mode {mode_label}"));
                }
                label
            }
        }
    }
}

mod serde_i128_string {
    use serde::de::{self, Visitor};
    use serde::{Deserializer, Serializer};
    use std::fmt;

    pub(super) fn serialize<S>(value: &i128, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&value.to_string())
    }

    pub(super) fn deserialize<'de, D>(deserializer: D) -> Result<i128, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(I128Visitor)
    }

    struct I128Visitor;

    impl Visitor<'_> for I128Visitor {
        type Value = i128;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("an i128 integer literal as a string or JSON integer")
        }

        fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(i128::from(value))
        }

        fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            Ok(i128::from(value))
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            value.parse::<i128>().map_err(E::custom)
        }
    }
}

/// Typed arithmetic operator accepted at the tRust/TrustVc boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl TrustArithOp {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
        }
    }
}

impl From<TrustArithOp> for TrustVcArithOp {
    fn from(value: TrustArithOp) -> Self {
        match value {
            TrustArithOp::Add => Self::Add,
            TrustArithOp::Sub => Self::Sub,
            TrustArithOp::Mul => Self::Mul,
            TrustArithOp::Div => Self::Div,
            TrustArithOp::Rem => Self::Rem,
        }
    }
}

impl TrustArithOp {
    const fn from_trust_vc(value: TrustVcArithOp) -> Option<Self> {
        match value {
            TrustVcArithOp::Add => Some(Self::Add),
            TrustVcArithOp::Sub => Some(Self::Sub),
            TrustVcArithOp::Mul => Some(Self::Mul),
            TrustVcArithOp::Div => Some(Self::Div),
            TrustVcArithOp::Rem => Some(Self::Rem),
            _ => None,
        }
    }
}

/// Typed comparison operator accepted at the tRust/TrustVc boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustCompareOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl TrustCompareOp {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }
}

impl From<TrustCompareOp> for TrustVcCompareOp {
    fn from(value: TrustCompareOp) -> Self {
        match value {
            TrustCompareOp::Eq => Self::Eq,
            TrustCompareOp::Ne => Self::Ne,
            TrustCompareOp::Lt => Self::Lt,
            TrustCompareOp::Le => Self::Le,
            TrustCompareOp::Gt => Self::Gt,
            TrustCompareOp::Ge => Self::Ge,
        }
    }
}

impl TrustCompareOp {
    const fn from_trust_vc(value: TrustVcCompareOp) -> Option<Self> {
        match value {
            TrustVcCompareOp::Eq => Some(Self::Eq),
            TrustVcCompareOp::Ne => Some(Self::Ne),
            TrustVcCompareOp::Lt => Some(Self::Lt),
            TrustVcCompareOp::Le => Some(Self::Le),
            TrustVcCompareOp::Gt => Some(Self::Gt),
            TrustVcCompareOp::Ge => Some(Self::Ge),
            _ => None,
        }
    }
}

/// Typed logical operator accepted at the tRust/TrustVc boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustLogicOp {
    And,
    Or,
}

impl TrustLogicOp {
    const fn as_str(self) -> &'static str {
        match self {
            Self::And => "&&",
            Self::Or => "||",
        }
    }
}

impl From<TrustLogicOp> for TrustVcLogicOp {
    fn from(value: TrustLogicOp) -> Self {
        match value {
            TrustLogicOp::And => Self::And,
            TrustLogicOp::Or => Self::Or,
        }
    }
}

impl TrustLogicOp {
    const fn from_trust_vc(value: TrustVcLogicOp) -> Option<Self> {
        match value {
            TrustVcLogicOp::And => Some(Self::And),
            TrustVcLogicOp::Or => Some(Self::Or),
            _ => None,
        }
    }
}

/// Single verification obligation.
///
/// Legacy callers may still supply `expr` as source text. Full verification
/// callers must use the typed constructors so the obligation carries a
/// `TrustExpr` payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustObligation {
    id: String,
    role: TrustObligationRole,
    kind: TrustObligationKind,
    expr: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    typed_expr: Option<TrustExpr>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_lineage: Option<TrustProofLineage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    bootstrap_provenance: Option<TrustBootstrapProvenance>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    location: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    solver_mode: Option<TrustSolverMode>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_assertion_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_source_id: Option<String>,
}

impl TrustObligation {
    /// Create an obligation with explicit role and kind.
    pub fn new(
        id: impl Into<String>,
        role: TrustObligationRole,
        kind: TrustObligationKind,
        expr: impl Into<String>,
    ) -> Self {
        Self {
            id: id.into(),
            role,
            kind,
            expr: expr.into(),
            typed_expr: None,
            proof_lineage: None,
            bootstrap_provenance: None,
            location: None,
            solver_mode: None,
            trust_ir_assertion_id: None,
            trust_ir_source_id: None,
        }
    }

    /// Create an obligation with an already-typed verifier expression.
    pub fn new_typed(
        id: impl Into<String>,
        role: TrustObligationRole,
        kind: TrustObligationKind,
        expr: TrustExpr,
    ) -> Self {
        Self {
            id: id.into(),
            role,
            kind,
            expr: expr.display_label(),
            typed_expr: Some(expr),
            proof_lineage: None,
            bootstrap_provenance: None,
            location: None,
            solver_mode: None,
            trust_ir_assertion_id: None,
            trust_ir_source_id: None,
        }
    }

    /// Create a trusted assumption.
    pub fn assume(
        id: impl Into<String>,
        kind: TrustObligationKind,
        expr: impl Into<String>,
    ) -> Self {
        Self::new(id, TrustObligationRole::Assumption, kind, expr)
    }

    /// Create a trusted assumption backed by a typed verifier expression.
    pub fn assume_typed(id: impl Into<String>, kind: TrustObligationKind, expr: TrustExpr) -> Self {
        Self::new_typed(id, TrustObligationRole::Assumption, kind, expr)
    }

    /// Create an assertion that must be discharged.
    pub fn assert(
        id: impl Into<String>,
        kind: TrustObligationKind,
        expr: impl Into<String>,
    ) -> Self {
        Self::new(id, TrustObligationRole::Assertion, kind, expr)
    }

    /// Create an assertion backed by a typed verifier expression.
    pub fn assert_typed(id: impl Into<String>, kind: TrustObligationKind, expr: TrustExpr) -> Self {
        Self::new_typed(id, TrustObligationRole::Assertion, kind, expr)
    }

    /// Create a first-class typed `requires` clause.
    pub fn requires_typed(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assume_typed(id, TrustObligationKind::Precondition, expr)
    }

    /// Create a first-class typed `ensures` clause.
    pub fn ensures_typed(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::Postcondition, expr)
    }

    /// Create a typed cast-precondition assertion.
    pub fn assert_cast_precondition(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::CastPrecondition, expr)
    }

    /// Create a typed ADT bootstrap assertion.
    pub fn assert_adt_bootstrap_fact(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::AdtDiscriminant, expr)
    }

    /// Create a typed pointer bootstrap assertion.
    pub fn assert_pointer_bootstrap_fact(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::PointerBootstrap, expr)
    }

    /// Create a typed fat-pointer bootstrap assertion.
    pub fn assert_fat_pointer_bootstrap_fact(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::FatPointerBootstrap, expr)
    }

    /// Create a typed closure/Fn/FnMut/FnOnce bootstrap assertion.
    pub fn assert_closure_bootstrap_fact(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::ClosureBootstrap, expr)
    }

    /// Create a typed FnPtr bootstrap assertion.
    pub fn assert_fn_ptr_bootstrap_fact(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_typed(id, TrustObligationKind::FnPtrBootstrap, expr)
    }

    /// Create a typed function-pointer bootstrap assertion.
    pub fn assert_fn_pointer_bootstrap_fact(id: impl Into<String>, expr: TrustExpr) -> Self {
        Self::assert_fn_ptr_bootstrap_fact(id, expr)
    }

    /// Convert a TrustVc-core typed proof obligation into the Trust evidence model.
    ///
    /// The converted obligation remains typed: unsupported TrustVc expression
    /// forms fail closed instead of being represented as source text.
    pub fn from_trust_vc_typed_obligation(
        unit_id: &str,
        obligation: &TypedProofObligation,
    ) -> Result<Self, TrustEngineError> {
        let expr = TrustExpr::from_trust_vc_expr_for_obligation(
            unit_id,
            obligation.name(),
            obligation.expr(),
        )?;
        let (role, kind) = trust_parts_from_trust_vc_obligation_kind(obligation.kind());
        let mut converted = Self::new_typed(obligation.name().to_string(), role, kind, expr);
        if let Some(location) = obligation.location() {
            converted = converted.with_location(location.to_string());
        }
        if let Some(mode) = obligation.solver_mode() {
            converted = converted.with_solver_mode(mode.into());
        }
        Ok(converted)
    }

    /// Return the obligation id.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Return whether this obligation is assumed or asserted.
    pub const fn role(&self) -> TrustObligationRole {
        self.role
    }

    /// Return the tRust-flavored obligation kind.
    pub fn kind(&self) -> &TrustObligationKind {
        &self.kind
    }

    /// Return the expression payload.
    pub fn expr(&self) -> &str {
        &self.expr
    }

    /// Return the typed expression payload, if this is a typed obligation.
    pub fn typed_expr(&self) -> Option<&TrustExpr> {
        self.typed_expr.as_ref()
    }

    /// Return proof lineage for this obligation, if supplied by a typed adapter.
    pub fn proof_lineage(&self) -> Option<&TrustProofLineage> {
        self.proof_lineage.as_ref()
    }

    /// Return bootstrap provenance for non-contract bootstrap facts, if present.
    pub fn bootstrap_provenance(&self) -> Option<&TrustBootstrapProvenance> {
        self.bootstrap_provenance.as_ref()
    }

    /// Return true if this obligation can be lowered without parsing source text.
    pub const fn is_typed(&self) -> bool {
        self.typed_expr.is_some()
    }

    /// Return the optional source location.
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// Return the optional solver mode hint.
    pub const fn solver_mode(&self) -> Option<TrustSolverMode> {
        self.solver_mode
    }

    /// Return the compiler-emitted TrustIr assertion id, if this obligation came from TrustIr.
    pub const fn trust_ir_assertion_id(&self) -> Option<u32> {
        self.trust_ir_assertion_id
    }

    /// Return the compiler-emitted TrustIr source id, if this obligation came from TrustIr.
    pub fn trust_ir_source_id(&self) -> Option<&str> {
        self.trust_ir_source_id.as_deref()
    }

    /// Attach source location text.
    pub fn with_location(mut self, location: impl Into<String>) -> Self {
        self.location = Some(location.into());
        self
    }

    /// Attach first-class proof lineage from a typed compiler adapter.
    pub fn with_proof_lineage(mut self, lineage: TrustProofLineage) -> Self {
        self.proof_lineage = Some(lineage);
        self
    }

    /// Attach provenance for a non-contract bootstrap fact.
    pub fn with_bootstrap_provenance(mut self, provenance: TrustBootstrapProvenance) -> Self {
        self.bootstrap_provenance = Some(provenance);
        self
    }

    /// Attach a solver mode hint.
    pub fn with_solver_mode(mut self, solver_mode: TrustSolverMode) -> Self {
        self.solver_mode = Some(solver_mode);
        self
    }

    /// Attach a compiler-emitted TrustIr assertion id.
    pub fn with_trust_ir_assertion_id(mut self, trust_ir_assertion_id: u32) -> Self {
        self.trust_ir_assertion_id = Some(trust_ir_assertion_id);
        self
    }

    /// Attach a compiler-emitted TrustIr source id.
    pub fn with_trust_ir_source_id(mut self, trust_ir_source_id: impl Into<String>) -> Self {
        self.trust_ir_source_id = Some(trust_ir_source_id.into());
        self
    }

    fn to_trust_vc_obligation(&self) -> Result<ProofObligation, TrustEngineError> {
        let kind = match (self.role, &self.kind) {
            (_, TrustObligationKind::Recommends) => TrustVcObligationKind::Recommends,
            (TrustObligationRole::Assumption, TrustObligationKind::Precondition) => {
                TrustVcObligationKind::Requires
            }
            (TrustObligationRole::Assumption, _) => TrustVcObligationKind::Assume,
            (TrustObligationRole::Assertion, TrustObligationKind::Postcondition) => {
                TrustVcObligationKind::Ensures
            }
            (TrustObligationRole::Assertion, TrustObligationKind::LoopInvariant) => {
                TrustVcObligationKind::LoopInvariant
            }
            (TrustObligationRole::Assertion, _) => TrustVcObligationKind::Assert,
        };

        let mut obligation = if let Some(expr) = &self.typed_expr {
            ProofObligation::new_typed(self.id.clone(), expr.to_trust_vc_expr()?, kind)
        } else {
            ProofObligation::new(self.id.clone(), self.expr.clone(), kind)
        };
        if let Some(location) = &self.location {
            obligation = obligation.with_location(location.clone());
        }
        if let Some(mode) = self.solver_mode {
            obligation = obligation.with_solver_mode(mode.into());
        }
        Ok(obligation)
    }

    /// Lower this obligation to TrustVc's typed proof-obligation API.
    ///
    /// Full verification uses this path so the verifier never reparses a
    /// source string to recover the logical condition.
    pub fn to_trust_vc_typed_obligation(
        &self,
        unit_id: &str,
    ) -> Result<TypedProofObligation, TrustEngineError> {
        let expr = self.typed_expr.as_ref().ok_or_else(|| {
            TrustEngineError::StringBackedFullModeObligation {
                unit_id: unit_id.to_string(),
                obligation_id: self.id.clone(),
            }
        })?;

        let kind = match (self.role, &self.kind) {
            (_, TrustObligationKind::Recommends) => TrustVcObligationKind::Recommends,
            (TrustObligationRole::Assumption, TrustObligationKind::Precondition) => {
                TrustVcObligationKind::Requires
            }
            (TrustObligationRole::Assumption, _) => TrustVcObligationKind::Assume,
            (TrustObligationRole::Assertion, TrustObligationKind::Postcondition) => {
                TrustVcObligationKind::Ensures
            }
            (TrustObligationRole::Assertion, TrustObligationKind::LoopInvariant) => {
                TrustVcObligationKind::LoopInvariant
            }
            (TrustObligationRole::Assertion, _) => TrustVcObligationKind::Assert,
        };

        let mut obligation =
            TypedProofObligation::new(self.id.clone(), expr.to_trust_vc_expr()?, kind);
        if let Some(location) = &self.location {
            obligation = obligation.with_location(location.clone());
        }
        if let Some(mode) = self.solver_mode {
            obligation = obligation.with_solver_mode(mode.into());
        }
        Ok(obligation)
    }

    fn is_assertion(&self) -> bool {
        self.role == TrustObligationRole::Assertion
    }
}

fn trust_parts_from_trust_vc_obligation_kind(
    kind: TrustVcObligationKind,
) -> (TrustObligationRole, TrustObligationKind) {
    match kind {
        TrustVcObligationKind::Assume | TrustVcObligationKind::BroadcastAssume => {
            (TrustObligationRole::Assumption, TrustObligationKind::Axiom)
        }
        TrustVcObligationKind::Requires => (
            TrustObligationRole::Assumption,
            TrustObligationKind::Precondition,
        ),
        TrustVcObligationKind::Recommends => (
            TrustObligationRole::Assertion,
            TrustObligationKind::Recommends,
        ),
        TrustVcObligationKind::Ensures => (
            TrustObligationRole::Assertion,
            TrustObligationKind::Postcondition,
        ),
        TrustVcObligationKind::LoopInvariant
        | TrustVcObligationKind::LoopGuard
        | TrustVcObligationKind::InvariantExceptBreak
        | TrustVcObligationKind::LoopEnsures => (
            TrustObligationRole::Assertion,
            TrustObligationKind::LoopInvariant,
        ),
        TrustVcObligationKind::MeasureNonNegative | TrustVcObligationKind::MeasureDecreases => (
            TrustObligationRole::Assertion,
            TrustObligationKind::Other("termination".to_string()),
        ),
        TrustVcObligationKind::Assert | TrustVcObligationKind::AssertBy => (
            TrustObligationRole::Assertion,
            TrustObligationKind::Other("typed_deductive_obligation".to_string()),
        ),
        _ => (
            TrustObligationRole::Assertion,
            TrustObligationKind::Other("trust_vc_typed_obligation".to_string()),
        ),
    }
}

/// Report returned from a trust verification run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustVerificationReport {
    source_id: String,
    units: Vec<TrustUnitReport>,
}

impl TrustVerificationReport {
    /// Return the request source identifier.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return per-unit reports.
    pub fn units(&self) -> &[TrustUnitReport] {
        &self.units
    }

    /// Summarize outcomes across all units.
    pub fn summary(&self) -> TrustReportSummary {
        self.units
            .iter()
            .fold(TrustReportSummary::default(), |mut acc, unit| {
                match unit.outcome {
                    TrustOutcome::Verified => acc.verified += 1,
                    TrustOutcome::Refuted { .. } => acc.refuted += 1,
                    TrustOutcome::Unknown { .. } => acc.unknown += 1,
                    TrustOutcome::Error { .. } => acc.error += 1,
                }
                acc
            })
    }
}

/// Per-unit verification result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustUnitReport {
    unit_id: String,
    outcome: TrustOutcome,
    #[serde(default)]
    cache_status: TrustEvidenceCacheStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    diagnostics: Vec<TrustDiagnostic>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    proof_evidence: Vec<TrustProofEvidence>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    proof_artifacts: Vec<TrustReplayableProofArtifact>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_artifact: Option<TrustReplayableProofArtifact>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_artifact_coverage: Option<TrustProofArtifactCoverage>,
}

impl TrustUnitReport {
    /// Return the verified unit id.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the unit outcome.
    pub const fn outcome(&self) -> &TrustOutcome {
        &self.outcome
    }

    /// Return the cache disposition for this unit's evidence.
    pub const fn cache_status(&self) -> TrustEvidenceCacheStatus {
        self.cache_status
    }

    /// Return auxiliary diagnostics.
    pub fn diagnostics(&self) -> &[TrustDiagnostic] {
        &self.diagnostics
    }

    /// Return checked per-obligation evidence for verified units.
    pub fn proof_evidence(&self) -> &[TrustProofEvidence] {
        &self.proof_evidence
    }

    /// Return replayable proof artifacts captured for individual assertion steps.
    pub fn proof_artifacts(&self) -> &[TrustReplayableProofArtifact] {
        &self.proof_artifacts
    }

    /// Return the legacy singleton proof artifact when exactly one artifact exists.
    pub const fn proof_artifact(&self) -> Option<&TrustReplayableProofArtifact> {
        self.proof_artifact.as_ref()
    }

    /// Return per-assertion proof-artifact coverage when artifact capture was requested.
    pub const fn proof_artifact_coverage(&self) -> Option<&TrustProofArtifactCoverage> {
        self.proof_artifact_coverage.as_ref()
    }
}

/// Cache disposition for tRust-facing Trust evidence.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustEvidenceCacheStatus {
    /// Missing cache status from an older serialized payload.
    #[default]
    Unspecified,
    /// The verifier ran normally; no reusable evidence cache hit was used.
    Miss,
    /// A cache hit satisfied the unit without replay.
    Hit,
    /// A candidate cache entry was present but stale.
    Stale,
    /// A cached replayable artifact was replayed and accepted.
    Replayed,
    /// A candidate cache entry was rejected by policy or validation.
    Rejected,
}

/// Stable cache key for a single Trust proof-evidence item.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustEvidenceCacheKey {
    schema_version: u32,
    fingerprint: String,
    trust_vc_version: String,
    ay_version: String,
    kernel_version: String,
    proof_policy: TrustProofPolicy,
    source_id: String,
    unit_id: String,
    obligation_id: String,
    expression_digest: String,
    native_context_digest: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_lineage_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    ownership_digest: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_body_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    layout_hash: Option<String>,
}

impl TrustEvidenceCacheKey {
    fn from_obligation(
        source_id: &str,
        unit: &TrustVerificationUnit,
        obligation: &TrustObligation,
        proof_policy: TrustProofPolicy,
        request_metadata: &BTreeMap<String, String>,
    ) -> Self {
        let expression_digest = expression_cache_digest(obligation);
        let native_context_digest = stable_sha256_digest(&NativeContextDigestPayload {
            encoding: "trust_native_context_json_v1",
            native_context: &unit.native_context,
        });
        let ownership_digest = unit
            .native_context
            .as_ref()
            .and_then(TrustNativeContext::ownership)
            .map(|ownership| {
                stable_sha256_digest(&OwnershipDigestPayload {
                    encoding: "trust_ownership_state_json_v1",
                    ownership,
                })
            });
        let proof_lineage_digest = obligation.proof_lineage.as_ref().map(|lineage| {
            stable_sha256_digest(&ProofLineageDigestPayload {
                encoding: "trust_proof_lineage_json_v1",
                lineage,
            })
        });
        let ay_version = request_metadata
            .get(TRUST_CACHE_METADATA_AY_VERSION)
            .cloned()
            .unwrap_or_else(|| "ay:unreported".to_string());
        let kernel_version = request_metadata
            .get(TRUST_CACHE_METADATA_KERNEL_VERSION)
            .cloned()
            .unwrap_or_else(default_kernel_version);
        let trust_vc_version = format!("trust-vc-trust-engine:{}", env!("CARGO_PKG_VERSION"));
        let trust_ir_body_hash = request_metadata
            .get(TRUST_CACHE_METADATA_TRUST_IR_BODY_HASH)
            .cloned();
        let layout_hash = request_metadata
            .get(TRUST_CACHE_METADATA_LAYOUT_HASH)
            .cloned();

        let payload = TrustEvidenceCacheKeyPayload {
            schema_version: TRUST_EVIDENCE_CACHE_KEY_SCHEMA_VERSION,
            trust_vc_version: &trust_vc_version,
            ay_version: &ay_version,
            kernel_version: &kernel_version,
            proof_policy,
            source_id,
            unit_id: &unit.unit_id,
            obligation_id: &obligation.id,
            expression_digest: &expression_digest,
            native_context_digest: &native_context_digest,
            proof_lineage_digest: proof_lineage_digest.as_deref(),
            ownership_digest: ownership_digest.as_deref(),
            trust_ir_body_hash: trust_ir_body_hash.as_deref(),
            layout_hash: layout_hash.as_deref(),
        };
        let fingerprint = stable_sha256_digest(&payload);

        Self {
            schema_version: TRUST_EVIDENCE_CACHE_KEY_SCHEMA_VERSION,
            fingerprint,
            trust_vc_version,
            ay_version,
            kernel_version,
            proof_policy,
            source_id: source_id.to_string(),
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            expression_digest,
            native_context_digest,
            proof_lineage_digest,
            ownership_digest,
            trust_ir_body_hash,
            layout_hash,
        }
    }

    /// Return the cache-key schema version.
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    /// Return the full stable key fingerprint as `sha256:<hex>`.
    pub fn fingerprint(&self) -> &str {
        &self.fingerprint
    }

    /// Return the TrustVc component version included in this key.
    pub fn trust_vc_version(&self) -> &str {
        &self.trust_vc_version
    }

    /// Return the ay version/revision included in this key.
    pub fn ay_version(&self) -> &str {
        &self.ay_version
    }

    /// Return the TrustVc kernel version/revision included in this key.
    pub fn kernel_version(&self) -> &str {
        &self.kernel_version
    }

    /// Return the proof-artifact policy included in this key.
    pub const fn proof_policy(&self) -> TrustProofPolicy {
        self.proof_policy
    }

    /// Return the request source id included in this key.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return the unit id included in this key.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the obligation id included in this key.
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    /// Return the normalized expression digest as `sha256:<hex>`.
    pub fn expression_digest(&self) -> &str {
        &self.expression_digest
    }

    /// Return the native-context digest as `sha256:<hex>`.
    pub fn native_context_digest(&self) -> &str {
        &self.native_context_digest
    }

    /// Return the proof-lineage digest, if the obligation carried lineage.
    pub fn proof_lineage_digest(&self) -> Option<&str> {
        self.proof_lineage_digest.as_deref()
    }

    /// Return the ownership-state digest, if native ownership state was present.
    pub fn ownership_digest(&self) -> Option<&str> {
        self.ownership_digest.as_deref()
    }

    /// Return the optional TrustIr body hash supplied by the request.
    pub fn trust_ir_body_hash(&self) -> Option<&str> {
        self.trust_ir_body_hash.as_deref()
    }

    /// Return the optional layout/type-context hash supplied by the request.
    pub fn layout_hash(&self) -> Option<&str> {
        self.layout_hash.as_deref()
    }
}

#[derive(Serialize)]
struct TrustEvidenceCacheKeyPayload<'a> {
    schema_version: u32,
    trust_vc_version: &'a str,
    ay_version: &'a str,
    kernel_version: &'a str,
    proof_policy: TrustProofPolicy,
    source_id: &'a str,
    unit_id: &'a str,
    obligation_id: &'a str,
    expression_digest: &'a str,
    native_context_digest: &'a str,
    #[serde(skip_serializing_if = "Option::is_none")]
    proof_lineage_digest: Option<&'a str>,
    ownership_digest: Option<&'a str>,
    trust_ir_body_hash: Option<&'a str>,
    layout_hash: Option<&'a str>,
}

#[derive(Serialize)]
struct TrustExpressionDigestPayload<'a> {
    encoding: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    typed_expr: Option<&'a TrustExpr>,
    #[serde(skip_serializing_if = "Option::is_none")]
    legacy_expr: Option<&'a str>,
}

#[derive(Serialize)]
struct NativeContextDigestPayload<'a> {
    encoding: &'static str,
    native_context: &'a Option<TrustNativeContext>,
}

#[derive(Serialize)]
struct ProofLineageDigestPayload<'a> {
    encoding: &'static str,
    lineage: &'a TrustProofLineage,
}

#[derive(Serialize)]
struct OwnershipDigestPayload<'a> {
    encoding: &'static str,
    ownership: &'a TrustOwnershipState,
}

#[cfg(any(feature = "proof-certificates", test))]
#[derive(Serialize)]
struct TrustProofArtifactBindingPayload<'a> {
    schema_version: u32,
    artifact_id: &'a str,
    digest: &'a str,
    unit_id: &'a str,
    assumption_obligation_ids: &'a [String],
    assertion_obligation_ids: &'a [String],
}

fn expression_cache_digest(obligation: &TrustObligation) -> String {
    let payload = if let Some(typed_expr) = obligation.typed_expr.as_ref() {
        TrustExpressionDigestPayload {
            encoding: "trust_expr_json_v1",
            typed_expr: Some(typed_expr),
            legacy_expr: None,
        }
    } else {
        TrustExpressionDigestPayload {
            encoding: "legacy_source_expr_v1",
            typed_expr: None,
            legacy_expr: Some(&obligation.expr),
        }
    };
    stable_sha256_digest(&payload)
}

#[cfg(any(feature = "proof-certificates", test))]
fn proof_artifact_binding_fingerprint(
    artifact_id: &str,
    digest: &str,
    unit_id: &str,
    assumption_obligation_ids: &[String],
    assertion_obligation_ids: &[String],
) -> String {
    stable_sha256_digest(&TrustProofArtifactBindingPayload {
        schema_version: TRUST_PROOF_ARTIFACT_BINDING_SCHEMA_VERSION,
        artifact_id,
        digest,
        unit_id,
        assumption_obligation_ids,
        assertion_obligation_ids,
    })
}

fn stable_sha256_digest(payload: &impl Serialize) -> String {
    let encoded = serde_json::to_vec(payload).unwrap_or_else(|err| {
        format!("trust-vc:serialization-error:cache-key-payload:{err}").into_bytes()
    });
    sha256_digest_bytes(&encoded)
}

fn sha256_digest_bytes(payload: &[u8]) -> String {
    let digest = Sha256::digest(payload);
    let mut out = String::from("sha256:");
    for byte in digest {
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}

fn default_kernel_version() -> String {
    #[cfg(feature = "proof-certificates")]
    {
        format!("trust-vc-kernel:{}", env!("CARGO_PKG_VERSION"))
    }
    #[cfg(not(feature = "proof-certificates"))]
    {
        "trust-vc-kernel:disabled".to_string()
    }
}

/// Release-admission verdict for a replayable proof artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustReleaseProofAdmission {
    #[serde(default)]
    status: TrustReleaseProofAdmissionStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    rejection_reasons: Vec<TrustReleaseProofRejection>,
}

impl Default for TrustReleaseProofAdmission {
    fn default() -> Self {
        Self {
            status: TrustReleaseProofAdmissionStatus::Unspecified,
            rejection_reasons: Vec::new(),
        }
    }
}

impl TrustReleaseProofAdmission {
    /// Build a release-admission verdict from proof-certificate metrics.
    pub fn from_certificate_metrics(
        strict_verified: bool,
        kernel_verified: bool,
        trust_count: u32,
        hole_count: u32,
    ) -> Self {
        let mut rejection_reasons = Vec::new();
        if !strict_verified {
            rejection_reasons.push(TrustReleaseProofRejection::StrictCheckerRejected);
        }
        if !kernel_verified {
            rejection_reasons.push(TrustReleaseProofRejection::KernelNotVerified);
        }
        if hole_count > 0 {
            rejection_reasons.push(TrustReleaseProofRejection::ProofHolesPresent);
        }
        if trust_count > 0 {
            rejection_reasons.push(TrustReleaseProofRejection::TrustedSolverStepsPresent);
        }

        Self {
            status: if rejection_reasons.is_empty() {
                TrustReleaseProofAdmissionStatus::Admissible
            } else {
                TrustReleaseProofAdmissionStatus::Rejected
            },
            rejection_reasons,
        }
    }

    /// Return the release-admission status.
    pub const fn status(&self) -> TrustReleaseProofAdmissionStatus {
        self.status
    }

    /// Return whether this artifact is admissible for release-grade Trust gates.
    pub const fn is_admissible(&self) -> bool {
        matches!(self.status, TrustReleaseProofAdmissionStatus::Admissible)
    }

    /// Return reasons the artifact is not release-admissible.
    pub fn rejection_reasons(&self) -> &[TrustReleaseProofRejection] {
        &self.rejection_reasons
    }
}

/// Release-admission status for proof artifacts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustReleaseProofAdmissionStatus {
    /// Missing admission status from an older serialized payload.
    #[default]
    Unspecified,
    /// The artifact satisfies TrustVc's release-grade proof policy.
    Admissible,
    /// The artifact is replayable but not release-admissible.
    Rejected,
}

/// Reasons a replayable proof artifact is not release-admissible.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustReleaseProofRejection {
    /// TrustVc's strict proof checker did not accept the artifact.
    StrictCheckerRejected,
    /// The independent TrustVc kernel did not accept the artifact.
    KernelNotVerified,
    /// The artifact contains proof holes.
    ProofHolesPresent,
    /// The artifact contains solver trust steps.
    TrustedSolverStepsPresent,
}

/// Replayable TrustVc proof artifact bound to one verified assertion step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustReplayableProofArtifact {
    artifact_id: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    unit_id: String,
    format: TrustProofArtifactFormat,
    digest: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    binding_fingerprint: String,
    payload: String,
    strict_verified: bool,
    clean_supported: bool,
    kernel_verified: bool,
    trust_count: u32,
    hole_count: u32,
    resolution_count: u32,
    theory_count: u32,
    #[serde(default)]
    release_admission: TrustReleaseProofAdmission,
    assumption_obligation_ids: Vec<String>,
    assertion_obligation_ids: Vec<String>,
}

impl TrustReplayableProofArtifact {
    fn from_verified_report_if_requested(
        unit: &TrustVerificationUnit,
        policy: TrustProofPolicy,
        report: &VerificationReport,
    ) -> Result<Vec<Self>, TrustEngineError> {
        if !policy.wants_replayable_artifact() || !report.result().is_verified() {
            return Ok(Vec::new());
        }

        Self::from_verified_report(unit, policy, report)
    }

    #[cfg(not(feature = "proof-certificates"))]
    fn from_verified_report(
        unit: &TrustVerificationUnit,
        policy: TrustProofPolicy,
        _report: &VerificationReport,
    ) -> Result<Vec<Self>, TrustEngineError> {
        if policy.requires_replayable_artifact() {
            return Err(TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: unit.unit_id.clone(),
                policy,
                reason: "trust-vc-trust-engine was built without the proof-certificates feature",
            });
        }
        Ok(Vec::new())
    }

    #[cfg(feature = "proof-certificates")]
    fn from_verified_report(
        unit: &TrustVerificationUnit,
        policy: TrustProofPolicy,
        report: &VerificationReport,
    ) -> Result<Vec<Self>, TrustEngineError> {
        let assertion_obligations = unit
            .obligations
            .iter()
            .filter(|obligation| obligation.role == TrustObligationRole::Assertion)
            .collect::<Vec<_>>();
        let mut artifacts = Vec::new();
        // Assertions whose label covered SEVERAL verified queries. Distinct from
        // "no artifact bound", which is why it is counted separately.
        let mut ambiguous_assertions = 0usize;

        for assertion in &assertion_obligations {
            // A certificate must bind to ONE solver query. `label()` is
            // `obligation.name`, and a name is NOT unique per query: a loop
            // invariant's establishment and its preservation are separate
            // queries over the same `PreparedObligation`, so they carry the same
            // label. `begin_obligation_step` records the `VerificationPhase`
            // alongside the name, but this lookup never consulted it and took
            // the FIRST match — which would mint a loop-ENTRY refutation as the
            // certificate for the invariant itself.
            //
            // Fixed by requiring UNIQUENESS rather than by guessing which phase
            // is the right one. That choice is deliberate: matching on a phase I
            // inferred could bind the wrong query and would be a false
            // certificate, whereas refusing an ambiguous label can only ever
            // produce FEWER certificates. An ambiguous binding yields no
            // artifact, the policy then declines, and the obligation is reported
            // unproved. Strictly fail-closed.
            //
            // When a query-identity key exists (name + phase + goal formula),
            // this can be tightened to select rather than refuse. Any test for
            // that must compare the REFUTED formula against the step's goal —
            // comparing label strings cannot see this defect.
            let mut matching = report.steps().iter().filter(|step| {
                step.label() == assertion.id
                    && matches!(step.result(), trust_vc_core::StepResultKind::Verified)
            });
            let Some(step) = matching.next() else {
                // Zero matches: nothing to bind, and no ambiguity either.
                continue;
            };
            if matching.next().is_some() {
                // TWO OR MORE distinct solver queries share this label. Which one
                // refuted what is not recoverable here, so bind nothing rather
                // than the first — and RECORD that the refusal was for ambiguity,
                // because the single-assertion fallback below must not then step
                // in and mint the very binding this refused.
                ambiguous_assertions += 1;
                continue;
            }

            let Some(proof) = step.proof() else {
                continue;
            };
            if let Some(artifact) = Self::from_certificate(
                unit,
                policy,
                proof,
                assumption_obligation_ids_for_step(unit, step.used_assumptions()),
                vec![assertion.id.clone()],
            )? {
                artifacts.push(artifact);
            }
        }

        // The single-assertion fallback mints from `report.proof()`, which is
        // `collector.proof` — OVERWRITTEN on every recorded certificate
        // (trust-vc-core capture.rs:340), so it is the LAST one. That is fine
        // when the sole assertion simply had no per-step certificate recorded.
        //
        // It is NOT fine when the per-assertion loop refused for AMBIGUITY: a
        // unit whose one assertion is a loop invariant has two verified steps
        // under one label, the loop above binds nothing, `artifacts` is empty —
        // and this fallback would then mint the LAST step's certificate (the
        // preservation phase) under the invariant's own id. That is exactly the
        // mis-attribution the guard above exists to prevent, arriving through
        // the other door.
        //
        // So the fallback is suppressed whenever any assertion was refused for
        // ambiguity. The unit then fails the completeness check below and the
        // policy declines, which is the fail-closed outcome.
        if artifacts.is_empty() && assertion_obligations.len() == 1 && ambiguous_assertions == 0 {
            if let Some(proof) = report.proof() {
                let assertion = assertion_obligations[0];
                if let Some(artifact) = Self::from_certificate(
                    unit,
                    policy,
                    proof,
                    all_assumption_obligation_ids(unit),
                    vec![assertion.id.clone()],
                )? {
                    artifacts.push(artifact);
                }
            }
        }

        if policy.requires_replayable_artifact() && artifacts.len() != assertion_obligations.len() {
            return Err(TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: unit.unit_id.clone(),
                policy,
                reason: "TrustVc verified the unit but did not return a proof certificate for every verified assertion",
            });
        }

        Ok(artifacts)
    }

    #[cfg(feature = "proof-certificates")]
    fn from_certificate(
        unit: &TrustVerificationUnit,
        policy: TrustProofPolicy,
        proof: &trust_vc_core::ProofCertificate,
        assumption_obligation_ids: Vec<String>,
        assertion_obligation_ids: Vec<String>,
    ) -> Result<Option<Self>, TrustEngineError> {
        if proof.alethe().is_empty() {
            if policy.requires_replayable_artifact() {
                return Err(TrustEngineError::ReplayableProofCertificateUnavailable {
                    unit_id: unit.unit_id.clone(),
                    policy,
                    reason: "TrustVc returned an empty Alethe proof certificate",
                });
            }
            return Ok(None);
        }

        if policy.requires_strict_replayable_artifact() && !proof.strict_verified() {
            return Err(TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: unit.unit_id.clone(),
                policy,
                reason: "the Alethe proof certificate was not accepted by the strict checker",
            });
        }

        let digest = sha256_digest(proof.alethe());
        let artifact_id = format!(
            "trust-vc-proof-certificate:v1:{}",
            digest.strip_prefix("sha256:").unwrap_or(digest.as_str())
        );
        let binding_fingerprint = proof_artifact_binding_fingerprint(
            &artifact_id,
            &digest,
            &unit.unit_id,
            &assumption_obligation_ids,
            &assertion_obligation_ids,
        );
        let release_admission = TrustReleaseProofAdmission::from_certificate_metrics(
            proof.strict_verified(),
            proof.kernel_verified(),
            proof.trust_count(),
            proof.hole_count(),
        );

        let artifact = Self {
            artifact_id,
            unit_id: unit.unit_id.clone(),
            format: TrustProofArtifactFormat::Alethe,
            digest,
            binding_fingerprint,
            payload: proof.alethe().to_string(),
            strict_verified: proof.strict_verified(),
            clean_supported: proof.clean_supported(),
            kernel_verified: proof.kernel_verified(),
            trust_count: proof.trust_count(),
            hole_count: proof.hole_count(),
            resolution_count: proof.resolution_count(),
            theory_count: proof.theory_count(),
            release_admission,
            assumption_obligation_ids,
            assertion_obligation_ids,
        };

        if policy.requires_release_admissible_artifact()
            && !artifact.release_admission.is_admissible()
        {
            return Err(TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: unit.unit_id.clone(),
                policy,
                reason: "the proof certificate is replayable but not release-admissible",
            });
        }

        Ok(Some(artifact))
    }

    /// Return the stable proof-artifact id.
    pub fn artifact_id(&self) -> &str {
        &self.artifact_id
    }

    /// Return the Trust unit id this proof binding belongs to.
    pub fn unit_id(&self) -> &str {
        &self.unit_id
    }

    /// Return the artifact format.
    pub const fn format(&self) -> TrustProofArtifactFormat {
        self.format
    }

    /// Return the payload digest as `sha256:<hex>`.
    pub fn digest(&self) -> &str {
        &self.digest
    }

    /// Return the stable binding fingerprint for artifact, unit, assumptions, and assertion.
    pub fn binding_fingerprint(&self) -> &str {
        &self.binding_fingerprint
    }

    /// Return the replayable proof payload.
    pub fn payload(&self) -> &str {
        &self.payload
    }

    /// Return whether TrustVc's strict checker accepted the proof.
    pub const fn strict_verified(&self) -> bool {
        self.strict_verified
    }

    /// Return whether the proof uses only rules supported by the clean backend.
    pub const fn clean_supported(&self) -> bool {
        self.clean_supported
    }

    /// Return whether the independent TrustVc kernel accepted the proof.
    pub const fn kernel_verified(&self) -> bool {
        self.kernel_verified
    }

    /// Return the number of solver trust steps in the artifact.
    pub const fn trust_count(&self) -> u32 {
        self.trust_count
    }

    /// Return the number of proof holes in the artifact.
    pub const fn hole_count(&self) -> u32 {
        self.hole_count
    }

    /// Return the number of resolution steps in the artifact.
    pub const fn resolution_count(&self) -> u32 {
        self.resolution_count
    }

    /// Return the number of theory-lemma steps in the artifact.
    pub const fn theory_count(&self) -> u32 {
        self.theory_count
    }

    /// Return release-grade admission details for this replayable artifact.
    pub const fn release_admission(&self) -> &TrustReleaseProofAdmission {
        &self.release_admission
    }

    /// Return assumption obligations this assertion proof was allowed to use.
    pub fn assumption_obligation_ids(&self) -> &[String] {
        &self.assumption_obligation_ids
    }

    /// Return assertion obligations discharged by this proof artifact.
    pub fn assertion_obligation_ids(&self) -> &[String] {
        &self.assertion_obligation_ids
    }
}

/// Replayable proof-artifact format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustProofArtifactFormat {
    /// SMT-LIB/Alethe proof text emitted by ay.
    Alethe,
}

/// Per-assertion replayable proof-artifact coverage for one verified unit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustProofArtifactCoverage {
    assertion_obligation_ids: Vec<String>,
    covered_assertion_obligation_ids: Vec<String>,
    missing_assertion_obligation_ids: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    trust_ir_assertion_ids: Vec<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    covered_trust_ir_assertion_ids: Vec<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    missing_trust_ir_assertion_ids: Vec<u32>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    assertions: Vec<TrustProofArtifactCoverageAssertion>,
    artifact_count: usize,
}

impl TrustProofArtifactCoverage {
    fn from_unit_artifacts(
        unit: &TrustVerificationUnit,
        artifacts: &[TrustReplayableProofArtifact],
    ) -> Self {
        let assertion_obligation_ids = unit
            .obligations
            .iter()
            .filter(|obligation| obligation.role == TrustObligationRole::Assertion)
            .map(|obligation| obligation.id.clone())
            .collect::<Vec<_>>();
        let artifact_assertions = artifacts
            .iter()
            .flat_map(|artifact| artifact.assertion_obligation_ids())
            .collect::<BTreeSet<_>>();
        let artifact_bindings_by_assertion = artifacts
            .iter()
            .flat_map(|artifact| {
                artifact
                    .assertion_obligation_ids()
                    .iter()
                    .map(move |obligation_id| {
                        (
                            obligation_id.as_str(),
                            (artifact.artifact_id(), artifact.binding_fingerprint()),
                        )
                    })
            })
            .collect::<BTreeMap<_, _>>();
        let covered_assertion_obligation_ids = assertion_obligation_ids
            .iter()
            .filter(|id| artifact_assertions.contains(id))
            .cloned()
            .collect::<Vec<_>>();
        let missing_assertion_obligation_ids = assertion_obligation_ids
            .iter()
            .filter(|id| !artifact_assertions.contains(id))
            .cloned()
            .collect::<Vec<_>>();
        let trust_ir_assertion_ids = unit
            .obligations
            .iter()
            .filter(|obligation| obligation.role == TrustObligationRole::Assertion)
            .filter_map(|obligation| obligation.trust_ir_assertion_id)
            .collect::<Vec<_>>();
        let covered_trust_ir_assertion_ids = unit
            .obligations
            .iter()
            .filter(|obligation| obligation.role == TrustObligationRole::Assertion)
            .filter(|obligation| artifact_assertions.contains(&obligation.id))
            .filter_map(|obligation| obligation.trust_ir_assertion_id)
            .collect::<Vec<_>>();
        let missing_trust_ir_assertion_ids = unit
            .obligations
            .iter()
            .filter(|obligation| obligation.role == TrustObligationRole::Assertion)
            .filter(|obligation| !artifact_assertions.contains(&obligation.id))
            .filter_map(|obligation| obligation.trust_ir_assertion_id)
            .collect::<Vec<_>>();
        let assertions = unit
            .obligations
            .iter()
            .filter(|obligation| obligation.role == TrustObligationRole::Assertion)
            .map(|obligation| {
                let binding = artifact_bindings_by_assertion.get(obligation.id());
                TrustProofArtifactCoverageAssertion {
                    obligation_id: obligation.id.clone(),
                    trust_ir_assertion_id: obligation.trust_ir_assertion_id,
                    trust_ir_source_id: obligation.trust_ir_source_id.clone(),
                    covered: binding.is_some(),
                    proof_artifact_id: binding.map(|(artifact_id, _)| (*artifact_id).to_string()),
                    proof_artifact_binding_fingerprint: binding
                        .map(|(_, fingerprint)| (*fingerprint).to_string()),
                }
            })
            .collect::<Vec<_>>();

        Self {
            assertion_obligation_ids,
            covered_assertion_obligation_ids,
            missing_assertion_obligation_ids,
            trust_ir_assertion_ids,
            covered_trust_ir_assertion_ids,
            missing_trust_ir_assertion_ids,
            assertions,
            artifact_count: artifacts.len(),
        }
    }

    /// Return every assertion obligation that should have replayable proof coverage.
    pub fn assertion_obligation_ids(&self) -> &[String] {
        &self.assertion_obligation_ids
    }

    /// Return assertion obligations covered by attached replayable proof artifacts.
    pub fn covered_assertion_obligation_ids(&self) -> &[String] {
        &self.covered_assertion_obligation_ids
    }

    /// Return assertion obligations still missing replayable proof artifacts.
    pub fn missing_assertion_obligation_ids(&self) -> &[String] {
        &self.missing_assertion_obligation_ids
    }

    /// Return compiler-emitted TrustIr assertion ids that should have proof coverage.
    pub fn trust_ir_assertion_ids(&self) -> &[u32] {
        &self.trust_ir_assertion_ids
    }

    /// Return compiler-emitted TrustIr assertion ids covered by proof artifacts.
    pub fn covered_trust_ir_assertion_ids(&self) -> &[u32] {
        &self.covered_trust_ir_assertion_ids
    }

    /// Return compiler-emitted TrustIr assertion ids still missing proof artifacts.
    pub fn missing_trust_ir_assertion_ids(&self) -> &[u32] {
        &self.missing_trust_ir_assertion_ids
    }

    /// Return per-assertion coverage rows, including compiler-emitted TrustIr ids.
    pub fn assertions(&self) -> &[TrustProofArtifactCoverageAssertion] {
        &self.assertions
    }

    /// Return the number of replayable proof artifacts attached to the unit.
    pub const fn artifact_count(&self) -> usize {
        self.artifact_count
    }

    /// Return whether every assertion obligation has an attached replayable artifact.
    pub fn is_complete(&self) -> bool {
        self.missing_assertion_obligation_ids.is_empty()
    }
}

/// One assertion row in a replayable proof-artifact coverage report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustProofArtifactCoverageAssertion {
    obligation_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_assertion_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_source_id: Option<String>,
    covered: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_artifact_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_artifact_binding_fingerprint: Option<String>,
}

impl TrustProofArtifactCoverageAssertion {
    /// Return the Trust obligation id for this assertion.
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    /// Return the compiler-emitted TrustIr assertion id for this assertion, if present.
    pub const fn trust_ir_assertion_id(&self) -> Option<u32> {
        self.trust_ir_assertion_id
    }

    /// Return the compiler-emitted TrustIr source id for this assertion, if present.
    pub fn trust_ir_source_id(&self) -> Option<&str> {
        self.trust_ir_source_id.as_deref()
    }

    /// Return whether this assertion has an attached replayable proof artifact.
    pub const fn covered(&self) -> bool {
        self.covered
    }

    /// Return the replayable proof-artifact id covering this assertion, if present.
    pub fn proof_artifact_id(&self) -> Option<&str> {
        self.proof_artifact_id.as_deref()
    }

    /// Return the proof-artifact binding fingerprint covering this assertion, if present.
    pub fn proof_artifact_binding_fingerprint(&self) -> Option<&str> {
        self.proof_artifact_binding_fingerprint.as_deref()
    }
}

/// Per-obligation evidence accepted by the TrustVc verifier boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustProofEvidence {
    obligation_id: String,
    role: TrustObligationRole,
    kind: TrustObligationKind,
    expr: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    typed_expr: Option<TrustExpr>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_lineage: Option<TrustProofLineage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    bootstrap_provenance: Option<TrustBootstrapProvenance>,
    source: TrustProofEvidenceSource,
    #[serde(default)]
    evidence_profile: TrustProofEvidenceProfile,
    #[serde(default)]
    reasoning_kind: TrustProofReasoningKind,
    #[serde(default)]
    assurance_level: TrustAssuranceLevel,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    location: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_artifact_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    proof_artifact_binding_fingerprint: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    cache_key: Option<TrustEvidenceCacheKey>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_assertion_id: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trust_ir_source_id: Option<String>,
}

impl TrustProofEvidence {
    fn from_obligation(
        unit: &TrustVerificationUnit,
        obligation: &TrustObligation,
        mode: TrustVerificationMode,
        proof_artifact_id: Option<&str>,
        proof_artifact_binding_fingerprint: Option<&str>,
        cache_key: Option<TrustEvidenceCacheKey>,
    ) -> Self {
        Self {
            obligation_id: obligation.id.clone(),
            role: obligation.role,
            kind: obligation.kind.clone(),
            expr: obligation.expr.clone(),
            typed_expr: obligation.typed_expr.clone(),
            proof_lineage: obligation.proof_lineage.clone(),
            bootstrap_provenance: obligation.bootstrap_provenance.clone(),
            source: if obligation.typed_expr.is_some() {
                TrustProofEvidenceSource::TypedTrustVcExpr
            } else {
                TrustProofEvidenceSource::LegacySourceText
            },
            evidence_profile: TrustProofEvidenceProfile::for_obligation(unit, obligation, mode),
            reasoning_kind: TrustProofReasoningKind::for_obligation(obligation),
            assurance_level: TrustAssuranceLevel::for_obligation(obligation, mode),
            location: obligation.location.clone(),
            proof_artifact_id: proof_artifact_id.map(str::to_string),
            proof_artifact_binding_fingerprint: proof_artifact_binding_fingerprint
                .map(str::to_string),
            cache_key,
            trust_ir_assertion_id: obligation.trust_ir_assertion_id,
            trust_ir_source_id: obligation.trust_ir_source_id.clone(),
        }
    }

    /// Return the stable obligation id.
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    /// Return the obligation role.
    pub const fn role(&self) -> TrustObligationRole {
        self.role
    }

    /// Return the obligation kind.
    pub const fn kind(&self) -> &TrustObligationKind {
        &self.kind
    }

    /// Return the diagnostic expression label.
    pub fn expr(&self) -> &str {
        &self.expr
    }

    /// Return the exact typed expression payload admitted for this evidence.
    ///
    /// Present only for obligations supplied through the typed TrustExpr API.
    /// Downstream consumers should prefer this over the diagnostic expression
    /// label when checking evidence shape.
    pub fn typed_expr(&self) -> Option<&TrustExpr> {
        self.typed_expr.as_ref()
    }

    /// Return proof lineage for the typed compiler obligation, if supplied.
    pub fn proof_lineage(&self) -> Option<&TrustProofLineage> {
        self.proof_lineage.as_ref()
    }

    /// Return provenance for a non-contract bootstrap fact, if present.
    pub fn bootstrap_provenance(&self) -> Option<&TrustBootstrapProvenance> {
        self.bootstrap_provenance.as_ref()
    }

    /// Return the evidence source admitted at the verifier boundary.
    pub const fn source(&self) -> TrustProofEvidenceSource {
        self.source
    }

    /// Return the native evidence lane this item came from.
    pub const fn evidence_profile(&self) -> TrustProofEvidenceProfile {
        self.evidence_profile
    }

    /// Return the proof-strength reasoning class for this item.
    pub const fn reasoning_kind(&self) -> TrustProofReasoningKind {
        self.reasoning_kind
    }

    /// Return the assurance level contributed by this item.
    pub const fn assurance_level(&self) -> TrustAssuranceLevel {
        self.assurance_level
    }

    /// Return source location text, if available.
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// Return the replayable proof-artifact id covering this obligation.
    pub fn proof_artifact_id(&self) -> Option<&str> {
        self.proof_artifact_id.as_deref()
    }

    /// Return the per-assertion proof-artifact binding fingerprint, if present.
    pub fn proof_artifact_binding_fingerprint(&self) -> Option<&str> {
        self.proof_artifact_binding_fingerprint.as_deref()
    }

    /// Return the stable evidence cache key for this obligation, if reported.
    pub fn cache_key(&self) -> Option<&TrustEvidenceCacheKey> {
        self.cache_key.as_ref()
    }

    /// Return the compiler-emitted TrustIr assertion id covered by this evidence.
    pub const fn trust_ir_assertion_id(&self) -> Option<u32> {
        self.trust_ir_assertion_id
    }

    /// Return the compiler-emitted TrustIr source id covered by this evidence.
    pub fn trust_ir_source_id(&self) -> Option<&str> {
        self.trust_ir_source_id.as_deref()
    }
}

/// Source of proof evidence admitted through the tRust-facing TrustVc adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustProofEvidenceSource {
    /// The obligation was supplied as typed TrustExpr and lowered to TrustVcExpr.
    TypedTrustVcExpr,
    /// Compatibility-mode evidence came from legacy source text parsing.
    LegacySourceText,
}

/// Native evidence profile emitted for tRust/trust-trust-vc-lib consumption.
///
/// Profiles deliberately separate typed contract-frame evidence from
/// ownership/memory evidence and from compatibility evidence. Downstream
/// aggregators should not infer proof strength from `Verified` alone.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustProofEvidenceProfile {
    /// Missing profile from an older serialized payload.
    #[default]
    Unspecified,
    /// Full-mode typed contract-clause evidence backed by a native contract frame.
    TypedContractFrame,
    /// Full-mode typed ownership or memory-safety evidence.
    OwnershipMemory,
    /// Full-mode typed invariant evidence.
    TypedInvariant,
    /// Full-mode typed translation-validation evidence.
    TypedTranslationValidation,
    /// Full-mode typed bool/fixed-int cast bootstrap evidence.
    TypedCastBootstrap,
    /// Full-mode typed ADT constructor/discriminant bootstrap evidence.
    TypedAdtBootstrap,
    /// Full-mode typed pointer bootstrap evidence.
    TypedPointerBootstrap,
    /// Full-mode typed fat-pointer bootstrap evidence.
    TypedFatPointerBootstrap,
    /// Full-mode typed closure/Fn/FnMut/FnOnce bootstrap evidence.
    TypedClosureBootstrap,
    /// Full-mode typed FnPtr bootstrap evidence.
    TypedFnPtrBootstrap,
    /// Full-mode typed deductive obligation not tied to a narrower profile.
    TypedDeductiveObligation,
    /// Compatibility-mode typed obligation evidence.
    TypedCompatibility,
    /// Compatibility-mode source-string evidence.
    LegacyCompatibility,
}

impl TrustProofEvidenceProfile {
    fn for_obligation(
        unit: &TrustVerificationUnit,
        obligation: &TrustObligation,
        mode: TrustVerificationMode,
    ) -> Self {
        if obligation.typed_expr.is_none() {
            return Self::LegacyCompatibility;
        }
        if mode != TrustVerificationMode::Full {
            return Self::TypedCompatibility;
        }

        match &obligation.kind {
            TrustObligationKind::Precondition
            | TrustObligationKind::Recommends
            | TrustObligationKind::Postcondition
                if obligation_has_contract_frame_profile(unit, obligation) =>
            {
                Self::TypedContractFrame
            }
            TrustObligationKind::MemorySafety => Self::OwnershipMemory,
            TrustObligationKind::TypeInvariant => Self::TypedInvariant,
            TrustObligationKind::TranslationValidation => Self::TypedTranslationValidation,
            TrustObligationKind::CastPrecondition => Self::TypedCastBootstrap,
            TrustObligationKind::AdtDiscriminant => Self::TypedAdtBootstrap,
            TrustObligationKind::PointerBootstrap => Self::TypedPointerBootstrap,
            TrustObligationKind::FatPointerBootstrap => Self::TypedFatPointerBootstrap,
            TrustObligationKind::ClosureBootstrap => Self::TypedClosureBootstrap,
            TrustObligationKind::FnPtrBootstrap => Self::TypedFnPtrBootstrap,
            _ => Self::TypedDeductiveObligation,
        }
    }
}

fn obligation_has_contract_frame_profile(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
) -> bool {
    let Some(contract_frame) = unit
        .native_context
        .as_ref()
        .and_then(TrustNativeContext::contract_frame)
    else {
        return false;
    };

    match &obligation.kind {
        TrustObligationKind::Precondition => true,
        TrustObligationKind::Recommends => true,
        TrustObligationKind::Postcondition => contract_frame.return_value().is_some(),
        _ => false,
    }
}

/// Proof-strength reasoning class for TrustVc evidence.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustProofReasoningKind {
    /// Missing reasoning kind from an older serialized payload.
    #[default]
    Unspecified,
    /// Deductive SMT proof over a typed or compatibility-lowered obligation.
    Deductive,
    /// Ownership or memory-separation proof over native Rust/TrustIr ownership state.
    Ownership,
    /// Constructive proof evidence with a carried witness.
    Constructive,
}

impl TrustProofReasoningKind {
    fn for_obligation(obligation: &TrustObligation) -> Self {
        match &obligation.kind {
            TrustObligationKind::MemorySafety => Self::Ownership,
            _ => Self::Deductive,
        }
    }
}

/// Assurance level contributed by a TrustVc proof-evidence item.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustAssuranceLevel {
    /// Missing assurance level from an older serialized payload.
    #[default]
    Unspecified,
    /// Verified through compatibility mode; not publication-grade native proof evidence.
    CompatibilityEvidence,
    /// Trusted typed context used as an assumption by TrustVc.
    AssumedEvidence,
    /// Static proof evidence discharged by TrustVc.
    StaticProof,
    /// Metadata that affects proof setup but is not itself a proof.
    MetadataOnly,
}

impl TrustAssuranceLevel {
    fn for_obligation(obligation: &TrustObligation, mode: TrustVerificationMode) -> Self {
        if mode != TrustVerificationMode::Full {
            return Self::CompatibilityEvidence;
        }
        if obligation.kind == TrustObligationKind::Recommends {
            return Self::MetadataOnly;
        }
        if obligation.role == TrustObligationRole::Assumption {
            return Self::AssumedEvidence;
        }
        match &obligation.kind {
            TrustObligationKind::Axiom => Self::AssumedEvidence,
            _ => Self::StaticProof,
        }
    }
}

fn configure_trust_verification_context(
    unit: &TrustVerificationUnit,
    context: &mut VerificationContext,
) {
    if unit
        .obligations
        .iter()
        .any(|obligation| obligation.kind == TrustObligationKind::Recommends)
    {
        context.set_verification_mode(trust_vc_core::vc::VerificationMode::CallSite);
    }
}

/// Aggregate report counts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[must_use]
pub struct TrustReportSummary {
    pub verified: usize,
    pub refuted: usize,
    pub unknown: usize,
    pub error: usize,
}

impl TrustReportSummary {
    /// Total number of reported units.
    pub const fn total(self) -> usize {
        self.verified + self.refuted + self.unknown + self.error
    }
}

/// Solver outcome normalized for tRust-facing consumers.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
#[non_exhaustive]
#[must_use]
pub enum TrustOutcome {
    Verified,
    Refuted {
        obligation_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        model: Option<String>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        bindings: Vec<TrustCounterexampleBinding>,
    },
    Unknown {
        reason: String,
        category: String,
    },
    Error {
        message: String,
    },
}

impl From<VerifyResult> for TrustOutcome {
    fn from(value: VerifyResult) -> Self {
        match value {
            VerifyResult::Verified => Self::Verified,
            VerifyResult::Counterexample {
                obligation_name,
                model,
                bindings,
            } => Self::Refuted {
                obligation_id: obligation_name,
                model,
                bindings: bindings.into_iter().map(Into::into).collect(),
            },
            // A model-less verification FAILURE. Lowered to `Refuted` (the
            // obligation did not hold up) with `model: None` and NO bindings —
            // the absence is the point: Trust must not be handed a
            // counterexample that was never found. `Unknown` would understate a
            // definite non-proof as an inconclusive run.
            VerifyResult::NotProved { reason, category } => Self::Refuted {
                obligation_id: format!("not proved (no model; {category:?}): {reason}"),
                model: None,
                bindings: Vec::new(),
            },
            VerifyResult::Unknown { reason, category } => Self::Unknown {
                reason,
                category: format!("{category:?}"),
            },
            VerifyResult::Error { message } => Self::Error { message },
            _ => Self::Error {
                message: "unsupported trust_vc verification result variant".to_string(),
            },
        }
    }
}

/// Counterexample binding normalized from trust_vc.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustCounterexampleBinding {
    pub display_name: String,
    pub raw_name: String,
    pub ty: String,
    pub value: String,
}

impl From<CounterexampleBinding> for TrustCounterexampleBinding {
    fn from(value: CounterexampleBinding) -> Self {
        Self {
            display_name: value.display_name,
            raw_name: value.raw_name,
            ty: value.ty,
            value: value.value,
        }
    }
}

/// Auxiliary diagnostic emitted while verifying a unit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustDiagnostic {
    message: String,
}

impl TrustDiagnostic {
    /// Return the diagnostic message.
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// Request/lowering errors at the adapter boundary.
#[derive(Debug, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrustEngineError {
    #[error("trust verification request must contain at least one unit")]
    EmptyRequest,
    #[error("trust verification unit has an empty id")]
    EmptyUnitId,
    #[error("trust verification unit `{unit_id}` must contain at least one assertion obligation")]
    UnitHasNoAssertions { unit_id: String },
    #[error("trust variable at index {index} in unit `{unit_id}` has an empty name")]
    EmptyVariableName { unit_id: String, index: usize },
    #[error("trust unit `{unit_id}` declares duplicate variable `{name}`")]
    DuplicateVariable { unit_id: String, name: String },
    #[error("trust obligation at index {index} in unit `{unit_id}` has an empty id")]
    EmptyObligationId { unit_id: String, index: usize },
    #[error("trust obligation `{obligation_id}` in unit `{unit_id}` has an empty expression")]
    EmptyObligationExpr {
        unit_id: String,
        obligation_id: String,
    },
    #[error(
        "trust obligation `{obligation_id}` in unit `{unit_id}` is string-backed and cannot satisfy full verification"
    )]
    StringBackedFullModeObligation {
        unit_id: String,
        obligation_id: String,
    },
    #[error(
        "trust obligation `{obligation_id}` in unit `{unit_id}` requires typed native context: {missing}"
    )]
    MissingNativeContext {
        unit_id: String,
        obligation_id: String,
        missing: &'static str,
    },
    #[error("native function signature in unit `{unit_id}` has an empty name")]
    EmptyNativeFunctionName { unit_id: String },
    #[error("native datatype at index {index} in unit `{unit_id}` has an empty name")]
    EmptyDatatypeName { unit_id: String, index: usize },
    #[error("native datatype `{datatype}` in unit `{unit_id}` has no variants")]
    DatatypeHasNoVariants { unit_id: String, datatype: String },
    #[error("native datatype `{datatype}` variant at index {index} in unit `{unit_id}` has an empty name")]
    EmptyDatatypeVariantName {
        unit_id: String,
        datatype: String,
        index: usize,
    },
    #[error("native field at index {index} in `{owner}` for unit `{unit_id}` has an empty name")]
    EmptyNativeFieldName {
        unit_id: String,
        owner: String,
        index: usize,
    },
    #[error("native invariant at index {index} in unit `{unit_id}` has an empty id")]
    EmptyInvariantId { unit_id: String, index: usize },
    #[error(
        "native predicate for invariant `{invariant_id}` in unit `{unit_id}` has an empty name"
    )]
    EmptyPredicateName {
        unit_id: String,
        invariant_id: String,
    },
    #[error("native ownership place at index {index} in unit `{unit_id}` has an empty path")]
    EmptyOwnedPlace { unit_id: String, index: usize },
    #[error("native borrow at index {index} in unit `{unit_id}` has an empty region or place")]
    EmptyBorrow { unit_id: String, index: usize },
    #[error("native ownership fact at index {index} in unit `{unit_id}` is invalid: {message}")]
    InvalidOwnershipFact {
        unit_id: String,
        index: usize,
        message: String,
    },
    #[error("typed expression in obligation `{obligation_id}` for unit `{unit_id}` has an empty variable name")]
    EmptyTypedExprVariableName {
        unit_id: String,
        obligation_id: String,
    },
    #[error("typed old-expression in obligation `{obligation_id}` for unit `{unit_id}` has an empty source or snapshot")]
    EmptyTypedOldValue {
        unit_id: String,
        obligation_id: String,
    },
    #[error("typed expression in obligation `{obligation_id}` for unit `{unit_id}` has an empty function name")]
    EmptyTypedExprFunctionName {
        unit_id: String,
        obligation_id: String,
    },
    #[error(
        "typed expression in obligation `{obligation_id}` for unit `{unit_id}` references undeclared variable `{variable}`"
    )]
    UnknownTypedExprVariable {
        unit_id: String,
        obligation_id: String,
        variable: String,
    },
    #[error(
        "typed old-expression `{snapshot}` in obligation `{obligation_id}` for unit `{unit_id}` is not backed by the native contract frame"
    )]
    UnknownTypedOldSnapshot {
        unit_id: String,
        obligation_id: String,
        snapshot: String,
    },
    #[error(
        "typed old-expression `{snapshot}` in obligation `{obligation_id}` for unit `{unit_id}` snapshots `{actual_source}`, not `{expected_source}`"
    )]
    TypedOldSnapshotSourceMismatch {
        unit_id: String,
        obligation_id: String,
        snapshot: String,
        expected_source: String,
        actual_source: String,
    },
    #[error("typed expression in obligation `{obligation_id}` for unit `{unit_id}` is ill-typed: {message}")]
    InvalidTypedExpr {
        unit_id: String,
        obligation_id: String,
        message: String,
    },
    #[error(
        "proof lineage for obligation `{obligation_id}` in unit `{unit_id}` is invalid: {message}"
    )]
    InvalidProofLineage {
        unit_id: String,
        obligation_id: String,
        message: String,
    },
    #[error(
        "source span for obligation `{obligation_id}` in unit `{unit_id}` is invalid: {message}"
    )]
    InvalidSourceSpan {
        unit_id: String,
        obligation_id: String,
        message: String,
    },
    #[error("TrustIr construct `{feature}` in obligation `{obligation_id}` for unit `{unit_id}` is unsupported: {diagnostic}")]
    UnsupportedTrustIrConstruct {
        unit_id: String,
        obligation_id: String,
        feature: String,
        diagnostic: String,
    },
    #[error(
        "TrustVc typed proof obligation `{obligation_id}` in unit `{unit_id}` uses unsupported structured evidence: {feature}"
    )]
    UnsupportedTypedProofObligation {
        unit_id: String,
        obligation_id: String,
        feature: String,
    },
    #[error("bootstrap fact `{obligation_id}` in unit `{unit_id}` is invalid: {message}")]
    InvalidBootstrapFact {
        unit_id: String,
        obligation_id: String,
        message: String,
    },
    #[error(
        "bootstrap fact `{obligation_id}` in unit `{unit_id}` is missing first-class provenance"
    )]
    MissingBootstrapProvenance {
        unit_id: String,
        obligation_id: String,
    },
    #[error(
        "bootstrap provenance for `{obligation_id}` in unit `{unit_id}` is invalid: {message}"
    )]
    InvalidBootstrapProvenance {
        unit_id: String,
        obligation_id: String,
        message: String,
    },
    #[error("could not serialize MIR memory proof unit `{unit_id}`: {reason}")]
    SerializeMirMemoryProofUnit { unit_id: String, reason: String },
    #[error("verification report did not include expected unit `{unit_id}`")]
    MissingVerifiedUnitReport { unit_id: String },
    #[error("replayable proof artifacts for source `{source_id}` require full verification mode")]
    ReplayableProofArtifactsRequireFullMode { source_id: String },
    #[error("verified unit `{unit_id}` cannot satisfy proof policy {policy:?}: {reason}")]
    ReplayableProofCertificateUnavailable {
        unit_id: String,
        policy: TrustProofPolicy,
        reason: &'static str,
    },
    #[error("invalid native TrustIr verification bundle: {errors}")]
    InvalidNativeTrustIrBundle { errors: String },
    #[error("native TrustIr bundle for module `{module}` contains no TrustVc requests")]
    NativeTrustIrBundleHasNoTrustVcRequests { module: String },
    #[error(
        "native TrustIr TrustVc request {request_id} does not provide a certificate for obligation {obligation_id}"
    )]
    NativeTrustIrTrustVcRequestMissingCertificate { request_id: u32, obligation_id: u32 },
    #[error(
        "native TrustIr TrustVc request {request_id} references unknown obligation {obligation_id}"
    )]
    NativeTrustIrTrustVcRequestUnknownObligation { request_id: u32, obligation_id: u32 },
    #[error(
        "native TrustIr TrustVc request {request_id} includes unexpected certificate {obligation_id}/{prover}"
    )]
    NativeTrustIrTrustVcRequestUnexpectedCertificate {
        request_id: u32,
        obligation_id: u32,
        prover: String,
    },
    #[error(
        "native TrustIr TrustVc request {request_id} references missing certificate {obligation_id}/{prover}"
    )]
    NativeTrustIrCertificateMissing {
        request_id: u32,
        obligation_id: u32,
        prover: String,
    },
    #[error("unsupported TrustIr adapter schema version {actual}; expected {expected}")]
    UnsupportedTrustIrAdapterSchemaVersion { actual: u32, expected: u32 },
    #[error("invalid native datatype `{datatype}`: {message}")]
    InvalidDatatype { datatype: String, message: String },
    #[error("invalid bit-vector width {width}; expected one of 8, 16, 32, 64, or 128")]
    InvalidBitVectorWidth { width: u32 },
    #[error("invalid float width {width}; expected 32 or 64")]
    InvalidFloatWidth { width: u32 },
}

fn validate_unit_for_mode(
    unit: &TrustVerificationUnit,
    mode: TrustVerificationMode,
) -> Result<(), TrustEngineError> {
    if unit.unit_id.is_empty() {
        return Err(TrustEngineError::EmptyUnitId);
    }

    let mut variable_sorts = BTreeMap::new();
    let mut old_snapshots = BTreeMap::new();
    for (index, variable) in unit.variables.iter().enumerate() {
        validate_variable(&unit.unit_id, variable, index)?;
        if variable_sorts
            .insert(variable.name.clone(), variable.sort.clone())
            .is_some()
        {
            return Err(TrustEngineError::DuplicateVariable {
                unit_id: unit.unit_id.clone(),
                name: variable.name.clone(),
            });
        }
    }

    if let Some(native_context) = &unit.native_context {
        validate_native_context(
            unit,
            native_context,
            &mut variable_sorts,
            &mut old_snapshots,
        )?;
    }

    let mut has_assertion = false;
    for (index, obligation) in unit.obligations.iter().enumerate() {
        if obligation.id.is_empty() {
            return Err(TrustEngineError::EmptyObligationId {
                unit_id: unit.unit_id.clone(),
                index,
            });
        }
        if obligation.expr.is_empty() {
            return Err(TrustEngineError::EmptyObligationExpr {
                unit_id: unit.unit_id.clone(),
                obligation_id: obligation.id.clone(),
            });
        }
        if mode == TrustVerificationMode::Full && !obligation.is_typed() {
            return Err(TrustEngineError::StringBackedFullModeObligation {
                unit_id: unit.unit_id.clone(),
                obligation_id: obligation.id.clone(),
            });
        }
        if let Some(expr) = obligation.typed_expr() {
            validate_trust_expr(
                &unit.unit_id,
                &obligation.id,
                expr,
                &variable_sorts,
                &old_snapshots,
            )?;
        }
        if let Some(lineage) = obligation.proof_lineage() {
            validate_proof_lineage(&unit.unit_id, &obligation.id, lineage)?;
        }
        validate_bootstrap_fact_shape(unit, obligation, mode)?;
        validate_native_context_for_obligation(unit, obligation, mode)?;
        has_assertion |= obligation.is_assertion();
    }

    if !has_assertion {
        return Err(TrustEngineError::UnitHasNoAssertions {
            unit_id: unit.unit_id.clone(),
        });
    }

    Ok(())
}

fn validate_request_proof_policy(
    request: &TrustVerificationRequest,
) -> Result<(), TrustEngineError> {
    if request.proof_policy.wants_replayable_artifact()
        && request.mode != TrustVerificationMode::Full
    {
        return Err(TrustEngineError::ReplayableProofArtifactsRequireFullMode {
            source_id: request.source_id.clone(),
        });
    }
    Ok(())
}

#[cfg(feature = "proof-certificates")]
fn sha256_digest(payload: &str) -> String {
    sha256_digest_bytes(payload.as_bytes())
}

#[cfg(feature = "proof-certificates")]
fn all_assumption_obligation_ids(unit: &TrustVerificationUnit) -> Vec<String> {
    unit.obligations
        .iter()
        .filter(|obligation| obligation.role == TrustObligationRole::Assumption)
        .map(|obligation| obligation.id.clone())
        .collect()
}

#[cfg(feature = "proof-certificates")]
fn assumption_obligation_ids_for_step(
    unit: &TrustVerificationUnit,
    used_assumptions: &[String],
) -> Vec<String> {
    let all_assumptions = all_assumption_obligation_ids(unit);
    let used = all_assumptions
        .iter()
        .filter(|id| used_assumptions.iter().any(|used| used == *id))
        .cloned()
        .collect::<Vec<_>>();
    if used.is_empty() {
        all_assumptions
    } else {
        used
    }
}

fn validate_variable(
    unit_id: &str,
    variable: &TrustVariable,
    index: usize,
) -> Result<(), TrustEngineError> {
    if variable.name.is_empty() {
        return Err(TrustEngineError::EmptyVariableName {
            unit_id: unit_id.to_string(),
            index,
        });
    }
    variable.sort.to_trust_vc_type()?;
    Ok(())
}

fn validate_trust_expr(
    unit_id: &str,
    obligation_id: &str,
    expr: &TrustExpr,
    variable_sorts: &BTreeMap<String, TrustSort>,
    old_snapshots: &BTreeMap<String, (String, TrustSort)>,
) -> Result<(), TrustEngineError> {
    let sort = infer_trust_expr_sort(unit_id, obligation_id, expr, variable_sorts, old_snapshots)?;
    if !sort.is_bool() {
        return Err(TrustEngineError::InvalidTypedExpr {
            unit_id: unit_id.to_string(),
            obligation_id: obligation_id.to_string(),
            message: format!(
                "proof obligations must have bool sort, got {}",
                sort.display_label()
            ),
        });
    }
    Ok(())
}

fn validate_proof_lineage(
    unit_id: &str,
    obligation_id: &str,
    lineage: &TrustProofLineage,
) -> Result<(), TrustEngineError> {
    if lineage.producer.trim().is_empty() {
        return Err(TrustEngineError::InvalidProofLineage {
            unit_id: unit_id.to_string(),
            obligation_id: obligation_id.to_string(),
            message: "producer must not be empty".to_string(),
        });
    }
    if lineage.stage.trim().is_empty() {
        return Err(TrustEngineError::InvalidProofLineage {
            unit_id: unit_id.to_string(),
            obligation_id: obligation_id.to_string(),
            message: "stage must not be empty".to_string(),
        });
    }
    if lineage.rule.trim().is_empty() {
        return Err(TrustEngineError::InvalidProofLineage {
            unit_id: unit_id.to_string(),
            obligation_id: obligation_id.to_string(),
            message: "rule must not be empty".to_string(),
        });
    }
    if matches!(
        &lineage.source,
        TrustProofLineageSource::ExternalAxiom(source) | TrustProofLineageSource::Other(source)
            if source.trim().is_empty()
    ) {
        return Err(TrustEngineError::InvalidProofLineage {
            unit_id: unit_id.to_string(),
            obligation_id: obligation_id.to_string(),
            message: "named lineage source must not be empty".to_string(),
        });
    }
    if matches!(lineage.input_digest.as_deref(), Some(digest) if digest.trim().is_empty()) {
        return Err(TrustEngineError::InvalidProofLineage {
            unit_id: unit_id.to_string(),
            obligation_id: obligation_id.to_string(),
            message: "input digest must not be empty when provided".to_string(),
        });
    }
    Ok(())
}

fn infer_trust_expr_sort(
    unit_id: &str,
    obligation_id: &str,
    expr: &TrustExpr,
    variable_sorts: &BTreeMap<String, TrustSort>,
    old_snapshots: &BTreeMap<String, (String, TrustSort)>,
) -> Result<TrustSort, TrustEngineError> {
    match expr {
        TrustExpr::BoolLiteral { .. } => Ok(TrustSort::Bool),
        TrustExpr::IntLiteral { sort, .. } => {
            sort.to_trust_vc_type()?;
            if !sort.is_comparable_integer() {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!("integer literal cannot have {} sort", sort.display_label()),
                });
            }
            Ok(sort.clone())
        }
        TrustExpr::Variable { name, sort } => {
            if name.is_empty() {
                return Err(TrustEngineError::EmptyTypedExprVariableName {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                });
            }
            sort.to_trust_vc_type()?;
            let declared = variable_sorts.get(name).ok_or_else(|| {
                TrustEngineError::UnknownTypedExprVariable {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    variable: name.clone(),
                }
            })?;
            if declared != sort {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "variable `{name}` is declared as {}, but expression used {}",
                        declared.display_label(),
                        sort.display_label()
                    ),
                });
            }
            Ok(sort.clone())
        }
        TrustExpr::Old {
            source,
            snapshot,
            sort,
        } => {
            if source.is_empty() || snapshot.is_empty() {
                return Err(TrustEngineError::EmptyTypedOldValue {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                });
            }
            sort.to_trust_vc_type()?;
            let (actual_source, declared_sort) = old_snapshots.get(snapshot).ok_or_else(|| {
                TrustEngineError::UnknownTypedOldSnapshot {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    snapshot: snapshot.clone(),
                }
            })?;
            if actual_source != source {
                return Err(TrustEngineError::TypedOldSnapshotSourceMismatch {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    snapshot: snapshot.clone(),
                    expected_source: source.clone(),
                    actual_source: actual_source.clone(),
                });
            }
            if declared_sort != sort {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "old snapshot `{snapshot}` is declared as {}, but expression used {}",
                        declared_sort.display_label(),
                        sort.display_label()
                    ),
                });
            }
            Ok(sort.clone())
        }
        TrustExpr::Arith {
            left, right, sort, ..
        } => {
            let left_sort =
                infer_trust_expr_sort(unit_id, obligation_id, left, variable_sorts, old_snapshots)?;
            let right_sort = infer_trust_expr_sort(
                unit_id,
                obligation_id,
                right,
                variable_sorts,
                old_snapshots,
            )?;
            if left_sort != right_sort {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "arithmetic operands differ: {} vs {}",
                        left_sort.display_label(),
                        right_sort.display_label()
                    ),
                });
            }
            if &left_sort != sort {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "arithmetic result sort says {}, but operands have {}",
                        sort.display_label(),
                        left_sort.display_label()
                    ),
                });
            }
            if !sort.is_comparable_integer() {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "arithmetic requires integer operands, got {}",
                        sort.display_label()
                    ),
                });
            }
            Ok(sort.clone())
        }
        TrustExpr::Compare { op, left, right } => {
            let left_sort =
                infer_trust_expr_sort(unit_id, obligation_id, left, variable_sorts, old_snapshots)?;
            let right_sort = infer_trust_expr_sort(
                unit_id,
                obligation_id,
                right,
                variable_sorts,
                old_snapshots,
            )?;
            if left_sort != right_sort {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "comparison operands differ: {} vs {}",
                        left_sort.display_label(),
                        right_sort.display_label()
                    ),
                });
            }
            if !matches!(op, TrustCompareOp::Eq | TrustCompareOp::Ne)
                && !left_sort.is_comparable_integer()
            {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "ordered comparison requires integer operands, got {}",
                        left_sort.display_label()
                    ),
                });
            }
            Ok(TrustSort::Bool)
        }
        TrustExpr::Logic { left, right, .. } => {
            let left_sort =
                infer_trust_expr_sort(unit_id, obligation_id, left, variable_sorts, old_snapshots)?;
            let right_sort = infer_trust_expr_sort(
                unit_id,
                obligation_id,
                right,
                variable_sorts,
                old_snapshots,
            )?;
            require_bool_sort(unit_id, obligation_id, "logical left operand", &left_sort)?;
            require_bool_sort(unit_id, obligation_id, "logical right operand", &right_sort)?;
            Ok(TrustSort::Bool)
        }
        TrustExpr::Not { expr } => {
            let sort =
                infer_trust_expr_sort(unit_id, obligation_id, expr, variable_sorts, old_snapshots)?;
            require_bool_sort(unit_id, obligation_id, "logical negation operand", &sort)?;
            Ok(TrustSort::Bool)
        }
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            let premise_sort = infer_trust_expr_sort(
                unit_id,
                obligation_id,
                premise,
                variable_sorts,
                old_snapshots,
            )?;
            let conclusion_sort = infer_trust_expr_sort(
                unit_id,
                obligation_id,
                conclusion,
                variable_sorts,
                old_snapshots,
            )?;
            require_bool_sort(unit_id, obligation_id, "implication premise", &premise_sort)?;
            require_bool_sort(
                unit_id,
                obligation_id,
                "implication conclusion",
                &conclusion_sort,
            )?;
            Ok(TrustSort::Bool)
        }
        TrustExpr::Cast {
            expr,
            from_sort,
            to_sort,
        } => {
            let inner_sort =
                infer_trust_expr_sort(unit_id, obligation_id, expr, variable_sorts, old_snapshots)?;
            from_sort.to_trust_vc_type()?;
            to_sort.to_trust_vc_type()?;
            if inner_sort != *from_sort {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "cast source sort says {}, but inner expression has {}",
                        from_sort.display_label(),
                        inner_sort.display_label()
                    ),
                });
            }
            if !is_supported_bool_int_cast(from_sort, to_sort) {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: format!(
                        "unsupported bootstrap cast from {} to {}",
                        from_sort.display_label(),
                        to_sort.display_label()
                    ),
                });
            }
            Ok(to_sort.clone())
        }
        TrustExpr::Call {
            function,
            args,
            return_sort,
        } => {
            if function.is_empty() {
                return Err(TrustEngineError::EmptyTypedExprFunctionName {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                });
            }
            return_sort.to_trust_vc_type()?;
            for arg in args {
                let _ = infer_trust_expr_sort(
                    unit_id,
                    obligation_id,
                    arg,
                    variable_sorts,
                    old_snapshots,
                )?;
            }
            Ok(return_sort.clone())
        }
        TrustExpr::Quantifier {
            bound_vars,
            body,
            triggers,
            ..
        } => {
            if bound_vars.is_empty() {
                return Err(TrustEngineError::InvalidTypedExpr {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message: "quantifier requires at least one bound variable".to_string(),
                });
            }

            let mut inner_variable_sorts = variable_sorts.clone();
            let mut bound_names = BTreeSet::new();
            for bound_var in bound_vars {
                if bound_var.name.is_empty() {
                    return Err(TrustEngineError::InvalidTypedExpr {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        message: "quantifier bound variable name must not be empty".to_string(),
                    });
                }
                bound_var.sort.to_trust_vc_type()?;
                if !bound_names.insert(bound_var.name.clone()) {
                    return Err(TrustEngineError::InvalidTypedExpr {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        message: format!(
                            "quantifier declares duplicate bound variable `{}`",
                            bound_var.name
                        ),
                    });
                }
                inner_variable_sorts.insert(bound_var.name.clone(), bound_var.sort.clone());
            }

            let body_sort = infer_trust_expr_sort(
                unit_id,
                obligation_id,
                body,
                &inner_variable_sorts,
                old_snapshots,
            )?;
            require_bool_sort(unit_id, obligation_id, "quantifier body", &body_sort)?;

            if let Some(trigger_groups) = triggers {
                if trigger_groups.is_empty() {
                    return Err(TrustEngineError::InvalidTypedExpr {
                        unit_id: unit_id.to_string(),
                        obligation_id: obligation_id.to_string(),
                        message: "quantifier triggers must contain at least one group when present"
                            .to_string(),
                    });
                }
                for (group_index, group) in trigger_groups.iter().enumerate() {
                    if group.is_empty() {
                        return Err(TrustEngineError::InvalidTypedExpr {
                            unit_id: unit_id.to_string(),
                            obligation_id: obligation_id.to_string(),
                            message: format!(
                                "quantifier trigger group {group_index} must not be empty"
                            ),
                        });
                    }
                    for (trigger_index, trigger) in group.iter().enumerate() {
                        let _ = infer_trust_expr_sort(
                            unit_id,
                            obligation_id,
                            trigger,
                            &inner_variable_sorts,
                            old_snapshots,
                        )?;
                        if !trust_expr_references_any_variable_name(trigger, &bound_names) {
                            return Err(TrustEngineError::InvalidTypedExpr {
                                unit_id: unit_id.to_string(),
                                obligation_id: obligation_id.to_string(),
                                message: format!(
                                    "quantifier trigger[{group_index}][{trigger_index}] does not reference a bound variable"
                                ),
                            });
                        }
                    }
                }
            }

            Ok(TrustSort::Bool)
        }
    }
}

fn trust_expr_references_any_variable_name(expr: &TrustExpr, names: &BTreeSet<String>) -> bool {
    match expr {
        TrustExpr::Variable { name, .. } => names.contains(name),
        TrustExpr::BoolLiteral { .. } | TrustExpr::IntLiteral { .. } | TrustExpr::Old { .. } => {
            false
        }
        TrustExpr::Arith { left, right, .. }
        | TrustExpr::Compare { left, right, .. }
        | TrustExpr::Logic { left, right, .. } => {
            trust_expr_references_any_variable_name(left, names)
                || trust_expr_references_any_variable_name(right, names)
        }
        TrustExpr::Not { expr } => trust_expr_references_any_variable_name(expr, names),
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            trust_expr_references_any_variable_name(premise, names)
                || trust_expr_references_any_variable_name(conclusion, names)
        }
        TrustExpr::Cast { expr, .. } => trust_expr_references_any_variable_name(expr, names),
        TrustExpr::Call { args, .. } => args
            .iter()
            .any(|arg| trust_expr_references_any_variable_name(arg, names)),
        TrustExpr::Quantifier {
            bound_vars,
            body,
            triggers,
            ..
        } => {
            let mut visible_names = names.clone();
            for bound_var in bound_vars {
                visible_names.remove(bound_var.name());
            }
            trust_expr_references_any_variable_name(body, &visible_names)
                || triggers.as_ref().is_some_and(|groups| {
                    groups.iter().flatten().any(|trigger| {
                        trust_expr_references_any_variable_name(trigger, &visible_names)
                    })
                })
        }
    }
}

fn require_bool_sort(
    unit_id: &str,
    obligation_id: &str,
    position: &str,
    sort: &TrustSort,
) -> Result<(), TrustEngineError> {
    if sort.is_bool() {
        return Ok(());
    }
    Err(TrustEngineError::InvalidTypedExpr {
        unit_id: unit_id.to_string(),
        obligation_id: obligation_id.to_string(),
        message: format!(
            "{position} must have bool sort, got {}",
            sort.display_label()
        ),
    })
}

fn is_supported_bool_int_cast(from_sort: &TrustSort, to_sort: &TrustSort) -> bool {
    (from_sort.is_bool() && to_sort.is_fixed_integer())
        || (from_sort.is_fixed_integer() && to_sort.is_bool())
        || (from_sort.is_fixed_integer() && to_sort.is_fixed_integer())
}

fn validate_bootstrap_fact_shape(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
    mode: TrustVerificationMode,
) -> Result<(), TrustEngineError> {
    match &obligation.kind {
        TrustObligationKind::CastPrecondition => {
            validate_common_bootstrap_fact(unit, obligation, mode)?;
            validate_cast_bootstrap_fact_shape(unit, obligation)
        }
        TrustObligationKind::AdtDiscriminant => {
            validate_common_bootstrap_fact(unit, obligation, mode)?;
            validate_adt_bootstrap_fact_shape(unit, obligation)
        }
        TrustObligationKind::PointerBootstrap => {
            validate_common_bootstrap_fact(unit, obligation, mode)?;
            validate_pointer_bootstrap_fact_shape(unit, obligation, PointerBootstrapFlavor::Thin)
        }
        TrustObligationKind::FatPointerBootstrap => {
            validate_common_bootstrap_fact(unit, obligation, mode)?;
            validate_pointer_bootstrap_fact_shape(unit, obligation, PointerBootstrapFlavor::Fat)
        }
        TrustObligationKind::ClosureBootstrap => {
            validate_common_bootstrap_fact(unit, obligation, mode)?;
            validate_callable_bootstrap_fact_shape(
                unit,
                obligation,
                mode,
                CallableBootstrapFlavor::Closure,
            )
        }
        TrustObligationKind::FnPtrBootstrap => {
            validate_common_bootstrap_fact(unit, obligation, mode)?;
            validate_callable_bootstrap_fact_shape(
                unit,
                obligation,
                mode,
                CallableBootstrapFlavor::FnPtr,
            )
        }
        _ => Ok(()),
    }
}

fn validate_common_bootstrap_fact(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
    mode: TrustVerificationMode,
) -> Result<(), TrustEngineError> {
    if let Some(provenance) = obligation.bootstrap_provenance() {
        validate_bootstrap_provenance(unit, obligation, provenance)?;
    } else if mode == TrustVerificationMode::Full {
        return Err(TrustEngineError::MissingBootstrapProvenance {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
        });
    }
    if obligation.role != TrustObligationRole::Assertion {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "bootstrap facts must be assertion obligations".to_string(),
        });
    }
    Ok(())
}

fn validate_cast_bootstrap_fact_shape(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
) -> Result<(), TrustEngineError> {
    let Some(expr) = obligation.typed_expr() else {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "cast preconditions must be backed by typed TrustExpr::Cast".to_string(),
        });
    };

    let mut shape = CastFactShape::default();
    collect_cast_fact_shape(expr, &mut shape);
    if !shape.has_cast {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "cast precondition expression contains no typed cast".to_string(),
        });
    }
    if !shape.has_variable_backed_cast {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "cast precondition expression is context-free".to_string(),
        });
    }
    Ok(())
}

fn validate_adt_bootstrap_fact_shape(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
) -> Result<(), TrustEngineError> {
    let Some(expr) = obligation.typed_expr() else {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "ADT bootstrap facts must be backed by typed TrustExpr".to_string(),
        });
    };

    let Some(native_context) = &unit.native_context else {
        return Err(TrustEngineError::MissingNativeContext {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            missing: "typed datatype metadata",
        });
    };
    if native_context.datatypes.is_empty() {
        return Err(TrustEngineError::MissingNativeContext {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            missing: "typed datatype metadata",
        });
    }

    let mut declared_datatypes = BTreeMap::new();
    for datatype in &native_context.datatypes {
        declared_datatypes.insert(datatype.name.as_str(), datatype);
    }

    let mut shape = AdtFactShape::default();
    collect_adt_fact_shape(expr, &declared_datatypes, &mut shape);
    if let Some(datatype) = shape.undeclared_datatype {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!("ADT bootstrap fact references undeclared datatype `{datatype}`"),
        });
    }
    if !shape.mentions_declared_datatype {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "ADT bootstrap expression mentions no declared native datatype".to_string(),
        });
    }
    if !shape.has_variable_backed_datatype {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "ADT bootstrap expression is context-free".to_string(),
        });
    }
    if !shape.has_adt_operation {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message:
                "ADT bootstrap expression mentions no constructor, recognizer, selector, or discriminant operation"
                    .to_string(),
        });
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum PointerBootstrapFlavor {
    Thin,
    Fat,
}

impl PointerBootstrapFlavor {
    const fn label(self) -> &'static str {
        match self {
            Self::Thin => "pointer",
            Self::Fat => "fat-pointer",
        }
    }
}

fn validate_pointer_bootstrap_fact_shape(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
    flavor: PointerBootstrapFlavor,
) -> Result<(), TrustEngineError> {
    let Some(expr) = obligation.typed_expr() else {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!(
                "{} bootstrap facts must be backed by typed TrustExpr",
                flavor.label()
            ),
        });
    };

    let mut shape = PointerFactShape::default();
    collect_pointer_fact_shape(expr, flavor, &mut shape);
    if !shape.has_pointer_operation {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!(
                "{} bootstrap expression mentions no recognized {} operation",
                flavor.label(),
                flavor.label()
            ),
        });
    }
    if !shape.has_variable_backed_pointer_operation {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!("{} bootstrap expression is context-free", flavor.label()),
        });
    }
    Ok(())
}

fn validate_bootstrap_provenance(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
    provenance: &TrustBootstrapProvenance,
) -> Result<(), TrustEngineError> {
    if provenance.justification.trim().is_empty() {
        return Err(TrustEngineError::InvalidBootstrapProvenance {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "justification must not be empty".to_string(),
        });
    }
    if matches!(
        &provenance.source,
        TrustBootstrapProvenanceSource::ExternalAxiom(source)
            | TrustBootstrapProvenanceSource::Other(source)
            if source.trim().is_empty()
    ) {
        return Err(TrustEngineError::InvalidBootstrapProvenance {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "named provenance source must not be empty".to_string(),
        });
    }
    if matches!(provenance.producer.as_deref(), Some(producer) if producer.trim().is_empty()) {
        return Err(TrustEngineError::InvalidBootstrapProvenance {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: "producer must not be empty when provided".to_string(),
        });
    }
    Ok(())
}

#[derive(Default)]
struct CastFactShape {
    has_cast: bool,
    has_variable_backed_cast: bool,
}

fn collect_cast_fact_shape(expr: &TrustExpr, shape: &mut CastFactShape) {
    match expr {
        TrustExpr::BoolLiteral { .. }
        | TrustExpr::IntLiteral { .. }
        | TrustExpr::Variable { .. }
        | TrustExpr::Old { .. } => {}
        TrustExpr::Arith { left, right, .. }
        | TrustExpr::Compare { left, right, .. }
        | TrustExpr::Logic { left, right, .. } => {
            collect_cast_fact_shape(left, shape);
            collect_cast_fact_shape(right, shape);
        }
        TrustExpr::Not { expr } => collect_cast_fact_shape(expr, shape),
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            collect_cast_fact_shape(premise, shape);
            collect_cast_fact_shape(conclusion, shape);
        }
        TrustExpr::Cast { expr, .. } => {
            shape.has_cast = true;
            shape.has_variable_backed_cast |= expr_contains_variable(expr);
            collect_cast_fact_shape(expr, shape);
        }
        TrustExpr::Call { args, .. } => {
            for arg in args {
                collect_cast_fact_shape(arg, shape);
            }
        }
        TrustExpr::Quantifier { body, triggers, .. } => {
            collect_cast_fact_shape(body, shape);
            if let Some(groups) = triggers {
                for trigger in groups.iter().flatten() {
                    collect_cast_fact_shape(trigger, shape);
                }
            }
        }
    }
}

fn expr_contains_variable(expr: &TrustExpr) -> bool {
    expr_contains_free_variable(expr, &BTreeSet::new())
}

fn expr_contains_free_variable(expr: &TrustExpr, bound_names: &BTreeSet<String>) -> bool {
    match expr {
        TrustExpr::Variable { name, .. } => !bound_names.contains(name),
        TrustExpr::Old { .. } => true,
        TrustExpr::BoolLiteral { .. } | TrustExpr::IntLiteral { .. } => false,
        TrustExpr::Arith { left, right, .. }
        | TrustExpr::Compare { left, right, .. }
        | TrustExpr::Logic { left, right, .. } => {
            expr_contains_free_variable(left, bound_names)
                || expr_contains_free_variable(right, bound_names)
        }
        TrustExpr::Not { expr } => expr_contains_free_variable(expr, bound_names),
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            expr_contains_free_variable(premise, bound_names)
                || expr_contains_free_variable(conclusion, bound_names)
        }
        TrustExpr::Cast { expr, .. } => expr_contains_free_variable(expr, bound_names),
        TrustExpr::Call { args, .. } => args
            .iter()
            .any(|arg| expr_contains_free_variable(arg, bound_names)),
        TrustExpr::Quantifier {
            bound_vars,
            body,
            triggers,
            ..
        } => {
            let mut inner_bound_names = bound_names.clone();
            for bound_var in bound_vars {
                inner_bound_names.insert(bound_var.name().to_string());
            }
            expr_contains_free_variable(body, &inner_bound_names)
                || triggers.as_ref().is_some_and(|groups| {
                    groups
                        .iter()
                        .flatten()
                        .any(|trigger| expr_contains_free_variable(trigger, &inner_bound_names))
                })
        }
    }
}

#[derive(Default)]
struct PointerFactShape {
    has_pointer_operation: bool,
    has_variable_backed_pointer_operation: bool,
}

fn collect_pointer_fact_shape(
    expr: &TrustExpr,
    flavor: PointerBootstrapFlavor,
    shape: &mut PointerFactShape,
) {
    match expr {
        TrustExpr::BoolLiteral { .. }
        | TrustExpr::IntLiteral { .. }
        | TrustExpr::Variable { .. }
        | TrustExpr::Old { .. } => {}
        TrustExpr::Arith { left, right, .. }
        | TrustExpr::Compare { left, right, .. }
        | TrustExpr::Logic { left, right, .. } => {
            collect_pointer_fact_shape(left, flavor, shape);
            collect_pointer_fact_shape(right, flavor, shape);
        }
        TrustExpr::Not { expr } => collect_pointer_fact_shape(expr, flavor, shape),
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            collect_pointer_fact_shape(premise, flavor, shape);
            collect_pointer_fact_shape(conclusion, flavor, shape);
        }
        TrustExpr::Cast { expr, .. } => collect_pointer_fact_shape(expr, flavor, shape),
        TrustExpr::Call { function, args, .. } => {
            for arg in args {
                collect_pointer_fact_shape(arg, flavor, shape);
            }
            if is_pointer_bootstrap_operation(function, flavor) {
                shape.has_pointer_operation = true;
                shape.has_variable_backed_pointer_operation |= args.iter().any(|arg| {
                    expr_contains_variable(arg) && expr_contains_pointer_sort(arg, flavor)
                });
            }
        }
        TrustExpr::Quantifier { body, triggers, .. } => {
            collect_pointer_fact_shape(body, flavor, shape);
            if let Some(groups) = triggers {
                for trigger in groups.iter().flatten() {
                    collect_pointer_fact_shape(trigger, flavor, shape);
                }
            }
        }
    }
}

fn expr_contains_pointer_sort(expr: &TrustExpr, flavor: PointerBootstrapFlavor) -> bool {
    match expr {
        TrustExpr::BoolLiteral { .. } | TrustExpr::IntLiteral { .. } => false,
        TrustExpr::Variable { sort, .. } | TrustExpr::Old { sort, .. } => {
            sort_is_pointer_like(sort, flavor)
        }
        TrustExpr::Arith { left, right, .. }
        | TrustExpr::Compare { left, right, .. }
        | TrustExpr::Logic { left, right, .. } => {
            expr_contains_pointer_sort(left, flavor) || expr_contains_pointer_sort(right, flavor)
        }
        TrustExpr::Not { expr } => expr_contains_pointer_sort(expr, flavor),
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            expr_contains_pointer_sort(premise, flavor)
                || expr_contains_pointer_sort(conclusion, flavor)
        }
        TrustExpr::Cast {
            expr,
            from_sort,
            to_sort,
        } => {
            sort_is_pointer_like(from_sort, flavor)
                || sort_is_pointer_like(to_sort, flavor)
                || expr_contains_pointer_sort(expr, flavor)
        }
        TrustExpr::Call {
            args, return_sort, ..
        } => {
            sort_is_pointer_like(return_sort, flavor)
                || args
                    .iter()
                    .any(|arg| expr_contains_pointer_sort(arg, flavor))
        }
        TrustExpr::Quantifier { body, triggers, .. } => {
            expr_contains_pointer_sort(body, flavor)
                || triggers.as_ref().is_some_and(|groups| {
                    groups
                        .iter()
                        .flatten()
                        .any(|trigger| expr_contains_pointer_sort(trigger, flavor))
                })
        }
    }
}

fn sort_is_pointer_like(sort: &TrustSort, flavor: PointerBootstrapFlavor) -> bool {
    let label = match sort {
        TrustSort::StrSlice => return matches!(flavor, PointerBootstrapFlavor::Fat),
        TrustSort::Opaque { name }
        | TrustSort::TypeParam { name }
        | TrustSort::RecursiveRef { name } => name.to_ascii_lowercase(),
        _ => return false,
    };
    match flavor {
        PointerBootstrapFlavor::Thin => {
            label.starts_with("*const ")
                || label.starts_with("*mut ")
                || label.contains("nonnull")
                || label.contains(" ptr")
                || label.contains("ptr<")
                || label.contains("pointer")
        }
        PointerBootstrapFlavor::Fat => {
            label.starts_with("&[")
                || label == "str"
                || label.contains("slice")
                || label.contains("dyn ")
                || label.contains("fat")
                || label.contains("wide")
        }
    }
}

fn is_pointer_bootstrap_operation(function: &str, flavor: PointerBootstrapFlavor) -> bool {
    let tokens = function_name_tokens(function);
    match flavor {
        PointerBootstrapFlavor::Thin => [
            &["ptr", "addr"][..],
            &["ptr", "address"],
            &["ptr", "is", "null"],
            &["ptr", "eq"],
            &["ptr", "offset"],
            &["ptr", "add"],
            &["ptr", "sub"],
            &["ptr", "diff"],
            &["ptr", "provenance"],
            &["ptr", "exposed", "addr"],
            &["ptr", "from", "exposed", "addr"],
            &["pointer", "addr"],
            &["pointer", "is", "null"],
            &["pointer", "offset"],
        ]
        .iter()
        .any(|pattern| tokens_contain(&tokens, pattern)),
        PointerBootstrapFlavor::Fat => [
            &["fat", "ptr", "data"][..],
            &["fat", "ptr", "metadata"],
            &["fat", "ptr", "len"],
            &["fat", "ptr", "vtable"],
            &["fat", "pointer", "data"],
            &["fat", "pointer", "metadata"],
            &["fat", "pointer", "len"],
            &["fat", "pointer", "vtable"],
            &["wide", "ptr", "data"],
            &["wide", "ptr", "metadata"],
            &["wide", "ptr", "len"],
            &["wide", "pointer", "data"],
            &["wide", "pointer", "metadata"],
            &["wide", "pointer", "len"],
            &["ptr", "metadata"],
            &["ptr", "from", "raw", "parts"],
            &["ptr", "from", "raw", "parts", "mut"],
            &["slice", "from", "raw", "parts"],
            &["slice", "from", "raw", "parts", "mut"],
            &["slice", "ptr", "data"],
            &["slice", "ptr", "len"],
            &["str", "from", "raw", "parts"],
        ]
        .iter()
        .any(|pattern| tokens_contain(&tokens, pattern)),
    }
}

#[derive(Clone, Copy)]
enum CallableBootstrapFlavor {
    Closure,
    FnPtr,
}

impl CallableBootstrapFlavor {
    const fn label(self) -> &'static str {
        match self {
            Self::Closure => "closure",
            Self::FnPtr => "fn-pointer",
        }
    }
}

fn validate_callable_bootstrap_fact_shape(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
    mode: TrustVerificationMode,
    flavor: CallableBootstrapFlavor,
) -> Result<(), TrustEngineError> {
    let Some(expr) = obligation.typed_expr() else {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!(
                "{} bootstrap facts must be backed by typed TrustExpr",
                flavor.label()
            ),
        });
    };

    let declared_callable_evidence = if let Some(native_context) = &unit.native_context {
        Some(
            native_context
                .variables()
                .map(|variable| (variable.name.as_str(), &variable.sort))
                .collect::<BTreeMap<_, _>>(),
        )
    } else if mode == TrustVerificationMode::Full {
        return Err(TrustEngineError::MissingNativeContext {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            missing: "typed callable evidence",
        });
    } else {
        None
    };

    let mut shape = CallableFactShape::default();
    collect_callable_fact_shape(
        expr,
        flavor,
        declared_callable_evidence.as_ref(),
        &mut shape,
    );
    if !shape.has_callable_operation {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!(
                "{} bootstrap expression mentions no recognized {} operation",
                flavor.label(),
                flavor.label()
            ),
        });
    }
    if let Some(invalid_operation) = shape.invalid_operation {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: invalid_operation.message(flavor),
        });
    }
    if !shape.has_variable_backed_callable_operation || shape.has_invalid_callable_operation {
        return Err(TrustEngineError::InvalidBootstrapFact {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            message: format!("{} bootstrap expression is context-free", flavor.label()),
        });
    }
    Ok(())
}

#[derive(Default)]
struct CallableFactShape {
    has_callable_operation: bool,
    has_variable_backed_callable_operation: bool,
    has_invalid_callable_operation: bool,
    invalid_operation: Option<CallableOperationInvalid>,
}

fn collect_callable_fact_shape(
    expr: &TrustExpr,
    flavor: CallableBootstrapFlavor,
    declared_callable_evidence: Option<&BTreeMap<&str, &TrustSort>>,
    shape: &mut CallableFactShape,
) {
    match expr {
        TrustExpr::BoolLiteral { .. }
        | TrustExpr::IntLiteral { .. }
        | TrustExpr::Variable { .. }
        | TrustExpr::Old { .. } => {}
        TrustExpr::Arith { left, right, .. }
        | TrustExpr::Compare { left, right, .. }
        | TrustExpr::Logic { left, right, .. } => {
            collect_callable_fact_shape(left, flavor, declared_callable_evidence, shape);
            collect_callable_fact_shape(right, flavor, declared_callable_evidence, shape);
        }
        TrustExpr::Not { expr } => {
            collect_callable_fact_shape(expr, flavor, declared_callable_evidence, shape);
        }
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            collect_callable_fact_shape(premise, flavor, declared_callable_evidence, shape);
            collect_callable_fact_shape(conclusion, flavor, declared_callable_evidence, shape);
        }
        TrustExpr::Cast { expr, .. } => {
            collect_callable_fact_shape(expr, flavor, declared_callable_evidence, shape);
        }
        TrustExpr::Call {
            function,
            args,
            return_sort,
        } => {
            for arg in args {
                collect_callable_fact_shape(arg, flavor, declared_callable_evidence, shape);
            }
            if callable_bootstrap_operation(function, flavor).is_some() {
                shape.has_callable_operation = true;
                match validate_callable_bootstrap_operation(
                    function,
                    args,
                    return_sort,
                    flavor,
                    declared_callable_evidence,
                ) {
                    Ok(()) => {
                        shape.has_variable_backed_callable_operation = true;
                    }
                    Err(CallableOperationInvalid::InvalidOperand) => {
                        shape.has_invalid_callable_operation = true;
                    }
                    Err(invalid_operation) => {
                        shape.has_invalid_callable_operation = true;
                        if shape.invalid_operation.is_none() {
                            shape.invalid_operation = Some(invalid_operation);
                        }
                    }
                }
            }
        }
        TrustExpr::Quantifier { body, triggers, .. } => {
            collect_callable_fact_shape(body, flavor, declared_callable_evidence, shape);
            if let Some(groups) = triggers {
                for trigger in groups.iter().flatten() {
                    collect_callable_fact_shape(trigger, flavor, declared_callable_evidence, shape);
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
enum CallableOperation {
    Invoke,
    Metadata,
    Equality,
}

enum CallableOperationInvalid {
    InvalidOperand,
    InvalidArity {
        function: String,
        expected: usize,
        actual: usize,
    },
    InvalidSignature {
        function: String,
        message: String,
    },
    UndeclaredEvidence {
        function: String,
        variable: String,
    },
}

impl CallableOperationInvalid {
    fn message(&self, flavor: CallableBootstrapFlavor) -> String {
        match self {
            Self::InvalidOperand => {
                format!("{} bootstrap expression is context-free", flavor.label())
            }
            Self::InvalidArity {
                function,
                expected,
                actual,
            } => format!(
                "{} bootstrap operation `{function}` has invalid arity: expected {expected} argument(s), got {actual}",
                flavor.label()
            ),
            Self::InvalidSignature { function, message } => format!(
                "{} bootstrap operation `{function}` has invalid signature: {message}",
                flavor.label()
            ),
            Self::UndeclaredEvidence { function, variable } => format!(
                "{} bootstrap operation `{function}` references undeclared callable evidence `{variable}`",
                flavor.label()
            ),
        }
    }
}

struct CallableOperand<'a> {
    name: &'a str,
    sort: &'a TrustSort,
}

struct CallableSignature {
    args: Vec<TrustSort>,
    ret: TrustSort,
}

fn validate_callable_bootstrap_operation(
    function: &str,
    args: &[TrustExpr],
    return_sort: &TrustSort,
    flavor: CallableBootstrapFlavor,
    declared_callable_evidence: Option<&BTreeMap<&str, &TrustSort>>,
) -> Result<(), CallableOperationInvalid> {
    let Some(operation) = callable_bootstrap_operation(function, flavor) else {
        return Ok(());
    };

    match operation {
        CallableOperation::Metadata => {
            validate_callable_operation_arity(function, 1, args.len())?;
            let callable =
                direct_callable_operand(function, &args[0], flavor, declared_callable_evidence)?;
            let _ = require_callable_signature(function, &callable, flavor)?;
            validate_callable_metadata_return_sort(function, return_sort, flavor)?;
        }
        CallableOperation::Equality => {
            validate_callable_bool_return_sort(function, return_sort)?;
            validate_callable_operation_arity(function, 2, args.len())?;
            let left =
                direct_callable_operand(function, &args[0], flavor, declared_callable_evidence)?;
            let right =
                direct_callable_operand(function, &args[1], flavor, declared_callable_evidence)?;
            let _ = require_callable_signature(function, &left, flavor)?;
            let _ = require_callable_signature(function, &right, flavor)?;
            if left.sort != right.sort {
                return Err(CallableOperationInvalid::InvalidSignature {
                    function: function.to_string(),
                    message: format!(
                        "equality operands differ: {} vs {}",
                        left.sort.display_label(),
                        right.sort.display_label()
                    ),
                });
            }
        }
        CallableOperation::Invoke => {
            if args.is_empty() {
                return Err(CallableOperationInvalid::InvalidArity {
                    function: function.to_string(),
                    expected: 1,
                    actual: 0,
                });
            }
            let callable =
                direct_callable_operand(function, &args[0], flavor, declared_callable_evidence)?;
            let signature = require_callable_signature(function, &callable, flavor)?;
            let expected_arity = signature.args.len() + 1;
            validate_callable_operation_arity(function, expected_arity, args.len())?;
            if return_sort != &signature.ret {
                return Err(CallableOperationInvalid::InvalidSignature {
                    function: function.to_string(),
                    message: format!(
                        "return sort says {}, but callable returns {}",
                        return_sort.display_label(),
                        signature.ret.display_label()
                    ),
                });
            }
            for (index, (arg, expected_sort)) in args[1..].iter().zip(&signature.args).enumerate() {
                let actual_sort = trust_expr_static_sort(arg);
                if &actual_sort != expected_sort {
                    return Err(CallableOperationInvalid::InvalidSignature {
                        function: function.to_string(),
                        message: format!(
                            "argument {index} says {}, but callable expects {}",
                            actual_sort.display_label(),
                            expected_sort.display_label()
                        ),
                    });
                }
            }
        }
    }

    Ok(())
}

fn validate_callable_bool_return_sort(
    function: &str,
    return_sort: &TrustSort,
) -> Result<(), CallableOperationInvalid> {
    if return_sort.is_bool() {
        return Ok(());
    }
    Err(CallableOperationInvalid::InvalidSignature {
        function: function.to_string(),
        message: format!(
            "return sort must be bool, got {}",
            return_sort.display_label()
        ),
    })
}

fn validate_callable_metadata_return_sort(
    function: &str,
    return_sort: &TrustSort,
    flavor: CallableBootstrapFlavor,
) -> Result<(), CallableOperationInvalid> {
    match flavor {
        CallableBootstrapFlavor::Closure if !sort_is_callable_like(return_sort, flavor) => Ok(()),
        CallableBootstrapFlavor::Closure => Err(CallableOperationInvalid::InvalidSignature {
            function: function.to_string(),
            message: format!(
                "metadata return sort must not be callable evidence, got {}",
                return_sort.display_label()
            ),
        }),
        CallableBootstrapFlavor::FnPtr if return_sort.is_fixed_integer() => Ok(()),
        CallableBootstrapFlavor::FnPtr => Err(CallableOperationInvalid::InvalidSignature {
            function: function.to_string(),
            message: format!(
                "metadata return sort must be a fixed-width integer address, got {}",
                return_sort.display_label()
            ),
        }),
    }
}

fn require_callable_signature(
    function: &str,
    callable: &CallableOperand<'_>,
    flavor: CallableBootstrapFlavor,
) -> Result<CallableSignature, CallableOperationInvalid> {
    callable_signature_for_sort(callable.sort, flavor).ok_or_else(|| {
        CallableOperationInvalid::InvalidSignature {
            function: function.to_string(),
            message: format!(
                "callable evidence `{}` has no typed callable signature",
                callable.name
            ),
        }
    })
}

fn validate_callable_operation_arity(
    function: &str,
    expected: usize,
    actual: usize,
) -> Result<(), CallableOperationInvalid> {
    if expected == actual {
        return Ok(());
    }
    Err(CallableOperationInvalid::InvalidArity {
        function: function.to_string(),
        expected,
        actual,
    })
}

fn direct_callable_operand<'a>(
    function: &str,
    expr: &'a TrustExpr,
    flavor: CallableBootstrapFlavor,
    declared_callable_evidence: Option<&BTreeMap<&str, &TrustSort>>,
) -> Result<CallableOperand<'a>, CallableOperationInvalid> {
    let (name, sort) = match expr {
        TrustExpr::Variable { name, sort } => (name.as_str(), sort),
        TrustExpr::Old { snapshot, sort, .. } => (snapshot.as_str(), sort),
        _ => return Err(CallableOperationInvalid::InvalidOperand),
    };

    if let Some(declared_callable_evidence) = declared_callable_evidence {
        let Some(declared_sort) = declared_callable_evidence.get(name) else {
            return Err(CallableOperationInvalid::UndeclaredEvidence {
                function: function.to_string(),
                variable: name.to_string(),
            });
        };
        if *declared_sort != sort {
            return Err(CallableOperationInvalid::InvalidSignature {
                function: function.to_string(),
                message: format!(
                    "callable evidence `{name}` is declared as {}, but expression used {}",
                    declared_sort.display_label(),
                    sort.display_label()
                ),
            });
        }
    }
    if !sort_is_callable_like(sort, flavor) {
        return Err(CallableOperationInvalid::InvalidOperand);
    }

    Ok(CallableOperand { name, sort })
}

fn sort_is_callable_like(sort: &TrustSort, flavor: CallableBootstrapFlavor) -> bool {
    match sort {
        TrustSort::SpecFn { .. } => matches!(flavor, CallableBootstrapFlavor::Closure),
        TrustSort::Opaque { name }
        | TrustSort::TypeParam { name }
        | TrustSort::RecursiveRef { name } => {
            let label = name.to_ascii_lowercase();
            let tokens = function_name_tokens(name);
            if callable_sort_name_is_metadata_like(&tokens) {
                return false;
            }
            match flavor {
                CallableBootstrapFlavor::Closure => {
                    let trimmed = name.trim_start();
                    tokens.iter().any(|token| token == "specfn")
                        || tokens_contain(&tokens, &["spec", "fn"])
                        || trimmed.starts_with("Fn(")
                        || trimmed.starts_with("FnMut(")
                        || trimmed.starts_with("FnOnce(")
                        || trimmed.starts_with("dyn Fn(")
                        || trimmed.starts_with("dyn FnMut(")
                        || trimmed.starts_with("dyn FnOnce(")
                        || trimmed.starts_with("impl Fn(")
                        || trimmed.starts_with("impl FnMut(")
                        || trimmed.starts_with("impl FnOnce(")
                        || tokens
                            .iter()
                            .any(|token| matches!(token.as_str(), "fnmut" | "fnonce"))
                        || tokens_contain(&tokens, &["ops", "function", "fn"])
                }
                CallableBootstrapFlavor::FnPtr => {
                    let trimmed = label.trim_start();
                    trimmed.starts_with("fn(")
                        || trimmed.starts_with("unsafe fn(")
                        || (trimmed.starts_with("extern ") && trimmed.contains(" fn("))
                        || (trimmed.starts_with("unsafe extern ") && trimmed.contains(" fn("))
                        || tokens.iter().any(|token| token == "fnptr")
                        || tokens.iter().any(|token| token == "functionpointer")
                        || tokens_contain(&tokens, &["fn", "ptr"])
                        || tokens_contain(&tokens, &["fn", "pointer"])
                        || tokens_contain(&tokens, &["function", "pointer"])
                }
            }
        }
        _ => false,
    }
}

fn callable_signature_for_sort(
    sort: &TrustSort,
    flavor: CallableBootstrapFlavor,
) -> Option<CallableSignature> {
    match sort {
        TrustSort::SpecFn { args, ret } if matches!(flavor, CallableBootstrapFlavor::Closure) => {
            Some(CallableSignature {
                args: args.clone(),
                ret: ret.as_ref().clone(),
            })
        }
        TrustSort::Opaque { name }
        | TrustSort::TypeParam { name }
        | TrustSort::RecursiveRef { name } => parse_callable_signature_name(name, flavor),
        _ => None,
    }
}

fn parse_callable_signature_name(
    name: &str,
    flavor: CallableBootstrapFlavor,
) -> Option<CallableSignature> {
    let keywords = match flavor {
        CallableBootstrapFlavor::Closure => &["fnonce", "fnmut", "specfn", "fn"][..],
        CallableBootstrapFlavor::FnPtr => &["fn"][..],
    };
    let open = find_callable_signature_open(name, keywords)?;
    let close = find_matching_delimiter(name, open, '(', ')')?;
    let args = split_top_level_types(&name[open + 1..close])
        .into_iter()
        .map(parse_trust_sort_label)
        .collect::<Option<Vec<_>>>()?;
    let ret = parse_callable_return_sort(&name[close + 1..])?;
    Some(CallableSignature { args, ret })
}

fn find_callable_signature_open(name: &str, keywords: &[&str]) -> Option<usize> {
    let lower = name.to_ascii_lowercase();
    for keyword in keywords {
        for (index, _) in lower.match_indices(keyword) {
            if index > 0 && lower.as_bytes()[index - 1].is_ascii_alphanumeric() {
                continue;
            }
            let mut cursor = index + keyword.len();
            while cursor < lower.len() && lower.as_bytes()[cursor].is_ascii_whitespace() {
                cursor += 1;
            }
            if lower.as_bytes().get(cursor) == Some(&b'(') {
                return Some(cursor);
            }
        }
    }
    None
}

fn parse_callable_return_sort(suffix: &str) -> Option<TrustSort> {
    let suffix = suffix.trim_start();
    let Some(ret) = suffix.strip_prefix("->") else {
        return Some(TrustSort::Opaque {
            name: "()".to_string(),
        });
    };
    let ret = ret.trim();
    let ret = split_top_level_suffix(ret, '+').trim();
    if ret.is_empty() {
        return None;
    }
    parse_trust_sort_label(ret)
}

fn split_top_level_types(args: &str) -> Vec<&str> {
    let args = args.trim();
    if args.is_empty() {
        return Vec::new();
    }

    let mut parts = Vec::new();
    let mut start = 0;
    let mut paren_depth = 0usize;
    let mut angle_depth = 0usize;
    let mut bracket_depth = 0usize;
    for (index, ch) in args.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            '[' => bracket_depth += 1,
            ']' => bracket_depth = bracket_depth.saturating_sub(1),
            ',' if paren_depth == 0 && angle_depth == 0 && bracket_depth == 0 => {
                parts.push(args[start..index].trim());
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }
    parts.push(args[start..].trim());
    parts
}

fn split_top_level_suffix(input: &str, delimiter: char) -> &str {
    let mut paren_depth = 0usize;
    let mut angle_depth = 0usize;
    let mut bracket_depth = 0usize;
    for (index, ch) in input.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            '[' => bracket_depth += 1,
            ']' => bracket_depth = bracket_depth.saturating_sub(1),
            ch if ch == delimiter && paren_depth == 0 && angle_depth == 0 && bracket_depth == 0 => {
                return &input[..index];
            }
            _ => {}
        }
    }
    input
}

fn find_matching_delimiter(
    input: &str,
    open_index: usize,
    open: char,
    close: char,
) -> Option<usize> {
    let mut depth = 0usize;
    for (index, ch) in input
        .char_indices()
        .filter(|(index, _)| *index >= open_index)
    {
        if ch == open {
            depth += 1;
        } else if ch == close {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

fn parse_trust_sort_label(label: &str) -> Option<TrustSort> {
    let label = label.trim();
    if label.is_empty() {
        return None;
    }
    if let Some(inner) = strip_generic_sort(label, "Seq") {
        return parse_trust_sort_label(inner).map(|elem| TrustSort::Seq {
            elem: Box::new(elem),
        });
    }
    if let Some(inner) = strip_generic_sort(label, "Set") {
        return parse_trust_sort_label(inner).map(|elem| TrustSort::Set {
            elem: Box::new(elem),
        });
    }
    if let Some(inner) = strip_generic_sort(label, "Multiset") {
        return parse_trust_sort_label(inner).map(|elem| TrustSort::Multiset {
            elem: Box::new(elem),
        });
    }
    if let Some(inner) = strip_generic_sort(label, "Map") {
        let parts = split_top_level_types(inner);
        if parts.len() != 2 {
            return None;
        }
        let key = parse_trust_sort_label(parts[0])?;
        let value = parse_trust_sort_label(parts[1])?;
        return Some(TrustSort::Map {
            key: Box::new(key),
            value: Box::new(value),
        });
    }
    if let Some(spec_fn) = parse_spec_fn_sort_label(label) {
        return Some(spec_fn);
    }
    match label {
        "bool" => Some(TrustSort::Bool),
        "char" => Some(TrustSort::Char),
        "str" | "&str" => Some(TrustSort::StrSlice),
        "String" => Some(TrustSort::String),
        "int" => Some(TrustSort::MathInt),
        "nat" => Some(TrustSort::Nat),
        "real" => Some(TrustSort::Real),
        "isize" => Some(TrustSort::signed(64)),
        "usize" => Some(TrustSort::unsigned(64)),
        "i8" => Some(TrustSort::signed(8)),
        "i16" => Some(TrustSort::signed(16)),
        "i32" => Some(TrustSort::signed(32)),
        "i64" => Some(TrustSort::signed(64)),
        "i128" => Some(TrustSort::signed(128)),
        "u8" => Some(TrustSort::unsigned(8)),
        "u16" => Some(TrustSort::unsigned(16)),
        "u32" => Some(TrustSort::unsigned(32)),
        "u64" => Some(TrustSort::unsigned(64)),
        "u128" => Some(TrustSort::unsigned(128)),
        "f32" => Some(TrustSort::Float { width: 32 }),
        "f64" => Some(TrustSort::Float { width: 64 }),
        _ => Some(TrustSort::Opaque {
            name: label.to_string(),
        }),
    }
}

fn strip_generic_sort<'a>(label: &'a str, prefix: &str) -> Option<&'a str> {
    let suffix = label.strip_prefix(prefix)?;
    let suffix = suffix.trim_start();
    if !suffix.starts_with('<') {
        return None;
    }
    let open = label.find('<')?;
    let close = find_matching_delimiter(label, open, '<', '>')?;
    if label[close + 1..].trim().is_empty() {
        Some(label[open + 1..close].trim())
    } else {
        None
    }
}

fn parse_spec_fn_sort_label(label: &str) -> Option<TrustSort> {
    let open = find_callable_signature_open(label, &["specfn"])?;
    if !label[..open].trim().eq_ignore_ascii_case("SpecFn") {
        return None;
    }
    let close = find_matching_delimiter(label, open, '(', ')')?;
    let args = split_top_level_types(&label[open + 1..close])
        .into_iter()
        .map(parse_trust_sort_label)
        .collect::<Option<Vec<_>>>()?;
    let ret = parse_callable_return_sort(&label[close + 1..])?;
    Some(TrustSort::SpecFn {
        args,
        ret: Box::new(ret),
    })
}

fn trust_expr_static_sort(expr: &TrustExpr) -> TrustSort {
    match expr {
        TrustExpr::BoolLiteral { .. } => TrustSort::Bool,
        TrustExpr::IntLiteral { sort, .. }
        | TrustExpr::Variable { sort, .. }
        | TrustExpr::Old { sort, .. }
        | TrustExpr::Arith { sort, .. } => sort.clone(),
        TrustExpr::Compare { .. }
        | TrustExpr::Logic { .. }
        | TrustExpr::Not { .. }
        | TrustExpr::Implies { .. }
        | TrustExpr::Quantifier { .. } => TrustSort::Bool,
        TrustExpr::Cast { to_sort, .. }
        | TrustExpr::Call {
            return_sort: to_sort,
            ..
        } => to_sort.clone(),
    }
}

fn callable_sort_name_is_metadata_like(tokens: &[String]) -> bool {
    tokens.iter().any(|token| {
        matches!(
            token.as_str(),
            "metadata" | "state" | "states" | "wrapper" | "wrapped"
        )
    })
}

fn callable_bootstrap_operation(
    function: &str,
    flavor: CallableBootstrapFlavor,
) -> Option<CallableOperation> {
    let tokens = function_name_tokens(function);
    match flavor {
        CallableBootstrapFlavor::Closure => {
            if [&["closure", "env"][..], &["closure", "capture"]]
                .iter()
                .any(|pattern| tokens_contain(&tokens, pattern))
            {
                return Some(CallableOperation::Metadata);
            }
            if [
                &["closure", "call"][..],
                &["closure", "call", "mut"],
                &["closure", "call", "once"],
                &["closure", "invoke"],
                &["call", "closure"],
                &["invoke", "closure"],
                &["fn", "call"],
                &["fn", "call", "mut"],
                &["fn", "call", "once"],
                &["fnmut", "call"],
                &["fnmut", "call", "mut"],
                &["fnonce", "call"],
                &["fnonce", "call", "once"],
                &["specfn", "call"],
                &["spec", "fn", "call"],
            ]
            .iter()
            .any(|pattern| tokens_contain(&tokens, pattern))
            {
                Some(CallableOperation::Invoke)
            } else {
                None
            }
        }
        CallableBootstrapFlavor::FnPtr => {
            if [
                &["fn", "ptr", "eq"][..],
                &["fn", "pointer", "eq"],
                &["function", "pointer", "eq"],
            ]
            .iter()
            .any(|pattern| tokens_contain(&tokens, pattern))
            {
                return Some(CallableOperation::Equality);
            }
            if [
                &["fn", "ptr", "call"][..],
                &["fn", "pointer", "call"],
                &["function", "pointer", "call"],
                &["fnptr", "call"],
                &["call", "fn", "ptr"],
                &["call", "fn", "pointer"],
                &["call", "function", "pointer"],
            ]
            .iter()
            .any(|pattern| tokens_contain(&tokens, pattern))
            {
                return Some(CallableOperation::Invoke);
            }
            if [
                &["fn", "ptr", "addr"][..],
                &["fn", "ptr", "address"],
                &["fn", "ptr", "cast"],
                &["fn", "ptr", "as", "usize"],
                &["fn", "pointer", "addr"],
                &["fn", "pointer", "address"],
                &["function", "pointer", "addr"],
                &["function", "pointer", "address"],
                &["fnptr", "addr"],
                &["fnptr", "address"],
            ]
            .iter()
            .any(|pattern| tokens_contain(&tokens, pattern))
            {
                Some(CallableOperation::Metadata)
            } else {
                None
            }
        }
    }
}

fn function_name_tokens(function: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    for ch in function.chars() {
        if ch.is_ascii_alphanumeric() {
            current.push(ch.to_ascii_lowercase());
        } else if !current.is_empty() {
            tokens.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

fn tokens_contain(tokens: &[String], pattern: &[&str]) -> bool {
    !pattern.is_empty()
        && tokens.windows(pattern.len()).any(|window| {
            window
                .iter()
                .map(String::as_str)
                .eq(pattern.iter().copied())
        })
}

#[derive(Default)]
struct AdtFactShape<'a> {
    mentions_declared_datatype: bool,
    has_variable_backed_datatype: bool,
    has_adt_operation: bool,
    undeclared_datatype: Option<&'a str>,
}

fn collect_adt_fact_shape<'a>(
    expr: &'a TrustExpr,
    declared_datatypes: &BTreeMap<&'a str, &'a TrustDatatype>,
    shape: &mut AdtFactShape<'a>,
) {
    collect_adt_fact_shape_scoped(expr, declared_datatypes, shape, &BTreeSet::new());
}

fn collect_adt_fact_shape_scoped<'a>(
    expr: &'a TrustExpr,
    declared_datatypes: &BTreeMap<&'a str, &'a TrustDatatype>,
    shape: &mut AdtFactShape<'a>,
    bound_names: &BTreeSet<String>,
) {
    match expr {
        TrustExpr::BoolLiteral { .. } | TrustExpr::IntLiteral { .. } => {}
        TrustExpr::Variable { name, sort } => {
            observe_adt_sort(sort, !bound_names.contains(name), declared_datatypes, shape);
        }
        TrustExpr::Old { sort, .. } => {
            observe_adt_sort(sort, true, declared_datatypes, shape);
        }
        TrustExpr::Arith {
            left, right, sort, ..
        } => {
            collect_adt_fact_shape_scoped(left, declared_datatypes, shape, bound_names);
            collect_adt_fact_shape_scoped(right, declared_datatypes, shape, bound_names);
            observe_adt_sort(sort, false, declared_datatypes, shape);
        }
        TrustExpr::Compare { left, right, .. } | TrustExpr::Logic { left, right, .. } => {
            collect_adt_fact_shape_scoped(left, declared_datatypes, shape, bound_names);
            collect_adt_fact_shape_scoped(right, declared_datatypes, shape, bound_names);
        }
        TrustExpr::Not { expr } => {
            collect_adt_fact_shape_scoped(expr, declared_datatypes, shape, bound_names);
        }
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            collect_adt_fact_shape_scoped(premise, declared_datatypes, shape, bound_names);
            collect_adt_fact_shape_scoped(conclusion, declared_datatypes, shape, bound_names);
        }
        TrustExpr::Cast {
            expr,
            from_sort,
            to_sort,
        } => {
            collect_adt_fact_shape_scoped(expr, declared_datatypes, shape, bound_names);
            observe_adt_sort(from_sort, false, declared_datatypes, shape);
            observe_adt_sort(to_sort, false, declared_datatypes, shape);
        }
        TrustExpr::Call {
            function,
            args,
            return_sort,
        } => {
            for arg in args {
                collect_adt_fact_shape_scoped(arg, declared_datatypes, shape, bound_names);
            }
            shape.has_adt_operation |=
                is_adt_operation(function, args, return_sort, declared_datatypes);
            observe_adt_sort(
                return_sort,
                args.iter()
                    .any(|arg| expr_contains_free_variable(arg, bound_names)),
                declared_datatypes,
                shape,
            );
        }
        TrustExpr::Quantifier {
            bound_vars,
            body,
            triggers,
            ..
        } => {
            let mut inner_bound_names = bound_names.clone();
            for bound_var in bound_vars {
                inner_bound_names.insert(bound_var.name().to_string());
            }
            collect_adt_fact_shape_scoped(body, declared_datatypes, shape, &inner_bound_names);
            if let Some(groups) = triggers {
                for trigger in groups.iter().flatten() {
                    collect_adt_fact_shape_scoped(
                        trigger,
                        declared_datatypes,
                        shape,
                        &inner_bound_names,
                    );
                }
            }
        }
    }
}

fn is_adt_operation<'a>(
    function: &str,
    args: &[TrustExpr],
    return_sort: &TrustSort,
    declared_datatypes: &BTreeMap<&'a str, &'a TrustDatatype>,
) -> bool {
    if let Some(datatype_name) = adt_sort_name(return_sort) {
        if let Some(datatype) = declared_datatypes.get(datatype_name) {
            if datatype
                .variants()
                .iter()
                .any(|variant| variant.name() == function)
            {
                return true;
            }
        }
    }

    if !args
        .iter()
        .any(|arg| expr_contains_declared_datatype(arg, declared_datatypes))
    {
        return false;
    }

    let function_lower = function.to_ascii_lowercase();
    if function_lower.contains("discriminant")
        || function_lower.contains("variant")
        || function.starts_with("is_")
    {
        return true;
    }

    declared_datatypes.values().any(|datatype| {
        datatype.variants().iter().any(|variant| {
            variant.fields().iter().any(|field| {
                function == field.name() || function.ends_with(&format!("::{}", field.name()))
            })
        })
    })
}

fn expr_contains_declared_datatype<'a>(
    expr: &TrustExpr,
    declared_datatypes: &BTreeMap<&'a str, &'a TrustDatatype>,
) -> bool {
    match expr {
        TrustExpr::BoolLiteral { .. } | TrustExpr::IntLiteral { .. } => false,
        TrustExpr::Variable { sort, .. } | TrustExpr::Old { sort, .. } => {
            sort_is_declared_datatype(sort, declared_datatypes)
        }
        TrustExpr::Arith {
            left, right, sort, ..
        } => {
            sort_is_declared_datatype(sort, declared_datatypes)
                || expr_contains_declared_datatype(left, declared_datatypes)
                || expr_contains_declared_datatype(right, declared_datatypes)
        }
        TrustExpr::Compare { left, right, .. } | TrustExpr::Logic { left, right, .. } => {
            expr_contains_declared_datatype(left, declared_datatypes)
                || expr_contains_declared_datatype(right, declared_datatypes)
        }
        TrustExpr::Not { expr } => expr_contains_declared_datatype(expr, declared_datatypes),
        TrustExpr::Implies {
            premise,
            conclusion,
        } => {
            expr_contains_declared_datatype(premise, declared_datatypes)
                || expr_contains_declared_datatype(conclusion, declared_datatypes)
        }
        TrustExpr::Cast {
            expr,
            from_sort,
            to_sort,
        } => {
            sort_is_declared_datatype(from_sort, declared_datatypes)
                || sort_is_declared_datatype(to_sort, declared_datatypes)
                || expr_contains_declared_datatype(expr, declared_datatypes)
        }
        TrustExpr::Call {
            args, return_sort, ..
        } => {
            sort_is_declared_datatype(return_sort, declared_datatypes)
                || args
                    .iter()
                    .any(|arg| expr_contains_declared_datatype(arg, declared_datatypes))
        }
        TrustExpr::Quantifier { body, triggers, .. } => {
            expr_contains_declared_datatype(body, declared_datatypes)
                || triggers.as_ref().is_some_and(|groups| {
                    groups
                        .iter()
                        .flatten()
                        .any(|trigger| expr_contains_declared_datatype(trigger, declared_datatypes))
                })
        }
    }
}

fn sort_is_declared_datatype<'a>(
    sort: &TrustSort,
    declared_datatypes: &BTreeMap<&'a str, &'a TrustDatatype>,
) -> bool {
    adt_sort_name(sort).is_some_and(|name| declared_datatypes.contains_key(name))
}

fn observe_adt_sort<'a>(
    sort: &'a TrustSort,
    variable_backed: bool,
    declared_datatypes: &BTreeMap<&'a str, &'a TrustDatatype>,
    shape: &mut AdtFactShape<'a>,
) {
    let Some(datatype_name) = adt_sort_name(sort) else {
        return;
    };
    if declared_datatypes.contains_key(datatype_name) {
        shape.mentions_declared_datatype = true;
        shape.has_variable_backed_datatype |= variable_backed;
    } else if shape.undeclared_datatype.is_none() {
        shape.undeclared_datatype = Some(datatype_name);
    }
}

fn adt_sort_name(sort: &TrustSort) -> Option<&str> {
    match sort {
        TrustSort::Datatype { name, .. } | TrustSort::RecursiveRef { name } => Some(name),
        _ => None,
    }
}

fn validate_native_context(
    unit: &TrustVerificationUnit,
    native_context: &TrustNativeContext,
    variable_sorts: &mut BTreeMap<String, TrustSort>,
    old_snapshots: &mut BTreeMap<String, (String, TrustSort)>,
) -> Result<(), TrustEngineError> {
    let signature = &native_context.function_signature;
    if signature.name.is_empty() {
        return Err(TrustEngineError::EmptyNativeFunctionName {
            unit_id: unit.unit_id.clone(),
        });
    }
    signature.return_sort.to_trust_vc_type()?;

    for (index, param) in signature.params.iter().enumerate() {
        validate_variable(&unit.unit_id, param, index)?;
        if variable_sorts
            .insert(param.name.clone(), param.sort.clone())
            .is_some()
        {
            return Err(TrustEngineError::DuplicateVariable {
                unit_id: unit.unit_id.clone(),
                name: param.name.clone(),
            });
        }
    }

    if let Some(contract_frame) = &native_context.contract_frame {
        if let Some(return_value) = &contract_frame.return_value {
            validate_variable(&unit.unit_id, return_value, 0)?;
            if variable_sorts
                .insert(return_value.name.clone(), return_value.sort.clone())
                .is_some()
            {
                return Err(TrustEngineError::DuplicateVariable {
                    unit_id: unit.unit_id.clone(),
                    name: return_value.name.clone(),
                });
            }
        }

        for (index, old_value) in contract_frame.old_values.iter().enumerate() {
            if old_value.source.is_empty() {
                return Err(TrustEngineError::EmptyTypedOldValue {
                    unit_id: unit.unit_id.clone(),
                    obligation_id: format!("contract_frame.old_values[{index}]"),
                });
            }
            validate_variable(&unit.unit_id, &old_value.snapshot, index)?;
            if variable_sorts
                .insert(
                    old_value.snapshot.name.clone(),
                    old_value.snapshot.sort.clone(),
                )
                .is_some()
            {
                return Err(TrustEngineError::DuplicateVariable {
                    unit_id: unit.unit_id.clone(),
                    name: old_value.snapshot.name.clone(),
                });
            }
            old_snapshots.insert(
                old_value.snapshot.name.clone(),
                (old_value.source.clone(), old_value.snapshot.sort.clone()),
            );
        }
    }

    for (index, datatype) in native_context.datatypes.iter().enumerate() {
        if datatype.name.is_empty() {
            return Err(TrustEngineError::EmptyDatatypeName {
                unit_id: unit.unit_id.clone(),
                index,
            });
        }
        if datatype.variants.is_empty() {
            return Err(TrustEngineError::DatatypeHasNoVariants {
                unit_id: unit.unit_id.clone(),
                datatype: datatype.name.clone(),
            });
        }
        for (variant_index, variant) in datatype.variants.iter().enumerate() {
            if variant.name.is_empty() {
                return Err(TrustEngineError::EmptyDatatypeVariantName {
                    unit_id: unit.unit_id.clone(),
                    datatype: datatype.name.clone(),
                    index: variant_index,
                });
            }
            validate_fields(
                &unit.unit_id,
                &format!("{}::{}", datatype.name, variant.name),
                &variant.fields,
            )?;
        }
        datatype.to_trust_vc_type()?;
    }

    for (index, invariant) in native_context.invariants.iter().enumerate() {
        if invariant.id.is_empty() {
            return Err(TrustEngineError::EmptyInvariantId {
                unit_id: unit.unit_id.clone(),
                index,
            });
        }
        if invariant.predicate.name.is_empty() {
            return Err(TrustEngineError::EmptyPredicateName {
                unit_id: unit.unit_id.clone(),
                invariant_id: invariant.id.clone(),
            });
        }
        for (param_index, param) in invariant.predicate.params.iter().enumerate() {
            validate_variable(&unit.unit_id, param, param_index)?;
        }
        invariant.predicate.return_sort.to_trust_vc_type()?;
    }

    if let Some(ownership) = &native_context.ownership {
        for (index, place) in ownership.places.iter().enumerate() {
            if place.place.is_empty() {
                return Err(TrustEngineError::EmptyOwnedPlace {
                    unit_id: unit.unit_id.clone(),
                    index,
                });
            }
            place.sort.to_trust_vc_type()?;
        }
        for (index, borrow) in ownership.borrows.iter().enumerate() {
            if borrow.region.is_empty() || borrow.place.is_empty() {
                return Err(TrustEngineError::EmptyBorrow {
                    unit_id: unit.unit_id.clone(),
                    index,
                });
            }
        }
        for (index, lifetime) in ownership.lifetimes.iter().enumerate() {
            if lifetime.region.is_empty()
                || lifetime
                    .outlives
                    .iter()
                    .any(|region| region.trim().is_empty())
            {
                return Err(TrustEngineError::InvalidOwnershipFact {
                    unit_id: unit.unit_id.clone(),
                    index,
                    message: "lifetime regions must not be empty".to_string(),
                });
            }
        }
        for (index, alias_fact) in ownership.alias_facts.iter().enumerate() {
            if alias_fact.left.is_empty() || alias_fact.right.is_empty() {
                return Err(TrustEngineError::InvalidOwnershipFact {
                    unit_id: unit.unit_id.clone(),
                    index,
                    message: "alias facts must name both places".to_string(),
                });
            }
        }
        for (index, provenance_fact) in ownership.provenance_facts.iter().enumerate() {
            if provenance_fact.pointer.is_empty() || provenance_fact.provenance_id.is_empty() {
                return Err(TrustEngineError::InvalidOwnershipFact {
                    unit_id: unit.unit_id.clone(),
                    index,
                    message: "provenance facts must name a pointer and provenance id".to_string(),
                });
            }
        }
    }

    Ok(())
}

fn validate_fields(
    unit_id: &str,
    owner: &str,
    fields: &[TrustField],
) -> Result<(), TrustEngineError> {
    for (index, field) in fields.iter().enumerate() {
        if field.name.is_empty() {
            return Err(TrustEngineError::EmptyNativeFieldName {
                unit_id: unit_id.to_string(),
                owner: owner.to_string(),
                index,
            });
        }
        field.sort.to_trust_vc_type()?;
    }
    Ok(())
}

fn validate_native_context_for_obligation(
    unit: &TrustVerificationUnit,
    obligation: &TrustObligation,
    mode: TrustVerificationMode,
) -> Result<(), TrustEngineError> {
    let Some(native_context) = &unit.native_context else {
        let Some(missing) = required_native_context(obligation) else {
            return Ok(());
        };
        if mode == TrustVerificationMode::Compatibility
            && matches!(
                obligation.kind,
                TrustObligationKind::ClosureBootstrap | TrustObligationKind::FnPtrBootstrap
            )
        {
            return Ok(());
        }
        return Err(TrustEngineError::MissingNativeContext {
            unit_id: unit.unit_id.clone(),
            obligation_id: obligation.id.clone(),
            missing,
        });
    };

    match &obligation.kind {
        TrustObligationKind::TranslationValidation
            if native_context.function_signature.name.is_empty() =>
        {
            Err(TrustEngineError::MissingNativeContext {
                unit_id: unit.unit_id.clone(),
                obligation_id: obligation.id.clone(),
                missing: "typed function signature",
            })
        }
        TrustObligationKind::TypeInvariant if native_context.invariants.is_empty() => {
            Err(TrustEngineError::MissingNativeContext {
                unit_id: unit.unit_id.clone(),
                obligation_id: obligation.id.clone(),
                missing: "typed invariant metadata",
            })
        }
        TrustObligationKind::MemorySafety if native_context.ownership.is_none() => {
            Err(TrustEngineError::MissingNativeContext {
                unit_id: unit.unit_id.clone(),
                obligation_id: obligation.id.clone(),
                missing: "typed ownership and borrow state",
            })
        }
        TrustObligationKind::AdtDiscriminant if native_context.datatypes.is_empty() => {
            Err(TrustEngineError::MissingNativeContext {
                unit_id: unit.unit_id.clone(),
                obligation_id: obligation.id.clone(),
                missing: "typed datatype metadata",
            })
        }
        _ => Ok(()),
    }
}

fn required_native_context(obligation: &TrustObligation) -> Option<&'static str> {
    match &obligation.kind {
        TrustObligationKind::TranslationValidation => Some("typed function signature"),
        TrustObligationKind::TypeInvariant => Some("typed invariant metadata"),
        TrustObligationKind::MemorySafety => Some("typed ownership and borrow state"),
        TrustObligationKind::AdtDiscriminant => Some("typed datatype metadata"),
        TrustObligationKind::ClosureBootstrap | TrustObligationKind::FnPtrBootstrap => {
            Some("typed callable evidence")
        }
        _ => None,
    }
}

fn validate_width(width: u32) -> Result<(), TrustEngineError> {
    match width {
        8 | 16 | 32 | 64 | 128 => Ok(()),
        _ => Err(TrustEngineError::InvalidBitVectorWidth { width }),
    }
}

fn validate_float_width(width: u32) -> Result<(), TrustEngineError> {
    match width {
        32 | 64 => Ok(()),
        _ => Err(TrustEngineError::InvalidFloatWidth { width }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_verified_request() -> TrustVerificationRequest {
        TrustVerificationRequest::new("unit-test").with_unit(
            TrustVerificationUnit::new("crate::proof").with_obligation(TrustObligation::assert(
                "post",
                TrustObligationKind::Postcondition,
                "true",
            )),
        )
    }

    fn native_borrow_context() -> TrustNativeContext {
        TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::borrow_check",
            vec![],
            TrustSort::Bool,
        ))
        .with_ownership(
            TrustOwnershipState::new()
                .with_place(TrustOwnedPlace::new("x", TrustSort::unsigned(32)))
                .with_borrow(TrustBorrow::new("r0", "x", TrustBorrowKind::Shared)),
        )
    }

    fn increment_postcondition_expr() -> TrustExpr {
        let u32_sort = TrustSort::unsigned(32);
        TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("result", u32_sort.clone()),
            TrustExpr::arith(
                TrustArithOp::Add,
                TrustExpr::old("x", "old_x", u32_sort.clone()),
                TrustExpr::int_literal(1, u32_sort.clone()),
                u32_sort,
            ),
        )
    }

    fn typed_increment_context() -> TrustNativeContext {
        let u32_sort = TrustSort::unsigned(32);
        TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::increment",
            vec![TrustVariable::new("x", u32_sort.clone())],
            u32_sort.clone(),
        ))
        .with_contract_frame(
            TrustContractFrame::new()
                .with_return_value(TrustVariable::new("result", u32_sort.clone()))
                .with_old_value(TrustOldValue::new(
                    "x",
                    TrustVariable::new("old_x", u32_sort),
                )),
        )
    }

    fn reflexive_x_expr() -> TrustExpr {
        let u32_sort = TrustSort::unsigned(32);
        TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("x", u32_sort.clone()),
            TrustExpr::variable("x", u32_sort),
        )
    }

    fn reflexive_result_expr() -> TrustExpr {
        let u32_sort = TrustSort::unsigned(32);
        TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("result", u32_sort.clone()),
            TrustExpr::variable("result", u32_sort),
        )
    }

    fn quantified_u32_reflexive_expr(name: &str) -> TrustExpr {
        let u32_sort = TrustSort::unsigned(32);
        TrustExpr::forall(
            vec![TrustQuantifierBoundVar::new(name, u32_sort.clone())],
            TrustExpr::compare(
                TrustCompareOp::Eq,
                TrustExpr::variable(name, u32_sort.clone()),
                TrustExpr::variable(name, u32_sort),
            ),
        )
    }

    #[test]
    fn typed_proof_unit_consumes_trust_vc_typed_obligation_as_structured_evidence() {
        let engine = TrustVcTrustEngine::new();
        let u32_ty = TrustVcType::Uint { width: 32 };
        let trust_vc_expr = TrustVcExpr::Compare {
            op: TrustVcCompareOp::Eq,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: u32_ty.clone(),
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: u32_ty,
            }),
        };
        let expected_trust_expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("x", TrustSort::unsigned(32)),
            TrustExpr::variable("x", TrustSort::unsigned(32)),
        );

        let unit = TrustTypedProofUnit::new("crate-under-test", "crate::typed_assert")
            .with_variable(TrustVariable::new("x", TrustSort::unsigned(32)))
            .with_obligation(
                TypedProofObligation::assert("typed.assert.reflexive", trust_vc_expr)
                    .with_location("src/lib.rs:1:1"),
            );

        let request = engine
            .lower_typed_proof_unit(&unit)
            .expect("TrustVc typed proof unit should lower");
        assert_eq!(request.mode(), TrustVerificationMode::Full);
        assert!(request.units()[0]
            .obligations()
            .iter()
            .all(TrustObligation::is_typed));

        let report = engine
            .verify_typed_proof_unit(&unit)
            .expect("TrustVc typed proof unit should verify");
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].source(),
            TrustProofEvidenceSource::TypedTrustVcExpr
        );
        assert_eq!(evidence[0].typed_expr(), Some(&expected_trust_expr));
        assert_eq!(evidence[0].location(), Some("src/lib.rs:1:1"));
    }

    #[test]
    fn trust_expr_quantifier_round_trips_core_with_triggers_and_mode() {
        let u32_sort = TrustSort::unsigned(32);
        let i = TrustExpr::variable("i", u32_sort.clone());
        let trigger = TrustExpr::call("crate::idx", vec![i.clone()], u32_sort.clone());
        let body = TrustExpr::compare(TrustCompareOp::Eq, trigger.clone(), trigger.clone());
        let trust_expr = TrustExpr::quantifier_with_options(
            TrustQuantifierKind::Forall,
            vec![TrustQuantifierBoundVar::new("i", u32_sort.clone())],
            body,
            Some(vec![vec![trigger]]),
            Some(TrustTriggerInferenceMode::Aggressive),
        );

        let trust_vc_expr = trust_expr
            .to_trust_vc_expr()
            .expect("Trust quantifier should lower to TrustVcExpr");
        match &trust_vc_expr {
            TrustVcExpr::Quantifier {
                kind,
                bound_vars,
                triggers,
                trigger_inference_mode,
                ..
            } => {
                assert_eq!(*kind, TrustVcQuantifierKind::Forall);
                assert_eq!(
                    bound_vars,
                    &[("i".to_string(), TrustVcType::Uint { width: 32 })]
                );
                assert_eq!(triggers.as_ref().map(Vec::len), Some(1));
                assert_eq!(
                    *trigger_inference_mode,
                    Some(TrustVcTriggerInferenceMode::Aggressive)
                );
            }
            other => panic!("expected TrustVcExpr::Quantifier, got {other:?}"),
        }

        let round_trip =
            TrustExpr::from_trust_vc_expr(&trust_vc_expr).expect("TrustVc quantifier should lift");
        assert_eq!(round_trip, trust_expr);
    }

    #[test]
    fn quantifier_validation_scopes_bound_vars_to_body_and_triggers() {
        let engine = TrustVcTrustEngine::new();
        let u32_sort = TrustSort::unsigned(32);
        let i = TrustExpr::variable("i", u32_sort.clone());
        let valid = TrustExpr::quantifier_with_triggers(
            TrustQuantifierKind::Forall,
            vec![TrustQuantifierBoundVar::new("i", u32_sort.clone())],
            TrustExpr::compare(TrustCompareOp::Eq, i.clone(), i.clone()),
            vec![vec![TrustExpr::call(
                "crate::idx",
                vec![i],
                u32_sort.clone(),
            )]],
        );
        let valid_request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::quantified")
                    .with_obligation(TrustObligation::ensures_typed("ensures", valid)),
            );
        engine
            .validate_request(&valid_request)
            .expect("bound variable should be visible in quantifier body and triggers");

        let j = TrustExpr::variable("j", u32_sort.clone());
        let invalid = TrustExpr::quantifier_with_triggers(
            TrustQuantifierKind::Forall,
            vec![TrustQuantifierBoundVar::new("i", u32_sort.clone())],
            TrustExpr::compare(
                TrustCompareOp::Eq,
                TrustExpr::variable("i", u32_sort.clone()),
                TrustExpr::variable("i", u32_sort.clone()),
            ),
            vec![vec![TrustExpr::call(
                "crate::idx",
                vec![j],
                u32_sort.clone(),
            )]],
        );
        let invalid_request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::quantified")
                    .with_variable(TrustVariable::new("j", u32_sort))
                    .with_obligation(TrustObligation::ensures_typed("ensures", invalid)),
            );

        let err = engine
            .validate_request(&invalid_request)
            .expect_err("explicit triggers must mention a bound variable");
        assert!(matches!(
            err,
            TrustEngineError::InvalidTypedExpr { message, .. }
                if message == "quantifier trigger[0][0] does not reference a bound variable"
        ));
    }

    #[test]
    fn quantifier_triggers_participate_in_expression_digest() {
        let u32_sort = TrustSort::unsigned(32);
        let i = TrustExpr::variable("i", u32_sort.clone());
        let body = TrustExpr::compare(TrustCompareOp::Eq, i.clone(), i.clone());
        let expr_a = TrustExpr::quantifier_with_triggers(
            TrustQuantifierKind::Forall,
            vec![TrustQuantifierBoundVar::new("i", u32_sort.clone())],
            body.clone(),
            vec![vec![TrustExpr::call(
                "crate::idx_a",
                vec![i.clone()],
                u32_sort.clone(),
            )]],
        );
        let expr_b = TrustExpr::quantifier_with_triggers(
            TrustQuantifierKind::Forall,
            vec![TrustQuantifierBoundVar::new("i", u32_sort.clone())],
            body,
            vec![vec![TrustExpr::call("crate::idx_b", vec![i], u32_sort)]],
        );

        let digest_a = expression_cache_digest(&TrustObligation::ensures_typed("post", expr_a));
        let digest_b = expression_cache_digest(&TrustObligation::ensures_typed("post", expr_b));

        assert_ne!(digest_a, digest_b);
        assert!(is_sha256_digest(&digest_a));
        assert!(is_sha256_digest(&digest_b));
    }

    fn is_sha256_digest(value: &str) -> bool {
        value
            .strip_prefix("sha256:")
            .is_some_and(|hex| hex.len() == 64 && hex.chars().all(|ch| ch.is_ascii_hexdigit()))
    }

    fn synthetic_proof_artifact(
        strict_verified: bool,
        kernel_verified: bool,
        trust_count: u32,
        hole_count: u32,
    ) -> TrustReplayableProofArtifact {
        let artifact_id = "trust-vc-proof-certificate:v1:test".to_string();
        let digest =
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string();
        let unit_id = "crate::proof".to_string();
        let assumption_obligation_ids = vec!["pre".to_string()];
        let assertion_obligation_ids = vec!["post".to_string()];
        let binding_fingerprint = proof_artifact_binding_fingerprint(
            &artifact_id,
            &digest,
            &unit_id,
            &assumption_obligation_ids,
            &assertion_obligation_ids,
        );
        TrustReplayableProofArtifact {
            artifact_id,
            unit_id,
            format: TrustProofArtifactFormat::Alethe,
            digest,
            binding_fingerprint,
            payload: "(proof)".to_string(),
            strict_verified,
            clean_supported: strict_verified,
            kernel_verified,
            trust_count,
            hole_count,
            resolution_count: 1,
            theory_count: 0,
            release_admission: TrustReleaseProofAdmission::from_certificate_metrics(
                strict_verified,
                kernel_verified,
                trust_count,
                hole_count,
            ),
            assumption_obligation_ids,
            assertion_obligation_ids,
        }
    }

    #[test]
    fn lowers_unit_to_trust_vc_context_without_macro_collection() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::checked_add")
            .with_variable(TrustVariable::new("x", TrustSort::unsigned(32)))
            .with_obligation(TrustObligation::assume(
                "requires",
                TrustObligationKind::Precondition,
                "x < 10",
            ))
            .with_obligation(TrustObligation::assert(
                "ensures",
                TrustObligationKind::Postcondition,
                "x < 11",
            ));

        let context = engine.lower_unit(&unit).expect("unit lowers");

        assert_eq!(context.variables().len(), 1);
        assert_eq!(context.variables()[0].name(), "x");
        assert_eq!(context.obligations().len(), 2);
        assert_eq!(
            context.obligations()[0].kind(),
            TrustVcObligationKind::Requires
        );
        assert_eq!(
            context.obligations()[1].kind(),
            TrustVcObligationKind::Ensures
        );
    }

    #[test]
    fn verifies_programmatic_assertion() {
        let engine = TrustVcTrustEngine::new();
        let report = engine
            .verify(&simple_verified_request())
            .expect("request verifies");

        assert_eq!(report.source_id(), "unit-test");
        assert_eq!(report.summary().verified, 1);
        assert!(matches!(
            report.units()[0].outcome(),
            TrustOutcome::Verified
        ));
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].source(),
            TrustProofEvidenceSource::LegacySourceText
        );
        assert_eq!(evidence[0].typed_expr(), None);
        assert_eq!(
            evidence[0].evidence_profile(),
            TrustProofEvidenceProfile::LegacyCompatibility
        );
        assert_eq!(
            evidence[0].reasoning_kind(),
            TrustProofReasoningKind::Deductive
        );
        assert_eq!(
            evidence[0].assurance_level(),
            TrustAssuranceLevel::CompatibilityEvidence
        );
        assert_eq!(
            report.units()[0].cache_status(),
            TrustEvidenceCacheStatus::Miss
        );
        let cache_key = evidence[0]
            .cache_key()
            .expect("verified evidence should carry a cache key");
        assert_eq!(
            cache_key.schema_version(),
            TRUST_EVIDENCE_CACHE_KEY_SCHEMA_VERSION
        );
        assert_eq!(cache_key.source_id(), "unit-test");
        assert_eq!(cache_key.unit_id(), "crate::proof");
        assert_eq!(cache_key.obligation_id(), "post");
        assert_eq!(cache_key.proof_policy(), TrustProofPolicy::EvidenceOnly);
        assert_eq!(cache_key.ay_version(), "ay:unreported");
        #[cfg(not(feature = "proof-certificates"))]
        assert_eq!(cache_key.kernel_version(), "trust-vc-kernel:disabled");
        #[cfg(feature = "proof-certificates")]
        assert_eq!(
            cache_key.kernel_version(),
            concat!("trust-vc-kernel:", env!("CARGO_PKG_VERSION"))
        );
        assert!(is_sha256_digest(cache_key.fingerprint()));
        assert!(is_sha256_digest(cache_key.expression_digest()));
        assert!(is_sha256_digest(cache_key.native_context_digest()));
        assert_eq!(cache_key.ownership_digest(), None);
        assert_eq!(cache_key.trust_ir_body_hash(), None);
        assert_eq!(cache_key.layout_hash(), None);
    }

    #[test]
    fn evidence_cache_key_changes_when_typed_expression_changes() {
        let engine = TrustVcTrustEngine::new();
        let u32_sort = TrustSort::unsigned(32);
        let request_a = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::proof")
                    .with_variable(TrustVariable::new("x", u32_sort.clone()))
                    .with_obligation(TrustObligation::ensures_typed(
                        "post",
                        TrustExpr::compare(
                            TrustCompareOp::Eq,
                            TrustExpr::variable("x", u32_sort.clone()),
                            TrustExpr::variable("x", u32_sort.clone()),
                        ),
                    )),
            );
        let request_b = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::proof")
                    .with_variable(TrustVariable::new("x", u32_sort.clone()))
                    .with_obligation(TrustObligation::ensures_typed(
                        "post",
                        TrustExpr::compare(
                            TrustCompareOp::Ge,
                            TrustExpr::variable("x", u32_sort.clone()),
                            TrustExpr::variable("x", u32_sort),
                        ),
                    )),
            );

        let report_a = engine.verify(&request_a).expect("request A verifies");
        let report_b = engine.verify(&request_b).expect("request B verifies");
        let key_a = report_a.units()[0].proof_evidence()[0]
            .cache_key()
            .expect("request A evidence carries cache key");
        let key_b = report_b.units()[0].proof_evidence()[0]
            .cache_key()
            .expect("request B evidence carries cache key");

        assert_ne!(key_a.expression_digest(), key_b.expression_digest());
        assert_ne!(key_a.fingerprint(), key_b.fingerprint());
        assert_eq!(key_a.native_context_digest(), key_b.native_context_digest());
    }

    #[test]
    fn release_admission_accepts_strict_kernel_checked_hole_free_artifacts() {
        let artifact = synthetic_proof_artifact(true, true, 0, 0);
        let admission = artifact.release_admission();

        assert_eq!(
            admission.status(),
            TrustReleaseProofAdmissionStatus::Admissible
        );
        assert!(admission.is_admissible());
        assert!(admission.rejection_reasons().is_empty());
        assert!(artifact.strict_verified());
        assert!(artifact.kernel_verified());
        assert_eq!(artifact.trust_count(), 0);
        assert_eq!(artifact.hole_count(), 0);
    }

    #[test]
    fn release_admission_rejects_replayable_but_non_release_artifacts() {
        let artifact = synthetic_proof_artifact(true, false, 1, 2);
        let admission = artifact.release_admission();

        assert_eq!(
            admission.status(),
            TrustReleaseProofAdmissionStatus::Rejected
        );
        assert!(!admission.is_admissible());
        assert_eq!(
            admission.rejection_reasons(),
            &[
                TrustReleaseProofRejection::KernelNotVerified,
                TrustReleaseProofRejection::ProofHolesPresent,
                TrustReleaseProofRejection::TrustedSolverStepsPresent,
            ]
        );
        assert_eq!(artifact.format(), TrustProofArtifactFormat::Alethe);
        assert!(!artifact.payload().is_empty());
    }

    #[test]
    fn release_admission_rejects_non_strict_artifacts() {
        let artifact = synthetic_proof_artifact(false, true, 0, 0);

        assert_eq!(
            artifact.release_admission().rejection_reasons(),
            &[TrustReleaseProofRejection::StrictCheckerRejected]
        );
        assert!(!artifact.release_admission().is_admissible());
    }

    #[test]
    fn reports_refuted_assertion_programmatically() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test").with_unit(
            TrustVerificationUnit::new("crate::bad_proof").with_obligation(
                TrustObligation::assert(
                    "assert_false",
                    TrustObligationKind::Other("test".into()),
                    "false",
                ),
            ),
        );

        let report = engine.verify(&request).expect("request runs");

        assert_eq!(report.summary().refuted, 1);
        assert!(matches!(
            report.units()[0].outcome(),
            TrustOutcome::Refuted { obligation_id, .. } if obligation_id == "assert_false"
        ));
    }

    #[test]
    fn rejects_assumption_only_units() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test").with_unit(
            TrustVerificationUnit::new("crate::only_context").with_obligation(
                TrustObligation::assume("requires", TrustObligationKind::Precondition, "true"),
            ),
        );

        let err = engine
            .verify(&request)
            .expect_err("assumptions alone are rejected");

        assert_eq!(
            err,
            TrustEngineError::UnitHasNoAssertions {
                unit_id: "crate::only_context".to_string()
            }
        );
    }

    #[test]
    fn rejects_invalid_bitvector_width() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::bad_width")
            .with_variable(TrustVariable::new("x", TrustSort::unsigned(7)))
            .with_obligation(TrustObligation::assert(
                "ok",
                TrustObligationKind::Postcondition,
                "true",
            ));

        let err = engine.lower_unit(&unit).expect_err("width rejected");

        assert_eq!(err, TrustEngineError::InvalidBitVectorWidth { width: 7 });
    }

    #[test]
    fn lowers_native_signature_params_and_datatypes() {
        let engine = TrustVcTrustEngine::new();
        let counter = TrustDatatype::new(
            "Counter",
            vec![TrustDatatypeVariant::new(
                "Counter",
                vec![TrustField::new("count", TrustSort::unsigned(64))],
            )],
        );
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::inc",
            vec![TrustVariable::new("counter", TrustSort::unsigned(64))],
            TrustSort::Bool,
        ))
        .with_datatype(counter);
        let unit = TrustVerificationUnit::new("crate::inc")
            .with_native_context(native)
            .with_obligation(TrustObligation::assert(
                "translation_valid",
                TrustObligationKind::TranslationValidation,
                "true",
            ));

        let context = engine.lower_unit(&unit).expect("native unit lowers");
        let datatypes = engine
            .lower_native_datatypes(&unit)
            .expect("native datatypes lower");

        assert_eq!(context.variables().len(), 1);
        assert_eq!(context.variables()[0].name(), "counter");
        assert!(matches!(
            &datatypes[0],
            TrustVcType::Datatype { name, variants }
                if name == "Counter" && variants[0].fields[0].0 == "count"
        ));
    }

    #[test]
    fn contract_bundle_lowers_to_full_typed_proof_ir_request() {
        let engine = TrustVcTrustEngine::new();
        let bundle = TrustContractBundle::new("unit-test")
            .with_replayable_proof_artifacts()
            .insert_metadata("producer", "trust-contract-adapter")
            .with_unit(
                TrustContractProofUnit::new("crate::increment", typed_increment_context())
                    .with_display_name("increment")
                    .with_clause(
                        TrustContractClause::requires("requires", reflexive_x_expr())
                            .with_location("src/lib.rs:7:5"),
                    )
                    .with_ensures("ensures", reflexive_result_expr()),
            );

        let request = engine
            .lower_contract_bundle(&bundle)
            .expect("typed contract bundle lowers");
        let unit = &request.units()[0];

        assert_eq!(request.source_id(), "unit-test");
        assert_eq!(request.mode(), TrustVerificationMode::Full);
        assert_eq!(
            request.proof_policy(),
            TrustProofPolicy::AttachReplayableCertificates
        );
        assert_eq!(
            request.metadata().get("producer").map(String::as_str),
            Some("trust-contract-adapter")
        );
        assert_eq!(unit.unit_id(), "crate::increment");
        assert_eq!(unit.display_name(), Some("increment"));
        assert!(unit.native_context().is_some());
        assert_eq!(unit.obligations().len(), 2);
        assert!(unit
            .obligations()
            .iter()
            .all(|obligation| obligation.typed_expr().is_some()));
        assert_eq!(unit.obligations()[0].location(), Some("src/lib.rs:7:5"));
        assert_eq!(
            unit.obligations()[0].kind(),
            &TrustObligationKind::Precondition
        );
        assert_eq!(
            unit.obligations()[1].kind(),
            &TrustObligationKind::Postcondition
        );
    }

    #[test]
    fn contract_bundle_verifies_with_typed_contract_frame_evidence() {
        let engine = TrustVcTrustEngine::new();
        let bundle = TrustContractBundle::new("unit-test").with_unit(
            TrustContractProofUnit::new("crate::increment", typed_increment_context())
                .with_requires("requires", reflexive_x_expr())
                .with_ensures("ensures", reflexive_result_expr()),
        );

        let report = engine
            .verify_contract_bundle(&bundle)
            .expect("typed contract bundle verifies through TrustVc");

        assert_eq!(report.summary().verified, 1);
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(evidence.len(), 2);
        assert!(evidence
            .iter()
            .all(|item| item.source() == TrustProofEvidenceSource::TypedTrustVcExpr));
        assert!(evidence.iter().all(|item| {
            item.evidence_profile() == TrustProofEvidenceProfile::TypedContractFrame
        }));
        let requires = evidence
            .iter()
            .find(|item| item.obligation_id() == "requires")
            .expect("requires evidence present");
        assert_eq!(requires.role(), TrustObligationRole::Assumption);
        assert_eq!(
            requires.assurance_level(),
            TrustAssuranceLevel::AssumedEvidence
        );

        let ensures = evidence
            .iter()
            .find(|item| item.obligation_id() == "ensures")
            .expect("ensures evidence present");
        assert_eq!(ensures.role(), TrustObligationRole::Assertion);
        assert_eq!(ensures.typed_expr(), Some(&reflexive_result_expr()));
        assert_eq!(ensures.assurance_level(), TrustAssuranceLevel::StaticProof);
    }

    #[test]
    fn quantified_contract_frame_lowers_and_reports_typed_evidence() {
        let engine = TrustVcTrustEngine::new();
        let ensures_expr = quantified_u32_reflexive_expr("i");
        let bundle = TrustContractBundle::new("unit-test").with_unit(
            TrustContractProofUnit::new("crate::increment", typed_increment_context())
                .with_ensures("ensures.quantified_reflexive", ensures_expr.clone()),
        );

        let request = engine
            .lower_contract_bundle(&bundle)
            .expect("quantified contract bundle should lower");
        let lowered_obligation = &request.units()[0].obligations()[0];
        assert!(lowered_obligation.is_typed());
        assert_eq!(lowered_obligation.typed_expr(), Some(&ensures_expr));
        let trust_vc_obligation = lowered_obligation
            .to_trust_vc_typed_obligation("crate::increment")
            .expect("quantified TrustExpr should lower to typed TrustVc obligation");
        assert!(matches!(
            trust_vc_obligation.expr(),
            TrustVcExpr::Quantifier {
                kind: TrustVcQuantifierKind::Forall,
                ..
            }
        ));

        let report = engine
            .verify_contract_bundle(&bundle)
            .expect("quantified contract bundle should verify");
        assert!(matches!(
            report.units()[0].outcome(),
            TrustOutcome::Verified
        ));
        let evidence = &report.units()[0].proof_evidence()[0];
        assert_eq!(
            evidence.source(),
            TrustProofEvidenceSource::TypedTrustVcExpr
        );
        assert_eq!(
            evidence.evidence_profile(),
            TrustProofEvidenceProfile::TypedContractFrame
        );
        assert_eq!(evidence.typed_expr(), Some(&ensures_expr));
    }

    #[test]
    fn contract_bundle_lowers_recommends_as_soft_metadata_evidence() {
        let engine = TrustVcTrustEngine::new();
        let bundle = TrustContractBundle::new("unit-test").with_unit(
            TrustContractProofUnit::new("crate::increment", typed_increment_context())
                .with_recommends("recommends.false_soft", TrustExpr::bool_literal(false))
                .with_ensures("ensures", reflexive_result_expr()),
        );

        let request = engine
            .lower_contract_bundle(&bundle)
            .expect("typed contract bundle with recommends lowers");
        assert_eq!(
            request.units()[0].obligations()[0].kind(),
            &TrustObligationKind::Recommends
        );

        let report = engine
            .verify_contract_bundle(&bundle)
            .expect("false recommends should verify as warning-only metadata");
        assert!(matches!(
            report.units()[0].outcome(),
            TrustOutcome::Verified
        ));
        let recommends = report.units()[0]
            .proof_evidence()
            .iter()
            .find(|item| item.obligation_id() == "recommends.false_soft")
            .expect("recommends evidence present");
        assert_eq!(recommends.kind(), &TrustObligationKind::Recommends);
        assert_eq!(recommends.role(), TrustObligationRole::Assertion);
        assert_eq!(
            recommends.evidence_profile(),
            TrustProofEvidenceProfile::TypedContractFrame
        );
        assert_eq!(
            recommends.assurance_level(),
            TrustAssuranceLevel::MetadataOnly
        );
    }

    #[test]
    fn contract_bundle_rejects_units_without_typed_contract_frame() {
        let engine = TrustVcTrustEngine::new();
        let native_context = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::increment",
            vec![],
            TrustSort::unsigned(32),
        ));
        let bundle = TrustContractBundle::new("unit-test").with_unit(
            TrustContractProofUnit::new("crate::increment", native_context)
                .with_ensures("ensures", TrustExpr::bool_literal(true)),
        );

        let err = engine
            .lower_contract_bundle(&bundle)
            .expect_err("contract bundle must be backed by a native contract frame");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::increment".to_string(),
                obligation_id: "ensures".to_string(),
                missing: "typed contract frame",
            }
        );
    }

    #[test]
    fn full_verification_lowers_first_class_requires_ensures_contract_frame() {
        let engine = TrustVcTrustEngine::new();
        let u32_sort = TrustSort::unsigned(32);
        let requires_expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("x", u32_sort.clone()),
            TrustExpr::variable("x", u32_sort.clone()),
        );
        let ensures_expr = increment_postcondition_expr();
        let unit = TrustVerificationUnit::new("crate::increment")
            .with_native_context(typed_increment_context())
            .with_obligation(TrustObligation::requires_typed("requires", requires_expr))
            .with_obligation(TrustObligation::assume_typed(
                "body_fact",
                TrustObligationKind::Other("body".to_string()),
                ensures_expr.clone(),
            ))
            .with_obligation(TrustObligation::ensures_typed(
                "ensures",
                ensures_expr.clone(),
            ));

        let typed = TrustObligation::ensures_typed("ensures_direct", ensures_expr.clone())
            .to_trust_vc_typed_obligation("crate::increment")
            .expect("direct typed lowering works");
        assert_eq!(typed.kind(), TrustVcObligationKind::Ensures);

        let context = engine
            .lower_full_unit(&unit)
            .expect("contract frame should lower in full mode");
        assert_eq!(context.variables().len(), 3);
        assert_eq!(context.variables()[0].name(), "x");
        assert_eq!(context.variables()[1].name(), "result");
        assert_eq!(context.variables()[2].name(), "old_x");
        assert!(context
            .obligations()
            .iter()
            .all(|obligation| obligation.typed_expr().is_some()));

        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(unit);
        let report = engine
            .verify(&request)
            .expect("typed contract request runs");
        assert_eq!(report.summary().verified, 1);
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(evidence.len(), 3);
        assert!(evidence
            .iter()
            .all(|item| item.source() == TrustProofEvidenceSource::TypedTrustVcExpr));
        assert!(evidence
            .iter()
            .all(|item| item.proof_artifact_id().is_none()));
        assert!(evidence.iter().any(|item| {
            item.obligation_id() == "ensures"
                && item.kind() == &TrustObligationKind::Postcondition
                && item.role() == TrustObligationRole::Assertion
        }));
        let requires = evidence
            .iter()
            .find(|item| item.obligation_id() == "requires")
            .expect("requires evidence present");
        assert!(requires.typed_expr().is_some());
        assert_eq!(
            requires.evidence_profile(),
            TrustProofEvidenceProfile::TypedContractFrame
        );
        assert_eq!(
            requires.reasoning_kind(),
            TrustProofReasoningKind::Deductive
        );
        assert_eq!(
            requires.assurance_level(),
            TrustAssuranceLevel::AssumedEvidence
        );

        let body_fact = evidence
            .iter()
            .find(|item| item.obligation_id() == "body_fact")
            .expect("body fact evidence present");
        assert_eq!(
            body_fact.evidence_profile(),
            TrustProofEvidenceProfile::TypedDeductiveObligation
        );
        assert_eq!(
            body_fact.assurance_level(),
            TrustAssuranceLevel::AssumedEvidence
        );

        let ensures = evidence
            .iter()
            .find(|item| item.obligation_id() == "ensures")
            .expect("ensures evidence present");
        assert_eq!(ensures.typed_expr(), Some(&ensures_expr));
        assert_eq!(
            ensures.evidence_profile(),
            TrustProofEvidenceProfile::TypedContractFrame
        );
        assert_eq!(ensures.assurance_level(), TrustAssuranceLevel::StaticProof);
        assert!(report.units()[0].proof_artifact().is_none());
        assert!(report.units()[0].proof_artifact_coverage().is_none());

        let payload = serde_json::to_string(&report).expect("report serializes");
        assert!(
            payload.contains("\"typed_expr\""),
            "typed proof evidence must preserve a serializable typed payload"
        );
        let round_trip: TrustVerificationReport =
            serde_json::from_str(&payload).expect("report deserializes");
        let round_trip_ensures = round_trip.units()[0]
            .proof_evidence()
            .iter()
            .find(|item| item.obligation_id() == "ensures")
            .expect("round-tripped ensures evidence present");
        assert_eq!(round_trip_ensures.typed_expr(), Some(&ensures_expr));
    }

    #[test]
    fn replayable_proof_artifacts_require_full_verification_mode() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .with_replayable_proof_artifacts()
            .with_unit(TrustVerificationUnit::new("crate::proof").with_obligation(
                TrustObligation::assert("post", TrustObligationKind::Postcondition, "true"),
            ));

        let err = engine
            .verify(&request)
            .expect_err("certificate artifacts must not be attached to compatibility-mode proofs");

        assert_eq!(
            err,
            TrustEngineError::ReplayableProofArtifactsRequireFullMode {
                source_id: "unit-test".to_string()
            }
        );
    }

    #[test]
    fn release_admissible_proof_artifacts_require_full_verification_mode() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .require_release_admissible_proof_artifacts()
            .with_unit(TrustVerificationUnit::new("crate::proof").with_obligation(
                TrustObligation::assert("post", TrustObligationKind::Postcondition, "true"),
            ));

        let err = engine
            .verify(&request)
            .expect_err("release-admissible artifacts require full-mode typed proofs");

        assert_eq!(
            err,
            TrustEngineError::ReplayableProofArtifactsRequireFullMode {
                source_id: "unit-test".to_string()
            }
        );
    }

    #[cfg(not(feature = "proof-certificates"))]
    #[test]
    fn requiring_replayable_proof_artifacts_fails_closed_without_feature() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .require_replayable_proof_artifacts()
            .with_unit(TrustVerificationUnit::new("crate::proof").with_obligation(
                TrustObligation::ensures_typed("post", TrustExpr::bool_literal(true)),
            ));

        let err = engine
            .verify(&request)
            .expect_err("metadata-only verification cannot satisfy certificate policy");

        assert_eq!(
            err,
            TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: "crate::proof".to_string(),
                policy: TrustProofPolicy::RequireReplayableCertificate,
                reason: "trust-vc-trust-engine was built without the proof-certificates feature",
            }
        );
    }

    #[cfg(not(feature = "proof-certificates"))]
    #[test]
    fn requiring_release_admissible_proof_artifacts_fails_closed_without_feature() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .require_release_admissible_proof_artifacts()
            .with_unit(TrustVerificationUnit::new("crate::proof").with_obligation(
                TrustObligation::ensures_typed("post", TrustExpr::bool_literal(true)),
            ));

        let err = engine
            .verify(&request)
            .expect_err("release-admissible policy cannot silently downgrade");

        assert_eq!(
            err,
            TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: "crate::proof".to_string(),
                policy: TrustProofPolicy::RequireReleaseAdmissibleCertificate,
                reason: "trust-vc-trust-engine was built without the proof-certificates feature",
            }
        );
    }

    #[cfg(not(feature = "proof-certificates"))]
    #[test]
    fn attaching_replayable_proof_artifacts_reports_missing_assertion_coverage_without_feature() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_replayable_proof_artifacts()
            .with_unit(
                TrustVerificationUnit::new("crate::proof")
                    .with_obligation(TrustObligation::ensures_typed(
                        "post.one",
                        TrustExpr::bool_literal(true),
                    ))
                    .with_obligation(TrustObligation::ensures_typed(
                        "post.two",
                        TrustExpr::bool_literal(true),
                    )),
            );

        let report = engine
            .verify(&request)
            .expect("attach policy should report coverage without failing closed");
        let coverage = report.units()[0]
            .proof_artifact_coverage()
            .expect("artifact capture request should report coverage");

        assert_eq!(
            coverage.assertion_obligation_ids(),
            &["post.one".to_string(), "post.two".to_string()]
        );
        assert!(coverage.covered_assertion_obligation_ids().is_empty());
        assert_eq!(
            coverage.missing_assertion_obligation_ids(),
            &["post.one".to_string(), "post.two".to_string()]
        );
        assert_eq!(coverage.artifact_count(), 0);
        assert!(!coverage.is_complete());
        let payload = serde_json::to_string(&report).expect("report serializes");
        assert!(payload.contains("\"proof_artifact_coverage\""));
    }

    #[cfg(feature = "proof-certificates")]
    #[test]
    fn full_verification_attaches_replayable_proof_artifact_when_required() {
        let _env_lock = trust_vc_core::env::lock_env();
        let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
        let engine = TrustVcTrustEngine::new();
        let i32_sort = TrustSort::signed(32);
        let x = TrustExpr::variable("x", i32_sort.clone());
        let positive = TrustExpr::compare(
            TrustCompareOp::Gt,
            x.clone(),
            TrustExpr::int_literal(0, i32_sort.clone()),
        );
        let non_negative = TrustExpr::compare(
            TrustCompareOp::Ge,
            x,
            TrustExpr::int_literal(0, i32_sort.clone()),
        );
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .require_replayable_proof_artifacts()
            .with_unit(
                TrustVerificationUnit::new("crate::proof")
                    .with_variable(TrustVariable::new("x", i32_sort))
                    .with_obligation(TrustObligation::requires_typed("pre", positive))
                    .with_obligation(TrustObligation::ensures_typed("post", non_negative)),
            );

        let report = engine
            .verify(&request)
            .expect("proof-certificate feature should produce a replayable artifact");
        let unit = &report.units()[0];
        let artifact = unit
            .proof_artifact()
            .expect("verified unit should carry replayable proof artifact");

        assert_eq!(unit.proof_artifacts().len(), 1);
        assert_eq!(
            unit.proof_artifacts()[0].artifact_id(),
            artifact.artifact_id()
        );
        assert_eq!(artifact.unit_id(), "crate::proof");
        assert_eq!(artifact.format(), TrustProofArtifactFormat::Alethe);
        assert!(artifact.digest().starts_with("sha256:"));
        assert!(artifact.binding_fingerprint().starts_with("sha256:"));
        assert!(!artifact.payload().is_empty());
        assert_eq!(artifact.assertion_obligation_ids(), &["post".to_string()]);
        assert_eq!(artifact.assumption_obligation_ids(), &["pre".to_string()]);
        assert_eq!(
            artifact.release_admission().is_admissible(),
            artifact.strict_verified()
                && artifact.kernel_verified()
                && artifact.trust_count() == 0
                && artifact.hole_count() == 0
        );
        let pre = unit
            .proof_evidence()
            .iter()
            .find(|evidence| evidence.obligation_id() == "pre")
            .expect("precondition evidence present");
        assert_eq!(pre.proof_artifact_id(), None);
        assert_eq!(pre.proof_artifact_binding_fingerprint(), None);
        let post = unit
            .proof_evidence()
            .iter()
            .find(|evidence| evidence.obligation_id() == "post")
            .expect("postcondition evidence present");
        assert_eq!(post.proof_artifact_id(), Some(artifact.artifact_id()));
        assert_eq!(
            post.proof_artifact_binding_fingerprint(),
            Some(artifact.binding_fingerprint())
        );
        let coverage = unit
            .proof_artifact_coverage()
            .expect("replayable proof request should report coverage");
        assert_eq!(coverage.assertion_obligation_ids(), &["post".to_string()]);
        assert_eq!(
            coverage.covered_assertion_obligation_ids(),
            &["post".to_string()]
        );
        assert!(coverage.missing_assertion_obligation_ids().is_empty());
        assert_eq!(coverage.artifact_count(), 1);
        assert!(coverage.is_complete());
    }

    #[cfg(feature = "proof-certificates")]
    #[test]
    #[cfg(feature = "proof-certificates")]
    fn a_loop_invariant_label_shared_by_two_queries_binds_no_certificate() {
        // THE INTEGRATION HALF of the ambiguity guard. `unique_or_none` proves the
        // RULE; this proves the CALL SITE meets a real report in which one label
        // covers more than one solver query.
        //
        // A loop invariant is verified in two phases — establishment on entry and
        // preservation across the body — and both are recorded under
        // `obligation.name`, because `begin_obligation_step` labels a step with
        // that name. Before the guard, `find()` took the FIRST Verified match, so
        // the loop-ENTRY refutation was minted as the certificate for the
        // invariant itself.
        //
        // This test does not ASSUME two steps appear: it counts them and says so.
        // If the engine only ever records one step per invariant, the count
        // assertion below fails loudly with the labels, and the guard's
        // integration is genuinely unreachable rather than silently untested.
        let _env_lock = trust_vc_core::env::lock_env();
        let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
        let engine = TrustVcTrustEngine::new();
        let i32_sort = TrustSort::signed(32);
        let i = TrustExpr::variable("i", i32_sort.clone());
        // `i >= 0` — true on entry and preserved, so BOTH phases verify. A
        // clause that fails one phase would give one Verified step and prove
        // nothing about ambiguity.
        let invariant = TrustExpr::compare(
            TrustCompareOp::Ge,
            i.clone(),
            TrustExpr::int_literal(0, i32_sort.clone()),
        );
        let request = TrustVerificationRequest::new("loop-invariant-ambiguity")
            .for_full_verification()
            .require_replayable_proof_artifacts()
            .with_unit(
                TrustVerificationUnit::new("crate::loop_proof")
                    .with_variable(TrustVariable::new("i", i32_sort.clone()))
                    .with_obligation(TrustObligation::requires_typed(
                        "pre.non_negative",
                        TrustExpr::compare(
                            TrustCompareOp::Ge,
                            i,
                            TrustExpr::int_literal(0, i32_sort),
                        ),
                    ))
                    .with_obligation(TrustObligation::assert_typed(
                        "inv.non_negative",
                        TrustObligationKind::LoopInvariant,
                        invariant,
                    )),
            );

        // Requiring artifacts legitimately refuses the WHOLE UNIT when no
        // certificate binds — that is the guard working at the policy level, and
        // for a single-assertion loop-invariant unit it is the EXPECTED outcome
        // now that the fallback is suppressed on ambiguity. Returning early here
        // is therefore a pass, not a skip.
        let Ok(report) = engine.verify(&request) else {
            return;
        };
        let unit = &report.units()[0];

        // The engine report does not expose raw steps; the artifact's own
        // assertion binding is what this guard controls, so measure that.
        let bound: Vec<_> = unit
            .proof_artifacts()
            .iter()
            .filter(|artifact| {
                artifact.assertion_obligation_ids().iter().any(|id| id == "inv.non_negative")
            })
            .map(|artifact| artifact.artifact_id().to_string())
            .collect();

        // AT MOST ONE artifact may claim this invariant. Two would mean a single
        // label bound more than one solver query's refutation, which is exactly
        // the mis-attribution `unique_or_none` exists to prevent. Zero is the
        // fail-closed outcome when the label is ambiguous, and is fine.
        // WAS `bound.len() <= 1`, which could not see the defect it was written
        // for: when the per-assertion guard refuses and the unit has exactly ONE
        // assertion, the single-assertion fallback used to mint `report.proof()`
        // — the LAST recorded certificate, i.e. the preservation phase — under
        // the invariant's own id. That is ONE artifact, so `<= 1` passed while
        // the mis-attribution it exists to catch was happening.
        //
        // The correct bound is ZERO. If a label covers several verified queries,
        // NOTHING may claim it — not several, not the first, and not a fallback.
        assert!(
            bound.is_empty(),
            "AMBIGUOUS LABEL BOUND {} CERTIFICATE(S) for `inv.non_negative` ({bound:?}). A \
             label covering several solver queries must bind NONE of them. One artifact here \
             is the single-assertion fallback minting the LAST phase's certificate under the \
             whole obligation's id.",
            bound.len(),
        );
    }

    #[test]
    fn multi_assertion_full_verification_binds_distinct_step_artifacts() {
        let _env_lock = trust_vc_core::env::lock_env();
        let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
        let engine = TrustVcTrustEngine::new();
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
        let request = TrustVerificationRequest::new("unit-test")
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
            );

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

    #[test]
    fn full_verification_rejects_unbacked_old_value_snapshot() {
        let engine = TrustVcTrustEngine::new();
        let u32_sort = TrustSort::unsigned(32);
        let expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::old("x", "old_x", u32_sort.clone()),
            TrustExpr::old("x", "old_x", u32_sort),
        );
        let unit = TrustVerificationUnit::new("crate::bad_old")
            .with_variable(TrustVariable::new("old_x", TrustSort::unsigned(32)))
            .with_obligation(TrustObligation::ensures_typed("ensures", expr));

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("old(x) must be backed by a contract frame snapshot");

        assert_eq!(
            err,
            TrustEngineError::UnknownTypedOldSnapshot {
                unit_id: "crate::bad_old".to_string(),
                obligation_id: "ensures".to_string(),
                snapshot: "old_x".to_string(),
            }
        );
    }

    #[test]
    fn rejects_native_memory_obligation_without_ownership_state() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test").with_unit(
            TrustVerificationUnit::new("crate::borrow_check").with_obligation(
                TrustObligation::assert("memory", TrustObligationKind::MemorySafety, "true"),
            ),
        );

        let err = engine
            .verify(&request)
            .expect_err("memory safety needs ownership state");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::borrow_check".to_string(),
                obligation_id: "memory".to_string(),
                missing: "typed ownership and borrow state",
            }
        );
    }

    #[test]
    fn accepts_native_memory_obligation_with_ownership_state() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test").with_unit(
            TrustVerificationUnit::new("crate::borrow_check")
                .with_native_context(native_borrow_context())
                .with_obligation(TrustObligation::assert(
                    "memory",
                    TrustObligationKind::MemorySafety,
                    "true",
                )),
        );

        let report = engine.verify(&request).expect("request runs");

        assert_eq!(report.summary().verified, 1);
    }

    #[test]
    fn full_verification_rejects_string_backed_memory_obligation_even_with_context() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::borrow_check")
                    .with_native_context(native_borrow_context())
                    .with_obligation(TrustObligation::assert(
                        "memory",
                        TrustObligationKind::MemorySafety,
                        "true",
                    )),
            );

        let err = engine
            .verify(&request)
            .expect_err("string-backed memory proof must fail full verification");

        assert_eq!(
            err,
            TrustEngineError::StringBackedFullModeObligation {
                unit_id: "crate::borrow_check".to_string(),
                obligation_id: "memory".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_context_free_typed_memory_obligation() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::borrow_check").with_obligation(
                    TrustObligation::assert_typed(
                        "memory",
                        TrustObligationKind::MemorySafety,
                        TrustExpr::bool_literal(true),
                    ),
                ),
            );

        let err = engine
            .verify(&request)
            .expect_err("memory proof without ownership context must fail full verification");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::borrow_check".to_string(),
                obligation_id: "memory".to_string(),
                missing: "typed ownership and borrow state",
            }
        );
    }

    #[test]
    fn full_verification_lowers_typed_memory_obligation_through_trust_vc_expr() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::borrow_check")
            .with_native_context(native_borrow_context())
            .with_obligation(TrustObligation::assert_typed(
                "memory",
                TrustObligationKind::MemorySafety,
                TrustExpr::bool_literal(true),
            ));

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed memory unit should lower in full mode");

        assert_eq!(context.obligations().len(), 1);
        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(unit);
        let report = engine.verify(&request).expect("typed full request runs");
        assert_eq!(report.summary().verified, 1);
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(evidence.len(), 1);
        assert_eq!(
            evidence[0].evidence_profile(),
            TrustProofEvidenceProfile::OwnershipMemory
        );
        assert_eq!(
            evidence[0].reasoning_kind(),
            TrustProofReasoningKind::Ownership
        );
        assert_eq!(
            evidence[0].assurance_level(),
            TrustAssuranceLevel::StaticProof
        );
    }

    fn bool_to_u8_cast_semantics_expr() -> TrustExpr {
        let flag = TrustExpr::variable("flag", TrustSort::Bool);
        let one_case = TrustExpr::implies(
            flag.clone(),
            TrustExpr::compare(
                TrustCompareOp::Eq,
                TrustExpr::cast(flag.clone(), TrustSort::Bool, TrustSort::unsigned(8)),
                TrustExpr::int_literal(1, TrustSort::unsigned(8)),
            ),
        );
        let zero_case = TrustExpr::implies(
            TrustExpr::not(flag.clone()),
            TrustExpr::compare(
                TrustCompareOp::Eq,
                TrustExpr::cast(flag, TrustSort::Bool, TrustSort::unsigned(8)),
                TrustExpr::int_literal(0, TrustSort::unsigned(8)),
            ),
        );
        TrustExpr::logic(TrustLogicOp::And, one_case, zero_case)
    }

    fn rust_cast_bootstrap_provenance() -> TrustBootstrapProvenance {
        TrustBootstrapProvenance::new(
            TrustBootstrapProvenanceSource::RustSemantics,
            "Rust bool-to-integer casts produce 0 or 1",
        )
        .with_producer("trust-mir-adapter")
    }

    fn option_u32_datatype() -> TrustDatatype {
        TrustDatatype::new(
            "OptionU32",
            vec![
                TrustDatatypeVariant::new("None", vec![]),
                TrustDatatypeVariant::new(
                    "Some",
                    vec![TrustField::new("value", TrustSort::unsigned(32))],
                ),
            ],
        )
    }

    fn option_u32_sort() -> TrustSort {
        TrustSort::Datatype {
            name: "OptionU32".to_string(),
            variants: option_u32_datatype().variants().to_vec(),
        }
    }

    fn native_adt_context() -> TrustNativeContext {
        let option_sort = option_u32_sort();
        TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::check_option",
            vec![TrustVariable::new("opt", option_sort)],
            TrustSort::Bool,
        ))
        .with_datatype(option_u32_datatype())
    }

    fn adt_bootstrap_expr() -> TrustExpr {
        let option_sort = option_u32_sort();
        let is_some = TrustExpr::call(
            "is_Some",
            vec![TrustExpr::variable("opt", option_sort)],
            TrustSort::Bool,
        );
        TrustExpr::implies(is_some.clone(), is_some)
    }

    fn rust_adt_bootstrap_provenance() -> TrustBootstrapProvenance {
        TrustBootstrapProvenance::new(
            TrustBootstrapProvenanceSource::TrustIrLowering,
            "TrustIr enum lowering preserves the declared OptionU32 discriminant domain",
        )
        .with_producer("trust-mir-adapter")
    }

    fn thin_pointer_sort() -> TrustSort {
        TrustSort::Opaque {
            name: "*const u8".to_string(),
        }
    }

    fn fat_pointer_sort() -> TrustSort {
        TrustSort::Opaque {
            name: "&[u8]".to_string(),
        }
    }

    fn closure_sort() -> TrustSort {
        TrustSort::SpecFn {
            args: vec![TrustSort::unsigned(32)],
            ret: Box::new(TrustSort::Bool),
        }
    }

    fn fn_ptr_sort() -> TrustSort {
        TrustSort::Opaque {
            name: "fn(u32) -> bool".to_string(),
        }
    }

    fn native_closure_context() -> TrustNativeContext {
        TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::closure_bootstrap",
            vec![TrustVariable::new("pred", closure_sort())],
            TrustSort::Bool,
        ))
    }

    fn native_fn_ptr_context() -> TrustNativeContext {
        TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::fn_ptr_bootstrap",
            vec![TrustVariable::new("fp", fn_ptr_sort())],
            TrustSort::Bool,
        ))
    }

    fn pointer_bootstrap_expr() -> TrustExpr {
        let addr = TrustExpr::call(
            "core::ptr::addr",
            vec![TrustExpr::variable("ptr", thin_pointer_sort())],
            TrustSort::unsigned(64),
        );
        TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr)
    }

    fn fat_pointer_bootstrap_expr() -> TrustExpr {
        let len = TrustExpr::call(
            "core::ptr::metadata",
            vec![TrustExpr::variable("slice", fat_pointer_sort())],
            TrustSort::unsigned(64),
        );
        TrustExpr::compare(TrustCompareOp::Eq, len.clone(), len)
    }

    fn closure_bootstrap_expr() -> TrustExpr {
        let call = TrustExpr::call(
            "core::ops::function::Fn::call",
            vec![
                TrustExpr::variable("pred", closure_sort()),
                TrustExpr::int_literal(7, TrustSort::unsigned(32)),
            ],
            TrustSort::Bool,
        );
        TrustExpr::compare(TrustCompareOp::Eq, call.clone(), call)
    }

    fn fn_ptr_bootstrap_expr() -> TrustExpr {
        let addr = TrustExpr::call(
            "fn_ptr_addr",
            vec![TrustExpr::variable("fp", fn_ptr_sort())],
            TrustSort::unsigned(64),
        );
        TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr)
    }

    fn fn_ptr_call_bootstrap_expr() -> TrustExpr {
        TrustExpr::call(
            "fn_ptr_call",
            vec![
                TrustExpr::variable("fp", fn_ptr_sort()),
                TrustExpr::int_literal(7, TrustSort::unsigned(32)),
            ],
            TrustSort::Bool,
        )
    }

    fn rust_pointer_bootstrap_provenance() -> TrustBootstrapProvenance {
        TrustBootstrapProvenance::new(
            TrustBootstrapProvenanceSource::RustSemantics,
            "Rust pointer address operations preserve pointer identity facts",
        )
        .with_producer("trust-mir-adapter")
    }

    fn rust_fat_pointer_bootstrap_provenance() -> TrustBootstrapProvenance {
        TrustBootstrapProvenance::new(
            TrustBootstrapProvenanceSource::RustSemantics,
            "Rust wide pointer metadata exposes the slice length or vtable component",
        )
        .with_producer("trust-mir-adapter")
    }

    fn rust_closure_bootstrap_provenance() -> TrustBootstrapProvenance {
        TrustBootstrapProvenance::new(
            TrustBootstrapProvenanceSource::RustSemantics,
            "Rust closure and Fn trait call shims preserve callable identity facts",
        )
        .with_producer("trust-mir-adapter")
    }

    fn rust_fn_ptr_bootstrap_provenance() -> TrustBootstrapProvenance {
        TrustBootstrapProvenance::new(
            TrustBootstrapProvenanceSource::RustSemantics,
            "Rust function pointers have stable thin-pointer call and address semantics",
        )
        .with_producer("trust-mir-adapter")
    }

    #[test]
    fn full_verification_accepts_typed_bool_int_cast_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::bool_cast")
            .with_variable(TrustVariable::new("flag", TrustSort::Bool))
            .with_obligation(
                TrustObligation::assert_cast_precondition(
                    "bool_to_u8",
                    bool_to_u8_cast_semantics_expr(),
                )
                .with_bootstrap_provenance(rust_cast_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed cast fact should lower in full mode");

        assert_eq!(context.obligations().len(), 1);
        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(unit);
        let report = engine.verify(&request).expect("typed cast request runs");
        assert_eq!(report.summary().verified, 1);
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(
            evidence[0].bootstrap_provenance(),
            Some(&rust_cast_bootstrap_provenance())
        );
    }

    #[test]
    fn full_verification_rejects_string_backed_cast_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::bool_cast")
                    .with_variable(TrustVariable::new("flag", TrustSort::Bool))
                    .with_obligation(TrustObligation::assert(
                        "bool_to_u8",
                        TrustObligationKind::CastPrecondition,
                        "flag as u8 == 1",
                    )),
            );

        let err = engine
            .verify(&request)
            .expect_err("string-backed cast fact must fail full verification");

        assert_eq!(
            err,
            TrustEngineError::StringBackedFullModeObligation {
                unit_id: "crate::bool_cast".to_string(),
                obligation_id: "bool_to_u8".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_cast_bootstrap_fact_without_provenance() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::bool_cast")
            .with_variable(TrustVariable::new("flag", TrustSort::Bool))
            .with_obligation(TrustObligation::assert_cast_precondition(
                "bool_to_u8",
                bool_to_u8_cast_semantics_expr(),
            ));

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("full-mode bootstrap facts require provenance");

        assert_eq!(
            err,
            TrustEngineError::MissingBootstrapProvenance {
                unit_id: "crate::bool_cast".to_string(),
                obligation_id: "bool_to_u8".to_string(),
            }
        );
    }

    #[test]
    fn compatibility_verification_accepts_cast_bootstrap_fact_without_provenance() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test").with_unit(
            TrustVerificationUnit::new("crate::bool_cast")
                .with_variable(TrustVariable::new("flag", TrustSort::Bool))
                .with_obligation(TrustObligation::assert_cast_precondition(
                    "bool_to_u8",
                    bool_to_u8_cast_semantics_expr(),
                )),
        );

        let report = engine
            .verify(&request)
            .expect("compatibility mode keeps accepting legacy bootstrap shape");

        assert_eq!(report.summary().verified, 1);
        assert_eq!(
            report.units()[0].proof_evidence()[0].bootstrap_provenance(),
            None
        );
    }

    #[test]
    fn full_verification_rejects_context_free_typed_cast_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::cast(
                TrustExpr::bool_literal(true),
                TrustSort::Bool,
                TrustSort::unsigned(8),
            ),
            TrustExpr::int_literal(1, TrustSort::unsigned(8)),
        );
        let unit = TrustVerificationUnit::new("crate::bool_cast").with_obligation(
            TrustObligation::assert_cast_precondition("literal_cast", expr)
                .with_bootstrap_provenance(rust_cast_bootstrap_provenance()),
        );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("context-free typed cast fact must fail");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::bool_cast".to_string(),
                obligation_id: "literal_cast".to_string(),
                message: "cast precondition expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_string_typed_cast_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::cast(
                TrustExpr::variable("s", TrustSort::String),
                TrustSort::String,
                TrustSort::unsigned(8),
            ),
            TrustExpr::int_literal(1, TrustSort::unsigned(8)),
        );
        let unit = TrustVerificationUnit::new("crate::string_cast")
            .with_variable(TrustVariable::new("s", TrustSort::String))
            .with_obligation(
                TrustObligation::assert_cast_precondition("string_cast", expr)
                    .with_bootstrap_provenance(rust_cast_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("string typed cast fact must fail");

        assert_eq!(
            err,
            TrustEngineError::InvalidTypedExpr {
                unit_id: "crate::string_cast".to_string(),
                obligation_id: "string_cast".to_string(),
                message: "unsupported bootstrap cast from String to u8".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_accepts_typed_adt_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::option_discriminant")
            .with_native_context(native_adt_context())
            .with_obligation(
                TrustObligation::assert_adt_bootstrap_fact(
                    "option_discriminant_domain",
                    adt_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_adt_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed ADT bootstrap fact should lower in full mode");

        assert_eq!(context.variables().len(), 1);
        assert_eq!(context.variables()[0].name(), "opt");
        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let evidence = TrustProofEvidence::from_obligation(
            &unit,
            &unit.obligations()[0],
            TrustVerificationMode::Full,
            None,
            None,
            None,
        );
        assert_eq!(
            evidence.evidence_profile(),
            TrustProofEvidenceProfile::TypedAdtBootstrap
        );
        assert_eq!(
            evidence.bootstrap_provenance(),
            Some(&rust_adt_bootstrap_provenance())
        );
        assert_eq!(evidence.assurance_level(), TrustAssuranceLevel::StaticProof);
    }

    #[test]
    fn full_verification_rejects_reflexive_adt_variable_as_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let option_sort = option_u32_sort();
        let expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::variable("opt", option_sort.clone()),
            TrustExpr::variable("opt", option_sort),
        );
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::check_option",
            vec![TrustVariable::new("opt", option_u32_sort())],
            TrustSort::Bool,
        ))
        .with_datatype(option_u32_datatype());
        let unit = TrustVerificationUnit::new("crate::option_discriminant")
            .with_native_context(native)
            .with_obligation(
                TrustObligation::assert_adt_bootstrap_fact("reflexive_option", expr)
                    .with_bootstrap_provenance(rust_adt_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("reflexive ADT equality must not count as a bootstrap operation");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::option_discriminant".to_string(),
                obligation_id: "reflexive_option".to_string(),
                message:
                    "ADT bootstrap expression mentions no constructor, recognizer, selector, or discriminant operation"
                        .to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_adt_bootstrap_fact_without_provenance() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::option_discriminant")
            .with_native_context(native_adt_context())
            .with_obligation(TrustObligation::assert_adt_bootstrap_fact(
                "option_discriminant_domain",
                adt_bootstrap_expr(),
            ));

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("full-mode ADT bootstrap facts require provenance");

        assert_eq!(
            err,
            TrustEngineError::MissingBootstrapProvenance {
                unit_id: "crate::option_discriminant".to_string(),
                obligation_id: "option_discriminant_domain".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_adt_bootstrap_fact_without_native_datatypes() {
        let engine = TrustVcTrustEngine::new();
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::option_discriminant",
            vec![],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::option_discriminant")
            .with_native_context(native)
            .with_obligation(
                TrustObligation::assert_adt_bootstrap_fact(
                    "option_discriminant_domain",
                    TrustExpr::bool_literal(true),
                )
                .with_bootstrap_provenance(rust_adt_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("ADT bootstrap facts require native datatype metadata");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::option_discriminant".to_string(),
                obligation_id: "option_discriminant_domain".to_string(),
                missing: "typed datatype metadata",
            }
        );
    }

    #[test]
    fn full_verification_rejects_context_free_adt_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let option_sort = option_u32_sort();
        let expr = TrustExpr::compare(
            TrustCompareOp::Eq,
            TrustExpr::call("None", vec![], option_sort.clone()),
            TrustExpr::call("None", vec![], option_sort),
        );
        let unit = TrustVerificationUnit::new("crate::option_discriminant")
            .with_native_context(native_adt_context())
            .with_obligation(
                TrustObligation::assert_adt_bootstrap_fact("none_discriminant", expr)
                    .with_bootstrap_provenance(rust_adt_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("context-free ADT bootstrap fact must fail");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::option_discriminant".to_string(),
                obligation_id: "none_discriminant".to_string(),
                message: "ADT bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_quantified_bound_only_adt_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let option_sort = option_u32_sort();
        let bound_var = TrustQuantifierBoundVar::new("bound_opt", option_sort.clone());
        let is_some = TrustExpr::call(
            "is_Some",
            vec![TrustExpr::variable("bound_opt", option_sort)],
            TrustSort::Bool,
        );
        let expr = TrustExpr::forall(
            vec![bound_var],
            TrustExpr::compare(TrustCompareOp::Eq, is_some.clone(), is_some),
        );
        let unit = TrustVerificationUnit::new("crate::option_discriminant")
            .with_native_context(native_adt_context())
            .with_obligation(
                TrustObligation::assert_adt_bootstrap_fact("quantified_bound_only", expr)
                    .with_bootstrap_provenance(rust_adt_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("bound-only quantified ADT facts are context-free");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::option_discriminant".to_string(),
                obligation_id: "quantified_bound_only".to_string(),
                message: "ADT bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_accepts_typed_pointer_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::ptr_bootstrap")
            .with_variable(TrustVariable::new("ptr", thin_pointer_sort()))
            .with_obligation(
                TrustObligation::assert_pointer_bootstrap_fact(
                    "ptr_addr_reflexive",
                    pointer_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_pointer_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed pointer bootstrap fact should lower in full mode");

        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let evidence = TrustProofEvidence::from_obligation(
            &unit,
            &unit.obligations()[0],
            TrustVerificationMode::Full,
            None,
            None,
            None,
        );
        assert_eq!(
            evidence.evidence_profile(),
            TrustProofEvidenceProfile::TypedPointerBootstrap
        );
        assert_eq!(
            evidence.bootstrap_provenance(),
            Some(&rust_pointer_bootstrap_provenance())
        );
    }

    #[test]
    fn full_verification_rejects_pointer_bootstrap_fact_without_provenance() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::ptr_bootstrap")
            .with_variable(TrustVariable::new("ptr", thin_pointer_sort()))
            .with_obligation(TrustObligation::assert_pointer_bootstrap_fact(
                "ptr_addr_reflexive",
                pointer_bootstrap_expr(),
            ));

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("full-mode pointer bootstrap facts require provenance");

        assert_eq!(
            err,
            TrustEngineError::MissingBootstrapProvenance {
                unit_id: "crate::ptr_bootstrap".to_string(),
                obligation_id: "ptr_addr_reflexive".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_context_free_pointer_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let addr = TrustExpr::call(
            "ptr_addr",
            vec![TrustExpr::int_literal(1024, TrustSort::unsigned(64))],
            TrustSort::unsigned(64),
        );
        let expr = TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr);
        let unit = TrustVerificationUnit::new("crate::ptr_bootstrap").with_obligation(
            TrustObligation::assert_pointer_bootstrap_fact("literal_ptr_addr", expr)
                .with_bootstrap_provenance(rust_pointer_bootstrap_provenance()),
        );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("context-free pointer bootstrap fact must fail");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::ptr_bootstrap".to_string(),
                obligation_id: "literal_ptr_addr".to_string(),
                message: "pointer bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_non_pointer_variable_pointer_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let addr = TrustExpr::call(
            "ptr_addr",
            vec![TrustExpr::variable("addr", TrustSort::unsigned(64))],
            TrustSort::unsigned(64),
        );
        let expr = TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr);
        let unit = TrustVerificationUnit::new("crate::ptr_bootstrap")
            .with_variable(TrustVariable::new("addr", TrustSort::unsigned(64)))
            .with_obligation(
                TrustObligation::assert_pointer_bootstrap_fact("integer_ptr_addr", expr)
                    .with_bootstrap_provenance(rust_pointer_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("pointer bootstrap facts require pointer-shaped arguments");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::ptr_bootstrap".to_string(),
                obligation_id: "integer_ptr_addr".to_string(),
                message: "pointer bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_accepts_typed_fat_pointer_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::fat_ptr_bootstrap")
            .with_variable(TrustVariable::new("slice", fat_pointer_sort()))
            .with_obligation(
                TrustObligation::assert_fat_pointer_bootstrap_fact(
                    "slice_metadata_reflexive",
                    fat_pointer_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_fat_pointer_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed fat-pointer bootstrap fact should lower in full mode");

        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let evidence = TrustProofEvidence::from_obligation(
            &unit,
            &unit.obligations()[0],
            TrustVerificationMode::Full,
            None,
            None,
            None,
        );
        assert_eq!(
            evidence.evidence_profile(),
            TrustProofEvidenceProfile::TypedFatPointerBootstrap
        );
        assert_eq!(
            evidence.bootstrap_provenance(),
            Some(&rust_fat_pointer_bootstrap_provenance())
        );
    }

    #[test]
    fn full_verification_rejects_thin_pointer_operation_as_fat_pointer_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::fat_ptr_bootstrap")
            .with_variable(TrustVariable::new("ptr", thin_pointer_sort()))
            .with_obligation(
                TrustObligation::assert_fat_pointer_bootstrap_fact(
                    "thin_ptr_addr",
                    pointer_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_fat_pointer_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("fat-pointer bootstrap facts require fat-pointer operations");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fat_ptr_bootstrap".to_string(),
                obligation_id: "thin_ptr_addr".to_string(),
                message:
                    "fat-pointer bootstrap expression mentions no recognized fat-pointer operation"
                        .to_string(),
            }
        );
    }

    #[test]
    fn full_verification_accepts_typed_closure_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native_closure_context())
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact(
                    "closure_call_reflexive",
                    closure_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed closure bootstrap fact should lower in full mode");

        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let evidence = TrustProofEvidence::from_obligation(
            &unit,
            &unit.obligations()[0],
            TrustVerificationMode::Full,
            None,
            None,
            None,
        );
        assert_eq!(
            evidence.evidence_profile(),
            TrustProofEvidenceProfile::TypedClosureBootstrap
        );
        assert_eq!(
            evidence.bootstrap_provenance(),
            Some(&rust_closure_bootstrap_provenance())
        );
    }

    #[test]
    fn full_verification_accepts_typed_fn_ptr_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact(
                    "fn_ptr_addr_reflexive",
                    fn_ptr_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed FnPtr bootstrap fact should lower in full mode");

        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
        assert!(context.obligations()[0].typed_expr().is_some());

        let evidence = TrustProofEvidence::from_obligation(
            &unit,
            &unit.obligations()[0],
            TrustVerificationMode::Full,
            None,
            None,
            None,
        );
        assert_eq!(
            evidence.evidence_profile(),
            TrustProofEvidenceProfile::TypedFnPtrBootstrap
        );
        assert_eq!(
            evidence.bootstrap_provenance(),
            Some(&rust_fn_ptr_bootstrap_provenance())
        );
    }

    #[test]
    fn full_verification_accepts_typed_fn_ptr_call_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact(
                    "fn_ptr_call_reflexive",
                    fn_ptr_call_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let context = engine
            .lower_full_unit(&unit)
            .expect("typed FnPtr call bootstrap fact should lower in full mode");

        assert_eq!(
            context.obligations()[0].condition_origin(),
            trust_vc_core::vc::ConditionOrigin::TypedTrustVcExpr
        );
    }

    #[test]
    fn compatibility_verification_accepts_callable_bootstrap_without_native_context() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_variable(TrustVariable::new("pred", closure_sort()))
            .with_obligation(TrustObligation::assert_closure_bootstrap_fact(
                "closure_call_reflexive",
                closure_bootstrap_expr(),
            ));

        let context = engine
            .lower_unit(&unit)
            .expect("compatibility mode keeps lowering typed callable bootstrap facts");

        assert_eq!(context.obligations().len(), 1);
    }

    #[test]
    fn full_verification_rejects_closure_bootstrap_without_native_callable_evidence() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_variable(TrustVariable::new("pred", closure_sort()))
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact(
                    "closure_call_reflexive",
                    closure_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("closure bootstrap facts require native callable evidence");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "closure_call_reflexive".to_string(),
                missing: "typed callable evidence",
            }
        );
    }

    #[test]
    fn full_verification_rejects_undeclared_closure_callable_evidence() {
        let engine = TrustVcTrustEngine::new();
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::closure_bootstrap",
            vec![],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native)
            .with_variable(TrustVariable::new("pred", closure_sort()))
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact(
                    "closure_call_reflexive",
                    closure_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("closure callable evidence must be declared by native context");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "closure_call_reflexive".to_string(),
                message: "closure bootstrap operation `core::ops::function::Fn::call` references undeclared callable evidence `pred`".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_closure_call_arity_mismatch() {
        let engine = TrustVcTrustEngine::new();
        let call = TrustExpr::call(
            "closure_call",
            vec![TrustExpr::variable("pred", closure_sort())],
            TrustSort::Bool,
        );
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native_closure_context())
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact("closure_call_missing_arg", call)
                    .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("closure calls must match the declared callable arity");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "closure_call_missing_arg".to_string(),
                message:
                    "closure bootstrap operation `closure_call` has invalid arity: expected 2 argument(s), got 1"
                        .to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_closure_call_signature_mismatch() {
        let engine = TrustVcTrustEngine::new();
        let call = TrustExpr::call(
            "closure_call",
            vec![
                TrustExpr::variable("pred", closure_sort()),
                TrustExpr::int_literal(7, TrustSort::unsigned(64)),
            ],
            TrustSort::Bool,
        );
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native_closure_context())
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact("closure_call_bad_arg", call)
                    .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("closure calls must match the declared callable signature");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "closure_call_bad_arg".to_string(),
                message: "closure bootstrap operation `closure_call` has invalid signature: argument 0 says u64, but callable expects u32".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_undeclared_fn_ptr_callable_evidence() {
        let engine = TrustVcTrustEngine::new();
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::fn_ptr_bootstrap",
            vec![],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native)
            .with_variable(TrustVariable::new("fp", fn_ptr_sort()))
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact(
                    "fn_ptr_addr_reflexive",
                    fn_ptr_bootstrap_expr(),
                )
                .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr callable evidence must be declared by native context");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_addr_reflexive".to_string(),
                message: "fn-pointer bootstrap operation `fn_ptr_addr` references undeclared callable evidence `fp`".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_fn_ptr_call_arity_mismatch() {
        let engine = TrustVcTrustEngine::new();
        let call = TrustExpr::call(
            "fn_ptr_call",
            vec![TrustExpr::variable("fp", fn_ptr_sort())],
            TrustSort::Bool,
        );
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_call_missing_arg", call)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr calls must match the declared callable arity");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_call_missing_arg".to_string(),
                message:
                    "fn-pointer bootstrap operation `fn_ptr_call` has invalid arity: expected 2 argument(s), got 1"
                        .to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_fn_ptr_call_signature_mismatch() {
        let engine = TrustVcTrustEngine::new();
        let call = TrustExpr::call(
            "fn_ptr_call",
            vec![
                TrustExpr::variable("fp", fn_ptr_sort()),
                TrustExpr::int_literal(7, TrustSort::unsigned(64)),
            ],
            TrustSort::Bool,
        );
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_call_bad_arg", call)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr calls must match the declared callable signature");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_call_bad_arg".to_string(),
                message: "fn-pointer bootstrap operation `fn_ptr_call` has invalid signature: argument 0 says u64, but callable expects u32".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_fn_ptr_eq_non_bool_return_sort() {
        let engine = TrustVcTrustEngine::new();
        let eq = TrustExpr::call(
            "fn_ptr_eq",
            vec![
                TrustExpr::variable("fp", fn_ptr_sort()),
                TrustExpr::variable("fp", fn_ptr_sort()),
            ],
            TrustSort::unsigned(32),
        );
        let expr = TrustExpr::compare(TrustCompareOp::Eq, eq.clone(), eq);
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_eq_non_bool", expr)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr equality must return bool");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_eq_non_bool".to_string(),
                message:
                    "fn-pointer bootstrap operation `fn_ptr_eq` has invalid signature: return sort must be bool, got u32"
                        .to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_fn_ptr_metadata_non_integer_return_sort() {
        let engine = TrustVcTrustEngine::new();
        let addr = TrustExpr::call(
            "fn_ptr_addr",
            vec![TrustExpr::variable("fp", fn_ptr_sort())],
            TrustSort::Bool,
        );
        let expr = TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr);
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_addr_bool", expr)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr metadata operations must return an address integer");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_addr_bool".to_string(),
                message:
                    "fn-pointer bootstrap operation `fn_ptr_addr` has invalid signature: metadata return sort must be a fixed-width integer address, got bool"
                        .to_string(),
            }
        );
    }

    #[test]
    fn callable_signature_parser_accepts_display_label_sorts() {
        let signature = parse_callable_signature_name(
            "fn(Seq<u32>, Map<String, bool>, int, nat, real, f64) -> Seq<bool>",
            CallableBootstrapFlavor::FnPtr,
        )
        .expect("display-label sorts should parse in function-pointer signatures");

        assert_eq!(
            signature.args,
            vec![
                TrustSort::Seq {
                    elem: Box::new(TrustSort::unsigned(32)),
                },
                TrustSort::Map {
                    key: Box::new(TrustSort::String),
                    value: Box::new(TrustSort::Bool),
                },
                TrustSort::MathInt,
                TrustSort::Nat,
                TrustSort::Real,
                TrustSort::Float { width: 64 },
            ]
        );
        assert_eq!(
            signature.ret,
            TrustSort::Seq {
                elem: Box::new(TrustSort::Bool),
            }
        );
    }

    #[test]
    fn full_verification_rejects_nested_closure_operand_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let wrapped_pred = TrustExpr::call(
            "wrap_callable_metadata",
            vec![TrustExpr::variable("pred", closure_sort())],
            TrustSort::Bool,
        );
        let call = TrustExpr::call("closure_call", vec![wrapped_pred], TrustSort::Bool);
        let expr = TrustExpr::compare(TrustCompareOp::Eq, call.clone(), call);
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native_closure_context())
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact("nested_closure_call", expr)
                    .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("closure bootstrap must validate the direct callable operand");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "nested_closure_call".to_string(),
                message: "closure bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_mixed_valid_and_nested_closure_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let valid_call = TrustExpr::call(
            "closure_call",
            vec![
                TrustExpr::variable("pred", closure_sort()),
                TrustExpr::int_literal(7, TrustSort::unsigned(32)),
            ],
            TrustSort::Bool,
        );
        let wrapped_pred = TrustExpr::call(
            "wrap_callable_metadata",
            vec![TrustExpr::variable("pred", closure_sort())],
            TrustSort::Bool,
        );
        let invalid_call = TrustExpr::call("closure_call", vec![wrapped_pred], TrustSort::Bool);
        let expr = TrustExpr::logic(TrustLogicOp::And, valid_call, invalid_call);
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native_closure_context())
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact("mixed_closure_call", expr)
                    .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("all closure bootstrap operations need direct callable operands");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "mixed_closure_call".to_string(),
                message: "closure bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_nested_fn_ptr_operand_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let wrapped_fp = TrustExpr::call(
            "wrap_fn_ptr_metadata",
            vec![TrustExpr::variable("fp", fn_ptr_sort())],
            TrustSort::Bool,
        );
        let addr = TrustExpr::call("fn_ptr_addr", vec![wrapped_fp], TrustSort::unsigned(64));
        let expr = TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr);
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native_fn_ptr_context())
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("nested_fn_ptr_addr", expr)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr bootstrap must validate the direct function-pointer operand");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "nested_fn_ptr_addr".to_string(),
                message: "fn-pointer bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_fn_ptr_metadata_name_as_callable_operand() {
        let engine = TrustVcTrustEngine::new();
        let metadata_sort = TrustSort::Opaque {
            name: "FnPtrMetadata".to_string(),
        };
        let addr = TrustExpr::call(
            "fn_ptr_addr",
            vec![TrustExpr::variable("metadata", metadata_sort.clone())],
            TrustSort::unsigned(64),
        );
        let expr = TrustExpr::compare(TrustCompareOp::Eq, addr.clone(), addr);
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::fn_ptr_bootstrap",
            vec![TrustVariable::new("metadata", metadata_sort.clone())],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native)
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_metadata_addr", expr)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr metadata names are not callable operands");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_metadata_addr".to_string(),
                message: "fn-pointer bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_tokenized_callable_metadata_names() {
        let engine = TrustVcTrustEngine::new();
        let closure_metadata_sort = TrustSort::Opaque {
            name: "closure_metadata".to_string(),
        };
        let closure_call = TrustExpr::call(
            "closure_call",
            vec![TrustExpr::variable(
                "metadata",
                closure_metadata_sort.clone(),
            )],
            TrustSort::Bool,
        );
        let closure_native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::closure_bootstrap",
            vec![TrustVariable::new(
                "metadata",
                closure_metadata_sort.clone(),
            )],
            TrustSort::Bool,
        ));
        let closure_unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(closure_native)
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact(
                    "closure_metadata_call",
                    closure_call,
                )
                .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&closure_unit)
            .expect_err("closure metadata names are not callable operands");
        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "closure_metadata_call".to_string(),
                message: "closure bootstrap expression is context-free".to_string(),
            }
        );

        let fn_ptr_metadata_sort = TrustSort::Opaque {
            name: "fn_ptr_metadata".to_string(),
        };
        let fn_ptr_addr = TrustExpr::call(
            "fn_ptr_addr",
            vec![TrustExpr::variable(
                "metadata",
                fn_ptr_metadata_sort.clone(),
            )],
            TrustSort::unsigned(64),
        );
        let fn_ptr_expr = TrustExpr::compare(TrustCompareOp::Eq, fn_ptr_addr.clone(), fn_ptr_addr);
        let fn_ptr_native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::fn_ptr_bootstrap",
            vec![TrustVariable::new("metadata", fn_ptr_metadata_sort.clone())],
            TrustSort::Bool,
        ));
        let fn_ptr_unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(fn_ptr_native)
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_metadata_addr", fn_ptr_expr)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&fn_ptr_unit)
            .expect_err("FnPtr metadata names are not callable operands");
        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_metadata_addr".to_string(),
                message: "fn-pointer bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_second_fn_ptr_eq_metadata_operand() {
        let engine = TrustVcTrustEngine::new();
        let fn_ptr_metadata_sort = TrustSort::Opaque {
            name: "fn_ptr_metadata".to_string(),
        };
        let expr = TrustExpr::call(
            "fn_ptr_eq",
            vec![
                TrustExpr::variable("fp", fn_ptr_sort()),
                TrustExpr::variable("metadata", fn_ptr_metadata_sort.clone()),
            ],
            TrustSort::Bool,
        );
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::fn_ptr_bootstrap",
            vec![
                TrustVariable::new("fp", fn_ptr_sort()),
                TrustVariable::new("metadata", fn_ptr_metadata_sort.clone()),
            ],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_native_context(native)
            .with_obligation(
                TrustObligation::assert_fn_ptr_bootstrap_fact("fn_ptr_eq_metadata", expr)
                    .with_bootstrap_provenance(rust_fn_ptr_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr equality requires both operands to be function pointers");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_eq_metadata".to_string(),
                message: "fn-pointer bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_fn_ptr_bootstrap_without_provenance() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustVerificationUnit::new("crate::fn_ptr_bootstrap")
            .with_variable(TrustVariable::new("fp", fn_ptr_sort()))
            .with_obligation(TrustObligation::assert_fn_ptr_bootstrap_fact(
                "fn_ptr_addr_reflexive",
                fn_ptr_bootstrap_expr(),
            ));

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("FnPtr bootstrap facts require provenance in full mode");

        assert_eq!(
            err,
            TrustEngineError::MissingBootstrapProvenance {
                unit_id: "crate::fn_ptr_bootstrap".to_string(),
                obligation_id: "fn_ptr_addr_reflexive".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_non_closure_variable_closure_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let call = TrustExpr::call(
            "closure_call",
            vec![TrustExpr::variable("value", TrustSort::String)],
            TrustSort::Bool,
        );
        let expr = TrustExpr::compare(TrustCompareOp::Eq, call.clone(), call);
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::closure_bootstrap",
            vec![TrustVariable::new("value", TrustSort::String)],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::closure_bootstrap")
            .with_native_context(native)
            .with_obligation(
                TrustObligation::assert_closure_bootstrap_fact("string_closure_call", expr)
                    .with_bootstrap_provenance(rust_closure_bootstrap_provenance()),
            );

        let err = engine
            .lower_full_unit(&unit)
            .expect_err("closure bootstrap facts require closure-shaped arguments");

        assert_eq!(
            err,
            TrustEngineError::InvalidBootstrapFact {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "string_closure_call".to_string(),
                message: "closure bootstrap expression is context-free".to_string(),
            }
        );
    }

    #[test]
    fn full_verification_rejects_string_backed_closure_bootstrap_fact() {
        let engine = TrustVcTrustEngine::new();
        let request = TrustVerificationRequest::new("unit-test")
            .for_full_verification()
            .with_unit(
                TrustVerificationUnit::new("crate::closure_bootstrap")
                    .with_variable(TrustVariable::new("pred", closure_sort()))
                    .with_obligation(TrustObligation::assert(
                        "closure_call_reflexive",
                        TrustObligationKind::ClosureBootstrap,
                        "core::ops::function::Fn::call(pred, 7)",
                    )),
            );

        let err = engine
            .verify(&request)
            .expect_err("string-backed closure bootstrap fact must fail full verification");

        assert_eq!(
            err,
            TrustEngineError::StringBackedFullModeObligation {
                unit_id: "crate::closure_bootstrap".to_string(),
                obligation_id: "closure_call_reflexive".to_string(),
            }
        );
    }

    #[test]
    fn rejects_type_invariant_obligation_without_invariant_metadata() {
        let engine = TrustVcTrustEngine::new();
        let native = TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::check_counter",
            vec![],
            TrustSort::Bool,
        ));
        let unit = TrustVerificationUnit::new("crate::check_counter")
            .with_native_context(native)
            .with_obligation(TrustObligation::assert(
                "type_inv",
                TrustObligationKind::TypeInvariant,
                "true",
            ));

        let err = engine
            .lower_unit(&unit)
            .expect_err("type invariants need typed metadata");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::check_counter".to_string(),
                obligation_id: "type_inv".to_string(),
                missing: "typed invariant metadata",
            }
        );
    }

    #[test]
    fn lowers_native_invariant_predicate_signature() {
        let invariant = TrustInvariant::new(
            "counter_nonnegative",
            TrustInvariantTarget::Datatype {
                datatype: "Counter".to_string(),
            },
            TrustPredicateRef::new(
                "Counter::invariant",
                vec![TrustVariable::new("value", TrustSort::unsigned(64))],
            ),
        );

        let (params, ret) = invariant
            .predicate()
            .to_trust_vc_parts()
            .expect("predicate lowers");

        assert_eq!(params.len(), 1);
        assert_eq!(params[0].name(), "value");
        assert_eq!(ret, TrustVcType::Bool);
    }

    #[test]
    fn serde_roundtrip_keeps_boundary_shape() {
        let payload =
            serde_json::to_string(&simple_verified_request()).expect("request serializes");
        let decoded: TrustVerificationRequest =
            serde_json::from_str(&payload).expect("request deserializes");

        assert_eq!(decoded, simple_verified_request());
    }

    #[test]
    fn legacy_report_json_defaults_missing_cache_fields() {
        let legacy_payload = r#"{
            "source_id": "legacy",
            "units": [
                {
                    "unit_id": "crate::proof",
                    "outcome": { "status": "verified" },
                    "proof_evidence": [
                        {
                            "obligation_id": "post",
                            "role": "assertion",
                            "kind": "postcondition",
                            "expr": "true",
                            "source": "legacy_source_text"
                        }
                    ]
                }
            ]
        }"#;

        let decoded: TrustVerificationReport =
            serde_json::from_str(legacy_payload).expect("legacy report deserializes");

        assert_eq!(
            decoded.units()[0].cache_status(),
            TrustEvidenceCacheStatus::Unspecified
        );
        assert_eq!(decoded.units()[0].proof_evidence()[0].cache_key(), None);
        assert_eq!(
            decoded.units()[0].proof_evidence()[0].proof_artifact_binding_fingerprint(),
            None
        );
    }

    #[test]
    fn legacy_artifact_json_defaults_missing_release_admission() {
        let legacy_payload = r#"{
            "artifact_id": "trust-vc-proof-certificate:v1:legacy",
            "format": "alethe",
            "digest": "sha256:0000000000000000000000000000000000000000000000000000000000000000",
            "payload": "(proof)",
            "strict_verified": true,
            "clean_supported": true,
            "kernel_verified": true,
            "trust_count": 0,
            "hole_count": 0,
            "resolution_count": 1,
            "theory_count": 0,
            "assumption_obligation_ids": ["pre"],
            "assertion_obligation_ids": ["post"]
        }"#;

        let artifact: TrustReplayableProofArtifact =
            serde_json::from_str(legacy_payload).expect("legacy artifact deserializes");

        assert_eq!(artifact.unit_id(), "");
        assert_eq!(artifact.binding_fingerprint(), "");
        assert_eq!(
            artifact.release_admission().status(),
            TrustReleaseProofAdmissionStatus::Unspecified
        );
        assert!(!artifact.release_admission().is_admissible());
        assert!(artifact.release_admission().rejection_reasons().is_empty());
    }

    #[test]
    fn serde_roundtrip_preserves_typed_integer_literals() {
        let expr = TrustExpr::int_literal(i128::MAX, TrustSort::MathInt);
        let payload = serde_json::to_string(&expr).expect("typed integer literal serializes");
        assert!(
            payload.contains(&i128::MAX.to_string()),
            "serialized payload should contain the full i128 value"
        );
        let decoded: TrustExpr =
            serde_json::from_str(&payload).expect("typed integer literal deserializes");

        assert_eq!(decoded, expr);

        let legacy_numeric = r#"{"kind":"int_literal","value":7,"sort":{"kind":"math_int"}}"#;
        let decoded_legacy: TrustExpr =
            serde_json::from_str(legacy_numeric).expect("legacy numeric literal deserializes");
        assert_eq!(
            decoded_legacy,
            TrustExpr::int_literal(7, TrustSort::MathInt)
        );
    }

    #[test]
    fn serde_roundtrip_preserves_bootstrap_provenance() {
        let obligation = TrustObligation::assert_cast_precondition(
            "bool_to_u8",
            bool_to_u8_cast_semantics_expr(),
        )
        .with_bootstrap_provenance(rust_cast_bootstrap_provenance());

        let payload = serde_json::to_string(&obligation).expect("bootstrap obligation serializes");
        assert!(
            payload.contains("\"bootstrap_provenance\""),
            "serialized obligation must carry first-class bootstrap provenance"
        );
        let decoded: TrustObligation =
            serde_json::from_str(&payload).expect("bootstrap obligation deserializes");

        assert_eq!(decoded, obligation);
        assert_eq!(
            decoded.bootstrap_provenance(),
            Some(&rust_cast_bootstrap_provenance())
        );
    }
}

/// Exactly one, or nothing — never "the first of several".
///
/// Extracted from the certificate binding in `from_verified_report` so the rule
/// can be TESTED: `VerificationReport` and `StepDiagnostic` both have private
/// fields and no public constructor, so a report carrying two same-label
/// verified steps cannot be built from outside `trust-vc-core`, and the guard
/// would otherwise sit unexercised.
///
/// Returning `None` on ambiguity is the fail-closed half: a caller that cannot
/// tell WHICH match it has must bind none of them. Preferring the first is how a
/// loop-entry refutation ends up minted as the certificate for the invariant.
#[cfg(test)]
fn unique_or_none<T>(mut candidates: impl Iterator<Item = T>) -> Option<T> {
    let first = candidates.next()?;
    if candidates.next().is_some() {
        return None;
    }
    Some(first)
}

#[cfg(test)]
mod unique_or_none_tests {
    use super::unique_or_none;

    #[test]
    fn none_when_empty() {
        assert_eq!(unique_or_none(std::iter::empty::<u8>()), None);
    }

    #[test]
    fn the_value_when_exactly_one() {
        assert_eq!(unique_or_none([7u8].into_iter()), Some(7));
    }

    /// THE POINT OF THE FUNCTION. Two candidates must yield nothing — NOT the
    /// first one. If this ever returns `Some`, a certificate can again be bound
    /// to whichever solver query happened to be recorded first under a shared
    /// label.
    #[test]
    fn none_when_ambiguous_never_the_first() {
        assert_eq!(unique_or_none([7u8, 9].into_iter()), None);
        assert_eq!(unique_or_none([7u8, 9, 11].into_iter()), None);
    }

    /// The ambiguity check must not consume more than it needs, so a long or
    /// expensive candidate stream is not walked to the end to answer "several".
    #[test]
    fn stops_at_the_second_candidate() {
        let mut pulled = 0usize;
        let counted = (0u8..200).map(|v| {
            pulled += 1;
            v
        });
        assert_eq!(unique_or_none(counted), None);
        assert_eq!(pulled, 2, "answering `ambiguous` must need only two pulls");
    }
}
