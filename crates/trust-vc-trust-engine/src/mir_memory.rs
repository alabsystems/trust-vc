//! Typed MIR memory/ownership facade for tRust integrations.
//!
//! This module is a narrow library boundary over the lower-level trust request
//! model in this crate. tRust can lower MIR memory and ownership facts into
//! [`TrustMirMemoryProofUnit`] values and ask [`TrustVcTrustEngine`] for the
//! resulting [`TrustUnitReport`] directly.

use crate::{
    TrustEngineError, TrustExpr, TrustNativeContext, TrustObligation, TrustObligationKind,
    TrustProofPolicy, TrustSolverMode, TrustUnitReport, TrustVariable, TrustVcTrustEngine,
    TrustVerificationReport, TrustVerificationRequest, TrustVerificationUnit, TrustVerifier,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Schema accepted for direct TrustVc MIR memory proof-unit payloads.
pub const TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION: &str = "trust_vc.mir-memory-proof-unit.v1";

/// Metadata key carrying an inline direct TrustVc MIR memory proof unit.
pub const TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY: &str = "trust_vc.mir_memory.proof_unit";

/// Metadata key marking TrustVc-native typed expression origins.
pub const TRUST_VC_CONDITION_ORIGIN_METADATA_KEY: &str = "trust_vc.condition_origin";

/// Metadata value for typed TrustVc expression origins.
pub const TRUST_VC_CONDITION_ORIGIN_TYPED_TRUST_VC_EXPR_VALUE: &str = "TypedTrustVcExpr";

/// Metadata key marking TrustVc typed proof-obligation lowering.
pub const TRUST_VC_PROOF_OBLIGATION_METADATA_KEY: &str = "trust_vc.proof_obligation";

/// Metadata value for TrustVc typed proof-obligation lowering.
pub const TRUST_VC_PROOF_OBLIGATION_TYPED_PROOF_OBLIGATION_VALUE: &str = "TypedProofObligation";

/// Metadata key marking native ownership/borrow context availability.
pub const TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY: &str = "trust_vc.ownership_context";

/// Metadata value for native ownership/borrow context availability.
pub const TRUST_VC_OWNERSHIP_CONTEXT_TYPED_VALUE: &str = "typed";

/// Return the stable metadata markers required for typed MIR memory evidence.
#[must_use]
pub fn typed_mir_memory_metadata() -> BTreeMap<String, String> {
    BTreeMap::from([
        (
            TRUST_VC_CONDITION_ORIGIN_METADATA_KEY.to_string(),
            TRUST_VC_CONDITION_ORIGIN_TYPED_TRUST_VC_EXPR_VALUE.to_string(),
        ),
        (
            TRUST_VC_PROOF_OBLIGATION_METADATA_KEY.to_string(),
            TRUST_VC_PROOF_OBLIGATION_TYPED_PROOF_OBLIGATION_VALUE.to_string(),
        ),
        (
            TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY.to_string(),
            TRUST_VC_OWNERSHIP_CONTEXT_TYPED_VALUE.to_string(),
        ),
    ])
}

/// One MIR memory or ownership obligation that TrustVc must discharge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustMirMemoryObligation {
    id: String,
    predicate: TrustExpr,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    location: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    solver_mode: Option<TrustSolverMode>,
}

impl TrustMirMemoryObligation {
    /// Create a typed MIR memory/ownership assertion.
    pub fn new(id: impl Into<String>, predicate: TrustExpr) -> Self {
        Self {
            id: id.into(),
            predicate,
            location: None,
            solver_mode: None,
        }
    }

    /// Return the stable obligation id.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Return the typed predicate that will be lowered to TrustVc IR.
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
        let mut obligation = TrustObligation::assert_typed(
            self.id.clone(),
            TrustObligationKind::MemorySafety,
            self.predicate.clone(),
        );
        if let Some(location) = &self.location {
            obligation = obligation.with_location(location.clone());
        }
        if let Some(solver_mode) = self.solver_mode {
            obligation = obligation.with_solver_mode(solver_mode);
        }
        obligation
    }
}

/// A single MIR function/proof boundary with memory and ownership obligations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustMirMemoryProofUnit {
    source_id: String,
    unit_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    display_name: Option<String>,
    native_context: TrustNativeContext,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    verifier_variables: Vec<TrustVariable>,
    obligations: Vec<TrustMirMemoryObligation>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    metadata: BTreeMap<String, String>,
}

impl TrustMirMemoryProofUnit {
    /// Create a typed MIR memory proof unit.
    ///
    /// `native_context` must carry the function signature plus ownership/borrow
    /// state for any memory-safety obligations. A present but empty ownership
    /// state is rejected when the unit is verified.
    pub fn new(
        source_id: impl Into<String>,
        unit_id: impl Into<String>,
        native_context: TrustNativeContext,
    ) -> Self {
        Self {
            source_id: source_id.into(),
            unit_id: unit_id.into(),
            display_name: None,
            native_context,
            verifier_variables: Vec::new(),
            obligations: Vec::new(),
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

    /// Return the typed native verifier context.
    pub const fn native_context(&self) -> &TrustNativeContext {
        &self.native_context
    }

    /// Return additional verifier variables referenced by obligations.
    pub fn verifier_variables(&self) -> &[TrustVariable] {
        &self.verifier_variables
    }

    /// Return MIR memory/ownership obligations.
    pub fn obligations(&self) -> &[TrustMirMemoryObligation] {
        &self.obligations
    }

    /// Return request metadata.
    pub fn metadata(&self) -> &BTreeMap<String, String> {
        &self.metadata
    }

    /// Return the stable direct MIR memory proof-unit schema version.
    pub const fn payload_schema_version() -> &'static str {
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_SCHEMA_VERSION
    }

    /// Return the metadata key used for inline proof-unit payloads.
    pub const fn metadata_payload_key() -> &'static str {
        TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY
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

    /// Append a MIR memory/ownership obligation.
    pub fn with_obligation(mut self, obligation: TrustMirMemoryObligation) -> Self {
        self.obligations.push(obligation);
        self
    }

    /// Insert request metadata.
    pub fn insert_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Serialize this proof unit as the JSON payload expected by tRust.
    pub fn to_json_value(&self) -> Result<serde_json::Value, TrustEngineError> {
        serde_json::to_value(self).map_err(|error| TrustEngineError::SerializeMirMemoryProofUnit {
            unit_id: self.unit_id.clone(),
            reason: error.to_string(),
        })
    }

    /// Serialize this proof unit as an inline metadata value.
    pub fn to_metadata_json(&self) -> Result<String, TrustEngineError> {
        serde_json::to_string(self).map_err(|error| TrustEngineError::SerializeMirMemoryProofUnit {
            unit_id: self.unit_id.clone(),
            reason: error.to_string(),
        })
    }

    /// Return typed evidence metadata plus the inline proof-unit payload.
    pub fn to_metadata_map(&self) -> Result<BTreeMap<String, String>, TrustEngineError> {
        let mut metadata = typed_mir_memory_metadata();
        metadata.insert(
            TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY.to_string(),
            self.to_metadata_json()?,
        );
        Ok(metadata)
    }

    /// Lower this facade into the general trust verification unit.
    pub fn to_trust_unit(&self) -> TrustVerificationUnit {
        let mut unit = TrustVerificationUnit::new(self.unit_id.clone())
            .with_native_context(self.native_context.clone());
        if let Some(display_name) = &self.display_name {
            unit = unit.with_display_name(display_name.clone());
        }
        for variable in &self.verifier_variables {
            unit = unit.with_variable(variable.clone());
        }
        for obligation in &self.obligations {
            unit = unit.with_obligation(obligation.to_trust_obligation());
        }
        unit
    }

    /// Lower this facade into the general trust verification request.
    ///
    /// The generated request always uses full verification mode so TrustVc never
    /// reparses source strings for MIR memory proof predicates.
    pub fn to_trust_request(&self, proof_policy: TrustProofPolicy) -> TrustVerificationRequest {
        let mut request = TrustVerificationRequest::new(self.source_id.clone())
            .for_full_verification()
            .with_proof_policy(proof_policy)
            .with_unit(self.to_trust_unit());
        for (key, value) in &self.metadata {
            request = request.insert_metadata(key.clone(), value.clone());
        }
        request
    }

    fn validate_for_verification(
        &self,
        engine: &TrustVcTrustEngine,
    ) -> Result<(), TrustEngineError> {
        let _ = engine.lower_full_unit(&self.to_trust_unit())?;
        self.validate_non_empty_ownership_context()
    }

    fn validate_non_empty_ownership_context(&self) -> Result<(), TrustEngineError> {
        let Some(first_obligation) = self.obligations.first() else {
            return Ok(());
        };
        let Some(ownership) = self.native_context.ownership() else {
            return Ok(());
        };
        if !ownership.is_empty() {
            return Ok(());
        }

        Err(TrustEngineError::MissingNativeContext {
            unit_id: self.unit_id.clone(),
            obligation_id: first_obligation.id.clone(),
            missing: "typed ownership and borrow state",
        })
    }
}

impl TrustVcTrustEngine {
    /// Verify one typed MIR memory proof unit and return the full Trust report.
    ///
    /// This is the report-shaped variant used by deterministic runner and
    /// stage2 integration paths. It keeps the MIR-memory facade validation,
    /// including fail-closed rejection of empty ownership state.
    pub fn verify_mir_memory_request(
        &self,
        unit: &TrustMirMemoryProofUnit,
        proof_policy: TrustProofPolicy,
    ) -> Result<TrustVerificationReport, TrustEngineError> {
        unit.validate_for_verification(self)?;
        let request = unit.to_trust_request(proof_policy);
        TrustVerifier::verify(self, &request)
    }

    /// Verify one typed MIR memory proof unit and return its unit report.
    ///
    /// Pass [`TrustProofPolicy::AttachReplayableCertificates`] or one of the
    /// require policies to request native replayable proof artifacts. Requiring
    /// artifacts fails closed when TrustVc is built without certificate support.
    pub fn verify_mir_memory_unit(
        &self,
        unit: &TrustMirMemoryProofUnit,
        proof_policy: TrustProofPolicy,
    ) -> Result<TrustUnitReport, TrustEngineError> {
        let report = self.verify_mir_memory_request(unit, proof_policy)?;
        report
            .units()
            .first()
            .cloned()
            .ok_or_else(|| TrustEngineError::MissingVerifiedUnitReport {
                unit_id: unit.unit_id.clone(),
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        TrustAssuranceLevel, TrustBorrow, TrustBorrowKind, TrustEvidenceCacheStatus,
        TrustFunctionSignature, TrustOutcome, TrustOwnedPlace, TrustOwnershipState,
        TrustProofEvidenceProfile, TrustProofReasoningKind, TrustSort,
        TRUST_CACHE_METADATA_AY_VERSION, TRUST_CACHE_METADATA_LAYOUT_HASH,
        TRUST_CACHE_METADATA_TRUST_IR_BODY_HASH,
    };

    fn ptr_live_tautology() -> TrustExpr {
        let ptr_live = TrustExpr::variable("ptr_live", TrustSort::Bool);
        TrustExpr::compare(crate::TrustCompareOp::Eq, ptr_live.clone(), ptr_live)
    }

    fn native_ownership_context() -> TrustNativeContext {
        TrustNativeContext::new(TrustFunctionSignature::new(
            "crate::take_shared",
            vec![TrustVariable::new("ptr_live", TrustSort::Bool)],
            TrustSort::Bool,
        ))
        .with_ownership(
            TrustOwnershipState::new()
                .with_place(TrustOwnedPlace::new("x", TrustSort::unsigned(32)))
                .with_borrow(TrustBorrow::new("r0", "x", TrustBorrowKind::Shared)),
        )
    }

    fn mir_memory_unit(obligation_id: &str) -> TrustMirMemoryProofUnit {
        TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        )
        .with_display_name("take_shared")
        .with_obligation(
            TrustMirMemoryObligation::new(obligation_id, ptr_live_tautology())
                .with_location("src/lib.rs:12:9"),
        )
    }

    #[test]
    fn mir_memory_facade_builds_full_typed_request() {
        let unit =
            mir_memory_unit("mir.memory.no_mut_alias").insert_metadata("mir_body", "DefId(0:3)");

        let request = unit.to_trust_request(TrustProofPolicy::AttachReplayableCertificates);
        let lowered = &request.units()[0];

        assert_eq!(request.source_id(), "crate-under-test");
        assert_eq!(request.mode(), crate::TrustVerificationMode::Full);
        assert_eq!(
            request.proof_policy(),
            TrustProofPolicy::AttachReplayableCertificates
        );
        assert_eq!(
            request.metadata().get("mir_body").map(String::as_str),
            Some("DefId(0:3)")
        );
        assert_eq!(lowered.unit_id(), "crate::take_shared");
        assert_eq!(lowered.display_name(), Some("take_shared"));
        assert!(lowered.native_context().is_some());
        assert_eq!(lowered.obligations().len(), 1);
        assert_eq!(
            lowered.obligations()[0].kind(),
            &TrustObligationKind::MemorySafety
        );
        assert!(lowered.obligations()[0].typed_expr().is_some());
        assert_eq!(lowered.obligations()[0].location(), Some("src/lib.rs:12:9"));
    }

    #[test]
    fn mir_memory_facade_exports_trust_metadata_schema() {
        assert_eq!(
            TrustMirMemoryProofUnit::payload_schema_version(),
            "trust_vc.mir-memory-proof-unit.v1"
        );
        assert_eq!(
            TrustMirMemoryProofUnit::metadata_payload_key(),
            "trust_vc.mir_memory.proof_unit"
        );

        let metadata = typed_mir_memory_metadata();
        assert_eq!(
            metadata
                .get(TRUST_VC_CONDITION_ORIGIN_METADATA_KEY)
                .map(String::as_str),
            Some("TypedTrustVcExpr")
        );
        assert_eq!(
            metadata
                .get(TRUST_VC_PROOF_OBLIGATION_METADATA_KEY)
                .map(String::as_str),
            Some("TypedProofObligation")
        );
        assert_eq!(
            metadata
                .get(TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY)
                .map(String::as_str),
            Some("typed")
        );
    }

    #[test]
    fn mir_memory_facade_serializes_trust_payload_without_ad_hoc_strings() {
        let unit = mir_memory_unit("mir.memory.no_mut_alias");
        let value = unit
            .to_json_value()
            .expect("MIR memory proof unit serializes to JSON");

        assert_eq!(value["source_id"], "crate-under-test");
        assert_eq!(value["unit_id"], "crate::take_shared");
        assert_eq!(value["display_name"], "take_shared");
        assert_eq!(
            value["native_context"]["ownership"]["places"][0]["place"],
            "x"
        );
        assert_eq!(
            value["native_context"]["ownership"]["borrows"][0]["kind"],
            "shared"
        );
        assert_eq!(value["obligations"][0]["id"], "mir.memory.no_mut_alias");
        assert_eq!(value["obligations"][0]["predicate"]["kind"], "compare");

        let metadata_json = unit
            .to_metadata_json()
            .expect("MIR memory proof unit serializes for metadata");
        let round_trip: TrustMirMemoryProofUnit =
            serde_json::from_str(&metadata_json).expect("metadata payload round-trips");
        assert_eq!(round_trip, unit);

        let metadata = unit
            .to_metadata_map()
            .expect("MIR memory proof unit metadata map serializes");
        assert_eq!(
            metadata
                .get(TRUST_VC_CONDITION_ORIGIN_METADATA_KEY)
                .map(String::as_str),
            Some(TRUST_VC_CONDITION_ORIGIN_TYPED_TRUST_VC_EXPR_VALUE)
        );
        assert_eq!(
            metadata
                .get(TRUST_VC_PROOF_OBLIGATION_METADATA_KEY)
                .map(String::as_str),
            Some(TRUST_VC_PROOF_OBLIGATION_TYPED_PROOF_OBLIGATION_VALUE)
        );
        assert_eq!(
            metadata
                .get(TRUST_VC_OWNERSHIP_CONTEXT_METADATA_KEY)
                .map(String::as_str),
            Some(TRUST_VC_OWNERSHIP_CONTEXT_TYPED_VALUE)
        );
        assert_eq!(
            metadata
                .get(TRUST_VC_MIR_MEMORY_PROOF_UNIT_METADATA_KEY)
                .map(String::as_str),
            Some(metadata_json.as_str())
        );
    }

    #[test]
    fn ownership_state_reports_empty_status() {
        assert!(TrustOwnershipState::new().is_empty());
        assert!(!TrustOwnershipState::new()
            .with_borrow(TrustBorrow::new("r0", "x", TrustBorrowKind::Shared))
            .is_empty());
    }

    #[test]
    fn mir_memory_facade_rejects_empty_obligation_sets() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        );

        let err = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::EvidenceOnly)
            .expect_err("MIR memory proof units must contain assertions");

        assert_eq!(
            err,
            TrustEngineError::UnitHasNoAssertions {
                unit_id: "crate::take_shared".to_string(),
            }
        );
    }

    #[test]
    fn mir_memory_facade_returns_unit_report_with_native_evidence() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        )
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            ptr_live_tautology(),
        ));

        let report = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::EvidenceOnly)
            .expect("typed MIR memory unit should verify");

        assert_eq!(report.unit_id(), "crate::take_shared");
        assert!(matches!(report.outcome(), TrustOutcome::Verified));
        assert!(report.proof_artifact().is_none());
        let evidence = report.proof_evidence();
        assert_eq!(evidence.len(), 1);
        assert_eq!(evidence[0].obligation_id(), "mir.memory.ptr_live");
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
        assert!(evidence[0].typed_expr().is_some());
        assert_eq!(report.cache_status(), TrustEvidenceCacheStatus::Miss);
    }

    #[test]
    fn mir_memory_facade_reports_cache_key_with_compiler_metadata() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        )
        .insert_metadata(TRUST_CACHE_METADATA_AY_VERSION, "ay:99506df4")
        .insert_metadata(
            TRUST_CACHE_METADATA_TRUST_IR_BODY_HASH,
            "trust_ir-body:abc123",
        )
        .insert_metadata(TRUST_CACHE_METADATA_LAYOUT_HASH, "layout:def456")
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            ptr_live_tautology(),
        ));

        let report = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::EvidenceOnly)
            .expect("typed MIR memory unit should verify");
        let cache_key = report.proof_evidence()[0]
            .cache_key()
            .expect("MIR memory evidence should carry a cache key");

        assert_eq!(report.cache_status(), TrustEvidenceCacheStatus::Miss);
        assert_eq!(cache_key.ay_version(), "ay:99506df4");
        assert_eq!(cache_key.trust_ir_body_hash(), Some("trust_ir-body:abc123"));
        assert_eq!(cache_key.layout_hash(), Some("layout:def456"));
        assert!(cache_key.ownership_digest().is_some());
        assert!(cache_key.fingerprint().starts_with("sha256:"));
    }

    #[test]
    fn mir_memory_facade_fails_without_ownership_context() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            TrustNativeContext::new(TrustFunctionSignature::new(
                "crate::take_shared",
                vec![],
                TrustSort::Bool,
            )),
        )
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            TrustExpr::bool_literal(true),
        ));

        let err = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::EvidenceOnly)
            .expect_err("memory proof requires ownership context");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::take_shared".to_string(),
                obligation_id: "mir.memory.ptr_live".to_string(),
                missing: "typed ownership and borrow state",
            }
        );
    }

    #[test]
    fn mir_memory_facade_fails_with_empty_ownership_context() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            TrustNativeContext::new(TrustFunctionSignature::new(
                "crate::take_shared",
                vec![],
                TrustSort::Bool,
            ))
            .with_ownership(TrustOwnershipState::new()),
        )
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            TrustExpr::bool_literal(true),
        ));

        let err = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::EvidenceOnly)
            .expect_err("empty ownership state cannot justify memory proof");

        assert_eq!(
            err,
            TrustEngineError::MissingNativeContext {
                unit_id: "crate::take_shared".to_string(),
                obligation_id: "mir.memory.ptr_live".to_string(),
                missing: "typed ownership and borrow state",
            }
        );
    }

    #[test]
    fn mir_memory_facade_rejects_duplicate_verifier_variables_after_lowering() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        )
        .with_variable(TrustVariable::new("ptr_live", TrustSort::Bool))
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            ptr_live_tautology(),
        ));

        let err = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::EvidenceOnly)
            .expect_err("duplicate variables lowered through the facade must be rejected");

        assert_eq!(
            err,
            TrustEngineError::DuplicateVariable {
                unit_id: "crate::take_shared".to_string(),
                name: "ptr_live".to_string(),
            }
        );
    }

    #[cfg(not(feature = "proof-certificates"))]
    #[test]
    fn mir_memory_facade_attach_replayable_policy_is_best_effort_without_feature() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        )
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            ptr_live_tautology(),
        ));

        let report = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::AttachReplayableCertificates)
            .expect("attach policy should verify without requiring a certificate");

        assert!(matches!(report.outcome(), TrustOutcome::Verified));
        assert!(report.proof_artifact().is_none());
    }

    #[cfg(not(feature = "proof-certificates"))]
    #[test]
    fn mir_memory_facade_require_replayable_policy_fails_closed_without_feature() {
        let engine = TrustVcTrustEngine::new();
        let unit = TrustMirMemoryProofUnit::new(
            "crate-under-test",
            "crate::take_shared",
            native_ownership_context(),
        )
        .with_obligation(TrustMirMemoryObligation::new(
            "mir.memory.ptr_live",
            ptr_live_tautology(),
        ));

        let err = engine
            .verify_mir_memory_unit(&unit, TrustProofPolicy::RequireReplayableCertificate)
            .expect_err("required certificate policy cannot silently downgrade");

        assert_eq!(
            err,
            TrustEngineError::ReplayableProofCertificateUnavailable {
                unit_id: "crate::take_shared".to_string(),
                policy: TrustProofPolicy::RequireReplayableCertificate,
                reason: "trust-vc-trust-engine was built without the proof-certificates feature",
            }
        );
    }
}
