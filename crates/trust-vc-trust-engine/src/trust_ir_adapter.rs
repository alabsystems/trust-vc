//! Versioned typed TrustIr/trust-types adapter facade.
//!
//! This module is intentionally data-only and serializable. It gives tRust a
//! stable JSON boundary for compiler integration while trust_vc avoids a direct
//! dependency on still-moving compiler crates.

use crate::{
    TrustEngineError, TrustExpr, TrustNativeContext, TrustObligation, TrustObligationKind,
    TrustObligationRole, TrustProofLineage, TrustProofLineageSource, TrustProofPolicy,
    TrustSolverMode, TrustVariable, TrustVcTrustEngine, TrustVerificationReport,
    TrustVerificationRequest, TrustVerificationUnit, TrustVerifier,
    TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Versioned typed TrustIr/trust-types request accepted by TrustVc.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustTrustIrAdapterRequest {
    #[serde(default = "default_trust_ir_adapter_schema_version")]
    schema_version: u32,
    source_id: String,
    units: Vec<TrustTrustIrProofUnit>,
    #[serde(default)]
    proof_policy: TrustProofPolicy,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    metadata: BTreeMap<String, String>,
}

impl TrustTrustIrAdapterRequest {
    /// Create an empty typed adapter request.
    pub fn new(source_id: impl Into<String>) -> Self {
        Self {
            schema_version: TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION,
            source_id: source_id.into(),
            units: Vec::new(),
            proof_policy: TrustProofPolicy::default(),
            metadata: BTreeMap::new(),
        }
    }

    /// Return the TrustIr adapter schema version.
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    /// Return the request source id.
    pub fn source_id(&self) -> &str {
        &self.source_id
    }

    /// Return typed TrustIr proof units.
    pub fn units(&self) -> &[TrustTrustIrProofUnit] {
        &self.units
    }

    /// Return the requested proof-artifact policy.
    pub const fn proof_policy(&self) -> TrustProofPolicy {
        self.proof_policy
    }

    /// Return request metadata.
    pub fn metadata(&self) -> &BTreeMap<String, String> {
        &self.metadata
    }

    /// Replace all units.
    pub fn with_units(mut self, units: Vec<TrustTrustIrProofUnit>) -> Self {
        self.units = units;
        self
    }

    /// Append one typed TrustIr proof unit.
    pub fn with_unit(mut self, unit: TrustTrustIrProofUnit) -> Self {
        self.units.push(unit);
        self
    }

    /// Set the proof-artifact policy for the lowered Trust request.
    pub fn with_proof_policy(mut self, proof_policy: TrustProofPolicy) -> Self {
        self.proof_policy = proof_policy;
        self
    }

    /// Insert a request metadata entry.
    pub fn insert_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Structurally lower to the general Trust request model.
    ///
    /// This path fails closed for unsupported TrustIr constructs before any solver
    /// invocation. Use [`TrustVcTrustEngine::lower_trust_ir_adapter_request`] when
    /// the caller also wants TrustVc request validation.
    pub fn to_trust_request(&self) -> Result<TrustVerificationRequest, TrustEngineError> {
        self.validate_schema_version()?;
        let mut request = TrustVerificationRequest::new(self.source_id.clone())
            .for_full_verification()
            .with_proof_policy(self.proof_policy);
        for unit in &self.units {
            request = request.with_unit(unit.to_trust_unit()?);
        }
        for (key, value) in &self.metadata {
            request = request.insert_metadata(key.clone(), value.clone());
        }
        Ok(request)
    }

    fn validate_schema_version(&self) -> Result<(), TrustEngineError> {
        if self.schema_version == TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION {
            return Ok(());
        }
        Err(TrustEngineError::UnsupportedTrustIrAdapterSchemaVersion {
            actual: self.schema_version,
            expected: TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION,
        })
    }
}

const fn default_trust_ir_adapter_schema_version() -> u32 {
    TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION
}

/// A single typed TrustIr function or proof boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustTrustIrProofUnit {
    unit_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    display_name: Option<String>,
    native_context: TrustNativeContext,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    verifier_variables: Vec<TrustVariable>,
    obligations: Vec<TrustTrustIrObligation>,
}

impl TrustTrustIrProofUnit {
    /// Create a typed TrustIr proof unit.
    pub fn new(unit_id: impl Into<String>, native_context: TrustNativeContext) -> Self {
        Self {
            unit_id: unit_id.into(),
            display_name: None,
            native_context,
            verifier_variables: Vec::new(),
            obligations: Vec::new(),
        }
    }

    /// Return the stable unit id.
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

    /// Return additional verifier variables referenced by obligations.
    pub fn verifier_variables(&self) -> &[TrustVariable] {
        &self.verifier_variables
    }

    /// Return typed TrustIr obligations.
    pub fn obligations(&self) -> &[TrustTrustIrObligation] {
        &self.obligations
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

    /// Append a typed TrustIr obligation.
    pub fn with_obligation(mut self, obligation: TrustTrustIrObligation) -> Self {
        self.obligations.push(obligation);
        self
    }

    /// Lower this TrustIr proof unit into the general verification unit.
    pub fn to_trust_unit(&self) -> Result<TrustVerificationUnit, TrustEngineError> {
        let mut unit = TrustVerificationUnit::new(self.unit_id.clone())
            .with_native_context(self.native_context.clone());
        if let Some(display_name) = &self.display_name {
            unit = unit.with_display_name(display_name.clone());
        }
        for variable in &self.verifier_variables {
            unit = unit.with_variable(variable.clone());
        }
        for obligation in &self.obligations {
            unit = unit.with_obligation(obligation.to_trust_obligation(&self.unit_id)?);
        }
        Ok(unit)
    }
}

/// One typed obligation emitted by tRust trust-types or TrustIr lowering.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustTrustIrObligation {
    id: String,
    kind: TrustTrustIrObligationKind,
    predicate: TrustTrustIrPredicate,
    lineage: TrustProofLineage,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    span: Option<TrustSourceSpan>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    solver_mode: Option<TrustSolverMode>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        alias = "tmir_assertion_id"
    )]
    trust_ir_assertion_id: Option<u32>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        alias = "tmir_source_id"
    )]
    trust_ir_source_id: Option<String>,
}

impl TrustTrustIrObligation {
    /// Create a typed TrustIr/trust-types obligation.
    pub fn new(
        id: impl Into<String>,
        kind: TrustTrustIrObligationKind,
        predicate: TrustTrustIrPredicate,
        lineage: TrustProofLineage,
    ) -> Self {
        Self {
            id: id.into(),
            kind,
            predicate,
            lineage,
            span: None,
            solver_mode: None,
            trust_ir_assertion_id: None,
            trust_ir_source_id: None,
        }
    }

    /// Create a typed obligation from a supported Trust expression.
    pub fn expr(
        id: impl Into<String>,
        kind: TrustTrustIrObligationKind,
        expr: TrustExpr,
        lineage: TrustProofLineage,
    ) -> Self {
        Self::new(id, kind, TrustTrustIrPredicate::expr(expr), lineage)
    }

    /// Create a fail-closed obligation for a not-yet-supported compiler construct.
    pub fn unsupported(
        id: impl Into<String>,
        kind: TrustTrustIrObligationKind,
        unsupported: TrustUnsupportedTrustIrConstruct,
        lineage: TrustProofLineage,
    ) -> Self {
        Self::new(
            id,
            kind,
            TrustTrustIrPredicate::unsupported(unsupported),
            lineage,
        )
    }

    /// Return the stable obligation id.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Return the typed obligation kind.
    pub const fn kind(&self) -> TrustTrustIrObligationKind {
        self.kind
    }

    /// Return the typed predicate payload.
    pub const fn predicate(&self) -> &TrustTrustIrPredicate {
        &self.predicate
    }

    /// Return proof lineage for this compiler obligation.
    pub const fn lineage(&self) -> &TrustProofLineage {
        &self.lineage
    }

    /// Return the source span, if supplied.
    pub const fn span(&self) -> Option<&TrustSourceSpan> {
        self.span.as_ref()
    }

    /// Return the optional solver strategy hint.
    pub const fn solver_mode(&self) -> Option<TrustSolverMode> {
        self.solver_mode
    }

    /// Return the compiler-emitted TrustIr assertion id, if supplied.
    pub const fn trust_ir_assertion_id(&self) -> Option<u32> {
        self.trust_ir_assertion_id
    }

    /// Return the compiler-emitted TrustIr source id, if supplied.
    pub fn trust_ir_source_id(&self) -> Option<&str> {
        self.trust_ir_source_id.as_deref()
    }

    /// Attach a typed source span.
    pub fn with_span(mut self, span: TrustSourceSpan) -> Self {
        self.span = Some(span);
        self
    }

    /// Attach a solver mode hint.
    pub fn with_solver_mode(mut self, solver_mode: TrustSolverMode) -> Self {
        self.solver_mode = Some(solver_mode);
        self
    }

    /// Attach the compiler-emitted TrustIr assertion id for coverage correlation.
    pub fn with_trust_ir_assertion_id(mut self, trust_ir_assertion_id: u32) -> Self {
        self.trust_ir_assertion_id = Some(trust_ir_assertion_id);
        self
    }

    /// Attach the compiler-emitted TrustIr source id for coverage correlation.
    pub fn with_trust_ir_source_id(mut self, trust_ir_source_id: impl Into<String>) -> Self {
        self.trust_ir_source_id = Some(trust_ir_source_id.into());
        self
    }

    fn to_trust_obligation(&self, unit_id: &str) -> Result<TrustObligation, TrustEngineError> {
        self.lineage.ensure_trust_ir_source(unit_id, &self.id)?;
        if let Some(span) = &self.span {
            span.validate(unit_id, &self.id)?;
        }
        if matches!(self.trust_ir_source_id.as_deref(), Some(source_id) if source_id.trim().is_empty())
        {
            return Err(TrustEngineError::InvalidProofLineage {
                unit_id: unit_id.to_string(),
                obligation_id: self.id.clone(),
                message: "TrustIr source id must not be empty when provided".to_string(),
            });
        }

        let expr = match &self.predicate {
            TrustTrustIrPredicate::Expr { expr } => expr.clone(),
            TrustTrustIrPredicate::Unsupported { construct } => {
                construct.validate(unit_id, &self.id)?;
                return Err(TrustEngineError::UnsupportedTrustIrConstruct {
                    unit_id: unit_id.to_string(),
                    obligation_id: self.id.clone(),
                    feature: construct.feature.clone(),
                    diagnostic: construct.diagnostic.clone(),
                });
            }
        };

        let (role, kind) = self.kind.to_trust_parts();
        let mut obligation = TrustObligation::new_typed(self.id.clone(), role, kind, expr)
            .with_proof_lineage(self.lineage.clone());
        if let Some(span) = &self.span {
            obligation = obligation.with_location(span.to_location_string());
        }
        if let Some(solver_mode) = self.solver_mode {
            obligation = obligation.with_solver_mode(solver_mode);
        }
        if let Some(trust_ir_assertion_id) = self.trust_ir_assertion_id {
            obligation = obligation.with_trust_ir_assertion_id(trust_ir_assertion_id);
        }
        if let Some(trust_ir_source_id) = &self.trust_ir_source_id {
            obligation = obligation.with_trust_ir_source_id(trust_ir_source_id.clone());
        }
        Ok(obligation)
    }
}

/// TrustIr/trust-types obligation class before lowering to TrustVc Trust.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum TrustTrustIrObligationKind {
    Requires,
    Recommends,
    Ensures,
    LoopInvariant,
    TypeInvariant,
    TranslationValidation,
    MemoryNoAlias,
    BorrowProvenance,
    PanicFreedom,
}

impl TrustTrustIrObligationKind {
    const fn to_trust_parts(self) -> (TrustObligationRole, TrustObligationKind) {
        match self {
            Self::Requires => (
                TrustObligationRole::Assumption,
                TrustObligationKind::Precondition,
            ),
            Self::Recommends => (
                TrustObligationRole::Assertion,
                TrustObligationKind::Recommends,
            ),
            Self::Ensures => (
                TrustObligationRole::Assertion,
                TrustObligationKind::Postcondition,
            ),
            Self::LoopInvariant => (
                TrustObligationRole::Assertion,
                TrustObligationKind::LoopInvariant,
            ),
            Self::TypeInvariant => (
                TrustObligationRole::Assertion,
                TrustObligationKind::TypeInvariant,
            ),
            Self::TranslationValidation => (
                TrustObligationRole::Assertion,
                TrustObligationKind::TranslationValidation,
            ),
            Self::MemoryNoAlias | Self::BorrowProvenance => (
                TrustObligationRole::Assertion,
                TrustObligationKind::MemorySafety,
            ),
            Self::PanicFreedom => (
                TrustObligationRole::Assertion,
                TrustObligationKind::PanicFreedom,
            ),
        }
    }
}

/// Typed predicate payload emitted by a compiler adapter.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
#[must_use]
pub enum TrustTrustIrPredicate {
    Expr {
        expr: TrustExpr,
    },
    Unsupported {
        construct: TrustUnsupportedTrustIrConstruct,
    },
}

impl TrustTrustIrPredicate {
    /// Wrap a supported typed Trust expression.
    pub fn expr(expr: TrustExpr) -> Self {
        Self::Expr { expr }
    }

    /// Wrap an unsupported compiler construct so lowering fails closed.
    pub fn unsupported(construct: TrustUnsupportedTrustIrConstruct) -> Self {
        Self::Unsupported { construct }
    }
}

/// Structured unsupported-construct diagnostic from the tRust adapter.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustUnsupportedTrustIrConstruct {
    feature: String,
    diagnostic: String,
}

impl TrustUnsupportedTrustIrConstruct {
    /// Create an unsupported-construct marker.
    pub fn new(feature: impl Into<String>, diagnostic: impl Into<String>) -> Self {
        Self {
            feature: feature.into(),
            diagnostic: diagnostic.into(),
        }
    }

    /// Return the unsupported feature or construct class.
    pub fn feature(&self) -> &str {
        &self.feature
    }

    /// Return the human-readable diagnostic.
    pub fn diagnostic(&self) -> &str {
        &self.diagnostic
    }

    fn validate(&self, unit_id: &str, obligation_id: &str) -> Result<(), TrustEngineError> {
        if self.feature.trim().is_empty() || self.diagnostic.trim().is_empty() {
            return Err(TrustEngineError::UnsupportedTrustIrConstruct {
                unit_id: unit_id.to_string(),
                obligation_id: obligation_id.to_string(),
                feature: self.feature.clone(),
                diagnostic: "unsupported construct feature and diagnostic must not be empty"
                    .to_string(),
            });
        }
        Ok(())
    }
}

/// Typed source span supplied by trust-types or TrustIr lowering.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[must_use]
pub struct TrustSourceSpan {
    file: String,
    line_start: u32,
    column_start: u32,
    line_end: u32,
    column_end: u32,
}

impl TrustSourceSpan {
    /// Create a typed source span.
    pub fn new(
        file: impl Into<String>,
        line_start: u32,
        column_start: u32,
        line_end: u32,
        column_end: u32,
    ) -> Self {
        Self {
            file: file.into(),
            line_start,
            column_start,
            line_end,
            column_end,
        }
    }

    /// Return the source file.
    pub fn file(&self) -> &str {
        &self.file
    }

    /// Return the starting 1-based line.
    pub const fn line_start(&self) -> u32 {
        self.line_start
    }

    /// Return the starting 1-based column.
    pub const fn column_start(&self) -> u32 {
        self.column_start
    }

    /// Return the ending 1-based line.
    pub const fn line_end(&self) -> u32 {
        self.line_end
    }

    /// Return the ending 1-based column.
    pub const fn column_end(&self) -> u32 {
        self.column_end
    }

    /// Render the span into the diagnostic location string used by Trust reports.
    pub fn to_location_string(&self) -> String {
        format!(
            "{}:{}:{}-{}:{}",
            self.file, self.line_start, self.column_start, self.line_end, self.column_end
        )
    }

    fn validate(&self, unit_id: &str, obligation_id: &str) -> Result<(), TrustEngineError> {
        if self.file.trim().is_empty() {
            return Err(TrustEngineError::InvalidSourceSpan {
                unit_id: unit_id.to_string(),
                obligation_id: obligation_id.to_string(),
                message: "file must not be empty".to_string(),
            });
        }
        if self.line_start == 0
            || self.column_start == 0
            || self.line_end == 0
            || self.column_end == 0
        {
            return Err(TrustEngineError::InvalidSourceSpan {
                unit_id: unit_id.to_string(),
                obligation_id: obligation_id.to_string(),
                message: "line and column values must be 1-based".to_string(),
            });
        }
        if (self.line_end, self.column_end) < (self.line_start, self.column_start) {
            return Err(TrustEngineError::InvalidSourceSpan {
                unit_id: unit_id.to_string(),
                obligation_id: obligation_id.to_string(),
                message: "end must not precede start".to_string(),
            });
        }
        Ok(())
    }
}

impl TrustVcTrustEngine {
    /// Validate a typed TrustIr/trust-types adapter request without running the solver.
    pub fn validate_trust_ir_adapter_request(
        &self,
        request: &TrustTrustIrAdapterRequest,
    ) -> Result<(), TrustEngineError> {
        let lowered = request.to_trust_request()?;
        self.validate_request(&lowered)?;
        for unit in request.units() {
            validate_trust_ir_unit_ownership(unit)?;
        }
        Ok(())
    }

    /// Lower a typed TrustIr/trust-types adapter request after fail-closed validation.
    pub fn lower_trust_ir_adapter_request(
        &self,
        request: &TrustTrustIrAdapterRequest,
    ) -> Result<TrustVerificationRequest, TrustEngineError> {
        let lowered = request.to_trust_request()?;
        self.validate_request(&lowered)?;
        for unit in request.units() {
            validate_trust_ir_unit_ownership(unit)?;
        }
        Ok(lowered)
    }

    /// Verify a typed TrustIr/trust-types adapter request through TrustVc.
    pub fn verify_trust_ir_adapter_request(
        &self,
        request: &TrustTrustIrAdapterRequest,
    ) -> Result<TrustVerificationReport, TrustEngineError> {
        let lowered = self.lower_trust_ir_adapter_request(request)?;
        TrustVerifier::verify(self, &lowered)
    }

    /// Verify a typed Tmir adapter request through TrustVc.
    ///
    /// Tmir is the current public name for the typed TrustIr adapter surface;
    /// this forwarder lets tRust-side bridges call into the engine using the
    /// Tmir naming.
    pub fn verify_tmir_adapter_request(
        &self,
        request: &TrustTrustIrAdapterRequest,
    ) -> Result<TrustVerificationReport, TrustEngineError> {
        self.verify_trust_ir_adapter_request(request)
    }
}

fn validate_trust_ir_unit_ownership(unit: &TrustTrustIrProofUnit) -> Result<(), TrustEngineError> {
    let Some(obligation) = unit
        .obligations()
        .iter()
        .find(|obligation| obligation.kind.requires_ownership_context())
    else {
        return Ok(());
    };

    let Some(ownership) = unit.native_context().ownership() else {
        return Ok(());
    };

    if !ownership.places().is_empty()
        || !ownership.borrows().is_empty()
        || !ownership.lifetimes().is_empty()
        || !ownership.alias_facts().is_empty()
        || !ownership.provenance_facts().is_empty()
    {
        return Ok(());
    }

    Err(TrustEngineError::MissingNativeContext {
        unit_id: unit.unit_id().to_string(),
        obligation_id: obligation.id().to_string(),
        missing: "typed ownership, lifetime, alias, or provenance facts",
    })
}

impl TrustTrustIrObligationKind {
    const fn requires_ownership_context(self) -> bool {
        matches!(self, Self::MemoryNoAlias | Self::BorrowProvenance)
    }
}

impl TrustProofLineage {
    pub(crate) fn ensure_trust_ir_source(
        &self,
        unit_id: &str,
        obligation_id: &str,
    ) -> Result<(), TrustEngineError> {
        match self.source() {
            TrustProofLineageSource::TrustTypesContract
            | TrustProofLineageSource::TrustIrLowering
            | TrustProofLineageSource::TrustIrOwnership
            | TrustProofLineageSource::TrustIrBorrowCheck
            | TrustProofLineageSource::TrustIrProvenance => Ok(()),
            TrustProofLineageSource::ExternalAxiom(_) | TrustProofLineageSource::Other(_) => {
                Err(TrustEngineError::InvalidProofLineage {
                    unit_id: unit_id.to_string(),
                    obligation_id: obligation_id.to_string(),
                    message:
                        "TrustIr adapter obligations must use a TrustIr or trust-types lineage source"
                            .to_string(),
                })
            }
        }
    }
}
