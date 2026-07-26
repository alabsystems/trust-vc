//! Native full-verification boundary for typed proof evidence.
//!
//! This module is intentionally stricter than the legacy `VerificationContext`
//! surface: proof evidence must carry a native `TrustVcExpr` payload. Raw
//! string-backed obligations may still exist for compatibility elsewhere, but
//! they are rejected here before solver execution.
//! Verified evidence summaries are the explicit handoff: downstream aggregators
//! receive proof source, reasoning kind, and assurance level instead of
//! upgrading an opaque verified bit.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use thiserror::Error;

use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_place::TrustVcPlace;
use crate::vc::{
    ConditionOrigin, ObligationKind, ProofObligation, TypedProofObligation, VariableDecl,
    VerificationContext,
};
use crate::{VerificationReport, VerificationReportOptions, VerifyResult};

/// A typed memory-safety fact that can be verified as native proof evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "typed memory-safety facts must be added to a full-verification request"]
pub struct TypedMemorySafetyFact {
    name: String,
    kind: MemorySafetyFactKind,
    expr: TrustVcExpr,
    location: Option<String>,
}

impl TypedMemorySafetyFact {
    /// Builds a fact proving that two root places are disjoint because they
    /// have distinct ownership roots.
    pub fn disjoint_roots(
        name: impl Into<String>,
        left_root: impl Into<String>,
        left_ty: TrustVcType,
        right_root: impl Into<String>,
        right_ty: TrustVcType,
    ) -> Self {
        let left = TrustVcPlace::root(left_root, left_ty);
        let right = TrustVcPlace::root(right_root, right_ty);
        Self {
            name: name.into(),
            kind: MemorySafetyFactKind::DisjointRoots,
            expr: TrustVcExpr::PlaceDisjoint { left, right },
            location: None,
        }
    }

    /// Builds a fact proving that two fields under the same owner root are
    /// disjoint because they are distinct memory projections.
    pub fn disjoint_fields(
        name: impl Into<String>,
        owner_root: impl Into<String>,
        owner_ty: TrustVcType,
        left_field: impl Into<String>,
        left_ty: TrustVcType,
        right_field: impl Into<String>,
        right_ty: TrustVcType,
    ) -> Self {
        let owner_root = owner_root.into();
        let owner_ty_for_right = owner_ty.clone();
        let left = TrustVcPlace::root(owner_root.clone(), owner_ty).field(left_field, left_ty);
        let right = TrustVcPlace::root(owner_root, owner_ty_for_right).field(right_field, right_ty);
        Self {
            name: name.into(),
            kind: MemorySafetyFactKind::DisjointFields,
            expr: TrustVcExpr::PlaceDisjoint { left, right },
            location: None,
        }
    }

    /// Builds a fact proving that two indexed places under the same owner root
    /// are disjoint when their index expressions are known to be unequal.
    pub fn disjoint_indexed_places(
        name: impl Into<String>,
        owner_root: impl Into<String>,
        owner_ty: TrustVcType,
        left_index: TrustVcExpr,
        right_index: TrustVcExpr,
        elem_ty: TrustVcType,
    ) -> Self {
        let owner_root = owner_root.into();
        let owner_ty_for_right = owner_ty.clone();
        let elem_ty_for_right = elem_ty.clone();
        let left = TrustVcPlace::root(owner_root.clone(), owner_ty).index(left_index, elem_ty);
        let right = TrustVcPlace::root(owner_root, owner_ty_for_right)
            .index(right_index, elem_ty_for_right);
        Self {
            name: name.into(),
            kind: MemorySafetyFactKind::DisjointIndexedPlaces,
            expr: TrustVcExpr::PlaceDisjoint { left, right },
            location: None,
        }
    }

    /// Attaches a source location string (file:line:col) for diagnostics.
    pub fn with_location(mut self, location: impl Into<String>) -> Self {
        self.location = Some(location.into());
        self
    }

    /// Returns the fact name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the memory-safety fact kind.
    #[must_use]
    pub const fn kind(&self) -> MemorySafetyFactKind {
        self.kind
    }

    /// Returns the typed expression that encodes this fact.
    #[must_use]
    pub const fn expr(&self) -> &TrustVcExpr {
        &self.expr
    }

    /// Returns the source location, if present.
    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    fn to_typed_obligation(&self) -> TypedProofObligation {
        let obligation = TypedProofObligation::assert(self.name.clone(), self.expr.clone());
        if let Some(location) = &self.location {
            obligation.with_location(location.clone())
        } else {
            obligation
        }
    }
}

/// Native memory-safety fact categories accepted by full verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MemorySafetyFactKind {
    /// Two root memory places have distinct ownership roots and are disjoint.
    DisjointRoots,
    /// Two fields under the same ownership root are statically disjoint.
    DisjointFields,
    /// Two indexed places under the same ownership root are disjoint because
    /// their indices are proven unequal.
    DisjointIndexedPlaces,
}

/// Evidence submitted to native full verification.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum FullVerificationEvidence {
    /// A typed verification obligation with an owned `TrustVcExpr` payload.
    TypedObligation(TypedProofObligation),
    /// A native memory-safety fact.
    MemorySafetyFact(TypedMemorySafetyFact),
    /// A raw obligation from a compatibility boundary. This is accepted only
    /// if it already carries a typed expression payload.
    RawObligation(ProofObligation),
}

impl From<TypedProofObligation> for FullVerificationEvidence {
    fn from(obligation: TypedProofObligation) -> Self {
        Self::TypedObligation(obligation)
    }
}

impl From<TypedMemorySafetyFact> for FullVerificationEvidence {
    fn from(fact: TypedMemorySafetyFact) -> Self {
        Self::MemorySafetyFact(fact)
    }
}

impl From<ProofObligation> for FullVerificationEvidence {
    fn from(obligation: ProofObligation) -> Self {
        Self::RawObligation(obligation)
    }
}

/// A request to verify a typed full-verification proof boundary.
#[derive(Debug, Clone, Default)]
#[must_use = "full-verification requests should be verified"]
pub struct FullVerificationRequest {
    context: VerificationContext,
    evidence: Vec<FullVerificationEvidence>,
}

impl FullVerificationRequest {
    /// Creates an empty full-verification request.
    #[must_use = "new requests must be verified or populated"]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a full-verification request from an existing context.
    #[must_use = "new requests must be verified or populated"]
    pub fn from_context(context: VerificationContext) -> Self {
        Self {
            context,
            evidence: Vec::new(),
        }
    }

    /// Adds a variable declaration to the verification context.
    pub fn declare_var_typed(&mut self, name: &str, ty: TrustVcType) {
        self.context.declare_var_typed(name, ty);
    }

    /// Builder variant of [`Self::declare_var_typed`].
    #[must_use = "builder methods return the updated request"]
    pub fn with_variable(mut self, variable: VariableDecl) -> Self {
        self.context.declare_var_typed_bounded(
            variable.name(),
            variable.ty().clone(),
            variable.bounded_len(),
        );
        self
    }

    /// Adds evidence to the request.
    pub fn push_evidence(&mut self, evidence: impl Into<FullVerificationEvidence>) {
        self.evidence.push(evidence.into());
    }

    /// Builder variant of [`Self::push_evidence`].
    #[must_use = "builder methods return the updated request"]
    pub fn with_evidence(mut self, evidence: impl Into<FullVerificationEvidence>) -> Self {
        self.push_evidence(evidence);
        self
    }

    /// Returns the underlying context before request evidence is applied.
    #[must_use = "borrowed verification context should be inspected"]
    pub const fn context(&self) -> &VerificationContext {
        &self.context
    }

    /// Returns the evidence items submitted with this request.
    #[must_use]
    pub fn evidence(&self) -> &[FullVerificationEvidence] {
        &self.evidence
    }

    /// Verifies the request and returns typed proof evidence on success.
    pub fn verify(self) -> Result<FullVerificationResult, FullVerificationError> {
        let mut context = self.context;
        let mut rejected = Vec::new();
        let mut memory_safety_facts = Vec::new();
        let mut verified_evidence = Vec::new();

        for evidence in self.evidence {
            match evidence {
                FullVerificationEvidence::TypedObligation(obligation) => {
                    verified_evidence
                        .push(VerifiedProofEvidence::from_typed_obligation(&obligation));
                    context.push_typed_obligation(obligation);
                }
                FullVerificationEvidence::MemorySafetyFact(fact) => {
                    verified_evidence.push(VerifiedProofEvidence::from_memory_safety_fact(&fact));
                    context.push_typed_obligation(fact.to_typed_obligation());
                    memory_safety_facts.push(fact);
                }
                FullVerificationEvidence::RawObligation(obligation) => {
                    if is_native_typed_evidence(&obligation) {
                        verified_evidence.push(VerifiedProofEvidence::from_raw_typed_obligation(
                            &obligation,
                        ));
                        context.push_obligation(obligation);
                    } else {
                        rejected.push(reject_raw_obligation(&context, &obligation));
                    }
                }
            }
        }

        if !rejected.is_empty() {
            return Err(FullVerificationError::RejectedEvidence { rejected });
        }

        let report = context.verify_with_report(VerificationReportOptions::new());
        if !matches!(report.result(), VerifyResult::Verified) {
            let result = report.result().clone();
            return Err(FullVerificationError::VerificationFailed {
                result,
                report: Box::new(report),
            });
        }

        Ok(FullVerificationResult {
            report,
            verified_evidence,
            verified_memory_safety_facts: memory_safety_facts
                .into_iter()
                .map(VerifiedMemorySafetyFact::from_typed_fact)
                .collect(),
        })
    }
}

fn is_native_typed_evidence(obligation: &ProofObligation) -> bool {
    obligation.typed_expr().is_some()
        && matches!(
            obligation.condition_origin(),
            ConditionOrigin::TypedTrustVcExpr | ConditionOrigin::PreBuiltExprCache
        )
}

fn reject_raw_obligation(
    context: &VerificationContext,
    obligation: &ProofObligation,
) -> EvidenceRejection {
    let reason = if context.variables().is_empty() {
        EvidenceRejectionReason::ContextFreeStringBackedObligation
    } else {
        EvidenceRejectionReason::StringBackedObligation
    };
    EvidenceRejection {
        obligation_name: obligation.name().to_string(),
        reason,
        condition_origin: obligation.condition_origin(),
    }
}

/// Successful native full-verification output.
#[derive(Debug, Clone)]
#[must_use = "full-verification results contain proof evidence"]
pub struct FullVerificationResult {
    report: VerificationReport,
    verified_evidence: Vec<VerifiedProofEvidence>,
    verified_memory_safety_facts: Vec<VerifiedMemorySafetyFact>,
}

impl FullVerificationResult {
    /// Returns the full solver report.
    #[must_use = "verification reports contain solver evidence"]
    pub const fn report(&self) -> &VerificationReport {
        &self.report
    }

    /// Returns verifier-owned proof summaries for every accepted evidence item.
    #[must_use = "verified proof evidence should be consumed by the adapter"]
    pub fn verified_evidence(&self) -> &[VerifiedProofEvidence] {
        &self.verified_evidence
    }

    /// Returns the verified native memory-safety facts.
    #[must_use = "verified memory-safety facts should be consumed by the adapter"]
    pub fn verified_memory_safety_facts(&self) -> &[VerifiedMemorySafetyFact] {
        &self.verified_memory_safety_facts
    }
}

/// A memory-safety fact accepted as verified typed evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct VerifiedMemorySafetyFact {
    name: String,
    kind: MemorySafetyFactKind,
    expr: TrustVcExpr,
    location: Option<String>,
    evidence_source: ProofEvidenceSource,
}

impl VerifiedMemorySafetyFact {
    fn from_typed_fact(fact: TypedMemorySafetyFact) -> Self {
        Self {
            name: fact.name,
            kind: fact.kind,
            expr: fact.expr,
            location: fact.location,
            evidence_source: ProofEvidenceSource::NativeTrustVcExpr,
        }
    }

    /// Returns the fact name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the verified memory-safety fact kind.
    #[must_use]
    pub const fn kind(&self) -> MemorySafetyFactKind {
        self.kind
    }

    /// Returns the typed expression used as proof evidence.
    #[must_use]
    pub const fn expr(&self) -> &TrustVcExpr {
        &self.expr
    }

    /// Returns the source location, if present.
    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// Returns the proof evidence source.
    #[must_use]
    pub const fn evidence_source(&self) -> ProofEvidenceSource {
        self.evidence_source
    }

    /// Returns the reasoning class for tRust proof-strength aggregation.
    #[must_use]
    pub const fn reasoning_kind(&self) -> ReasoningKind {
        ReasoningKind::Ownership
    }

    /// Returns the assurance level for tRust proof-strength aggregation.
    #[must_use]
    pub const fn assurance_level(&self) -> AssuranceLevel {
        AssuranceLevel::StaticProof
    }
}

/// One verifier-owned proof summary accepted by the native full-verification boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct VerifiedProofEvidence {
    name: String,
    obligation_kind: ObligationKind,
    location: Option<String>,
    evidence_source: ProofEvidenceSource,
    reasoning_kind: ReasoningKind,
    assurance_level: AssuranceLevel,
    condition_origin: ConditionOrigin,
}

impl VerifiedProofEvidence {
    fn from_typed_obligation(obligation: &TypedProofObligation) -> Self {
        Self {
            name: obligation.name().to_string(),
            obligation_kind: obligation.kind(),
            location: obligation.location().map(str::to_string),
            evidence_source: ProofEvidenceSource::NativeTrustVcExpr,
            reasoning_kind: ReasoningKind::Deductive,
            assurance_level: assurance_level_for_obligation_kind(obligation.kind()),
            condition_origin: ConditionOrigin::TypedTrustVcExpr,
        }
    }

    fn from_memory_safety_fact(fact: &TypedMemorySafetyFact) -> Self {
        Self {
            name: fact.name().to_string(),
            obligation_kind: ObligationKind::Assert,
            location: fact.location().map(str::to_string),
            evidence_source: ProofEvidenceSource::NativeTrustVcExpr,
            reasoning_kind: ReasoningKind::Ownership,
            assurance_level: AssuranceLevel::StaticProof,
            condition_origin: ConditionOrigin::TypedTrustVcExpr,
        }
    }

    fn from_raw_typed_obligation(obligation: &ProofObligation) -> Self {
        Self {
            name: obligation.name().to_string(),
            obligation_kind: obligation.kind(),
            location: obligation.location().map(str::to_string),
            evidence_source: ProofEvidenceSource::TypedCompatibilityBoundary,
            reasoning_kind: ReasoningKind::Deductive,
            assurance_level: assurance_level_for_obligation_kind(obligation.kind()),
            condition_origin: obligation.condition_origin(),
        }
    }

    /// Returns the accepted evidence name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the obligation kind discharged for this evidence item.
    #[must_use]
    pub const fn obligation_kind(&self) -> ObligationKind {
        self.obligation_kind
    }

    /// Returns the source location, if present.
    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    /// Returns the proof evidence source.
    #[must_use]
    pub const fn evidence_source(&self) -> ProofEvidenceSource {
        self.evidence_source
    }

    /// Returns the proof-strength reasoning class.
    #[must_use]
    pub const fn reasoning_kind(&self) -> ReasoningKind {
        self.reasoning_kind
    }

    /// Returns the assurance level contributed by this evidence.
    #[must_use]
    pub const fn assurance_level(&self) -> AssuranceLevel {
        self.assurance_level
    }

    /// Returns how the accepted condition reached the full-verification boundary.
    #[must_use]
    pub const fn condition_origin(&self) -> ConditionOrigin {
        self.condition_origin
    }
}

fn assurance_level_for_obligation_kind(kind: ObligationKind) -> AssuranceLevel {
    match kind {
        ObligationKind::Assume
        | ObligationKind::BroadcastAssume
        | ObligationKind::Requires
        | ObligationKind::LoopGuard
        | ObligationKind::PostLoopAssume => AssuranceLevel::AssumedEvidence,
        ObligationKind::Reveal | ObligationKind::Hide | ObligationKind::BroadcastUse => {
            AssuranceLevel::MetadataOnly
        }
        _ => AssuranceLevel::StaticProof,
    }
}

/// Proof-strength reasoning classes exported by TrustVc full verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ReasoningKind {
    /// A deductive SMT proof over a typed TrustVc obligation.
    Deductive,
    /// An ownership or memory-separation proof over typed place expressions.
    Ownership,
    /// Constructive evidence whose witness is carried by the typed proof term.
    Constructive,
}

/// Assurance level exported for tRust proof-strength aggregation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AssuranceLevel {
    /// Static proof evidence accepted by TrustVc after solver verification.
    StaticProof,
    /// Typed evidence accepted as an assumption, not independently proven.
    AssumedEvidence,
    /// Metadata that affects solver context but is not itself proof evidence.
    MetadataOnly,
}

/// Source of accepted proof evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ProofEvidenceSource {
    /// Evidence was supplied as native typed TrustVc IR.
    NativeTrustVcExpr,
    /// Evidence crossed a compatibility boundary but still carried typed TrustVc IR.
    TypedCompatibilityBoundary,
}

/// A rejected evidence item.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct EvidenceRejection {
    obligation_name: String,
    reason: EvidenceRejectionReason,
    condition_origin: ConditionOrigin,
}

impl EvidenceRejection {
    /// Returns the rejected obligation name.
    #[must_use]
    pub fn obligation_name(&self) -> &str {
        &self.obligation_name
    }

    /// Returns why the evidence was rejected.
    #[must_use]
    pub const fn reason(&self) -> EvidenceRejectionReason {
        self.reason
    }

    /// Returns the raw obligation condition origin.
    #[must_use]
    pub const fn condition_origin(&self) -> ConditionOrigin {
        self.condition_origin
    }
}

/// Why a proof evidence item was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum EvidenceRejectionReason {
    /// The obligation has no typed `TrustVcExpr` payload.
    StringBackedObligation,
    /// The obligation has no typed payload and no declared verification context.
    ContextFreeStringBackedObligation,
}

/// Full-verification failure.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum FullVerificationError {
    /// One or more evidence items were rejected before solver execution.
    #[error("full verification rejected non-native proof evidence")]
    RejectedEvidence {
        /// Rejected evidence items.
        rejected: Vec<EvidenceRejection>,
    },
    /// Solver execution completed but did not verify the request.
    #[error("full verification failed: {result:?}")]
    VerificationFailed {
        /// Solver result.
        result: VerifyResult,
        /// Full solver report.
        report: Box<VerificationReport>,
    },
}

impl FullVerificationError {
    /// Returns rejected evidence when this is a rejection error.
    #[must_use = "rejected evidence explains why full verification did not run"]
    pub fn rejected(&self) -> &[EvidenceRejection] {
        match self {
            Self::RejectedEvidence { rejected } => rejected,
            Self::VerificationFailed { .. } => &[],
        }
    }
}
