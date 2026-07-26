// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde::{Deserialize, Serialize};

/// Opaque clause identifier within a proof certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WireClauseId(pub u64);

/// A literal is a signed variable reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Literal(pub i64);

/// A clause is a disjunction of literals.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WireClause {
    /// Unique identifier within the certificate.
    pub id: WireClauseId,
    /// Literals in this clause.
    pub literals: Vec<Literal>,
}

/// A single resolution step in the UNSAT derivation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct WireResolutionStep {
    /// Identifier of the clause produced by this step.
    pub result_id: WireClauseId,
    /// First antecedent clause.
    pub antecedent_a: WireClauseId,
    /// Second antecedent clause.
    pub antecedent_b: WireClauseId,
    /// Pivot literal resolved upon.
    pub pivot: Literal,
    /// Resulting clause literals.
    pub result_literals: Vec<Literal>,
}

/// Classification of a theory lemma origin.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TheoryLemmaKind {
    /// Equality and Uninterpreted Functions.
    Euf,
    /// Linear Real Arithmetic.
    Lra,
    /// Non-linear Integer Arithmetic.
    Nia,
    /// Bitvector theory.
    BitVector,
    /// Array theory.
    Array,
    /// Sequence theory.
    Sequence,
    /// Other or unclassified theory.
    Other,
}

/// A clause introduced by a theory solver.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct WireTheoryLemma {
    /// Identifier assigned to this lemma clause.
    pub id: WireClauseId,
    /// Which theory produced this lemma.
    pub kind: TheoryLemmaKind,
    /// Literals of the lemma clause.
    pub literals: Vec<Literal>,
    /// Human-readable justification, when available.
    #[serde(default)]
    pub justification: Option<String>,
}

/// Provenance metadata embedded in every certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CertificateMetadata {
    /// ISO-8601 timestamp of certificate creation.
    pub timestamp: String,
    /// TrustVc version that produced the certificate.
    pub trust_vc_version: String,
    /// ay-dpll solver version used.
    pub solver_version: String,
}

/// Self-contained UNSAT proof certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct TrustVcProofCertificate {
    /// Wire format version.
    pub version: u32,
    /// SHA-256 hash of the verified source text.
    pub source_hash: [u8; 32],
    /// SHA-256 hash of the verification condition.
    pub vc_hash: [u8; 32],
    /// Resolution derivation steps.
    pub resolution_steps: Vec<WireResolutionStep>,
    /// Theory lemmas introduced by decision-procedure solvers.
    pub theory_lemmas: Vec<WireTheoryLemma>,
    /// Input clauses fed to the SAT solver.
    pub input_clauses: Vec<WireClause>,
    /// Identifier of the derived empty clause.
    pub empty_clause_id: WireClauseId,
    /// Creation metadata.
    pub metadata: CertificateMetadata,
}
