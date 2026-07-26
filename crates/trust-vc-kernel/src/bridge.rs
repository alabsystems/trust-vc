// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bridge from ay-dpll proof artifacts to the trust-vc-kernel proof trace.
//!
//! This module defines [`AYProofArtifact`], a simplified intermediate
//! representation of ay-dpll's UNSAT proof output. The actual conversion
//! from `ay_dpll::api::UnsatProofArtifact` to [`AYProofArtifact`] is done
//! in `trust-vc-core` — this crate has no ay dependency.
//!
//! The [`convert_ay_artifact`] function maps the intermediate representation
//! to a [`ProofTrace`] suitable for the kernel's resolution checker.

use crate::types::{Clause, ClauseId, LiteralId, ProofTrace, ResolutionStep, TheoryLemma};

// ---------------------------------------------------------------------------
// Intermediate representation (ay-dpll agnostic)
// ---------------------------------------------------------------------------

/// Classification of which theory solver produced a lemma.
///
/// Mirrors `trust_vc_kernel::format::TheoryLemmaKind` but lives in the bridge
/// to avoid coupling the conversion path to the wire format module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AYTheoryKind {
    /// Equality and uninterpreted functions.
    Euf,
    /// Linear real arithmetic.
    Lra,
    /// Non-linear integer arithmetic.
    Nia,
    /// Bitvector theory.
    BitVector,
    /// Array theory (select/store).
    Array,
    /// Sequence theory.
    Sequence,
    /// Other / unclassified.
    Other,
}

impl AYTheoryKind {
    /// Human-readable label used in [`TheoryLemma::theory`].
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Euf => "EUF",
            Self::Lra => "LRA",
            Self::Nia => "NIA",
            Self::BitVector => "BV",
            Self::Array => "Array",
            Self::Sequence => "Seq",
            Self::Other => "Other",
        }
    }
}

/// A clause in the ay proof artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYClause {
    /// Unique clause identifier assigned by ay-dpll.
    pub id: u64,
    /// Literal values (positive = variable asserted true, negative = negation).
    pub literals: Vec<i64>,
}

/// A resolution step recorded by ay-dpll.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYResolutionStep {
    /// Identifier of the clause produced by this resolution step.
    pub result_id: u64,
    /// Pivot literal resolved upon.
    pub pivot: i64,
    /// First antecedent clause.
    pub antecedent_a: u64,
    /// Second antecedent clause.
    pub antecedent_b: u64,
    /// The clause claimed to be produced by this resolution step.
    pub result_literals: Option<Vec<i64>>,
}

/// A theory lemma recorded by ay-dpll.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYTheoryLemma {
    /// Identifier assigned to this lemma clause.
    pub id: u64,
    /// Which theory solver produced this lemma.
    pub kind: AYTheoryKind,
    /// Literals in the lemma clause.
    pub literals: Vec<i64>,
}

/// Simplified intermediate representation of a ay-dpll UNSAT proof.
///
/// `trust-vc-core` constructs this from `ay_dpll::api::UnsatProofArtifact` and
/// hands it to [`convert_ay_artifact`] for verification by the kernel checker.
///
/// This type intentionally has no ay dependency — it is a plain data transfer
/// object that decouples the kernel from the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AYProofArtifact {
    /// Input clauses (the CNF encoding of the negated verification condition).
    pub input_clauses: Vec<AYClause>,
    /// Resolution steps deriving new clauses from existing ones.
    pub resolution_steps: Vec<AYResolutionStep>,
    /// Theory lemmas introduced by ay-dpll's theory solvers.
    pub theory_lemmas: Vec<AYTheoryLemma>,
    /// Identifier of the derived empty clause (the UNSAT witness).
    pub empty_clause_id: u64,
}

// ---------------------------------------------------------------------------
// Conversion
// ---------------------------------------------------------------------------

/// Convert a [`AYProofArtifact`] into the kernel's [`ProofTrace`] format.
///
/// This is a direct structural mapping — clause IDs, literal values, and
/// step ordering are preserved exactly. The resulting `ProofTrace` is
/// ready to be passed to [`crate::checker::check_proof`].
#[must_use]
pub fn convert_ay_artifact(artifact: &AYProofArtifact) -> ProofTrace {
    let input_clauses: Vec<Clause> = artifact
        .input_clauses
        .iter()
        .map(|c| Clause {
            id: c.id as ClauseId,
            literals: c.literals.iter().copied().map(|l| l as LiteralId).collect(),
        })
        .collect();

    let resolution_steps: Vec<ResolutionStep> = artifact
        .resolution_steps
        .iter()
        .map(|s| ResolutionStep {
            id: s.result_id as ClauseId,
            pivot: s.pivot as LiteralId,
            parent1: s.antecedent_a as ClauseId,
            parent2: s.antecedent_b as ClauseId,
            result_literals: s.result_literals.as_ref().map(|literals| {
                literals
                    .iter()
                    .copied()
                    .map(|lit| lit as LiteralId)
                    .collect()
            }),
        })
        .collect();

    let theory_lemmas: Vec<TheoryLemma> = artifact
        .theory_lemmas
        .iter()
        .map(|tl| TheoryLemma {
            id: tl.id as ClauseId,
            theory: tl.kind.as_str().to_string(),
            clause: Clause {
                id: tl.id as ClauseId,
                literals: tl
                    .literals
                    .iter()
                    .copied()
                    .map(|l| l as LiteralId)
                    .collect(),
            },
        })
        .collect();

    ProofTrace {
        input_clauses,
        resolution_steps,
        theory_lemmas,
        empty_clause_id: artifact.empty_clause_id as ClauseId,
    }
}

#[cfg(test)]
mod tests;
