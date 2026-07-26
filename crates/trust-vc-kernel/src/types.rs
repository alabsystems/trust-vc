// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Core types for proof traces and verification results.

use serde::{Deserialize, Serialize};

/// Unique identifier for a clause within a proof trace.
pub type ClauseId = u64;

/// A literal: positive values represent the variable, negative values
/// represent the negation of the variable. Zero is not a valid literal.
pub type LiteralId = i64;

/// A disjunctive clause (a set of literals joined by OR).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Clause {
    pub id: ClauseId,
    pub literals: Vec<LiteralId>,
}

/// A single resolution step deriving a new clause from two parents
/// by resolving on a pivot variable.
///
/// The resolvent is `(parent1 \ {pivot}) | (parent2 \ {-pivot})`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolutionStep {
    pub id: ClauseId,
    pub pivot: LiteralId,
    pub parent1: ClauseId,
    pub parent2: ClauseId,
    /// The clause claimed to be produced by this step, when carried by the
    /// input artifact. Older in-memory callers may leave this absent.
    #[serde(default)]
    pub result_literals: Option<Vec<LiteralId>>,
}

/// A clause introduced by a theory solver, trusted without proof in Phase 1.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoryLemma {
    pub id: ClauseId,
    pub theory: String,
    pub clause: Clause,
}

/// A complete proof trace: input clauses, theory lemmas, resolution steps,
/// and the identity of the final (empty) clause.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofTrace {
    pub input_clauses: Vec<Clause>,
    pub resolution_steps: Vec<ResolutionStep>,
    pub theory_lemmas: Vec<TheoryLemma>,
    pub empty_clause_id: ClauseId,
}

/// Result of proof checking.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CheckResult {
    /// The proof is valid: derives the empty clause correctly.
    Valid,
    /// The proof is invalid at the given step.
    Invalid { step: ClauseId, reason: String },
}

/// Result of checking a single theory lemma.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TheoryCheckResult {
    /// The theory lemma was independently verified as valid.
    Verified,
    /// The theory lemma could not be verified and is accepted on trust.
    Trusted,
    /// The theory lemma was found to be invalid.
    Invalid { reason: String },
}

/// Aggregate statistics from theory lemma checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TheoryStats {
    /// Number of theory lemmas independently verified.
    pub verified_count: usize,
    /// Number of theory lemmas accepted on trust.
    pub trusted_count: usize,
    /// Number of theory lemmas found to be invalid.
    pub invalid_count: usize,
}

impl TheoryStats {
    /// Total number of theory lemmas processed.
    #[must_use]
    pub const fn total(&self) -> usize {
        self.verified_count + self.trusted_count + self.invalid_count
    }
}

/// Extended result of proof checking, including theory lemma statistics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CheckResultWithStats {
    /// The overall proof check result.
    pub result: CheckResult,
    /// Theory lemma checking statistics.
    pub theory_stats: TheoryStats,
}
