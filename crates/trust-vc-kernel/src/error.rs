// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Error types for the proof kernel.

use crate::types::{ClauseId, LiteralId};

/// Errors that can occur during proof checking.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum KernelError {
    /// A resolution step references a clause ID that does not exist.
    #[error("step {step}: references unknown clause {clause_id}")]
    MissingClause { step: ClauseId, clause_id: ClauseId },

    /// The pivot literal does not appear in a parent clause.
    #[error("step {step}: pivot {pivot} not found in parent {parent}")]
    PivotNotInParent {
        step: ClauseId,
        pivot: i64,
        parent: ClauseId,
    },

    /// The empty clause ID does not correspond to any derived clause.
    #[error("empty clause ID {0} not found in proof")]
    EmptyClauseNotFound(ClauseId),

    /// The clause designated as empty still contains literals.
    #[error("clause {id} designated as empty but contains {count} literal(s)")]
    FinalClauseNotEmpty { id: ClauseId, count: usize },

    /// The declared resolvent clause does not match the derived clause.
    #[error(
        "step {step}: declared resolvent {expected:?} does not match derived clause {actual:?}"
    )]
    ResultClauseMismatch {
        step: ClauseId,
        expected: Vec<LiteralId>,
        actual: Vec<LiteralId>,
    },

    /// Duplicate clause IDs detected in the proof trace.
    #[error("duplicate clause ID {0}")]
    DuplicateClauseId(ClauseId),

    /// The proof certificate has no clauses, no resolution steps, and no
    /// theory lemmas.
    #[error("empty proof certificate")]
    EmptyCertificate,

    /// The certificate version is unsupported.
    #[error("unsupported certificate version {found} (expected ≤ {expected})")]
    UnsupportedVersion { found: u32, expected: u32 },

    /// The proof exceeds the configured maximum size.
    #[error("proof too large: {actual} steps exceeds limit of {max}")]
    ProofTooLarge { actual: usize, max: usize },

    /// Strict mode rejects proofs that contain trusted (unverified) theory lemmas.
    #[error("strict mode: {trusted_count} theory lemma(s) accepted on trust")]
    StrictUntrustedTheory { trusted_count: usize },

    /// An error in the export stage.
    #[error("export error: {0}")]
    Export(String),

    /// An error in certificate format parsing.
    #[error("format error: {0}")]
    Format(String),
}

impl From<crate::export::ExportError> for KernelError {
    fn from(e: crate::export::ExportError) -> Self {
        KernelError::Export(e.to_string())
    }
}
