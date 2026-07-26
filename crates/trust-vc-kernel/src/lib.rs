// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! TrustVc kernel: proof certificate wire format and verification kernel.
//!
//! This crate provides three complementary pieces:
//!
//! 1. **Wire format** ([`format`]): The serializable [`TrustVcProofCertificate`]
//!    that captures a full resolution trace from ay-dpll.
//!
//! 2. **Proof checker** ([`checker`]): A propositional resolution checker that
//!    verifies proof traces derive the empty clause from input clauses.
//!
//! 3. **Theory checker** ([`theory_check`]): Structural validation of theory
//!    lemmas for EUF (transitivity/congruence) and LRA (Farkas certificates).
//!    Unsupported theories (NIA, BV, Array, Seq) are accepted on trust.

// Trust bootstrap applies rustc-internal warning policy to this standalone
// verifier crate; trust_vc keeps public APIs for downstream verifier consumers and
// intentionally uses std hashes/non-query iteration outside rustc query providers.
#![allow(
    rustc::default_hash_types,
    rustc::potential_query_instability,
    unreachable_pub
)]

/// Bridge from ay-dpll proof artifacts to the kernel proof trace.
pub mod bridge;
/// Certificate chain validation and incremental chain building.
pub mod certificate_chain;
/// Propositional resolution proof checker.
pub mod checker;
/// Dead-branch elimination to produce minimal proof traces.
pub mod compaction;
/// Error types for proof checking.
pub mod error;
/// Multi-format export (JSON, binary, Alethe, DRAT).
pub mod export;
/// Wire format types for serializable proof certificates.
pub mod format;
/// Lean5 proof term export.
pub mod lean_export;
/// Offline Lean5 syntax validation for generated proof terms.
pub mod lean_syntax_check;
/// Text parser and formatter for ay-dpll UNSAT proof traces.
pub mod parse;
/// End-to-end pipeline wiring checker, theory checker, compaction, and export.
pub mod pipeline;
/// Advanced proof compression via subproof merging and redundancy elimination.
pub mod proof_compression;
/// Proof differencing for incremental checking and evolution tracking.
pub mod proof_diff;
/// Step-by-step proof re-execution for independent validation.
pub mod proof_replay;
/// Complexity analysis, resolution depth/width metrics, and quality scoring.
pub mod proof_statistics;
/// Theory-specific lemma verification (EUF, LRA).
pub mod theory_check;
/// Core types for proof traces and verification results.
pub mod types;

/// Encode raw bytes as a lowercase hex string.
pub(crate) fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// Re-export checker API
pub use checker::{check_proof, check_proof_with_theory};
pub use error::KernelError;
pub use parse::{format_proof_trace, parse_proof_trace, ParseError};
pub use types::{
    CheckResult, CheckResultWithStats, Clause, ClauseId, LiteralId, ProofTrace, ResolutionStep,
    TheoryCheckResult, TheoryLemma, TheoryStats,
};

// Re-export theory check API
pub use theory_check::check_theory_lemma;

// Re-export Lean5 export API
pub use lean_export::{export_lean5, LeanExportError};

// Re-export Lean5 syntax checker API
pub use lean_syntax_check::{is_valid_lean_ident, validate_lean_syntax, SyntaxError};

// Re-export wire format API
pub use format::{
    sha256, CertificateMetadata, FormatError, TheoryLemmaKind, TrustVcProofCertificate,
    BINARY_MAGIC, CERTIFICATE_VERSION,
};

// Re-export bridge API
pub use bridge::{
    convert_ay_artifact, AYClause, AYProofArtifact, AYResolutionStep, AYTheoryKind, AYTheoryLemma,
};

#[cfg(test)]
mod test_utils;

#[cfg(test)]
mod bench_tests;

#[cfg(test)]
mod tests;
