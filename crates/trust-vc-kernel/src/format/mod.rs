// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof certificate wire format — compact binary and JSON debug views.
//!
//! [`TrustVcProofCertificate`] is the self-contained artifact that captures a
//! full UNSAT resolution trace from ay-dpll. The certificate includes input
//! clauses, resolution steps, theory lemmas, and provenance metadata
//! sufficient to independently verify the proof without re-running the solver.

mod codec;
mod types;

pub use codec::{sha256, FormatError};
pub use types::{
    CertificateMetadata, Literal, TheoryLemmaKind, TrustVcProofCertificate, WireClause,
    WireClauseId, WireResolutionStep, WireTheoryLemma,
};

/// Current certificate schema version.
pub const CERTIFICATE_VERSION: u32 = 1;

/// Magic bytes that prefix every binary certificate: `CPRF`.
pub const BINARY_MAGIC: [u8; 4] = *b"CPRF";

pub(crate) const BINARY_FORMAT_VERSION: u8 = 1;
pub(crate) const MIN_BINARY_HEADER_LEN: usize = BINARY_MAGIC.len() + std::mem::size_of::<u8>() + 1;

#[cfg(test)]
mod tests;
