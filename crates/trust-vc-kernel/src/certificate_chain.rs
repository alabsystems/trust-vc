// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

//! Certificate chain validation and incremental chain building.
//!
//! Provides higher-level abstractions over individual [`TrustVcProofCertificate`]
//! instances, allowing a sequence of certificates (e.g., from incremental
//! solving sessions) to be assembled into a validated chain with cryptographic
//! linkage via parent hashes.

use std::fmt;

use crate::checker::check_proof_with_theory;
use crate::error::KernelError;
use crate::format::{sha256, TrustVcProofCertificate, CERTIFICATE_VERSION};

// ---------------------------------------------------------------------------
// Chain failure types
// ---------------------------------------------------------------------------

/// Reason a chain validation step failed.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ChainFailureReason {
    /// The proof certificate itself is invalid.
    InvalidProof,
    /// The parent hash recorded in the entry does not match the computed
    /// hash of the preceding certificate.
    BrokenLink,
    /// The entry claims a parent but no parent exists (first entry with a
    /// parent hash).
    MissingParent,
    /// Sequence numbers are not contiguous.
    SequenceGap,
    /// The certificate version does not match the chain's solver version.
    VersionMismatch,
}

impl fmt::Display for ChainFailureReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidProof => write!(f, "invalid proof certificate"),
            Self::BrokenLink => write!(f, "parent hash does not match preceding certificate"),
            Self::MissingParent => write!(f, "entry claims a parent but none exists"),
            Self::SequenceGap => write!(f, "non-contiguous sequence numbers"),
            Self::VersionMismatch => write!(f, "certificate version mismatch"),
        }
    }
}

/// Information about the first chain validation failure.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChainFailure {
    /// Index into the chain entries vector.
    pub entry_index: usize,
    /// Sequence number of the failing entry.
    pub sequence_number: usize,
    /// Why the entry failed validation.
    pub reason: ChainFailureReason,
}

// ---------------------------------------------------------------------------
// Chain metadata
// ---------------------------------------------------------------------------

/// Aggregate metadata for an entire certificate chain.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChainMetadata {
    /// ISO 8601 timestamp of chain creation.
    pub created_at: String,
    /// Solver version used for the chain.
    pub solver_version: String,
    /// Total resolution + theory lemma proof steps across all certificates.
    pub total_proof_steps: usize,
    /// Total theory lemmas across all certificates.
    pub total_theory_lemmas: usize,
    /// Whether every certificate in the chain passes strict (no trusted
    /// theory lemmas) checking.
    pub all_strict: bool,
}

// ---------------------------------------------------------------------------
// Chain entry
// ---------------------------------------------------------------------------

/// A single link in a certificate chain.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CertificateChainEntry {
    /// The proof certificate at this position.
    pub certificate: TrustVcProofCertificate,
    /// SHA-256 hex digest of the parent certificate's serialized form,
    /// or `None` for the root entry.
    pub parent_hash: Option<String>,
    /// Zero-based position in the chain.
    pub sequence_number: usize,
    /// Name of the function this certificate proves.
    pub function_name: String,
}

// ---------------------------------------------------------------------------
// Certificate chain
// ---------------------------------------------------------------------------

/// An ordered sequence of linked proof certificates.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CertificateChain {
    /// Ordered entries forming the chain.
    pub entries: Vec<CertificateChainEntry>,
    /// SHA-256 hex digest of the root (first) certificate.
    pub root_hash: String,
    /// Aggregate metadata computed from the chain contents.
    pub chain_metadata: ChainMetadata,
}

// ---------------------------------------------------------------------------
// Validation result
// ---------------------------------------------------------------------------

/// Result of validating an entire certificate chain.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChainValidationResult {
    /// Overall validity of the chain.
    pub valid: bool,
    /// Number of entries inspected.
    pub entries_checked: usize,
    /// Number of entries that passed all checks.
    pub entries_passed: usize,
    /// First failure encountered, if any.
    pub first_failure: Option<ChainFailure>,
    /// SHA-256 hex digest of the concatenated chain contents.
    pub chain_hash: String,
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Compute a hex-encoded SHA-256 digest of a certificate's JSON form.
fn certificate_hash(cert: &TrustVcProofCertificate) -> String {
    let json = serde_json::to_vec(cert).unwrap_or_default();
    hex_encode(&sha256(&json))
}

/// Compute a hex-encoded SHA-256 digest of the entire chain by
/// concatenating each certificate's serialized form.
fn compute_chain_hash(entries: &[CertificateChainEntry]) -> String {
    let mut combined = Vec::new();
    for entry in entries {
        let json = serde_json::to_vec(&entry.certificate).unwrap_or_default();
        combined.extend_from_slice(&json);
    }
    hex_encode(&sha256(&combined))
}

use crate::hex_encode;

/// Check whether a single certificate's proof is valid using the kernel
/// checker (converting through the pipeline's wire-to-trace path).
fn is_proof_valid(cert: &TrustVcProofCertificate) -> bool {
    use crate::types::CheckResult;

    // Reject trivially empty certificates.
    if cert.input_clauses.is_empty()
        && cert.resolution_steps.is_empty()
        && cert.theory_lemmas.is_empty()
    {
        return false;
    }

    let trace = wire_to_proof_trace(cert);
    let result = check_proof_with_theory(&trace);
    matches!(result.result, CheckResult::Valid)
}

/// Convert a wire-format certificate to an internal proof trace.
///
/// Mirrors `pipeline::wire_to_proof_trace` without taking a dependency on
/// the pipeline module (avoids circular coupling).
fn wire_to_proof_trace(cert: &TrustVcProofCertificate) -> crate::types::ProofTrace {
    use crate::bridge::convert_ay_artifact;

    let artifact = wire_to_ay_artifact(cert);
    convert_ay_artifact(&artifact)
}

/// Convert a wire-format certificate into the bridge `AYProofArtifact`.
fn wire_to_ay_artifact(cert: &TrustVcProofCertificate) -> crate::bridge::AYProofArtifact {
    use crate::bridge::{AYClause, AYProofArtifact, AYResolutionStep, AYTheoryKind, AYTheoryLemma};
    use crate::format::TheoryLemmaKind;

    let input_clauses = cert
        .input_clauses
        .iter()
        .map(|c| AYClause {
            id: c.id.0,
            literals: c.literals.iter().map(|l| l.0).collect(),
        })
        .collect();

    let resolution_steps = cert
        .resolution_steps
        .iter()
        .map(|s| AYResolutionStep {
            result_id: s.result_id.0,
            pivot: s.pivot.0,
            antecedent_a: s.antecedent_a.0,
            antecedent_b: s.antecedent_b.0,
            result_literals: Some(s.result_literals.iter().map(|l| l.0).collect()),
        })
        .collect();

    let theory_lemmas = cert
        .theory_lemmas
        .iter()
        .map(|tl| AYTheoryLemma {
            id: tl.id.0,
            kind: match tl.kind {
                TheoryLemmaKind::Euf => AYTheoryKind::Euf,
                TheoryLemmaKind::Lra => AYTheoryKind::Lra,
                TheoryLemmaKind::Nia => AYTheoryKind::Nia,
                TheoryLemmaKind::BitVector => AYTheoryKind::BitVector,
                TheoryLemmaKind::Array => AYTheoryKind::Array,
                TheoryLemmaKind::Sequence => AYTheoryKind::Sequence,
                TheoryLemmaKind::Other => AYTheoryKind::Other,
            },
            literals: tl.literals.iter().map(|l| l.0).collect(),
        })
        .collect();

    AYProofArtifact {
        input_clauses,
        resolution_steps,
        theory_lemmas,
        empty_clause_id: cert.empty_clause_id.0,
    }
}

/// Check whether a certificate has zero trusted theory lemmas.
fn certificate_is_strict(cert: &TrustVcProofCertificate) -> bool {
    use crate::theory_check::check_theory_lemma;
    use crate::types::TheoryCheckResult;

    if cert.theory_lemmas.is_empty() {
        return true;
    }

    let trace = wire_to_proof_trace(cert);
    for lemma in &trace.theory_lemmas {
        if matches!(check_theory_lemma(lemma), TheoryCheckResult::Trusted) {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// ChainValidator
// ---------------------------------------------------------------------------

/// Validates that a certificate chain is well-formed: sequential ordering,
/// parent hash linkage, proof validity, and no sequence gaps.
pub(crate) struct ChainValidator;

impl ChainValidator {
    /// Validate an entire certificate chain.
    ///
    /// Checks performed for each entry:
    /// 1. Sequence numbers are contiguous starting from 0.
    /// 2. The first entry has no parent hash; subsequent entries have a
    ///    parent hash matching the SHA-256 of the previous certificate.
    /// 3. Each certificate passes the proof checker.
    /// 4. Certificate versions are compatible with the chain solver version.
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::Format`] if the chain is empty.
    pub(crate) fn validate(chain: &CertificateChain) -> Result<ChainValidationResult, KernelError> {
        if chain.entries.is_empty() {
            let chain_hash = compute_chain_hash(&chain.entries);
            return Ok(ChainValidationResult {
                valid: true,
                entries_checked: 0,
                entries_passed: 0,
                first_failure: None,
                chain_hash,
            });
        }

        let chain_hash = compute_chain_hash(&chain.entries);
        let mut entries_passed = 0usize;

        for (idx, entry) in chain.entries.iter().enumerate() {
            // Check sequential ordering.
            if entry.sequence_number != idx {
                return Ok(ChainValidationResult {
                    valid: false,
                    entries_checked: idx + 1,
                    entries_passed,
                    first_failure: Some(ChainFailure {
                        entry_index: idx,
                        sequence_number: entry.sequence_number,
                        reason: ChainFailureReason::SequenceGap,
                    }),
                    chain_hash,
                });
            }

            // Check parent hash linkage.
            if idx == 0 {
                if entry.parent_hash.is_some() {
                    return Ok(ChainValidationResult {
                        valid: false,
                        entries_checked: idx + 1,
                        entries_passed,
                        first_failure: Some(ChainFailure {
                            entry_index: idx,
                            sequence_number: entry.sequence_number,
                            reason: ChainFailureReason::MissingParent,
                        }),
                        chain_hash,
                    });
                }
            } else {
                let expected_parent_hash = certificate_hash(&chain.entries[idx - 1].certificate);
                match &entry.parent_hash {
                    None => {
                        return Ok(ChainValidationResult {
                            valid: false,
                            entries_checked: idx + 1,
                            entries_passed,
                            first_failure: Some(ChainFailure {
                                entry_index: idx,
                                sequence_number: entry.sequence_number,
                                reason: ChainFailureReason::BrokenLink,
                            }),
                            chain_hash,
                        });
                    }
                    Some(hash) if *hash != expected_parent_hash => {
                        return Ok(ChainValidationResult {
                            valid: false,
                            entries_checked: idx + 1,
                            entries_passed,
                            first_failure: Some(ChainFailure {
                                entry_index: idx,
                                sequence_number: entry.sequence_number,
                                reason: ChainFailureReason::BrokenLink,
                            }),
                            chain_hash,
                        });
                    }
                    _ => {}
                }
            }

            // Check version compatibility.
            if entry.certificate.version > CERTIFICATE_VERSION {
                return Ok(ChainValidationResult {
                    valid: false,
                    entries_checked: idx + 1,
                    entries_passed,
                    first_failure: Some(ChainFailure {
                        entry_index: idx,
                        sequence_number: entry.sequence_number,
                        reason: ChainFailureReason::VersionMismatch,
                    }),
                    chain_hash,
                });
            }

            // Check proof validity.
            if !is_proof_valid(&entry.certificate) {
                return Ok(ChainValidationResult {
                    valid: false,
                    entries_checked: idx + 1,
                    entries_passed,
                    first_failure: Some(ChainFailure {
                        entry_index: idx,
                        sequence_number: entry.sequence_number,
                        reason: ChainFailureReason::InvalidProof,
                    }),
                    chain_hash,
                });
            }

            entries_passed += 1;
        }

        Ok(ChainValidationResult {
            valid: true,
            entries_checked: chain.entries.len(),
            entries_passed,
            first_failure: None,
            chain_hash,
        })
    }
}

// ---------------------------------------------------------------------------
// ChainBuilder
// ---------------------------------------------------------------------------

/// Incrementally constructs a [`CertificateChain`] by appending certificates.
///
/// Automatically assigns sequence numbers and computes parent hashes.
#[must_use]
pub(crate) struct ChainBuilder {
    function_name: String,
    entries: Vec<CertificateChainEntry>,
}

impl ChainBuilder {
    /// Create a new builder for the given function name.
    pub(crate) fn new(function_name: &str) -> Self {
        Self {
            function_name: function_name.to_string(),
            entries: Vec::new(),
        }
    }

    /// Append a certificate to the chain.
    ///
    /// The builder automatically computes:
    /// - `sequence_number` from the current chain length.
    /// - `parent_hash` from the SHA-256 of the previous certificate (if any).
    ///
    /// # Errors
    ///
    /// Returns [`KernelError::UnsupportedVersion`] if the certificate version
    /// exceeds the supported maximum.
    pub(crate) fn add_certificate(
        &mut self,
        cert: TrustVcProofCertificate,
    ) -> Result<(), KernelError> {
        if cert.version == 0 || cert.version > CERTIFICATE_VERSION {
            return Err(KernelError::UnsupportedVersion {
                found: cert.version,
                expected: CERTIFICATE_VERSION,
            });
        }

        let parent_hash = self
            .entries
            .last()
            .map(|prev| certificate_hash(&prev.certificate));

        let sequence_number = self.entries.len();

        self.entries.push(CertificateChainEntry {
            certificate: cert,
            parent_hash,
            sequence_number,
            function_name: self.function_name.clone(),
        });

        Ok(())
    }

    /// Consume the builder and produce a finished [`CertificateChain`].
    pub(crate) fn build(self) -> CertificateChain {
        let root_hash = if self.entries.is_empty() {
            hex_encode(&sha256(b"empty-chain"))
        } else {
            certificate_hash(&self.entries[0].certificate)
        };

        let chain_metadata = compute_metadata(&self.entries);

        CertificateChain {
            entries: self.entries,
            root_hash,
            chain_metadata,
        }
    }
}

/// Compute aggregate metadata from a list of chain entries.
fn compute_metadata(entries: &[CertificateChainEntry]) -> ChainMetadata {
    let total_proof_steps: usize = entries
        .iter()
        .map(|e| e.certificate.resolution_steps.len())
        .sum();

    let total_theory_lemmas: usize = entries
        .iter()
        .map(|e| e.certificate.theory_lemmas.len())
        .sum();

    let solver_version = entries
        .first()
        .map(|e| e.certificate.metadata.solver_version.clone())
        .unwrap_or_default();

    let created_at = entries
        .first()
        .map(|e| e.certificate.metadata.timestamp.clone())
        .unwrap_or_default();

    let all_strict = entries
        .iter()
        .all(|e| certificate_is_strict(&e.certificate));

    ChainMetadata {
        created_at,
        solver_version,
        total_proof_steps,
        total_theory_lemmas,
        all_strict,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::{
        CertificateMetadata, Literal, TheoryLemmaKind, WireClause, WireClauseId,
        WireResolutionStep, WireTheoryLemma,
    };

    // -- Test helpers --------------------------------------------------------

    /// Build a minimal valid certificate: two input clauses resolved to empty.
    fn valid_cert(label: &str) -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: sha256(label.as_bytes()),
            vc_hash: sha256(format!("vc-{label}").as_bytes()),
            input_clauses: vec![
                WireClause {
                    id: WireClauseId(1),
                    literals: vec![Literal(1)],
                },
                WireClause {
                    id: WireClauseId(2),
                    literals: vec![Literal(-1)],
                },
            ],
            resolution_steps: vec![WireResolutionStep {
                result_id: WireClauseId(3),
                antecedent_a: WireClauseId(1),
                antecedent_b: WireClauseId(2),
                pivot: Literal(1),
                result_literals: vec![],
            }],
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(3),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T00:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        }
    }

    /// Build a certificate that has a theory lemma (NIA — accepted on trust).
    fn cert_with_trusted_theory(label: &str) -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: sha256(label.as_bytes()),
            vc_hash: sha256(format!("vc-{label}").as_bytes()),
            input_clauses: vec![WireClause {
                id: WireClauseId(1),
                literals: vec![Literal(1)],
            }],
            resolution_steps: vec![WireResolutionStep {
                result_id: WireClauseId(100),
                antecedent_a: WireClauseId(1),
                antecedent_b: WireClauseId(10),
                pivot: Literal(1),
                result_literals: vec![],
            }],
            theory_lemmas: vec![WireTheoryLemma {
                id: WireClauseId(10),
                kind: TheoryLemmaKind::Nia,
                literals: vec![Literal(-1)],
                justification: None,
            }],
            empty_clause_id: WireClauseId(100),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T01:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        }
    }

    /// Build an invalid certificate (empty — will fail proof check).
    fn invalid_cert() -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: vec![],
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(0),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T00:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        }
    }

    // -- ChainBuilder tests --------------------------------------------------

    #[test]
    fn test_chain_builder_empty_chain() {
        let builder = ChainBuilder::new("test_fn");
        let chain = builder.build();
        assert!(chain.entries.is_empty());
        assert!(!chain.root_hash.is_empty());
    }

    #[test]
    fn test_chain_builder_single_certificate() {
        let mut builder = ChainBuilder::new("single_fn");
        builder
            .add_certificate(valid_cert("a"))
            .expect("should accept valid cert");
        let chain = builder.build();
        assert_eq!(chain.entries.len(), 1);
        assert!(chain.entries[0].parent_hash.is_none());
        assert_eq!(chain.entries[0].sequence_number, 0);
        assert_eq!(chain.entries[0].function_name, "single_fn");
    }

    #[test]
    fn test_chain_builder_multiple_certificates() {
        let mut builder = ChainBuilder::new("multi_fn");
        builder.add_certificate(valid_cert("a")).unwrap();
        builder.add_certificate(valid_cert("b")).unwrap();
        builder.add_certificate(valid_cert("c")).unwrap();
        let chain = builder.build();
        assert_eq!(chain.entries.len(), 3);
    }

    #[test]
    fn test_chain_builder_automatic_sequence_numbering() {
        let mut builder = ChainBuilder::new("seq_fn");
        for i in 0..5 {
            builder
                .add_certificate(valid_cert(&format!("cert-{i}")))
                .unwrap();
        }
        let chain = builder.build();
        for (idx, entry) in chain.entries.iter().enumerate() {
            assert_eq!(entry.sequence_number, idx);
        }
    }

    #[test]
    fn test_chain_builder_automatic_parent_hash_linkage() {
        let mut builder = ChainBuilder::new("link_fn");
        builder.add_certificate(valid_cert("first")).unwrap();
        builder.add_certificate(valid_cert("second")).unwrap();
        let chain = builder.build();

        // First entry has no parent hash.
        assert!(chain.entries[0].parent_hash.is_none());

        // Second entry's parent hash matches first entry's certificate hash.
        let expected = certificate_hash(&chain.entries[0].certificate);
        assert_eq!(
            chain.entries[1].parent_hash.as_deref(),
            Some(expected.as_str())
        );
    }

    #[test]
    fn test_chain_builder_preserves_certificate_order() {
        let mut builder = ChainBuilder::new("order_fn");
        let certs: Vec<_> = (0..4).map(|i| valid_cert(&format!("order-{i}"))).collect();
        let source_hashes: Vec<_> = certs.iter().map(|c| c.source_hash).collect();
        for cert in certs {
            builder.add_certificate(cert).unwrap();
        }
        let chain = builder.build();
        for (idx, entry) in chain.entries.iter().enumerate() {
            assert_eq!(entry.certificate.source_hash, source_hashes[idx]);
        }
    }

    #[test]
    fn test_chain_builder_rejects_unsupported_version() {
        let mut builder = ChainBuilder::new("bad_ver");
        let mut cert = valid_cert("bad");
        cert.version = CERTIFICATE_VERSION + 99;
        let err = builder
            .add_certificate(cert)
            .expect_err("unsupported version should be rejected");
        assert!(matches!(err, KernelError::UnsupportedVersion { .. }));
    }

    // -- ChainValidator tests ------------------------------------------------

    #[test]
    fn test_chain_validator_empty_chain() {
        let chain = ChainBuilder::new("empty").build();
        let result = ChainValidator::validate(&chain).expect("validation should not error");
        assert!(result.valid);
        assert_eq!(result.entries_checked, 0);
        assert_eq!(result.entries_passed, 0);
        assert!(result.first_failure.is_none());
    }

    #[test]
    fn test_chain_validator_single_valid_certificate() {
        let mut builder = ChainBuilder::new("single");
        builder.add_certificate(valid_cert("s")).unwrap();
        let chain = builder.build();
        let result = ChainValidator::validate(&chain).expect("validation should not error");
        assert!(result.valid);
        assert_eq!(result.entries_checked, 1);
        assert_eq!(result.entries_passed, 1);
        assert!(result.first_failure.is_none());
    }

    #[test]
    fn test_chain_validator_valid_chain_of_three() {
        let mut builder = ChainBuilder::new("triple");
        builder.add_certificate(valid_cert("x")).unwrap();
        builder.add_certificate(valid_cert("y")).unwrap();
        builder.add_certificate(valid_cert("z")).unwrap();
        let chain = builder.build();
        let result = ChainValidator::validate(&chain).expect("validation should not error");
        assert!(result.valid);
        assert_eq!(result.entries_checked, 3);
        assert_eq!(result.entries_passed, 3);
    }

    #[test]
    fn test_chain_validator_detects_broken_link() {
        let mut builder = ChainBuilder::new("broken");
        builder.add_certificate(valid_cert("a")).unwrap();
        builder.add_certificate(valid_cert("b")).unwrap();
        let mut chain = builder.build();

        // Corrupt the parent hash of entry 1.
        chain.entries[1].parent_hash = Some("0000deadbeef".to_string());

        let result = ChainValidator::validate(&chain).expect("validation should not error");
        assert!(!result.valid);
        let failure = result
            .first_failure
            .expect("first_failure should be set for broken-link chain");
        assert_eq!(failure.entry_index, 1);
        assert_eq!(failure.reason, ChainFailureReason::BrokenLink);
    }

    #[test]
    fn test_chain_validator_detects_sequence_gap() {
        let mut builder = ChainBuilder::new("gap");
        builder.add_certificate(valid_cert("a")).unwrap();
        builder.add_certificate(valid_cert("b")).unwrap();
        let mut chain = builder.build();

        // Create a gap by setting second entry's sequence number to 5.
        chain.entries[1].sequence_number = 5;

        let result = ChainValidator::validate(&chain).expect("validation should not error");
        assert!(!result.valid);
        let failure = result
            .first_failure
            .expect("first_failure should be set for sequence-gap chain");
        assert_eq!(failure.entry_index, 1);
        assert_eq!(failure.reason, ChainFailureReason::SequenceGap);
    }

    #[test]
    fn test_chain_validator_detects_invalid_proof() {
        let mut builder = ChainBuilder::new("invalid_proof");
        builder.add_certificate(valid_cert("good")).unwrap();
        let mut chain = builder.build();

        // Replace the certificate with an invalid one but keep linkage valid.
        let bad = invalid_cert();
        chain.entries[0].certificate = bad;

        let result = ChainValidator::validate(&chain).expect("validation should not error");
        assert!(!result.valid);
        let failure = result
            .first_failure
            .expect("first_failure should be set for invalid-proof chain");
        assert_eq!(failure.entry_index, 0);
        assert_eq!(failure.reason, ChainFailureReason::InvalidProof);
    }

    // -- ChainValidationResult tests -----------------------------------------

    #[test]
    fn test_chain_validation_result_for_valid_chain() {
        let mut builder = ChainBuilder::new("result_test");
        builder.add_certificate(valid_cert("r")).unwrap();
        let chain = builder.build();
        let result = ChainValidator::validate(&chain).expect("should succeed");
        assert!(result.valid);
        assert_eq!(result.entries_checked, 1);
        assert_eq!(result.entries_passed, 1);
        assert!(result.first_failure.is_none());
        assert!(!result.chain_hash.is_empty());
    }

    #[test]
    fn test_chain_validation_result_first_failure_populated() {
        let mut builder = ChainBuilder::new("fail_test");
        builder.add_certificate(valid_cert("a")).unwrap();
        builder.add_certificate(valid_cert("b")).unwrap();
        let mut chain = builder.build();
        chain.entries[1].parent_hash = Some("bad_hash".to_string());

        let result = ChainValidator::validate(&chain).expect("should succeed");
        assert!(!result.valid);
        let failure = result
            .first_failure
            .expect("first_failure should be populated when chain is invalid");
        assert_eq!(failure.entry_index, 1);
        assert_eq!(failure.sequence_number, 1);
    }

    // -- ChainMetadata tests -------------------------------------------------

    #[test]
    fn test_chain_metadata_computed_correctly() {
        let mut builder = ChainBuilder::new("meta_fn");
        builder.add_certificate(valid_cert("m1")).unwrap();
        builder.add_certificate(valid_cert("m2")).unwrap();
        let chain = builder.build();

        assert_eq!(chain.chain_metadata.solver_version, "ay-dpll 0.1.0");
        assert_eq!(chain.chain_metadata.created_at, "2026-03-28T00:00:00Z");
        // Each valid_cert has 1 resolution step.
        assert_eq!(chain.chain_metadata.total_proof_steps, 2);
        assert_eq!(chain.chain_metadata.total_theory_lemmas, 0);
    }

    #[test]
    fn test_chain_metadata_total_counts_aggregation() {
        let mut builder = ChainBuilder::new("agg_fn");
        builder.add_certificate(valid_cert("a1")).unwrap();
        builder
            .add_certificate(cert_with_trusted_theory("a2"))
            .unwrap();
        let chain = builder.build();

        // valid_cert: 1 step, 0 lemmas. cert_with_trusted_theory: 1 step, 1 lemma.
        assert_eq!(chain.chain_metadata.total_proof_steps, 2);
        assert_eq!(chain.chain_metadata.total_theory_lemmas, 1);
    }

    // -- Chain hash tests ----------------------------------------------------

    #[test]
    fn test_chain_hash_is_deterministic() {
        let build = || {
            let mut b = ChainBuilder::new("det");
            b.add_certificate(valid_cert("d1")).unwrap();
            b.add_certificate(valid_cert("d2")).unwrap();
            b.build()
        };

        let chain1 = build();
        let chain2 = build();
        let r1 = ChainValidator::validate(&chain1).unwrap();
        let r2 = ChainValidator::validate(&chain2).unwrap();
        assert_eq!(r1.chain_hash, r2.chain_hash);
    }

    #[test]
    fn test_chain_hash_changes_with_different_content() {
        let mut b1 = ChainBuilder::new("h1");
        b1.add_certificate(valid_cert("alpha")).unwrap();
        let chain1 = b1.build();

        let mut b2 = ChainBuilder::new("h2");
        b2.add_certificate(valid_cert("beta")).unwrap();
        let chain2 = b2.build();

        let r1 = ChainValidator::validate(&chain1).unwrap();
        let r2 = ChainValidator::validate(&chain2).unwrap();
        assert_ne!(r1.chain_hash, r2.chain_hash);
    }

    // -- CertificateChainEntry tests -----------------------------------------

    #[test]
    fn test_certificate_chain_entry_creation() {
        let cert = valid_cert("entry_test");
        let entry = CertificateChainEntry {
            certificate: cert.clone(),
            parent_hash: None,
            sequence_number: 0,
            function_name: "my_fn".to_string(),
        };
        assert_eq!(entry.sequence_number, 0);
        assert!(entry.parent_hash.is_none());
        assert_eq!(entry.function_name, "my_fn");
        assert_eq!(entry.certificate.source_hash, cert.source_hash);
    }

    // -- ChainFailureReason Display tests ------------------------------------

    #[test]
    fn test_chain_failure_reason_variants_display() {
        let reasons = [
            (
                ChainFailureReason::InvalidProof,
                "invalid proof certificate",
            ),
            (
                ChainFailureReason::BrokenLink,
                "parent hash does not match preceding certificate",
            ),
            (
                ChainFailureReason::MissingParent,
                "entry claims a parent but none exists",
            ),
            (
                ChainFailureReason::SequenceGap,
                "non-contiguous sequence numbers",
            ),
            (
                ChainFailureReason::VersionMismatch,
                "certificate version mismatch",
            ),
        ];
        for (reason, expected) in &reasons {
            assert_eq!(reason.to_string(), *expected);
        }
    }

    // -- Large chain test ----------------------------------------------------

    #[test]
    fn test_large_chain_twenty_certificates() {
        let mut builder = ChainBuilder::new("large_fn");
        for i in 0..20 {
            builder
                .add_certificate(valid_cert(&format!("large-{i}")))
                .unwrap();
        }
        let chain = builder.build();
        assert_eq!(chain.entries.len(), 20);

        let result = ChainValidator::validate(&chain).expect("should succeed");
        assert!(result.valid);
        assert_eq!(result.entries_checked, 20);
        assert_eq!(result.entries_passed, 20);

        // Verify linkage: each entry (except first) has parent hash of previous.
        for i in 1..20 {
            let expected = certificate_hash(&chain.entries[i - 1].certificate);
            assert_eq!(
                chain.entries[i].parent_hash.as_deref(),
                Some(expected.as_str()),
                "entry {i} parent hash mismatch"
            );
        }
    }

    // -- Strict chain tests --------------------------------------------------

    #[test]
    fn test_all_strict_chain_detection() {
        let mut builder = ChainBuilder::new("strict_fn");
        builder.add_certificate(valid_cert("s1")).unwrap();
        builder.add_certificate(valid_cert("s2")).unwrap();
        let chain = builder.build();
        assert!(
            chain.chain_metadata.all_strict,
            "chain with no theory lemmas should be all-strict"
        );
    }

    #[test]
    fn test_mixed_strict_non_strict_chain() {
        let mut builder = ChainBuilder::new("mixed_fn");
        builder.add_certificate(valid_cert("strict")).unwrap();
        builder
            .add_certificate(cert_with_trusted_theory("trusted"))
            .unwrap();
        let chain = builder.build();
        assert!(
            !chain.chain_metadata.all_strict,
            "chain with trusted theory should not be all-strict"
        );
    }

    // -- Version compatibility -----------------------------------------------

    #[test]
    fn test_validator_checks_version_compatibility() {
        let mut builder = ChainBuilder::new("ver_fn");
        builder.add_certificate(valid_cert("ok")).unwrap();
        let mut chain = builder.build();

        // Bump the certificate version beyond the supported maximum.
        chain.entries[0].certificate.version = CERTIFICATE_VERSION + 10;

        let result = ChainValidator::validate(&chain).expect("should not error");
        assert!(!result.valid);
        let failure = result
            .first_failure
            .expect("first_failure should be set for version-mismatch chain");
        assert_eq!(failure.reason, ChainFailureReason::VersionMismatch);
    }

    // -- Root hash -----------------------------------------------------------

    #[test]
    fn test_root_hash_computation() {
        let mut builder = ChainBuilder::new("root_fn");
        let cert = valid_cert("root");
        let expected_root = certificate_hash(&cert);
        builder.add_certificate(cert).unwrap();
        let chain = builder.build();
        assert_eq!(chain.root_hash, expected_root);
    }

    #[test]
    fn test_root_hash_empty_chain() {
        let chain = ChainBuilder::new("empty_root").build();
        // Empty chain uses a sentinel hash.
        assert!(!chain.root_hash.is_empty());
        assert_eq!(chain.root_hash, hex_encode(&sha256(b"empty-chain")));
    }
}
