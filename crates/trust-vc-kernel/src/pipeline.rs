// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kernel bridge pipeline: wires the proof checker, theory checker,
//! compaction, and export stages into a single verification pass.
//!
//! # Pipeline stages
//!
//! 1. **Validate** — reject empty or version-incompatible certificates.
//! 2. **Check proof** — propositional resolution verification via
//!    [`crate::checker::check_proof_with_theory`].
//! 3. **Theory check** — per-lemma structural validation (EUF/LRA).
//! 4. **Compact** — optional dead-branch elimination via
//!    [`crate::compaction::compact_with_stats`].
//! 5. **Export** — optional serialization to JSON, binary, human-readable,
//!    or SMT-LIB2.

use std::time::Instant;

use crate::bridge::convert_ay_artifact;
use crate::checker::check_proof_with_theory;
use crate::compaction::{compact_with_stats, ProofStats};
use crate::error::KernelError;
use crate::export::{export_certificate, ExportFormat};
use crate::format::{TrustVcProofCertificate, CERTIFICATE_VERSION};
use crate::theory_check::check_theory_lemma;
use crate::types::{CheckResultWithStats, TheoryCheckResult, TheoryStats};

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Controls which pipeline stages execute and their parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct PipelineConfig {
    /// Run per-lemma theory validation after proof checking.
    pub check_theory_lemmas: bool,
    /// Run dead-branch compaction on the proof certificate.
    pub compact_proof: bool,
    /// If set, export the (possibly compacted) certificate in this format.
    pub export_format: Option<ExportFormat>,
    /// In strict mode, any theory lemma accepted on trust causes an error.
    pub strict_mode: bool,
    /// Maximum total proof steps (resolution + theory lemmas) allowed.
    pub max_proof_size: usize,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            check_theory_lemmas: true,
            compact_proof: true,
            export_format: None,
            strict_mode: false,
            max_proof_size: 100_000,
        }
    }
}

impl PipelineConfig {
    /// Create a new configuration with default values.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set whether to check theory lemmas.
    #[must_use]
    pub fn with_check_theory_lemmas(mut self, enabled: bool) -> Self {
        self.check_theory_lemmas = enabled;
        self
    }

    /// Set whether to compact the proof.
    #[must_use]
    pub fn with_compact_proof(mut self, enabled: bool) -> Self {
        self.compact_proof = enabled;
        self
    }

    /// Set the export format.
    #[must_use]
    pub fn with_export_format(mut self, format: ExportFormat) -> Self {
        self.export_format = Some(format);
        self
    }

    /// Set strict mode.
    #[must_use]
    pub fn with_strict_mode(mut self, enabled: bool) -> Self {
        self.strict_mode = enabled;
        self
    }

    /// Set the maximum proof size.
    #[must_use]
    pub fn with_max_proof_size(mut self, max: usize) -> Self {
        self.max_proof_size = max;
        self
    }
}

// ---------------------------------------------------------------------------
// Result
// ---------------------------------------------------------------------------

/// Aggregated output from a full pipeline run.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PipelineResult {
    /// The proof check result with statistics.
    pub check_result: CheckResultWithStats,
    /// Compaction statistics, if compaction was enabled.
    pub compaction_stats: Option<ProofStats>,
    /// Exported bytes, if an export format was configured.
    pub exported_bytes: Option<Vec<u8>>,
    /// Theory lemma statistics from the checking pass.
    pub theory_stats: TheoryStats,
    /// Wall-clock time for the entire pipeline.
    pub elapsed: std::time::Duration,
}

// ---------------------------------------------------------------------------
// Pipeline entry points
// ---------------------------------------------------------------------------

/// Run the full verification pipeline on a proof certificate.
///
/// # Stages
///
/// 1. Validate certificate structure (non-empty, supported version).
/// 2. Enforce proof size limit.
/// 3. Convert to internal proof trace and run the resolution checker.
/// 4. Optionally run per-lemma theory validation.
/// 5. Optionally compact the proof and record statistics.
/// 6. Optionally export the certificate.
///
/// # Errors
///
/// Returns [`KernelError`] on empty certificates, unsupported versions,
/// size violations, strict-mode trust violations, or export failures.
#[must_use = "pipeline result contains check outcome and exported bytes"]
pub fn run_pipeline(
    cert: &TrustVcProofCertificate,
    config: &PipelineConfig,
) -> Result<PipelineResult, KernelError> {
    let start = Instant::now();

    // Step 1: validate certificate structure.
    validate_certificate(cert)?;

    // Step 2: enforce proof size limit.
    let total_steps = cert.resolution_steps.len() + cert.theory_lemmas.len();
    if total_steps > config.max_proof_size {
        return Err(KernelError::ProofTooLarge {
            actual: total_steps,
            max: config.max_proof_size,
        });
    }

    // Step 3: convert to internal trace and run proof checker.
    let trace = wire_to_proof_trace(cert);
    let check_result = check_proof_with_theory(&trace);

    // Step 4: optional per-lemma theory validation + strict mode.
    let theory_stats = if config.check_theory_lemmas {
        let mut stats = TheoryStats::default();
        for lemma in &trace.theory_lemmas {
            match check_theory_lemma(lemma) {
                TheoryCheckResult::Verified => stats.verified_count += 1,
                TheoryCheckResult::Trusted => stats.trusted_count += 1,
                TheoryCheckResult::Invalid { .. } => stats.invalid_count += 1,
            }
        }
        if config.strict_mode && stats.trusted_count > 0 {
            return Err(KernelError::StrictUntrustedTheory {
                trusted_count: stats.trusted_count,
            });
        }
        stats
    } else {
        check_result.theory_stats
    };

    // Step 5: optional compaction.
    let compaction_stats = if config.compact_proof {
        let artifact = wire_to_ay_artifact(cert);
        let (_compacted, stats) = compact_with_stats(&artifact);
        Some(stats)
    } else {
        None
    };

    // Step 6: optional export.
    let exported_bytes = if let Some(format) = config.export_format {
        let bytes = export_certificate(cert, format)?;
        Some(bytes)
    } else {
        None
    };

    Ok(PipelineResult {
        check_result,
        compaction_stats,
        exported_bytes,
        theory_stats,
        elapsed: start.elapsed(),
    })
}

/// Convenience function: validate a certificate and export it in one call.
///
/// Runs the full pipeline with default settings plus the specified export
/// format. Returns the exported bytes on success.
///
/// # Errors
///
/// Returns [`KernelError`] on invalid certificates or export failures.
#[must_use = "exported bytes should be consumed"]
pub fn validate_and_export(
    cert: &TrustVcProofCertificate,
    format: ExportFormat,
) -> Result<Vec<u8>, KernelError> {
    let config = PipelineConfig::new().with_export_format(format);
    let result = run_pipeline(cert, &config)?;
    result
        .exported_bytes
        .ok_or_else(|| KernelError::Export("pipeline completed without exported bytes".to_string()))
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Validate certificate structure: non-empty and supported version.
fn validate_certificate(cert: &TrustVcProofCertificate) -> Result<(), KernelError> {
    // Version check.
    if cert.version == 0 || cert.version > CERTIFICATE_VERSION {
        return Err(KernelError::UnsupportedVersion {
            found: cert.version,
            expected: CERTIFICATE_VERSION,
        });
    }

    // Empty certificate check.
    if cert.input_clauses.is_empty()
        && cert.resolution_steps.is_empty()
        && cert.theory_lemmas.is_empty()
    {
        return Err(KernelError::EmptyCertificate);
    }

    Ok(())
}

/// Convert a wire-format certificate into the internal `ProofTrace` for
/// the resolution checker.
fn wire_to_proof_trace(cert: &TrustVcProofCertificate) -> crate::types::ProofTrace {
    let artifact = wire_to_ay_artifact(cert);
    convert_ay_artifact(&artifact)
}

/// Convert a wire-format certificate into the bridge `AYProofArtifact`
/// used by the compaction module.
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::{
        CertificateMetadata, Literal, TheoryLemmaKind, TrustVcProofCertificate, WireClause,
        WireClauseId, WireResolutionStep, WireTheoryLemma, CERTIFICATE_VERSION,
    };
    use crate::types::CheckResult;

    // -- Test helpers ---------------------------------------------------------

    /// Build a minimal valid certificate: two input clauses resolved to empty.
    fn minimal_valid_cert() -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
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
            metadata: test_metadata(),
        }
    }

    /// Build a certificate with EUF and NIA theory lemmas.
    fn cert_with_theories() -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
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
            theory_lemmas: vec![
                WireTheoryLemma {
                    id: WireClauseId(10),
                    kind: TheoryLemmaKind::Euf,
                    literals: vec![Literal(-1)],
                    justification: Some("congruence".to_string()),
                },
                WireTheoryLemma {
                    id: WireClauseId(11),
                    kind: TheoryLemmaKind::Nia,
                    literals: vec![Literal(2), Literal(-3)],
                    justification: None,
                },
            ],
            empty_clause_id: WireClauseId(100),
            metadata: test_metadata(),
        }
    }

    /// Build a certificate with dead branches suitable for compaction testing.
    fn cert_with_dead_branches() -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: vec![
                WireClause {
                    id: WireClauseId(1),
                    literals: vec![Literal(1)],
                },
                WireClause {
                    id: WireClauseId(2),
                    literals: vec![Literal(-1)],
                },
                // Dead branch inputs.
                WireClause {
                    id: WireClauseId(10),
                    literals: vec![Literal(5)],
                },
                WireClause {
                    id: WireClauseId(11),
                    literals: vec![Literal(-5)],
                },
            ],
            resolution_steps: vec![
                // Dead: resolves 10 and 11 on pivot 5.
                WireResolutionStep {
                    result_id: WireClauseId(20),
                    antecedent_a: WireClauseId(10),
                    antecedent_b: WireClauseId(11),
                    pivot: Literal(5),
                    result_literals: vec![],
                },
                // Live: resolves 1 and 2 on pivot 1.
                WireResolutionStep {
                    result_id: WireClauseId(30),
                    antecedent_a: WireClauseId(1),
                    antecedent_b: WireClauseId(2),
                    pivot: Literal(1),
                    result_literals: vec![],
                },
            ],
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(30),
            metadata: test_metadata(),
        }
    }

    /// Build a large certificate with many resolution steps.
    fn large_cert(num_steps: usize) -> TrustVcProofCertificate {
        // Chain: clause 1 = {1}, clause 2 = {-1, 2}, ..., clause n+1 = {-n}.
        // Resolution: step_{n+2} = resolve(1, 2, pivot=1) -> {2}
        //             step_{n+3} = resolve(step_{n+2}, 3, pivot=2) -> {3}
        //             ...
        let n = num_steps;
        let mut inputs = vec![WireClause {
            id: WireClauseId(1),
            literals: vec![Literal(1)],
        }];
        for i in 1..n {
            inputs.push(WireClause {
                id: WireClauseId((i + 1) as u64),
                literals: vec![Literal(-(i as i64)), Literal((i + 1) as i64)],
            });
        }
        inputs.push(WireClause {
            id: WireClauseId((n + 1) as u64),
            literals: vec![Literal(-(n as i64))],
        });

        let base = (n + 2) as u64;
        let mut steps = vec![WireResolutionStep {
            result_id: WireClauseId(base),
            antecedent_a: WireClauseId(1),
            antecedent_b: WireClauseId(2),
            pivot: Literal(1),
            result_literals: vec![Literal(2)],
        }];
        for i in 2..n {
            steps.push(WireResolutionStep {
                result_id: WireClauseId(base + (i - 1) as u64),
                antecedent_a: WireClauseId(base + (i - 2) as u64),
                antecedent_b: WireClauseId((i + 1) as u64),
                pivot: Literal(i as i64),
                result_literals: vec![Literal((i + 1) as i64)],
            });
        }
        let final_id = base + (n - 1) as u64;
        steps.push(WireResolutionStep {
            result_id: WireClauseId(final_id),
            antecedent_a: WireClauseId(final_id - 1),
            antecedent_b: WireClauseId((n + 1) as u64),
            pivot: Literal(n as i64),
            result_literals: vec![],
        });

        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: inputs,
            resolution_steps: steps,
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(final_id),
            metadata: test_metadata(),
        }
    }

    fn test_metadata() -> CertificateMetadata {
        CertificateMetadata {
            timestamp: "2026-03-28T00:00:00Z".to_string(),
            trust_vc_version: "1.0.0".to_string(),
            solver_version: "ay-dpll 0.1.0".to_string(),
        }
    }

    // -- Tests ----------------------------------------------------------------

    #[test]
    fn test_pipeline_default_config_valid_cert() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::default();
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        assert_eq!(result.check_result.result, CheckResult::Valid);
        assert!(
            result.compaction_stats.is_some(),
            "compaction on by default"
        );
        assert!(result.exported_bytes.is_none(), "no export by default");
    }

    #[test]
    fn test_pipeline_rejects_mismatched_result_literals() {
        let mut cert = large_cert(3);
        cert.resolution_steps[0].result_literals = vec![Literal(99)];

        let result = run_pipeline(&cert, &PipelineConfig::default())
            .expect("pipeline should return a check result");
        assert!(matches!(
            result.check_result.result,
            CheckResult::Invalid { .. }
        ));
    }

    #[test]
    fn test_pipeline_all_options_enabled() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::new()
            .with_check_theory_lemmas(true)
            .with_compact_proof(true)
            .with_export_format(ExportFormat::Json)
            .with_strict_mode(false)
            .with_max_proof_size(1_000);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        assert_eq!(result.check_result.result, CheckResult::Valid);
        assert!(
            result.compaction_stats.is_some(),
            "compaction_stats should be populated when compaction is enabled"
        );
        let bytes = result
            .exported_bytes
            .expect("exported_bytes should be present when export format is set");
        assert!(!bytes.is_empty(), "exported JSON should be non-empty");
    }

    #[test]
    fn test_pipeline_compaction_plus_export() {
        let cert = cert_with_dead_branches();
        let config = PipelineConfig::new()
            .with_compact_proof(true)
            .with_export_format(ExportFormat::Json);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        assert_eq!(result.check_result.result, CheckResult::Valid);
        let stats = result
            .compaction_stats
            .expect("compaction_stats should be present when compaction is enabled");
        assert!(
            stats.removed_steps > 0,
            "dead branches should be removed: {stats:?}"
        );
        assert!(
            result.exported_bytes.is_some(),
            "exported_bytes should be present when export format is set"
        );
    }

    #[test]
    fn test_pipeline_rejects_empty_certificate() {
        let cert = TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: vec![],
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(0),
            metadata: test_metadata(),
        };
        let config = PipelineConfig::default();
        let err = run_pipeline(&cert, &config).expect_err("empty cert should fail");
        assert!(
            matches!(err, KernelError::EmptyCertificate),
            "expected EmptyCertificate, got: {err}"
        );
    }

    #[test]
    fn test_pipeline_rejects_invalid_version() {
        let mut cert = minimal_valid_cert();
        cert.version = CERTIFICATE_VERSION + 99;
        let config = PipelineConfig::default();
        let err = run_pipeline(&cert, &config).expect_err("bad version should fail");
        assert!(
            matches!(err, KernelError::UnsupportedVersion { .. }),
            "expected UnsupportedVersion, got: {err}"
        );
    }

    #[test]
    fn test_pipeline_strict_mode_fails_on_untrusted_theory() {
        let cert = cert_with_theories();
        let config = PipelineConfig::new()
            .with_check_theory_lemmas(true)
            .with_strict_mode(true)
            .with_compact_proof(false);
        let err =
            run_pipeline(&cert, &config).expect_err("strict mode should reject trusted lemmas");
        assert!(
            matches!(err, KernelError::StrictUntrustedTheory { trusted_count: 1 }),
            "expected StrictUntrustedTheory with count 1, got: {err}"
        );
    }

    #[test]
    fn test_pipeline_timing_is_populated() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::default();
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        // Duration should be non-negative (it always is, but verify it was set).
        assert!(
            result.elapsed.as_nanos() > 0,
            "elapsed time should be greater than zero"
        );
    }

    #[test]
    fn test_validate_and_export_json() {
        let cert = minimal_valid_cert();
        let bytes = validate_and_export(&cert, ExportFormat::Json)
            .expect("validate_and_export should succeed");
        assert!(!bytes.is_empty());
        // The exported bytes should be valid JSON.
        let json = std::str::from_utf8(&bytes).expect("exported JSON should be valid UTF-8");
        assert!(json.contains("resolution_steps") || json.contains("input_clauses"));
    }

    #[test]
    fn test_pipeline_large_certificate() {
        let cert = large_cert(50);
        let config = PipelineConfig::new()
            .with_compact_proof(true)
            .with_max_proof_size(200);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed on large cert");
        assert_eq!(result.check_result.result, CheckResult::Valid);
        assert!(
            result.compaction_stats.is_some(),
            "compaction_stats should be populated for large cert with compaction enabled"
        );
    }

    #[test]
    fn test_pipeline_export_format_binary() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::new()
            .with_export_format(ExportFormat::Binary)
            .with_compact_proof(false);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        let bytes = result
            .exported_bytes
            .expect("binary export should produce bytes");
        assert!(!bytes.is_empty());
    }

    #[test]
    fn test_pipeline_export_format_human_readable() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::new()
            .with_export_format(ExportFormat::HumanReadable)
            .with_compact_proof(false);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        let bytes = result
            .exported_bytes
            .expect("human-readable export should produce bytes");
        let text = std::str::from_utf8(&bytes).expect("human-readable output should be UTF-8");
        assert!(!text.is_empty());
    }

    #[test]
    fn test_pipeline_export_format_smtlib2() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::new()
            .with_export_format(ExportFormat::SmtLib2)
            .with_compact_proof(false);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        let bytes = result
            .exported_bytes
            .expect("SMT-LIB2 export should produce bytes");
        let text = std::str::from_utf8(&bytes).expect("SMT-LIB2 output should be UTF-8");
        assert!(!text.is_empty());
    }

    #[test]
    fn test_pipeline_config_builder_pattern() {
        let config = PipelineConfig::new()
            .with_check_theory_lemmas(false)
            .with_compact_proof(false)
            .with_strict_mode(true)
            .with_max_proof_size(42);
        assert!(!config.check_theory_lemmas);
        assert!(!config.compact_proof);
        assert!(config.strict_mode);
        assert_eq!(config.max_proof_size, 42);
        assert!(config.export_format.is_none());

        let config2 = PipelineConfig::new().with_export_format(ExportFormat::Json);
        assert_eq!(config2.export_format, Some(ExportFormat::Json));
    }

    #[test]
    fn test_pipeline_theory_stats_populated() {
        let cert = cert_with_theories();
        let config = PipelineConfig::new()
            .with_check_theory_lemmas(true)
            .with_strict_mode(false)
            .with_compact_proof(false);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        // EUF lemma should be verified, NIA lemma should be trusted.
        assert_eq!(result.theory_stats.verified_count, 1);
        assert_eq!(result.theory_stats.trusted_count, 1);
        assert_eq!(result.theory_stats.invalid_count, 0);
        assert_eq!(result.theory_stats.total(), 2);
    }

    #[test]
    fn test_pipeline_compaction_reduces_step_count() {
        let cert = cert_with_dead_branches();
        let config = PipelineConfig::new()
            .with_compact_proof(true)
            .with_check_theory_lemmas(false);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        let stats = result.compaction_stats.expect("compaction should run");
        assert!(
            stats.compacted_steps < stats.original_steps,
            "compaction should reduce steps: {} < {}",
            stats.compacted_steps,
            stats.original_steps,
        );
        assert!(stats.removed_steps > 0);
    }

    #[test]
    fn test_pipeline_max_proof_size_enforcement() {
        let cert = large_cert(20);
        // Set max_proof_size to less than the actual step count.
        let config = PipelineConfig::new().with_max_proof_size(5);
        let err = run_pipeline(&cert, &config).expect_err("should reject oversized proof");
        assert!(
            matches!(err, KernelError::ProofTooLarge { .. }),
            "expected ProofTooLarge, got: {err}"
        );
    }

    #[test]
    fn test_pipeline_version_zero_rejected() {
        let mut cert = minimal_valid_cert();
        cert.version = 0;
        let config = PipelineConfig::default();
        let err = run_pipeline(&cert, &config).expect_err("version 0 should be rejected");
        assert!(
            matches!(err, KernelError::UnsupportedVersion { found: 0, .. }),
            "expected UnsupportedVersion with found=0, got: {err}"
        );
    }

    #[test]
    fn test_pipeline_no_compaction_no_export() {
        let cert = minimal_valid_cert();
        let config = PipelineConfig::new()
            .with_compact_proof(false)
            .with_check_theory_lemmas(false);
        let result = run_pipeline(&cert, &config).expect("pipeline should succeed");
        assert_eq!(result.check_result.result, CheckResult::Valid);
        assert!(result.compaction_stats.is_none());
        assert!(result.exported_bytes.is_none());
    }

    #[test]
    fn test_pipeline_strict_mode_passes_without_trusted() {
        // Certificate with no theory lemmas: strict mode should pass.
        let cert = minimal_valid_cert();
        let config = PipelineConfig::new()
            .with_strict_mode(true)
            .with_check_theory_lemmas(true)
            .with_compact_proof(false);
        let result =
            run_pipeline(&cert, &config).expect("strict mode should pass with no theories");
        assert_eq!(result.check_result.result, CheckResult::Valid);
        assert_eq!(result.theory_stats.trusted_count, 0);
    }

    #[test]
    fn test_validate_and_export_rejects_empty() {
        let cert = TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: vec![],
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(0),
            metadata: test_metadata(),
        };
        let err = validate_and_export(&cert, ExportFormat::Json)
            .expect_err("empty cert should be rejected");
        assert!(matches!(err, KernelError::EmptyCertificate));
    }
}
