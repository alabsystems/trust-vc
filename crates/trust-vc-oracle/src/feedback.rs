// trust-vc-oracle — Proof feedback types
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::time::Duration;

use serde::{Deserialize, Serialize};

/// Structured feedback from a single verification attempt.
///
/// This is the core type that differentiates trust_vc's proof oracle from
/// black-box verifiers. Instead of pass/fail, the oracle returns typed
/// counterexample values, failure localization, and solver diagnostics.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofFeedback {
    /// All assertions verified successfully.
    Verified {
        /// Per-assertion results with solver stats.
        steps: Vec<StepSummary>,
        /// Total verification time.
        elapsed: Duration,
        /// UNSAT proof certificate (if `proof-certificates` feature enabled).
        #[serde(skip_serializing_if = "Option::is_none")]
        certificate_info: Option<CertificateInfo>,
    },

    /// Verification found a counterexample — the proposed spec is too strong
    /// or the code has a bug.
    Failed {
        /// Typed counterexample bindings (e.g., x: Vec![3,-1,7], result: -1).
        counterexamples: Vec<CounterexampleField>,
        /// Which assertion failed and where in a compound assertion.
        localization: FailureLocalization,
        /// Name of the failing obligation.
        obligation_name: String,
        /// Which solver mode was used.
        solver_mode: String,
        /// Total verification time.
        elapsed: Duration,
    },

    /// Verification could not determine satisfiability.
    Unknown {
        /// Human-readable reason.
        reason: String,
        /// Classified category for programmatic handling.
        category: String,
        /// Whether retrying with different parameters might help.
        is_retriable: bool,
        /// Actionable suggestion for the LLM.
        suggestion: String,
        elapsed: Duration,
    },

    /// Verification infrastructure error (not a spec problem).
    Error { message: String },
}

/// A single counterexample variable binding with type information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CounterexampleField {
    /// User-facing variable name (e.g., "x", "old(x)", "result").
    pub name: String,
    /// Type of the variable (e.g., "i32", "Seq<u64>", "Set<bool>").
    pub ty: String,
    /// Rendered value (e.g., "-42", "[1, 2, 3]", "{true, false}").
    pub value: String,
}

/// Localization of which part of a compound assertion failed.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FailureLocalization {
    /// The full assertion that was checked.
    pub full_assertion: Option<String>,
    /// Sub-assertions with pass/fail status.
    pub sub_results: Vec<SubAssertionResult>,
}

/// Result of a single sub-assertion after localization splitting.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SubAssertionResult {
    pub label: String,
    pub status: SubAssertionStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SubAssertionStatus {
    Pass,
    Fail,
    Unknown,
    Error,
}

/// Summary of a single verification step.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StepSummary {
    pub label: String,
    pub phase: String,
    pub elapsed: Duration,
    pub result: String,
    /// Assumptions that were actually used in the proof (from UNSAT core).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub used_assumptions: Vec<String>,
}

/// Proof certificate metadata (without the full certificate content).
///
/// It describes the last certificate recorded for the run, which refutes one
/// obligation; it is not a claim about every obligation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateInfo {
    pub strict_verified: bool,
    pub clean_supported: bool,
    pub trust_count: u32,
    pub hole_count: u32,
    pub resolution_count: u32,
    pub theory_count: u32,
}

impl ProofFeedback {
    pub fn is_verified(&self) -> bool {
        matches!(self, ProofFeedback::Verified { .. })
    }

    pub fn is_failed(&self) -> bool {
        matches!(self, ProofFeedback::Failed { .. })
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, ProofFeedback::Unknown { .. })
    }

    pub fn is_error(&self) -> bool {
        matches!(self, ProofFeedback::Error { .. })
    }

    /// Serialize to JSON for LLM consumption.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Render a concise text summary suitable for LLM prompt context.
    pub fn to_llm_summary(&self) -> String {
        match self {
            ProofFeedback::Verified { steps, elapsed, .. } => {
                format!(
                    "VERIFIED: All {} assertions passed in {:.1}ms.",
                    steps.len(),
                    elapsed.as_secs_f64() * 1000.0
                )
            }
            ProofFeedback::Failed {
                counterexamples,
                localization,
                obligation_name,
                ..
            } => {
                let mut out = format!(
                    "FAILED: Assertion '{}' has a counterexample.\n",
                    obligation_name
                );
                out.push_str("Counterexample values:\n");
                for cx in counterexamples {
                    out.push_str(&format!("  {}: {} = {}\n", cx.name, cx.ty, cx.value));
                }
                if !localization.sub_results.is_empty() {
                    out.push_str("Localization (which parts failed):\n");
                    for sub in &localization.sub_results {
                        out.push_str(&format!("  [{}] {}\n", sub.status.as_str(), sub.label));
                    }
                }
                out
            }
            ProofFeedback::Unknown {
                reason, suggestion, ..
            } => {
                format!("UNKNOWN: {}.\nSuggestion: {}", reason, suggestion)
            }
            ProofFeedback::Error { message } => {
                format!("ERROR: {}", message)
            }
        }
    }
}

impl SubAssertionStatus {
    pub fn as_str(&self) -> &'static str {
        match self {
            SubAssertionStatus::Pass => "PASS",
            SubAssertionStatus::Fail => "FAIL",
            SubAssertionStatus::Unknown => "UNKNOWN",
            SubAssertionStatus::Error => "ERROR",
        }
    }
}
