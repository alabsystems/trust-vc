// trust-vc-oracle — LLM backend trait
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::feedback::ProofFeedback;
use crate::OracleError;

/// A proposed set of annotations from an LLM.
#[derive(Debug, Clone)]
pub struct ProposedAnnotations {
    /// Preconditions (requires! clauses).
    pub requires: Vec<String>,
    /// Postconditions (ensures! clauses).
    pub ensures: Vec<String>,
    /// Loop invariants (invariant! clauses), keyed by loop label.
    pub invariants: Vec<(String, String)>,
    /// Decreases clauses for termination.
    pub decreases: Vec<String>,
    /// Raw LLM response text (for debugging/logging).
    pub raw_response: String,
}

/// Configuration for an LLM backend.
#[derive(Debug, Clone)]
pub struct LlmConfig {
    /// Model identifier (e.g., "claude-sonnet-4-6", "qwen3-32b").
    pub model: String,
    /// Maximum tokens to generate per request.
    pub max_tokens: usize,
    /// Temperature for sampling (0.0 = deterministic).
    pub temperature: f64,
    /// System prompt override (None = use default oracle system prompt).
    pub system_prompt: Option<String>,
}

impl Default for LlmConfig {
    fn default() -> Self {
        Self {
            model: "claude-sonnet-4-6".to_string(),
            max_tokens: 4096,
            temperature: 0.0,
            system_prompt: None,
        }
    }
}

/// Trait for pluggable LLM backends.
///
/// Implementations provide the LLM interaction for the oracle loop.
/// The oracle calls `propose_annotations` with the source code and
/// accumulated feedback history, and the backend returns proposed specs.
pub trait LlmBackend: Send + Sync {
    /// Propose annotations for a function given its source and feedback history.
    ///
    /// `source` is the Rust function source code (without annotations).
    /// `feedback_history` is the list of prior (proposal, feedback) pairs.
    /// The backend should use the history to avoid repeating failed proposals.
    fn propose_annotations(
        &self,
        source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError>;

    /// Return the backend name for logging.
    fn name(&self) -> &str;

    /// Check whether the backend's CLI tool is installed and reachable.
    ///
    /// Returns `true` if the tool can be found on `$PATH`, `false` otherwise.
    /// The default implementation always returns `true` (appropriate for
    /// backends like `MockBackend` that need no external tooling).
    fn is_available(&self) -> bool {
        true
    }
}

/// A mock backend for testing that returns pre-configured annotations.
pub struct MockBackend {
    proposals: Vec<ProposedAnnotations>,
}

impl MockBackend {
    pub fn new(proposals: Vec<ProposedAnnotations>) -> Self {
        Self { proposals }
    }
}

impl LlmBackend for MockBackend {
    fn propose_annotations(
        &self,
        _source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        let idx = feedback_history.len();
        self.proposals
            .get(idx)
            .cloned()
            .ok_or(OracleError::BackendExhausted { attempts: idx })
    }

    fn name(&self) -> &str {
        "mock"
    }
}
