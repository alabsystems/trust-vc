// trust-vc-oracle — Oracle engine (propose → verify → feedback → refine loop)
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::backend::{LlmBackend, ProposedAnnotations};
use crate::feedback::ProofFeedback;
use crate::verify::verify_with_annotations;
use crate::OracleError;

/// Configuration for the oracle engine.
#[derive(Debug, Clone)]
pub struct OracleConfig {
    /// Maximum number of propose-verify-feedback iterations.
    pub max_iterations: usize,
    /// Whether to enable verbose logging.
    pub verbose: bool,
}

impl Default for OracleConfig {
    fn default() -> Self {
        Self {
            max_iterations: 10,
            verbose: false,
        }
    }
}

/// A function signature extracted from source code, used as input to the oracle.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct FunctionSignature {
    /// Function name.
    pub name: String,
    /// Parameters as (name, type) pairs.
    pub params: Vec<(String, String)>,
    /// Return type (if any).
    pub return_type: Option<String>,
    /// The full source code of the function.
    pub source: String,
    /// Generic type parameters (e.g. `["T: Clone", "'a"]`).
    pub generics: Vec<String>,
    /// Where clause predicates (e.g. `["T: Display + Debug"]`).
    pub where_clause: Vec<String>,
    /// Whether the function is `async`.
    pub is_async: bool,
    /// Whether the function is `const`.
    pub is_const: bool,
    /// Whether the function is `unsafe`.
    pub is_unsafe: bool,
    /// Byte offset of the function signature in the source file.
    pub span_start: Option<usize>,
    /// Byte length of the entire function item in the source file.
    pub span_len: Option<usize>,
}

impl FunctionSignature {
    /// Create a new `FunctionSignature` with the four core fields.
    ///
    /// New fields added in future versions will be set to their defaults.
    /// This is the recommended way to construct a `FunctionSignature` from
    /// outside the crate (the struct is `#[non_exhaustive]`).
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        params: Vec<(String, String)>,
        return_type: Option<String>,
        source: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            params,
            return_type,
            source: source.into(),
            ..Default::default()
        }
    }
}

/// Result of a complete oracle session.
#[derive(Debug)]
pub struct OracleResult {
    /// The final feedback (Verified if successful).
    pub final_feedback: ProofFeedback,
    /// The winning annotations (if verified).
    pub annotations: Option<ProposedAnnotations>,
    /// Full history of (proposal, feedback) pairs.
    pub history: Vec<(ProposedAnnotations, ProofFeedback)>,
    /// Number of iterations used.
    pub iterations: usize,
}

impl OracleResult {
    pub fn is_verified(&self) -> bool {
        self.final_feedback.is_verified()
    }
}

/// Run the oracle loop: propose annotations → verify → feedback → refine.
///
/// This is the main entry point for the proof oracle. It takes a function
/// signature, an LLM backend, and configuration, then iterates until
/// either the function is verified or the iteration budget is exhausted.
pub fn run_oracle(
    func: &FunctionSignature,
    backend: &dyn LlmBackend,
    config: &OracleConfig,
) -> Result<OracleResult, OracleError> {
    let mut history: Vec<(ProposedAnnotations, ProofFeedback)> = Vec::new();

    for iteration in 0..config.max_iterations {
        if config.verbose {
            eprintln!(
                "[oracle] iteration {}/{} using {} backend",
                iteration + 1,
                config.max_iterations,
                backend.name()
            );
        }

        // Step 1: Ask the LLM to propose annotations
        let proposal = backend.propose_annotations(&func.source, &history)?;

        if config.verbose {
            eprintln!(
                "[oracle]   proposed: {} requires, {} ensures",
                proposal.requires.len(),
                proposal.ensures.len()
            );
        }

        // Step 2: Verify the proposed annotations
        let feedback = verify_with_annotations(
            &func.name,
            &func.params,
            &proposal.requires,
            &proposal.ensures,
        );

        if config.verbose {
            eprintln!(
                "[oracle]   result: {}",
                feedback.to_llm_summary().lines().next().unwrap_or("")
            );
        }

        // Step 3: Check if we succeeded
        if feedback.is_verified() {
            let winning = proposal.clone();
            history.push((proposal, feedback.clone()));
            return Ok(OracleResult {
                final_feedback: feedback,
                annotations: Some(winning),
                history,
                iterations: iteration + 1,
            });
        }

        // Step 4: Record feedback and continue
        history.push((proposal, feedback));
    }

    // Budget exhausted
    let final_feedback = history
        .last()
        .map(|(_, f)| f.clone())
        .unwrap_or(ProofFeedback::Error {
            message: "No iterations completed".to_string(),
        });

    Ok(OracleResult {
        final_feedback,
        annotations: None,
        history,
        iterations: config.max_iterations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::MockBackend;

    #[test]
    fn test_oracle_finds_correct_spec_on_first_try() {
        let func = FunctionSignature {
            name: "nonneg".to_string(),
            params: vec![("x".to_string(), "u32".to_string())],
            return_type: Some("u32".to_string()),
            source: "fn nonneg(x: u32) -> u32 { x }".to_string(),
            ..Default::default()
        };

        // u32 x >= 0 is trivially true
        let backend = MockBackend::new(vec![ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_string(),
        }]);

        let config = OracleConfig {
            max_iterations: 5,
            verbose: false,
        };

        let result = run_oracle(&func, &backend, &config).unwrap();
        assert!(
            result.is_verified(),
            "u32 x >= 0 should verify: {:?}",
            result.final_feedback
        );
        assert_eq!(result.iterations, 1);
        assert!(result.annotations.is_some());
    }

    #[test]
    fn test_oracle_refines_after_failure() {
        let func = FunctionSignature {
            name: "positive".to_string(),
            params: vec![("x".to_string(), "i32".to_string())],
            return_type: Some("i32".to_string()),
            source: "fn positive(x: i32) -> i32 { x }".to_string(),
            ..Default::default()
        };

        // First proposal: too strong (i32 can be negative or zero)
        // Second proposal: add precondition, correct
        let backend = MockBackend::new(vec![
            ProposedAnnotations {
                requires: vec![],
                ensures: vec!["x > 0".to_string()],
                invariants: vec![],
                decreases: vec![],
                raw_response: "ensures!(x > 0)".to_string(),
            },
            ProposedAnnotations {
                requires: vec!["x > 0".to_string()],
                ensures: vec!["x >= 1".to_string()],
                invariants: vec![],
                decreases: vec![],
                raw_response: "requires!(x > 0) ensures!(x >= 1)".to_string(),
            },
        ]);

        let config = OracleConfig {
            max_iterations: 5,
            verbose: false,
        };

        let result = run_oracle(&func, &backend, &config).unwrap();
        assert!(
            result.is_verified(),
            "x > 0 => x >= 1 should verify: {:?}",
            result.final_feedback
        );
        assert_eq!(result.iterations, 2);
        assert_eq!(result.history.len(), 2);
        // First attempt should have failed
        assert!(result.history[0].1.is_failed() || result.history[0].1.is_unknown());
    }

    #[test]
    fn test_oracle_exhausts_budget() {
        let func = FunctionSignature {
            name: "impossible".to_string(),
            params: vec![("x".to_string(), "i32".to_string())],
            return_type: Some("i32".to_string()),
            source: "fn impossible(x: i32) -> i32 { x }".to_string(),
            ..Default::default()
        };

        // All proposals are wrong — i32 can be anything
        let backend = MockBackend::new(vec![
            ProposedAnnotations {
                requires: vec![],
                ensures: vec!["x > 100".to_string()],
                invariants: vec![],
                decreases: vec![],
                raw_response: "ensures!(x > 100)".to_string(),
            },
            ProposedAnnotations {
                requires: vec![],
                ensures: vec!["x > 50".to_string()],
                invariants: vec![],
                decreases: vec![],
                raw_response: "ensures!(x > 50)".to_string(),
            },
        ]);

        let config = OracleConfig {
            max_iterations: 2,
            verbose: false,
        };

        let result = run_oracle(&func, &backend, &config).unwrap();
        assert!(!result.is_verified());
        assert_eq!(result.iterations, 2);
        assert!(result.annotations.is_none());
    }
}
