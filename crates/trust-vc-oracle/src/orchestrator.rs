// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Orchestrator — integrates the strategy planner and verify adapter into
// the main oracle loop. Plans a strategy based on function complexity,
// iterates through propose/verify/score/refine cycles, tracks convergence,
// and returns structured results.

#![allow(dead_code)]

use crate::backend::{LlmBackend, ProposedAnnotations};
use crate::convergence::DifficultyClassifier;
use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;
use crate::OracleError;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the proof orchestrator.
#[derive(Debug, Clone)]
pub struct OrchestratorConfig {
    /// Maximum number of propose-verify-refine iterations.
    pub max_iterations: usize,
    /// Maximum proposals to evaluate per iteration.
    pub budget_per_iteration: usize,
    /// Score threshold at which to declare convergence (0.0 to 1.0).
    pub convergence_threshold: f64,
    /// Whether to enable CGSR (Counterexample-Guided Specification Refinement).
    pub enable_cgsr: bool,
    /// Whether to enable function decomposition for complex proofs.
    pub enable_decomposition: bool,
    /// Whether to emit verbose diagnostics to stderr.
    pub verbose: bool,
}

impl Default for OrchestratorConfig {
    fn default() -> Self {
        Self {
            max_iterations: 10,
            budget_per_iteration: 5,
            convergence_threshold: 0.95,
            enable_cgsr: true,
            enable_decomposition: true,
            verbose: false,
        }
    }
}

/// Builder for `OrchestratorConfig`.
#[derive(Debug, Clone)]
#[must_use]
pub struct OrchestratorConfigBuilder {
    config: OrchestratorConfig,
}

impl OrchestratorConfigBuilder {
    /// Start building from defaults.
    pub fn new() -> Self {
        Self {
            config: OrchestratorConfig::default(),
        }
    }

    /// Set the maximum number of iterations.
    pub fn max_iterations(mut self, n: usize) -> Self {
        self.config.max_iterations = n;
        self
    }

    /// Set the per-iteration proposal budget.
    pub fn budget_per_iteration(mut self, n: usize) -> Self {
        self.config.budget_per_iteration = n;
        self
    }

    /// Set the convergence score threshold.
    pub fn convergence_threshold(mut self, t: f64) -> Self {
        self.config.convergence_threshold = t.clamp(0.0, 1.0);
        self
    }

    /// Enable or disable CGSR.
    pub fn enable_cgsr(mut self, enabled: bool) -> Self {
        self.config.enable_cgsr = enabled;
        self
    }

    /// Enable or disable function decomposition.
    pub fn enable_decomposition(mut self, enabled: bool) -> Self {
        self.config.enable_decomposition = enabled;
        self
    }

    /// Enable or disable verbose logging.
    pub fn verbose(mut self, v: bool) -> Self {
        self.config.verbose = v;
        self
    }

    /// Build the final configuration.
    pub fn build(self) -> OrchestratorConfig {
        self.config
    }
}

impl Default for OrchestratorConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl OrchestratorConfig {
    /// Create a builder for this config type.
    pub fn builder() -> OrchestratorConfigBuilder {
        OrchestratorConfigBuilder::new()
    }
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Final annotations produced by the orchestrator.
#[derive(Debug, Clone)]
pub struct FinalAnnotations {
    /// Preconditions (`requires!` clauses).
    pub requires: Vec<String>,
    /// Postconditions (`ensures!` clauses).
    pub ensures: Vec<String>,
    /// Loop invariants (`invariant!` clauses).
    pub invariants: Vec<String>,
}

impl From<&ProposedAnnotations> for FinalAnnotations {
    fn from(p: &ProposedAnnotations) -> Self {
        Self {
            requires: p.requires.clone(),
            ensures: p.ensures.clone(),
            invariants: p.invariants.iter().map(|(_, inv)| inv.clone()).collect(),
        }
    }
}

/// Record of a single orchestrator iteration.
#[derive(Debug, Clone)]
pub struct IterationRecord {
    /// 1-indexed iteration number.
    pub iteration: usize,
    /// Name of the strategy used in this iteration.
    pub strategy_used: String,
    /// Number of proposals evaluated.
    pub proposal_count: usize,
    /// Best score achieved in this iteration (0.0 to 1.0).
    pub best_score: f64,
    /// Whether the best proposal was verified.
    pub verified: bool,
}

/// Result of a complete orchestrator session.
#[derive(Debug, Clone)]
pub struct OrchestratorResult {
    /// The winning annotations, if verification succeeded.
    pub final_annotations: Option<FinalAnnotations>,
    /// Number of iterations used.
    pub iterations_used: usize,
    /// Total number of proposals evaluated across all iterations.
    pub total_proposals: usize,
    /// Whether the orchestrator converged (score >= threshold).
    pub converged: bool,
    /// Per-iteration history.
    pub history: Vec<IterationRecord>,
}

// ---------------------------------------------------------------------------
// Strategy selection
// ---------------------------------------------------------------------------

/// Strategy selected by the orchestrator based on function analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Strategy {
    /// Simple function: use template mining for direct spec proposals.
    TemplateMining,
    /// Function contains loops: use CGSR for invariant synthesis.
    Cgsr,
    /// Complex function: decompose into sub-proofs.
    Decomposition,
    /// Fallback: plain oracle query.
    PlainOracle,
}

impl Strategy {
    fn as_str(&self) -> &str {
        match self {
            Strategy::TemplateMining => "template_mining",
            Strategy::Cgsr => "cgsr",
            Strategy::Decomposition => "decomposition",
            Strategy::PlainOracle => "plain_oracle",
        }
    }
}

/// Select a strategy based on function characteristics and config.
fn select_strategy(func: &FunctionSignature, config: &OrchestratorConfig) -> Strategy {
    let has_loops = func.source.contains("while ")
        || func.source.contains("for ")
        || func.source.contains("loop ");

    let complexity = DifficultyClassifier::complexity_score(func);

    // Loop-containing functions benefit from CGSR invariant synthesis.
    if has_loops && config.enable_cgsr {
        return Strategy::Cgsr;
    }

    // High-complexity functions benefit from decomposition.
    if complexity >= 6 && config.enable_decomposition {
        return Strategy::Decomposition;
    }

    // Simple functions: try template mining first.
    if complexity <= 3 {
        return Strategy::TemplateMining;
    }

    // Medium complexity without loops: plain oracle.
    Strategy::PlainOracle
}

// ---------------------------------------------------------------------------
// Scoring
// ---------------------------------------------------------------------------

/// Score a verification result on a 0.0-to-1.0 scale.
///
/// - Verified: 1.0
/// - Failed with counterexamples: partial credit based on how many
///   sub-assertions passed vs. failed.
/// - Unknown (retriable): 0.1
/// - Unknown (non-retriable) or Error: 0.0
fn score_feedback(feedback: &ProofFeedback) -> f64 {
    match feedback {
        ProofFeedback::Verified { .. } => 1.0,
        ProofFeedback::Failed { localization, .. } => {
            if localization.sub_results.is_empty() {
                return 0.2;
            }
            let total = localization.sub_results.len() as f64;
            let passed = localization
                .sub_results
                .iter()
                .filter(|r| r.status == crate::feedback::SubAssertionStatus::Pass)
                .count() as f64;
            // Scale: 0.2 base + 0.6 * (passed / total)
            // This gives a range of 0.2 to 0.8 for failed results.
            0.2 + 0.6 * (passed / total)
        }
        ProofFeedback::Unknown { is_retriable, .. } => {
            if *is_retriable {
                0.1
            } else {
                0.0
            }
        }
        ProofFeedback::Error { .. } => 0.0,
    }
}

// ---------------------------------------------------------------------------
// Orchestrator
// ---------------------------------------------------------------------------

/// Main proof orchestrator that integrates strategy planning, verification,
/// and convergence tracking into a single loop.
pub struct ProofOrchestrator<'a> {
    func: &'a FunctionSignature,
    config: OrchestratorConfig,
    backend: &'a dyn LlmBackend,
}

impl<'a> ProofOrchestrator<'a> {
    /// Create a new orchestrator for a function.
    pub fn new(
        func: &'a FunctionSignature,
        config: OrchestratorConfig,
        backend: &'a dyn LlmBackend,
    ) -> Self {
        Self {
            func,
            config,
            backend,
        }
    }

    /// Run the orchestrator loop to convergence or budget exhaustion.
    pub fn run(&self) -> Result<OrchestratorResult, OracleError> {
        let strategy = select_strategy(self.func, &self.config);
        let mut history: Vec<IterationRecord> = Vec::new();
        let mut feedback_history: Vec<(ProposedAnnotations, ProofFeedback)> = Vec::new();
        let mut total_proposals = 0usize;
        let mut best_overall_score = 0.0f64;
        let mut best_annotations: Option<ProposedAnnotations> = None;
        let mut prev_best_score = 0.0f64;
        let mut _stagnation_count = 0usize;

        for iteration in 1..=self.config.max_iterations {
            if self.config.verbose {
                eprintln!(
                    "[orchestrator] iteration {}/{} strategy={}",
                    iteration,
                    self.config.max_iterations,
                    strategy.as_str(),
                );
            }

            let mut iter_best_score = 0.0f64;
            let mut iter_best_proposal: Option<ProposedAnnotations> = None;
            let mut iter_verified = false;
            let mut iter_proposal_count = 0usize;

            // Evaluate up to budget_per_iteration proposals.
            for _ in 0..self.config.budget_per_iteration {
                let proposal = match self
                    .backend
                    .propose_annotations(&self.func.source, &feedback_history)
                {
                    Ok(p) => p,
                    Err(OracleError::BackendExhausted { .. }) => break,
                    Err(e) => return Err(e),
                };

                iter_proposal_count += 1;
                total_proposals += 1;

                // Verify the proposal using the lightweight verify path.
                let feedback = crate::verify::verify_with_annotations(
                    &self.func.name,
                    &self.func.params,
                    &proposal.requires,
                    &proposal.ensures,
                );

                let score = score_feedback(&feedback);

                if self.config.verbose {
                    eprintln!(
                        "[orchestrator]   proposal {} score={:.3} verified={}",
                        iter_proposal_count,
                        score,
                        feedback.is_verified(),
                    );
                }

                if score > iter_best_score {
                    iter_best_score = score;
                    iter_best_proposal = Some(proposal.clone());
                    iter_verified = feedback.is_verified();
                }

                feedback_history.push((proposal, feedback));

                // Early exit if we verified this iteration.
                if iter_verified {
                    break;
                }
            }

            // Track best overall.
            if iter_best_score > best_overall_score {
                best_overall_score = iter_best_score;
                best_annotations = iter_best_proposal;
            }

            // Track stagnation for convergence detection.
            if (iter_best_score - prev_best_score).abs() < 1e-9 {
                _stagnation_count += 1;
            } else {
                _stagnation_count = 0;
            }
            prev_best_score = iter_best_score;

            history.push(IterationRecord {
                iteration,
                strategy_used: strategy.as_str().to_owned(),
                proposal_count: iter_proposal_count,
                best_score: iter_best_score,
                verified: iter_verified,
            });

            // Convergence check: score meets threshold.
            if best_overall_score >= self.config.convergence_threshold {
                if self.config.verbose {
                    eprintln!(
                        "[orchestrator] converged at iteration {} (score {:.3} >= {:.3})",
                        iteration, best_overall_score, self.config.convergence_threshold,
                    );
                }

                let final_annotations = best_annotations.as_ref().map(FinalAnnotations::from);

                return Ok(OrchestratorResult {
                    final_annotations,
                    iterations_used: iteration,
                    total_proposals,
                    converged: true,
                    history,
                });
            }

            // If no proposals were generated this iteration, stop early.
            if iter_proposal_count == 0 {
                break;
            }
        }

        // Budget exhausted or no more proposals.
        let converged = best_overall_score >= self.config.convergence_threshold;
        let final_annotations = if converged {
            best_annotations.as_ref().map(FinalAnnotations::from)
        } else {
            None
        };

        Ok(OrchestratorResult {
            final_annotations,
            iterations_used: history.len(),
            total_proposals,
            converged,
            history,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::MockBackend;

    // --- Helper constructors ---

    fn simple_func(name: &str) -> FunctionSignature {
        FunctionSignature {
            name: name.to_owned(),
            params: vec![("x".to_owned(), "u32".to_owned())],
            return_type: Some("u32".to_owned()),
            source: format!("fn {}(x: u32) -> u32 {{ x }}", name),
            ..Default::default()
        }
    }

    fn loop_func(name: &str) -> FunctionSignature {
        FunctionSignature {
            name: name.to_owned(),
            params: vec![
                ("data".to_owned(), "&[u32]".to_owned()),
                ("target".to_owned(), "u32".to_owned()),
            ],
            return_type: Some("usize".to_owned()),
            source: format!(
                "fn {}(data: &[u32], target: u32) -> usize {{ \
                 let mut i = 0; while i < data.len() {{ i += 1; }} i }}",
                name
            ),
            ..Default::default()
        }
    }

    fn complex_func(name: &str) -> FunctionSignature {
        FunctionSignature {
            name: name.to_owned(),
            params: vec![
                ("root".to_owned(), "&mut Map<Key, Value>".to_owned()),
                ("proof".to_owned(), "Vec<Hash>".to_owned()),
                ("leaf".to_owned(), "&[u8]".to_owned()),
                ("config".to_owned(), "Config<'a>".to_owned()),
            ],
            return_type: Some("Result<Option<Proof>, Error>".to_owned()),
            source: format!(
                "fn {}<'a>(root: &mut Map<Key, Value>, proof: Vec<Hash>, \
                 leaf: &[u8], config: Config<'a>) -> Result<Option<Proof>, Error> {{ todo!() }}",
                name
            ),
            ..Default::default()
        }
    }

    fn empty_func() -> FunctionSignature {
        FunctionSignature {
            name: "empty".to_owned(),
            params: vec![],
            return_type: None,
            source: "fn empty() {}".to_owned(),
            ..Default::default()
        }
    }

    fn make_verifiable_proposal() -> ProposedAnnotations {
        ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_owned()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_owned(),
        }
    }

    fn make_failing_proposal(ensures: &str) -> ProposedAnnotations {
        ProposedAnnotations {
            requires: vec![],
            ensures: vec![ensures.to_owned()],
            invariants: vec![],
            decreases: vec![],
            raw_response: format!("ensures!({})", ensures),
        }
    }

    // --- OrchestratorConfig tests ---

    #[test]
    fn test_config_default_values() {
        let config = OrchestratorConfig::default();
        assert_eq!(config.max_iterations, 10);
        assert_eq!(config.budget_per_iteration, 5);
        assert!((config.convergence_threshold - 0.95).abs() < f64::EPSILON);
        assert!(config.enable_cgsr);
        assert!(config.enable_decomposition);
        assert!(!config.verbose);
    }

    #[test]
    fn test_config_builder_defaults_match() {
        let from_default = OrchestratorConfig::default();
        let from_builder = OrchestratorConfig::builder().build();
        assert_eq!(from_default.max_iterations, from_builder.max_iterations);
        assert_eq!(
            from_default.budget_per_iteration,
            from_builder.budget_per_iteration
        );
        assert!(
            (from_default.convergence_threshold - from_builder.convergence_threshold).abs()
                < f64::EPSILON
        );
        assert_eq!(from_default.enable_cgsr, from_builder.enable_cgsr);
        assert_eq!(
            from_default.enable_decomposition,
            from_builder.enable_decomposition
        );
        assert_eq!(from_default.verbose, from_builder.verbose);
    }

    #[test]
    fn test_config_builder_custom_values() {
        let config = OrchestratorConfig::builder()
            .max_iterations(20)
            .budget_per_iteration(3)
            .convergence_threshold(0.8)
            .enable_cgsr(false)
            .enable_decomposition(false)
            .verbose(true)
            .build();
        assert_eq!(config.max_iterations, 20);
        assert_eq!(config.budget_per_iteration, 3);
        assert!((config.convergence_threshold - 0.8).abs() < f64::EPSILON);
        assert!(!config.enable_cgsr);
        assert!(!config.enable_decomposition);
        assert!(config.verbose);
    }

    #[test]
    fn test_config_builder_clamps_threshold() {
        let config = OrchestratorConfig::builder()
            .convergence_threshold(1.5)
            .build();
        assert!((config.convergence_threshold - 1.0).abs() < f64::EPSILON);

        let config_neg = OrchestratorConfig::builder()
            .convergence_threshold(-0.5)
            .build();
        assert!((config_neg.convergence_threshold - 0.0).abs() < f64::EPSILON);
    }

    // --- IterationRecord tests ---

    #[test]
    fn test_iteration_record_creation() {
        let record = IterationRecord {
            iteration: 1,
            strategy_used: "template_mining".to_owned(),
            proposal_count: 3,
            best_score: 0.75,
            verified: false,
        };
        assert_eq!(record.iteration, 1);
        assert_eq!(record.strategy_used, "template_mining");
        assert_eq!(record.proposal_count, 3);
        assert!((record.best_score - 0.75).abs() < f64::EPSILON);
        assert!(!record.verified);
    }

    #[test]
    fn test_iteration_record_verified() {
        let record = IterationRecord {
            iteration: 5,
            strategy_used: "cgsr".to_owned(),
            proposal_count: 1,
            best_score: 1.0,
            verified: true,
        };
        assert!(record.verified);
        assert!((record.best_score - 1.0).abs() < f64::EPSILON);
    }

    // --- FinalAnnotations tests ---

    #[test]
    fn test_final_annotations_from_proposed() {
        let proposed = ProposedAnnotations {
            requires: vec!["x > 0".to_owned()],
            ensures: vec!["result >= 1".to_owned()],
            invariants: vec![
                ("loop1".to_owned(), "i >= 0".to_owned()),
                ("loop2".to_owned(), "j < n".to_owned()),
            ],
            decreases: vec!["n - i".to_owned()],
            raw_response: "raw".to_owned(),
        };
        let final_ann = FinalAnnotations::from(&proposed);
        assert_eq!(final_ann.requires, vec!["x > 0"]);
        assert_eq!(final_ann.ensures, vec!["result >= 1"]);
        assert_eq!(final_ann.invariants, vec!["i >= 0", "j < n"]);
    }

    // --- Strategy selection tests ---

    #[test]
    fn test_strategy_simple_function_uses_template_mining() {
        let func = simple_func("add_one");
        let config = OrchestratorConfig::default();
        let strategy = select_strategy(&func, &config);
        assert_eq!(strategy, Strategy::TemplateMining);
    }

    #[test]
    fn test_strategy_loop_function_uses_cgsr() {
        let func = loop_func("search");
        let config = OrchestratorConfig::default();
        let strategy = select_strategy(&func, &config);
        assert_eq!(strategy, Strategy::Cgsr);
    }

    #[test]
    fn test_strategy_complex_function_uses_decomposition() {
        let func = complex_func("verify_tree");
        let config = OrchestratorConfig::default();
        let strategy = select_strategy(&func, &config);
        assert_eq!(strategy, Strategy::Decomposition);
    }

    #[test]
    fn test_strategy_cgsr_disabled_falls_through() {
        let func = loop_func("search");
        let config = OrchestratorConfig::builder().enable_cgsr(false).build();
        let strategy = select_strategy(&func, &config);
        // Loop func has 2 params + no generics = score 2, which is <= 3.
        // But the source contains "while " so without CGSR it should still
        // route based on complexity. Score 2 means TemplateMining.
        assert_eq!(strategy, Strategy::TemplateMining);
    }

    #[test]
    fn test_strategy_decomposition_disabled_falls_to_oracle() {
        let func = complex_func("verify_tree");
        let config = OrchestratorConfig::builder()
            .enable_decomposition(false)
            .build();
        let strategy = select_strategy(&func, &config);
        // Complex func, no decomposition => PlainOracle (score >= 6 but
        // decomposition disabled, and complexity > 3).
        assert_eq!(strategy, Strategy::PlainOracle);
    }

    // --- Score feedback tests ---

    #[test]
    fn test_score_verified_is_one() {
        use std::time::Duration;
        let fb = ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::from_millis(10),
            certificate_info: None,
        };
        assert!((score_feedback(&fb) - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_failed_no_sub_assertions() {
        use std::time::Duration;
        let fb = ProofFeedback::Failed {
            counterexamples: vec![],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures".to_owned(),
            solver_mode: "Default".to_owned(),
            elapsed: Duration::from_millis(5),
        };
        assert!((score_feedback(&fb) - 0.2).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_unknown_retriable() {
        use std::time::Duration;
        let fb = ProofFeedback::Unknown {
            reason: "timeout".to_owned(),
            category: "timeout".to_owned(),
            is_retriable: true,
            suggestion: "simplify".to_owned(),
            elapsed: Duration::from_millis(100),
        };
        assert!((score_feedback(&fb) - 0.1).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_error_is_zero() {
        let fb = ProofFeedback::Error {
            message: "crash".to_owned(),
        };
        assert!((score_feedback(&fb) - 0.0).abs() < f64::EPSILON);
    }

    // --- Orchestrator integration tests ---

    #[test]
    fn test_orchestrator_converges_on_first_try() {
        let func = simple_func("nonneg");
        let backend = MockBackend::new(vec![make_verifiable_proposal()]);
        let config = OrchestratorConfig::builder()
            .max_iterations(5)
            .budget_per_iteration(1)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(result.converged);
        assert!(result.final_annotations.is_some());
        assert_eq!(result.iterations_used, 1);
        assert_eq!(result.total_proposals, 1);
        assert_eq!(result.history.len(), 1);
        assert!(result.history[0].verified);
        assert!((result.history[0].best_score - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_orchestrator_hits_budget_limit() {
        let func = simple_func("hard");
        // All proposals fail (x > 100 for u32 identity is too strong without requires).
        let proposals: Vec<ProposedAnnotations> = (0..10)
            .map(|i| make_failing_proposal(&format!("x > {}", 100 + i)))
            .collect();
        let backend = MockBackend::new(proposals);
        let config = OrchestratorConfig::builder()
            .max_iterations(2)
            .budget_per_iteration(1)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(!result.converged);
        assert!(result.final_annotations.is_none());
        assert_eq!(result.iterations_used, 2);
        assert_eq!(result.history.len(), 2);
    }

    #[test]
    fn test_orchestrator_empty_function() {
        let func = empty_func();
        let backend = MockBackend::new(vec![ProposedAnnotations {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            decreases: vec![],
            raw_response: String::new(),
        }]);
        let config = OrchestratorConfig::builder()
            .max_iterations(3)
            .budget_per_iteration(1)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        // Empty function with empty annotations verifies trivially.
        assert!(result.converged);
        assert_eq!(result.iterations_used, 1);
    }

    #[test]
    fn test_orchestrator_history_tracking() {
        let func = simple_func("tracked");
        let proposals = vec![
            make_failing_proposal("x > 100"),
            make_failing_proposal("x > 50"),
            make_verifiable_proposal(),
        ];
        let backend = MockBackend::new(proposals);
        let config = OrchestratorConfig::builder()
            .max_iterations(5)
            .budget_per_iteration(1)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(result.converged);
        assert_eq!(result.history.len(), 3);

        // First two iterations should not be verified.
        assert!(!result.history[0].verified);
        assert!(!result.history[1].verified);
        // Third should be verified.
        assert!(result.history[2].verified);

        // Iteration numbers should be sequential.
        for (i, rec) in result.history.iter().enumerate() {
            assert_eq!(rec.iteration, i + 1);
        }
    }

    #[test]
    fn test_orchestrator_multiple_proposals_per_iteration() {
        let func = simple_func("multi");
        // 3 failing proposals then 1 verifiable.
        let proposals = vec![
            make_failing_proposal("x > 100"),
            make_failing_proposal("x > 50"),
            make_failing_proposal("x > 10"),
            make_verifiable_proposal(),
        ];
        let backend = MockBackend::new(proposals);
        let config = OrchestratorConfig::builder()
            .max_iterations(5)
            .budget_per_iteration(4)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(result.converged);
        // All 4 proposals should be evaluated in the first iteration
        // (budget_per_iteration=4, and the 4th verifies).
        assert_eq!(result.iterations_used, 1);
        assert_eq!(result.total_proposals, 4);
    }

    #[test]
    fn test_orchestrator_backend_exhausted_stops_gracefully() {
        let func = simple_func("exhaust");
        // Only 1 failing proposal available.
        let backend = MockBackend::new(vec![make_failing_proposal("x > 100")]);
        let config = OrchestratorConfig::builder()
            .max_iterations(10)
            .budget_per_iteration(3)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        // Should stop after using the single proposal, then backend is exhausted.
        assert!(!result.converged);
        assert_eq!(result.total_proposals, 1);
    }

    #[test]
    fn test_orchestrator_convergence_detection_via_score() {
        let func = simple_func("converge_test");
        // A proposal that verifies (score 1.0) should trigger convergence
        // even with a high threshold.
        let backend = MockBackend::new(vec![make_verifiable_proposal()]);
        let config = OrchestratorConfig::builder()
            .convergence_threshold(0.99)
            .max_iterations(10)
            .budget_per_iteration(1)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(result.converged);
        assert_eq!(result.iterations_used, 1);
    }

    #[test]
    fn test_orchestrator_strategy_recorded_in_history() {
        let func = simple_func("strat_check");
        let backend = MockBackend::new(vec![make_verifiable_proposal()]);
        let config = OrchestratorConfig::default();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(!result.history.is_empty());
        // Simple func should use template_mining strategy.
        assert_eq!(result.history[0].strategy_used, "template_mining");
    }

    #[test]
    fn test_orchestrator_loop_func_strategy_in_history() {
        let func = loop_func("loop_strat");
        let backend = MockBackend::new(vec![make_verifiable_proposal()]);
        let config = OrchestratorConfig::default();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(!result.history.is_empty());
        assert_eq!(result.history[0].strategy_used, "cgsr");
    }

    #[test]
    fn test_orchestrator_result_total_proposals_accumulates() {
        let func = simple_func("accumulate");
        let proposals = vec![
            make_failing_proposal("x > 100"),
            make_failing_proposal("x > 50"),
            make_failing_proposal("x > 10"),
            make_failing_proposal("x > 5"),
            make_verifiable_proposal(),
        ];
        let backend = MockBackend::new(proposals);
        let config = OrchestratorConfig::builder()
            .max_iterations(10)
            .budget_per_iteration(2)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(result.converged);
        assert_eq!(result.total_proposals, 5);
        // 2 proposals per iteration for first 2 iterations, then 1 in the third.
        assert_eq!(result.iterations_used, 3);
    }

    #[test]
    fn test_strategy_as_str_values() {
        assert_eq!(Strategy::TemplateMining.as_str(), "template_mining");
        assert_eq!(Strategy::Cgsr.as_str(), "cgsr");
        assert_eq!(Strategy::Decomposition.as_str(), "decomposition");
        assert_eq!(Strategy::PlainOracle.as_str(), "plain_oracle");
    }

    #[test]
    fn test_orchestrator_zero_max_iterations() {
        let func = simple_func("zero_iter");
        let backend = MockBackend::new(vec![make_verifiable_proposal()]);
        let config = OrchestratorConfig::builder().max_iterations(0).build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(!result.converged);
        assert_eq!(result.iterations_used, 0);
        assert_eq!(result.total_proposals, 0);
        assert!(result.history.is_empty());
        assert!(result.final_annotations.is_none());
    }

    #[test]
    fn test_orchestrator_score_monotonic_best_tracking() {
        let func = simple_func("mono");
        // Proposals with increasing quality (the third verifies).
        let proposals = vec![
            make_failing_proposal("x > 100"),
            make_failing_proposal("x > 50"),
            make_verifiable_proposal(),
        ];
        let backend = MockBackend::new(proposals);
        let config = OrchestratorConfig::builder()
            .max_iterations(10)
            .budget_per_iteration(1)
            .build();
        let orch = ProofOrchestrator::new(&func, config, &backend);
        let result = orch.run().unwrap();

        assert!(result.converged);
        // Best score should be recorded in the final iteration.
        let last = result.history.last().unwrap();
        assert!((last.best_score - 1.0).abs() < f64::EPSILON);
    }
}
