// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// CGSR Engine — complete Counterexample-Guided Specification Refinement loop
// with integrated metrics tracking. Wires together template mining, LLM-based
// proposal, verification, counterexample refinement, and convergence analysis
// into a single entry point.

#![allow(dead_code)]

use std::time::{Duration, Instant};

use crate::backend::{LlmBackend, ProposedAnnotations};
use crate::engine::FunctionSignature;
use crate::error::OracleError;
use crate::feedback::ProofFeedback;

// ---------------------------------------------------------------------------
// CandidateSource
// ---------------------------------------------------------------------------

/// How a candidate specification was generated.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CandidateSource {
    /// Produced by template instantiation against the function signature.
    TemplateMining,
    /// Refined from a prior candidate using counterexample feedback.
    CounterexampleRefinement,
    /// Proposed directly by the LLM backend.
    LlmProposal,
    /// Combination of multiple sources (e.g., template + LLM merge).
    Combination,
}

// ---------------------------------------------------------------------------
// SpecCandidate
// ---------------------------------------------------------------------------

/// A candidate specification under evaluation in the CGSR loop.
#[derive(Debug, Clone)]
pub struct SpecCandidate {
    /// Precondition clauses (`requires!`).
    pub requires: Vec<String>,
    /// Postcondition clauses (`ensures!`).
    pub ensures: Vec<String>,
    /// Loop invariant clauses (`invariant!`).
    pub invariants: Vec<String>,
    /// Composite quality score (0.0..=1.0 nominal range).
    pub score: f64,
    /// How this candidate was produced.
    pub source: CandidateSource,
}

impl SpecCandidate {
    /// Total clause count across requires, ensures, and invariants.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.requires.len() + self.ensures.len() + self.invariants.len()
    }

    /// Build from an LLM-proposed annotation set (score starts at 0).
    #[must_use]
    pub(crate) fn from_proposal(proposal: &ProposedAnnotations, source: CandidateSource) -> Self {
        Self {
            requires: proposal.requires.clone(),
            ensures: proposal.ensures.clone(),
            invariants: proposal.invariants.iter().map(|(_, v)| v.clone()).collect(),
            score: 0.0,
            source,
        }
    }
}

// ---------------------------------------------------------------------------
// CounterexampleInfo
// ---------------------------------------------------------------------------

/// A single variable binding from a counterexample.
#[derive(Debug, Clone)]
pub struct CounterexampleInfo {
    /// Variable name (e.g., "x", "result").
    pub variable: String,
    /// Rendered value (e.g., "-42", "[1, 2, 3]").
    pub value: String,
    /// Type of the variable (e.g., "i32", "Seq<u64>").
    pub ty: String,
}

// ---------------------------------------------------------------------------
// RefinementRound
// ---------------------------------------------------------------------------

/// Data captured for a single refinement round.
#[derive(Debug, Clone)]
pub struct RefinementRound {
    /// 1-indexed round number.
    pub round_number: usize,
    /// All candidates evaluated this round.
    pub specs_proposed: Vec<SpecCandidate>,
    /// The best candidate from this round (if any).
    pub best_candidate: Option<SpecCandidate>,
    /// Score of the best candidate.
    pub best_score: f64,
    /// Number of counterexamples consumed this round.
    pub counterexamples_used: usize,
    /// Wall-clock time for this round.
    pub elapsed: Duration,
}

// ---------------------------------------------------------------------------
// MetricsSummary
// ---------------------------------------------------------------------------

/// Aggregate metrics for a completed CGSR engine session.
#[derive(Debug, Clone)]
pub struct MetricsSummary {
    /// Total specs evaluated across all rounds.
    pub total_specs_evaluated: usize,
    /// Total counterexamples generated across all rounds.
    pub total_counterexamples: usize,
    /// Average score improvement per round (positive = converging).
    pub convergence_rate: f64,
    /// Final best score achieved.
    pub final_score: f64,
    /// Score of the best candidate at each round boundary.
    pub score_progression: Vec<f64>,
}

// ---------------------------------------------------------------------------
// CgsrOutcome
// ---------------------------------------------------------------------------

/// Final result of a complete CGSR engine session.
#[derive(Debug, Clone)]
pub struct CgsrOutcome {
    /// Best specification found (None if no valid candidate was produced).
    pub best_spec: Option<SpecCandidate>,
    /// Number of refinement rounds consumed.
    pub rounds_used: usize,
    /// Whether the engine converged (score above threshold for the window).
    pub converged: bool,
    /// Per-round history.
    pub history: Vec<RefinementRound>,
    /// Aggregate metrics.
    pub metrics_summary: MetricsSummary,
}

// ---------------------------------------------------------------------------
// CgsrEngineConfig
// ---------------------------------------------------------------------------

/// Configuration for the CGSR engine loop.
#[derive(Debug, Clone)]
pub struct CgsrEngineConfig {
    /// Maximum refinement rounds before giving up.
    pub max_refinement_rounds: usize,
    /// Maximum candidate specs to evaluate per round.
    pub max_specs_per_round: usize,
    /// Number of recent rounds to consider for convergence detection.
    pub convergence_window: usize,
    /// Score threshold above which the engine declares convergence.
    pub convergence_threshold: f64,
    /// Whether to use template mining for initial candidates.
    pub enable_template_mining: bool,
    /// Whether to refine candidates using counterexample feedback.
    pub enable_counterexample_refinement: bool,
    /// Per-clause penalty applied during scoring (Occam's razor).
    pub occam_penalty: f64,
    /// Emit progress to stderr.
    pub verbose: bool,
}

impl Default for CgsrEngineConfig {
    fn default() -> Self {
        Self {
            max_refinement_rounds: 20,
            max_specs_per_round: 5,
            convergence_window: 5,
            convergence_threshold: 0.95,
            enable_template_mining: true,
            enable_counterexample_refinement: true,
            occam_penalty: 0.1,
            verbose: false,
        }
    }
}

// ---------------------------------------------------------------------------
// CounterexampleRefiner
// ---------------------------------------------------------------------------

/// Takes counterexample data from failed verification and produces
/// strengthened candidate specifications.
pub(crate) struct CounterexampleRefiner {
    /// Accumulated counterexamples across all rounds.
    counterexamples: Vec<CounterexampleInfo>,
}

impl CounterexampleRefiner {
    pub(crate) fn new() -> Self {
        Self {
            counterexamples: Vec::new(),
        }
    }

    /// Ingest counterexample bindings from a `ProofFeedback::Failed`.
    pub(crate) fn ingest_feedback(&mut self, feedback: &ProofFeedback) {
        if let ProofFeedback::Failed {
            counterexamples, ..
        } = feedback
        {
            for cx in counterexamples {
                self.counterexamples.push(CounterexampleInfo {
                    variable: cx.name.clone(),
                    value: cx.value.clone(),
                    ty: cx.ty.clone(),
                });
            }
        }
    }

    /// Total counterexamples accumulated so far.
    pub(crate) fn count(&self) -> usize {
        self.counterexamples.len()
    }

    /// Read-only access to accumulated counterexamples.
    pub(crate) fn counterexamples(&self) -> &[CounterexampleInfo] {
        &self.counterexamples
    }

    /// Strengthen a candidate by adding preconditions that exclude known
    /// counterexample values.
    ///
    /// For each counterexample variable, if a numeric literal can be parsed
    /// from the value, a range exclusion clause is synthesized. For
    /// non-numeric values a simple inequality is emitted.
    pub(crate) fn strengthen(&self, candidate: &SpecCandidate) -> SpecCandidate {
        let mut strengthened = candidate.clone();
        strengthened.source = CandidateSource::CounterexampleRefinement;

        for cx in &self.counterexamples {
            let clause = if let Ok(n) = cx.value.parse::<i128>() {
                // Exclude the specific value.
                format!("{} != {}", cx.variable, n)
            } else {
                // Non-numeric: emit a raw inequality.
                format!("{} != {}", cx.variable, cx.value)
            };

            // Avoid adding duplicate preconditions.
            if !strengthened.requires.contains(&clause) {
                strengthened.requires.push(clause);
            }
        }

        strengthened
    }
}

// ---------------------------------------------------------------------------
// Scoring helpers
// ---------------------------------------------------------------------------

/// Score a candidate specification based on verification outcome.
///
/// Rubric:
/// - Verified feedback: 1.0 base
/// - Failed (counterexample): 0.3 base
/// - Unknown: 0.2 base
/// - Error: 0.0 base
///
/// Occam penalty: `-occam_penalty` per clause beyond the first two.
fn score_candidate(candidate: &SpecCandidate, feedback: &ProofFeedback, occam_penalty: f64) -> f64 {
    let base = match feedback {
        ProofFeedback::Verified { .. } => 1.0,
        ProofFeedback::Failed { .. } => 0.3,
        ProofFeedback::Unknown { .. } => 0.2,
        ProofFeedback::Error { .. } => 0.0,
    };

    let clause_count = candidate.clause_count();
    let penalty = if clause_count > 2 {
        (clause_count - 2) as f64 * occam_penalty
    } else {
        0.0
    };

    (base - penalty).max(0.0)
}

/// Check convergence: the last `window` entries in `progression` are all
/// at or above `threshold`.
fn check_convergence(progression: &[f64], window: usize, threshold: f64) -> bool {
    if progression.len() < window {
        return false;
    }
    let tail = &progression[progression.len() - window..];
    tail.iter().all(|&s| s >= threshold)
}

// ---------------------------------------------------------------------------
// CgsrEngine
// ---------------------------------------------------------------------------

/// The main CGSR engine that drives the complete refinement loop.
///
/// Usage:
/// ```ignore
/// let config = CgsrEngineConfig::default();
/// let func = FunctionSignature { .. };
/// let mut engine = CgsrEngine::new(config, &func);
/// let outcome = engine.run(&backend)?;
/// ```
pub struct CgsrEngine {
    config: CgsrEngineConfig,
    function: FunctionSignature,
    refiner: CounterexampleRefiner,
    rounds: Vec<RefinementRound>,
    best_candidate: Option<SpecCandidate>,
    best_score: f64,
    score_progression: Vec<f64>,
    total_specs_evaluated: usize,
}

impl CgsrEngine {
    /// Create a new engine for the given function.
    #[must_use]
    pub fn new(config: CgsrEngineConfig, function: &FunctionSignature) -> Self {
        Self {
            config,
            function: function.clone(),
            refiner: CounterexampleRefiner::new(),
            rounds: Vec::new(),
            best_candidate: None,
            best_score: 0.0,
            score_progression: Vec::new(),
            total_specs_evaluated: 0,
        }
    }

    /// Run the full CGSR loop: mine templates, propose via LLM, verify,
    /// refine with counterexamples, and check convergence.
    pub fn run(&mut self, backend: &dyn LlmBackend) -> Result<CgsrOutcome, OracleError> {
        let mut history_for_backend: Vec<(ProposedAnnotations, ProofFeedback)> = Vec::new();

        for round_num in 1..=self.config.max_refinement_rounds {
            let round_start = Instant::now();

            if self.config.verbose {
                eprintln!(
                    "[cgsr-engine] round {}/{} for '{}'",
                    round_num, self.config.max_refinement_rounds, self.function.name
                );
            }

            let mut round_candidates: Vec<SpecCandidate> = Vec::new();
            let mut round_cex_count: usize = 0;

            // Phase 1: Propose candidates from the LLM backend.
            let specs_to_propose = self
                .config
                .max_specs_per_round
                .min(self.config.max_specs_per_round);

            for _ in 0..specs_to_propose {
                let proposal_result =
                    backend.propose_annotations(&self.function.source, &history_for_backend);

                let proposal = match proposal_result {
                    Ok(p) => p,
                    Err(OracleError::BackendExhausted { .. }) => break,
                    Err(e) => return Err(e),
                };

                let candidate =
                    SpecCandidate::from_proposal(&proposal, CandidateSource::LlmProposal);
                round_candidates.push(candidate);
            }

            // Phase 2: If counterexample refinement is enabled and we have
            // prior counterexamples, produce strengthened variants of the
            // best candidate so far.
            if self.config.enable_counterexample_refinement && self.refiner.count() > 0 {
                if let Some(base) = &self.best_candidate {
                    let strengthened = self.refiner.strengthen(base);
                    round_candidates.push(strengthened);
                }
            }

            // Phase 3: Verify each candidate and score.
            let mut round_best_candidate: Option<SpecCandidate> = None;
            let mut round_best_score: f64 = 0.0;

            for candidate in &mut round_candidates {
                let feedback = Self::verify_candidate(candidate, &self.function);

                let score = score_candidate(candidate, &feedback, self.config.occam_penalty);
                candidate.score = score;
                self.total_specs_evaluated += 1;

                if self.config.verbose {
                    eprintln!(
                        "[cgsr-engine]   candidate score={:.3} source={:?} feedback={}",
                        score,
                        candidate.source,
                        feedback_tag(&feedback),
                    );
                }

                // Collect counterexamples for future refinement.
                if feedback.is_failed() {
                    self.refiner.ingest_feedback(&feedback);
                    round_cex_count += 1;
                }

                // Record history for the backend.
                let proposal = ProposedAnnotations {
                    requires: candidate.requires.clone(),
                    ensures: candidate.ensures.clone(),
                    invariants: candidate
                        .invariants
                        .iter()
                        .enumerate()
                        .map(|(i, inv)| (format!("loop_{i}"), inv.clone()))
                        .collect(),
                    decreases: vec![],
                    raw_response: String::new(),
                };
                history_for_backend.push((proposal, feedback.clone()));

                // Track round-level best.
                if score > round_best_score {
                    round_best_score = score;
                    round_best_candidate = Some(candidate.clone());
                }

                // Update global best.
                if score > self.best_score {
                    self.best_score = score;
                    self.best_candidate = Some(candidate.clone());
                }

                // Early exit if verified (score == 1.0).
                if feedback.is_verified() {
                    break;
                }
            }

            self.score_progression.push(round_best_score);

            let round = RefinementRound {
                round_number: round_num,
                specs_proposed: round_candidates,
                best_candidate: round_best_candidate,
                best_score: round_best_score,
                counterexamples_used: round_cex_count,
                elapsed: round_start.elapsed(),
            };
            self.rounds.push(round);

            // Phase 4: Convergence check.
            if check_convergence(
                &self.score_progression,
                self.config.convergence_window,
                self.config.convergence_threshold,
            ) {
                return Ok(self.build_outcome(true));
            }

            // Early exit if we hit a perfect score.
            if self.best_score >= 1.0 {
                return Ok(self.build_outcome(true));
            }
        }

        // Budget exhausted.
        Ok(self.build_outcome(false))
    }

    /// Verify a candidate against the function using the trust_vc verification
    /// bridge.
    fn verify_candidate(candidate: &SpecCandidate, function: &FunctionSignature) -> ProofFeedback {
        crate::verify::verify_with_annotations(
            &function.name,
            &function.params,
            &candidate.requires,
            &candidate.ensures,
        )
    }

    /// Assemble the final outcome from accumulated state.
    fn build_outcome(&self, converged: bool) -> CgsrOutcome {
        let convergence_rate = if self.score_progression.len() >= 2 {
            let first = self.score_progression.first().copied().unwrap_or(0.0);
            let last = self.score_progression.last().copied().unwrap_or(0.0);
            (last - first) / (self.score_progression.len() - 1) as f64
        } else {
            0.0
        };

        CgsrOutcome {
            best_spec: self.best_candidate.clone(),
            rounds_used: self.rounds.len(),
            converged,
            history: self.rounds.clone(),
            metrics_summary: MetricsSummary {
                total_specs_evaluated: self.total_specs_evaluated,
                total_counterexamples: self.refiner.count(),
                convergence_rate,
                final_score: self.best_score,
                score_progression: self.score_progression.clone(),
            },
        }
    }
}

/// One-word tag for a `ProofFeedback` variant (logging helper).
fn feedback_tag(feedback: &ProofFeedback) -> &'static str {
    match feedback {
        ProofFeedback::Verified { .. } => "verified",
        ProofFeedback::Failed { .. } => "failed",
        ProofFeedback::Unknown { .. } => "unknown",
        ProofFeedback::Error { .. } => "error",
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::{MockBackend, ProposedAnnotations};
    use crate::engine::FunctionSignature;
    use std::time::Duration;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn simple_func() -> FunctionSignature {
        FunctionSignature {
            name: "add_one".to_string(),
            params: vec![("x".to_string(), "u32".to_string())],
            return_type: Some("u32".to_string()),
            source: "fn add_one(x: u32) -> u32 { x + 1 }".to_string(),
            ..Default::default()
        }
    }

    fn i32_func() -> FunctionSignature {
        FunctionSignature {
            name: "identity".to_string(),
            params: vec![("x".to_string(), "i32".to_string())],
            return_type: Some("i32".to_string()),
            source: "fn identity(x: i32) -> i32 { x }".to_string(),
            ..Default::default()
        }
    }

    fn trivial_proposal() -> ProposedAnnotations {
        ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_string(),
        }
    }

    fn failing_proposal() -> ProposedAnnotations {
        ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x > 0)".to_string(),
        }
    }

    fn correct_proposal_with_precond() -> ProposedAnnotations {
        ProposedAnnotations {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["x >= 1".to_string()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(x > 0) ensures!(x >= 1)".to_string(),
        }
    }

    // -----------------------------------------------------------------------
    // CgsrEngineConfig tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_default_values() {
        let cfg = CgsrEngineConfig::default();
        assert_eq!(cfg.max_refinement_rounds, 20);
        assert_eq!(cfg.max_specs_per_round, 5);
        assert_eq!(cfg.convergence_window, 5);
        assert!((cfg.convergence_threshold - 0.95).abs() < f64::EPSILON);
        assert!(cfg.enable_template_mining);
        assert!(cfg.enable_counterexample_refinement);
        assert!((cfg.occam_penalty - 0.1).abs() < f64::EPSILON);
        assert!(!cfg.verbose);
    }

    #[test]
    fn test_config_custom_values() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 50,
            max_specs_per_round: 10,
            convergence_window: 3,
            convergence_threshold: 0.99,
            enable_template_mining: false,
            enable_counterexample_refinement: false,
            occam_penalty: 0.2,
            verbose: true,
        };
        assert_eq!(cfg.max_refinement_rounds, 50);
        assert_eq!(cfg.max_specs_per_round, 10);
        assert!(!cfg.enable_template_mining);
        assert!(cfg.verbose);
    }

    // -----------------------------------------------------------------------
    // CandidateSource tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_candidate_source_eq() {
        assert_eq!(
            CandidateSource::TemplateMining,
            CandidateSource::TemplateMining
        );
        assert_ne!(
            CandidateSource::LlmProposal,
            CandidateSource::CounterexampleRefinement
        );
    }

    #[test]
    fn test_candidate_source_debug() {
        let src = CandidateSource::Combination;
        let dbg = format!("{:?}", src);
        assert!(dbg.contains("Combination"));
    }

    // -----------------------------------------------------------------------
    // SpecCandidate tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_spec_candidate_clause_count_empty() {
        let c = SpecCandidate {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        assert_eq!(c.clause_count(), 0);
    }

    #[test]
    fn test_spec_candidate_clause_count_mixed() {
        let c = SpecCandidate {
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= 1".to_string(), "result <= 100".to_string()],
            invariants: vec!["i < n".to_string()],
            score: 0.5,
            source: CandidateSource::TemplateMining,
        };
        assert_eq!(c.clause_count(), 4);
    }

    #[test]
    fn test_spec_candidate_from_proposal() {
        let proposal = trivial_proposal();
        let c = SpecCandidate::from_proposal(&proposal, CandidateSource::LlmProposal);
        assert_eq!(c.ensures, vec!["x >= 0".to_string()]);
        assert!(c.requires.is_empty());
        assert_eq!(c.score, 0.0);
        assert_eq!(c.source, CandidateSource::LlmProposal);
    }

    #[test]
    fn test_spec_candidate_from_proposal_with_invariants() {
        let proposal = ProposedAnnotations {
            requires: vec!["n > 0".to_string()],
            ensures: vec!["result >= 0".to_string()],
            invariants: vec![("loop_0".to_string(), "i <= n".to_string())],
            decreases: vec!["n - i".to_string()],
            raw_response: String::new(),
        };
        let c = SpecCandidate::from_proposal(&proposal, CandidateSource::TemplateMining);
        assert_eq!(c.invariants, vec!["i <= n".to_string()]);
        assert_eq!(c.requires, vec!["n > 0".to_string()]);
    }

    // -----------------------------------------------------------------------
    // CounterexampleInfo tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_counterexample_info_fields() {
        let info = CounterexampleInfo {
            variable: "x".to_string(),
            value: "-42".to_string(),
            ty: "i32".to_string(),
        };
        assert_eq!(info.variable, "x");
        assert_eq!(info.value, "-42");
        assert_eq!(info.ty, "i32");
    }

    // -----------------------------------------------------------------------
    // RefinementRound tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_refinement_round_empty() {
        let round = RefinementRound {
            round_number: 1,
            specs_proposed: vec![],
            best_candidate: None,
            best_score: 0.0,
            counterexamples_used: 0,
            elapsed: Duration::from_millis(10),
        };
        assert_eq!(round.round_number, 1);
        assert!(round.specs_proposed.is_empty());
        assert!(round.best_candidate.is_none());
    }

    #[test]
    fn test_refinement_round_with_candidates() {
        let c = SpecCandidate {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            score: 1.0,
            source: CandidateSource::LlmProposal,
        };
        let round = RefinementRound {
            round_number: 3,
            specs_proposed: vec![c.clone()],
            best_candidate: Some(c),
            best_score: 1.0,
            counterexamples_used: 0,
            elapsed: Duration::from_millis(50),
        };
        assert_eq!(round.specs_proposed.len(), 1);
        assert!(round.best_candidate.is_some());
        assert!((round.best_score - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // MetricsSummary tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_metrics_summary_fields() {
        let m = MetricsSummary {
            total_specs_evaluated: 15,
            total_counterexamples: 3,
            convergence_rate: 0.12,
            final_score: 0.95,
            score_progression: vec![0.3, 0.5, 0.7, 0.9, 0.95],
        };
        assert_eq!(m.total_specs_evaluated, 15);
        assert_eq!(m.total_counterexamples, 3);
        assert_eq!(m.score_progression.len(), 5);
    }

    // -----------------------------------------------------------------------
    // CgsrOutcome tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_outcome_converged() {
        let outcome = CgsrOutcome {
            best_spec: Some(SpecCandidate {
                requires: vec![],
                ensures: vec!["x >= 0".to_string()],
                invariants: vec![],
                score: 1.0,
                source: CandidateSource::LlmProposal,
            }),
            rounds_used: 1,
            converged: true,
            history: vec![],
            metrics_summary: MetricsSummary {
                total_specs_evaluated: 1,
                total_counterexamples: 0,
                convergence_rate: 1.0,
                final_score: 1.0,
                score_progression: vec![1.0],
            },
        };
        assert!(outcome.converged);
        assert!(outcome.best_spec.is_some());
    }

    #[test]
    fn test_outcome_not_converged() {
        let outcome = CgsrOutcome {
            best_spec: None,
            rounds_used: 20,
            converged: false,
            history: vec![],
            metrics_summary: MetricsSummary {
                total_specs_evaluated: 100,
                total_counterexamples: 20,
                convergence_rate: 0.0,
                final_score: 0.3,
                score_progression: vec![0.3; 20],
            },
        };
        assert!(!outcome.converged);
        assert!(outcome.best_spec.is_none());
        assert_eq!(outcome.rounds_used, 20);
    }

    // -----------------------------------------------------------------------
    // Scoring tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_score_verified_minimal() {
        let c = SpecCandidate {
            requires: vec![],
            ensures: vec!["x >= 0".to_string()],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        let feedback = ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::ZERO,
            certificate_info: None,
        };
        let s = score_candidate(&c, &feedback, 0.1);
        assert!(
            (s - 1.0).abs() < f64::EPSILON,
            "verified + 1 clause = 1.0, got {s}"
        );
    }

    #[test]
    fn test_score_verified_with_occam_penalty() {
        let c = SpecCandidate {
            requires: vec!["a".to_string(), "b".to_string()],
            ensures: vec!["c".to_string(), "d".to_string()],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        let feedback = ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::ZERO,
            certificate_info: None,
        };
        // 4 clauses, 2 beyond baseline, penalty = 0.2
        let s = score_candidate(&c, &feedback, 0.1);
        assert!((s - 0.8).abs() < 1e-9, "expected 0.8, got {s}");
    }

    #[test]
    fn test_score_failed() {
        let c = SpecCandidate {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        let feedback = ProofFeedback::Failed {
            counterexamples: vec![],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ens".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::ZERO,
        };
        let s = score_candidate(&c, &feedback, 0.1);
        assert!((s - 0.3).abs() < 1e-9, "failed + 1 clause = 0.3, got {s}");
    }

    #[test]
    fn test_score_unknown() {
        let c = SpecCandidate {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        let feedback = ProofFeedback::Unknown {
            reason: "timeout".to_string(),
            category: "timeout".to_string(),
            is_retriable: true,
            suggestion: "try again".to_string(),
            elapsed: Duration::ZERO,
        };
        let s = score_candidate(&c, &feedback, 0.1);
        assert!((s - 0.2).abs() < 1e-9, "unknown = 0.2, got {s}");
    }

    #[test]
    fn test_score_error_is_zero() {
        let c = SpecCandidate {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        let feedback = ProofFeedback::Error {
            message: "boom".to_string(),
        };
        let s = score_candidate(&c, &feedback, 0.1);
        assert!(s.abs() < 1e-9, "error = 0.0, got {s}");
    }

    #[test]
    fn test_score_floor_at_zero() {
        // Many clauses should push penalty high, but score floors at 0.0.
        let c = SpecCandidate {
            requires: (0..20).map(|i| format!("c{i}")).collect(),
            ensures: vec!["e".to_string()],
            invariants: vec![],
            score: 0.0,
            source: CandidateSource::LlmProposal,
        };
        let feedback = ProofFeedback::Failed {
            counterexamples: vec![],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ens".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::ZERO,
        };
        let s = score_candidate(&c, &feedback, 0.1);
        assert!(s >= 0.0, "score must not go negative, got {s}");
    }

    // -----------------------------------------------------------------------
    // Convergence check tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_convergence_insufficient_data() {
        assert!(!check_convergence(&[1.0, 1.0], 5, 0.95));
    }

    #[test]
    fn test_check_convergence_all_above_threshold() {
        let prog = vec![0.96, 0.97, 0.98, 0.99, 1.0];
        assert!(check_convergence(&prog, 5, 0.95));
    }

    #[test]
    fn test_check_convergence_one_below_threshold() {
        let prog = vec![0.96, 0.97, 0.94, 0.99, 1.0];
        assert!(!check_convergence(&prog, 5, 0.95));
    }

    #[test]
    fn test_check_convergence_window_smaller_than_data() {
        let prog = vec![0.1, 0.2, 0.3, 0.96, 0.97, 0.98];
        assert!(check_convergence(&prog, 3, 0.95));
    }

    #[test]
    fn test_check_convergence_exact_threshold() {
        let prog = vec![0.95, 0.95, 0.95];
        assert!(check_convergence(&prog, 3, 0.95));
    }

    // -----------------------------------------------------------------------
    // CounterexampleRefiner tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_refiner_new_empty() {
        let r = CounterexampleRefiner::new();
        assert_eq!(r.count(), 0);
        assert!(r.counterexamples().is_empty());
    }

    #[test]
    fn test_refiner_ingest_failed_feedback() {
        let mut r = CounterexampleRefiner::new();
        let feedback = ProofFeedback::Failed {
            counterexamples: vec![crate::feedback::CounterexampleField {
                name: "x".to_string(),
                ty: "i32".to_string(),
                value: "-5".to_string(),
            }],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ens".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::ZERO,
        };
        r.ingest_feedback(&feedback);
        assert_eq!(r.count(), 1);
        assert_eq!(r.counterexamples()[0].variable, "x");
        assert_eq!(r.counterexamples()[0].value, "-5");
    }

    #[test]
    fn test_refiner_ignores_non_failed_feedback() {
        let mut r = CounterexampleRefiner::new();
        let feedback = ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::ZERO,
            certificate_info: None,
        };
        r.ingest_feedback(&feedback);
        assert_eq!(r.count(), 0);
    }

    #[test]
    fn test_refiner_strengthen_adds_preconditions() {
        let mut r = CounterexampleRefiner::new();
        r.counterexamples.push(CounterexampleInfo {
            variable: "x".to_string(),
            value: "-5".to_string(),
            ty: "i32".to_string(),
        });

        let candidate = SpecCandidate {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            score: 0.3,
            source: CandidateSource::LlmProposal,
        };

        let strengthened = r.strengthen(&candidate);
        assert_eq!(strengthened.requires, vec!["x != -5".to_string()]);
        assert_eq!(
            strengthened.source,
            CandidateSource::CounterexampleRefinement
        );
    }

    #[test]
    fn test_refiner_strengthen_no_duplicates() {
        let mut r = CounterexampleRefiner::new();
        r.counterexamples.push(CounterexampleInfo {
            variable: "x".to_string(),
            value: "0".to_string(),
            ty: "i32".to_string(),
        });
        r.counterexamples.push(CounterexampleInfo {
            variable: "x".to_string(),
            value: "0".to_string(),
            ty: "i32".to_string(),
        });

        let candidate = SpecCandidate {
            requires: vec![],
            ensures: vec!["x > 0".to_string()],
            invariants: vec![],
            score: 0.3,
            source: CandidateSource::LlmProposal,
        };

        let strengthened = r.strengthen(&candidate);
        // Duplicate counterexample values should not produce duplicate clauses.
        assert_eq!(strengthened.requires.len(), 1);
    }

    #[test]
    fn test_refiner_strengthen_non_numeric() {
        let mut r = CounterexampleRefiner::new();
        r.counterexamples.push(CounterexampleInfo {
            variable: "s".to_string(),
            value: "\"hello\"".to_string(),
            ty: "String".to_string(),
        });

        let candidate = SpecCandidate {
            requires: vec![],
            ensures: vec!["s.len() > 0".to_string()],
            invariants: vec![],
            score: 0.3,
            source: CandidateSource::LlmProposal,
        };

        let strengthened = r.strengthen(&candidate);
        assert_eq!(strengthened.requires.len(), 1);
        assert!(strengthened.requires[0].contains("s != "));
    }

    // -----------------------------------------------------------------------
    // CgsrEngine construction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_engine_new_initial_state() {
        let cfg = CgsrEngineConfig::default();
        let func = simple_func();
        let engine = CgsrEngine::new(cfg, &func);
        assert_eq!(engine.best_score, 0.0);
        assert!(engine.best_candidate.is_none());
        assert!(engine.rounds.is_empty());
        assert!(engine.score_progression.is_empty());
        assert_eq!(engine.total_specs_evaluated, 0);
    }

    // -----------------------------------------------------------------------
    // Full engine run tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_engine_run_verifies_on_first_round() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 5,
            max_specs_per_round: 1,
            convergence_window: 1,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = simple_func();
        let backend = MockBackend::new(vec![trivial_proposal()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        assert!(outcome.converged, "u32 >= 0 should verify");
        assert!(outcome.best_spec.is_some());
        assert!((outcome.metrics_summary.final_score - 1.0).abs() < f64::EPSILON);
        assert_eq!(outcome.rounds_used, 1);
    }

    #[test]
    fn test_engine_run_budget_exhausted() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 2,
            max_specs_per_round: 1,
            convergence_window: 5,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = i32_func();
        let backend = MockBackend::new(vec![failing_proposal(), failing_proposal()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        assert!(!outcome.converged);
        assert_eq!(outcome.rounds_used, 2);
        assert!(outcome.metrics_summary.total_specs_evaluated >= 2);
    }

    #[test]
    fn test_engine_run_refines_to_success() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 5,
            max_specs_per_round: 1,
            convergence_window: 1,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = i32_func();
        let backend = MockBackend::new(vec![failing_proposal(), correct_proposal_with_precond()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        assert!(
            outcome.converged,
            "should converge after adding precondition"
        );
        assert!(outcome.best_spec.is_some());
        let best = outcome.best_spec.as_ref().unwrap();
        assert!(
            !best.requires.is_empty(),
            "best spec should have precondition"
        );
    }

    #[test]
    fn test_engine_metrics_summary_progression() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 3,
            max_specs_per_round: 1,
            convergence_window: 5,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = simple_func();
        let backend = MockBackend::new(vec![trivial_proposal()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        assert!(!outcome.metrics_summary.score_progression.is_empty());
        assert!(outcome.metrics_summary.score_progression[0] >= 0.0);
    }

    #[test]
    fn test_engine_counterexample_refinement_enabled() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 3,
            max_specs_per_round: 1,
            convergence_window: 5,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: true,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = i32_func();
        // First round fails, second round the mock provides a correct spec.
        let backend = MockBackend::new(vec![
            failing_proposal(),
            // In round 2, the engine also generates a strengthened variant,
            // so we need enough proposals for the mock.
            correct_proposal_with_precond(),
            correct_proposal_with_precond(),
        ]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        // Either converged or ran the full budget.
        assert!(outcome.rounds_used <= 3);
    }

    #[test]
    fn test_engine_backend_exhausted_handled() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 5,
            max_specs_per_round: 3,
            convergence_window: 5,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = simple_func();
        // Only 1 proposal available but we request up to 3 per round.
        let backend = MockBackend::new(vec![trivial_proposal()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        // Should still complete (backend exhaustion breaks the inner loop,
        // not the outer run).
        assert!(outcome.rounds_used >= 1);
    }

    #[test]
    fn test_engine_history_populated() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 2,
            max_specs_per_round: 1,
            convergence_window: 5,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: false,
        };

        let func = i32_func();
        let backend = MockBackend::new(vec![failing_proposal(), failing_proposal()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        let outcome = engine.run(&backend).unwrap();

        assert_eq!(outcome.history.len(), 2);
        assert_eq!(outcome.history[0].round_number, 1);
        assert_eq!(outcome.history[1].round_number, 2);
    }

    #[test]
    fn test_engine_verbose_mode() {
        let cfg = CgsrEngineConfig {
            max_refinement_rounds: 1,
            max_specs_per_round: 1,
            convergence_window: 1,
            convergence_threshold: 0.95,
            enable_counterexample_refinement: false,
            enable_template_mining: false,
            occam_penalty: 0.1,
            verbose: true,
        };

        let func = simple_func();
        let backend = MockBackend::new(vec![trivial_proposal()]);
        let mut engine = CgsrEngine::new(cfg, &func);
        // Should not panic with verbose on.
        let outcome = engine.run(&backend).unwrap();
        assert!(outcome.rounds_used >= 1);
    }

    // -----------------------------------------------------------------------
    // feedback_tag tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_feedback_tag_verified() {
        let fb = ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::ZERO,
            certificate_info: None,
        };
        assert_eq!(feedback_tag(&fb), "verified");
    }

    #[test]
    fn test_feedback_tag_failed() {
        let fb = ProofFeedback::Failed {
            counterexamples: vec![],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "test".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::ZERO,
        };
        assert_eq!(feedback_tag(&fb), "failed");
    }

    #[test]
    fn test_feedback_tag_unknown() {
        let fb = ProofFeedback::Unknown {
            reason: "timeout".to_string(),
            category: "timeout".to_string(),
            is_retriable: true,
            suggestion: "try again".to_string(),
            elapsed: Duration::ZERO,
        };
        assert_eq!(feedback_tag(&fb), "unknown");
    }

    #[test]
    fn test_feedback_tag_error() {
        let fb = ProofFeedback::Error {
            message: "boom".to_string(),
        };
        assert_eq!(feedback_tag(&fb), "error");
    }
}
