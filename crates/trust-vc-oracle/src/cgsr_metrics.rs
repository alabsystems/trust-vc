// trust-vc-oracle — CGSR convergence metrics and scoring
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Provides end-to-end Counterexample-Guided Specification Refinement (CGSR)
// convergence tracking, scoring, and reporting. Tracks per-function iteration
// history, analyzes convergence trends, and produces human-readable summaries.

#![allow(dead_code)]

use std::fmt;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// SpecSnapshot
// ---------------------------------------------------------------------------

/// Frozen specification state at a particular CGSR iteration.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecSnapshot {
    /// Precondition clauses (`requires!` expressions).
    pub requires: Vec<String>,
    /// Postcondition clauses (`ensures!` expressions).
    pub ensures: Vec<String>,
    /// Loop invariant clauses (`invariant!` expressions).
    pub invariants: Vec<String>,
}

impl SpecSnapshot {
    /// Total number of clauses across requires, ensures, and invariants.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.requires.len() + self.ensures.len() + self.invariants.len()
    }

    /// Complexity score based on clause lengths and nesting depth.
    ///
    /// Each clause contributes its character length divided by 50 (a
    /// "typical" clause length) plus a nesting bonus. Nesting depth is
    /// estimated by counting matched parenthesis/bracket pairs beyond the
    /// first level.
    #[must_use]
    pub fn complexity_score(&self) -> f64 {
        let all_clauses = self
            .requires
            .iter()
            .chain(self.ensures.iter())
            .chain(self.invariants.iter());

        let mut total = 0.0;
        for clause in all_clauses {
            // Length component: normalised by 50 chars.
            let length_component = clause.len() as f64 / 50.0;

            // Nesting component: count max parenthesis depth.
            let nesting = Self::max_nesting_depth(clause);
            let nesting_component = nesting as f64 * 0.5;

            total += length_component + nesting_component;
        }
        total
    }

    /// Maximum parenthesis/bracket nesting depth in a clause string.
    fn max_nesting_depth(clause: &str) -> usize {
        let mut depth: usize = 0;
        let mut max_depth: usize = 0;
        for ch in clause.chars() {
            match ch {
                '(' | '[' | '{' => {
                    depth += 1;
                    max_depth = max_depth.max(depth);
                }
                ')' | ']' | '}' => {
                    depth = depth.saturating_sub(1);
                }
                _ => {}
            }
        }
        max_depth
    }
}

// ---------------------------------------------------------------------------
// IterationOutcome
// ---------------------------------------------------------------------------

/// Outcome of a single CGSR verification attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IterationOutcome {
    /// All obligations proved.
    Verified,
    /// At least one counterexample was found.
    CounterexampleFound,
    /// Solver returned unknown/timeout.
    Unknown,
    /// Infrastructure or encoding error.
    Error,
}

impl fmt::Display for IterationOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IterationOutcome::Verified => write!(f, "Verified"),
            IterationOutcome::CounterexampleFound => write!(f, "CounterexampleFound"),
            IterationOutcome::Unknown => write!(f, "Unknown"),
            IterationOutcome::Error => write!(f, "Error"),
        }
    }
}

// ---------------------------------------------------------------------------
// CgsrIteration
// ---------------------------------------------------------------------------

/// Data captured for a single CGSR iteration.
#[derive(Debug, Clone)]
pub struct CgsrIteration {
    /// 1-indexed iteration number.
    pub iteration_number: usize,
    /// Spec proposed at this iteration.
    pub spec_proposed: SpecSnapshot,
    /// Verification outcome.
    pub verification_result: IterationOutcome,
    /// Number of counterexamples found (0 when verified/unknown/error).
    pub counterexample_count: usize,
    /// Composite score for this iteration (0.0..=1.0 nominal range).
    pub score: f64,
    /// Score change from the previous iteration (0.0 for the first).
    pub delta_from_previous: f64,
    /// Wall-clock time spent on this iteration.
    pub elapsed: Duration,
}

// ---------------------------------------------------------------------------
// CgsrMetrics
// ---------------------------------------------------------------------------

/// Per-function convergence tracking across CGSR iterations.
#[derive(Debug)]
pub struct CgsrMetrics {
    /// Fully-qualified function name.
    pub function_name: String,
    /// Ordered iteration history.
    pub iterations: Vec<CgsrIteration>,
    /// Timestamp when tracking began.
    pub started_at: Instant,
    /// Best score observed so far.
    pub current_best_score: f64,
}

impl CgsrMetrics {
    /// Start tracking a new function.
    #[must_use]
    pub fn new(function_name: String) -> Self {
        Self {
            function_name,
            iterations: Vec::new(),
            started_at: Instant::now(),
            current_best_score: 0.0,
        }
    }

    /// Record a completed iteration. Updates `current_best_score` if the new
    /// score exceeds it.
    pub fn record_iteration(&mut self, iteration: CgsrIteration) {
        if iteration.score > self.current_best_score {
            self.current_best_score = iteration.score;
        }
        self.iterations.push(iteration);
    }

    /// Total elapsed time since tracking started.
    #[must_use]
    pub fn total_elapsed(&self) -> Duration {
        self.started_at.elapsed()
    }
}

// ---------------------------------------------------------------------------
// ConvergenceTrend
// ---------------------------------------------------------------------------

/// Classification of the convergence behaviour observed in the iteration
/// history window.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ConvergenceTrend {
    /// Scores are monotonically improving.
    Converging { rate: f64 },
    /// No meaningful score improvement for the entire window.
    Stalled { since_iteration: usize },
    /// Scores alternate between improving and worsening.
    Oscillating { amplitude: f64 },
    /// Scores are worsening over the window.
    Diverging { rate: f64 },
    /// Not enough data points to classify.
    Insufficient,
}

impl fmt::Display for ConvergenceTrend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConvergenceTrend::Converging { rate } => {
                write!(f, "Converging (rate={rate:.4}/iter)")
            }
            ConvergenceTrend::Stalled { since_iteration } => {
                write!(f, "Stalled since iteration {since_iteration}")
            }
            ConvergenceTrend::Oscillating { amplitude } => {
                write!(f, "Oscillating (amplitude={amplitude:.4})")
            }
            ConvergenceTrend::Diverging { rate } => {
                write!(f, "Diverging (rate={rate:.4}/iter)")
            }
            ConvergenceTrend::Insufficient => write!(f, "Insufficient data"),
        }
    }
}

// ---------------------------------------------------------------------------
// ConvergenceAnalyzer
// ---------------------------------------------------------------------------

/// Sliding-window analyzer that classifies the convergence behaviour of a
/// stream of CGSR iterations.
#[derive(Debug)]
pub struct ConvergenceAnalyzer {
    /// Number of recent iterations to consider.
    window_size: usize,
    /// Ordered score history (most recent at the end).
    scores: Vec<f64>,
    /// Iteration numbers corresponding to each score entry.
    iteration_numbers: Vec<usize>,
    /// Absolute improvement threshold below which progress is considered zero.
    epsilon: f64,
}

impl ConvergenceAnalyzer {
    /// Create a new analyzer with the given sliding-window size.
    #[must_use]
    pub fn new(window_size: usize) -> Self {
        Self {
            window_size,
            scores: Vec::new(),
            iteration_numbers: Vec::new(),
            epsilon: 1e-6,
        }
    }

    /// Feed a new iteration into the analyzer.
    pub fn feed(&mut self, iteration: &CgsrIteration) {
        self.scores.push(iteration.score);
        self.iteration_numbers.push(iteration.iteration_number);
    }

    /// Returns the most recent `window_size` scores, or all scores if fewer.
    fn window(&self) -> &[f64] {
        let len = self.scores.len();
        if len <= self.window_size {
            &self.scores
        } else {
            &self.scores[len - self.window_size..]
        }
    }

    /// True if scores are monotonically non-decreasing within the window,
    /// with at least one strict improvement, and the window is full.
    #[must_use]
    pub fn is_converging(&self) -> bool {
        let w = self.window();
        if w.len() < self.window_size {
            return false;
        }
        let mut any_improvement = false;
        for pair in w.windows(2) {
            if pair[1] < pair[0] - self.epsilon {
                return false;
            }
            if pair[1] > pair[0] + self.epsilon {
                any_improvement = true;
            }
        }
        any_improvement
    }

    /// True if no score in the window improves by more than `epsilon` over
    /// its predecessor, and the window is full.
    #[must_use]
    pub fn is_stalled(&self) -> bool {
        let w = self.window();
        if w.len() < self.window_size {
            return false;
        }
        for pair in w.windows(2) {
            if (pair[1] - pair[0]).abs() > self.epsilon {
                return false;
            }
        }
        true
    }

    /// True if scores strictly alternate between rising and falling for the
    /// full window.
    #[must_use]
    pub fn is_oscillating(&self) -> bool {
        let w = self.window();
        if w.len() < self.window_size || w.len() < 3 {
            return false;
        }
        let deltas: Vec<f64> = w.windows(2).map(|p| p[1] - p[0]).collect();
        // Each consecutive pair of deltas should have opposite signs.
        for pair in deltas.windows(2) {
            // Both must be non-trivial and opposite-signed.
            if pair[0].abs() <= self.epsilon || pair[1].abs() <= self.epsilon {
                return false;
            }
            if pair[0].signum() == pair[1].signum() {
                return false;
            }
        }
        true
    }

    /// Average score improvement per iteration over the window.
    #[must_use]
    pub fn convergence_rate(&self) -> f64 {
        let w = self.window();
        if w.len() < 2 {
            return 0.0;
        }
        let total_delta = w.last().unwrap_or(&0.0) - w.first().unwrap_or(&0.0);
        total_delta / (w.len() - 1) as f64
    }

    /// Estimate how many more iterations are needed to reach `target_score`
    /// at the current convergence rate. Returns `None` if the rate is
    /// non-positive or if the current score already meets/exceeds the target.
    #[must_use]
    pub fn estimated_iterations_remaining(&self, target_score: f64) -> Option<usize> {
        let current = *self.scores.last()?;
        if current >= target_score {
            return Some(0);
        }
        let rate = self.convergence_rate();
        if rate <= self.epsilon {
            return None;
        }
        let remaining = (target_score - current) / rate;
        Some(remaining.ceil() as usize)
    }

    /// Classify the overall trend across the window.
    #[must_use]
    pub fn trend(&self) -> ConvergenceTrend {
        let w = self.window();
        if w.len() < self.window_size {
            return ConvergenceTrend::Insufficient;
        }

        if self.is_oscillating() {
            let deltas: Vec<f64> = w.windows(2).map(|p| (p[1] - p[0]).abs()).collect();
            let amplitude = deltas.iter().copied().sum::<f64>() / deltas.len() as f64;
            return ConvergenceTrend::Oscillating { amplitude };
        }

        if self.is_stalled() {
            // Identify the iteration number where the stall began.
            let start_idx = self.scores.len().saturating_sub(self.window_size);
            let since = self.iteration_numbers.get(start_idx).copied().unwrap_or(0);
            return ConvergenceTrend::Stalled {
                since_iteration: since,
            };
        }

        let rate = self.convergence_rate();
        if rate > self.epsilon {
            ConvergenceTrend::Converging { rate }
        } else if rate < -self.epsilon {
            ConvergenceTrend::Diverging { rate }
        } else {
            // Edge case: rate ~0 but not detected as stalled (mixed deltas).
            ConvergenceTrend::Stalled {
                since_iteration: self.iteration_numbers.first().copied().unwrap_or(0),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// CgsrScorer
// ---------------------------------------------------------------------------

/// Scores a specification proposal based on verification outcome and
/// structural properties.
pub struct CgsrScorer;

impl CgsrScorer {
    /// Score a spec proposal.
    ///
    /// Rubric:
    /// - Verified: 1.0 base
    /// - CounterexampleFound: 0.0-0.5 (proximity heuristic based on
    ///   counterexample count: fewer counterexamples = closer to correct)
    /// - Unknown: 0.3
    /// - Error: 0.0
    ///
    /// Adjustments:
    /// - -0.1 per clause beyond the first two (Occam's razor)
    /// - -0.05 per deeply nested quantifier (nesting > 2)
    #[must_use]
    pub fn score_spec(
        spec: &SpecSnapshot,
        verification_result: &IterationOutcome,
        counterexample_count: usize,
    ) -> f64 {
        let base = match verification_result {
            IterationOutcome::Verified => 1.0,
            IterationOutcome::CounterexampleFound => {
                // Fewer counterexamples → higher score, capped at 0.5.
                let proximity = 1.0 / (1.0 + counterexample_count as f64);
                proximity * 0.5
            }
            IterationOutcome::Unknown => 0.3,
            IterationOutcome::Error => 0.0,
        };

        // Occam penalty: -0.1 per clause beyond a "baseline" of 2.
        let clause_count = spec.clause_count();
        let occam_penalty = if clause_count > 2 {
            (clause_count - 2) as f64 * 0.1
        } else {
            0.0
        };

        // Nesting penalty: count clauses with max nesting depth > 2.
        let deep_clauses = spec
            .requires
            .iter()
            .chain(spec.ensures.iter())
            .chain(spec.invariants.iter())
            .filter(|c| SpecSnapshot::max_nesting_depth(c) > 2)
            .count();
        let nesting_penalty = deep_clauses as f64 * 0.05;

        (base - occam_penalty - nesting_penalty).max(0.0)
    }
}

// ---------------------------------------------------------------------------
// CgsrReport
// ---------------------------------------------------------------------------

/// Summary of a complete CGSR run for a single function.
#[derive(Debug, Clone)]
pub struct CgsrReport {
    /// Function under refinement.
    pub function_name: String,
    /// Total iterations executed.
    pub total_iterations: usize,
    /// Final composite score.
    pub final_score: f64,
    /// Whether the CGSR loop converged (reached Verified).
    pub converged: bool,
    /// Trend classification at end of run.
    pub trend: ConvergenceTrend,
    /// Best specification found (highest scoring).
    pub best_spec: Option<SpecSnapshot>,
    /// Time from first iteration to convergence (None if not converged).
    pub time_to_convergence: Option<Duration>,
}

impl CgsrReport {
    /// Render a human-readable report string.
    #[must_use]
    pub fn render(&self) -> String {
        let mut lines = Vec::new();
        lines.push(format!("CGSR Report: {}", self.function_name));
        lines.push(format!("  Iterations:  {}", self.total_iterations));
        lines.push(format!("  Final score: {:.4}", self.final_score));
        lines.push(format!(
            "  Converged:   {}",
            if self.converged { "yes" } else { "no" }
        ));
        lines.push(format!("  Trend:       {}", self.trend));

        if let Some(ref spec) = self.best_spec {
            lines.push(format!(
                "  Best spec:   {} clauses (complexity {:.2})",
                spec.clause_count(),
                spec.complexity_score()
            ));
        }

        if let Some(ttc) = self.time_to_convergence {
            lines.push(format!("  Time to convergence: {:.2}s", ttc.as_secs_f64()));
        }

        lines.join("\n")
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---- helpers ----------------------------------------------------------

    fn simple_spec() -> SpecSnapshot {
        SpecSnapshot {
            requires: vec!["x > 0".into()],
            ensures: vec!["result >= 0".into()],
            invariants: vec![],
        }
    }

    fn complex_spec() -> SpecSnapshot {
        SpecSnapshot {
            requires: vec!["forall(|i: usize| (i < seq.len()) ==> (seq[i] >= 0))".into()],
            ensures: vec![
                "exists(|j: usize| (j < result.len()) && (result[j] == old(seq[0])))".into(),
            ],
            invariants: vec!["forall(|k: usize| (k < idx) ==> (acc + arr[k] >= 0))".into()],
        }
    }

    fn verbose_spec() -> SpecSnapshot {
        SpecSnapshot {
            requires: vec![
                "x > 0".into(),
                "y > 0".into(),
                "z > 0".into(),
                "w > 0".into(),
            ],
            ensures: vec!["result >= 0".into()],
            invariants: vec![],
        }
    }

    fn deeply_nested_spec() -> SpecSnapshot {
        SpecSnapshot {
            requires: vec![
                "f(g(h(x)))".into(), // nesting depth 3
            ],
            ensures: vec![
                "a(b(c(d(e(result)))))".into(), // nesting depth 5
            ],
            invariants: vec![],
        }
    }

    fn make_iteration(
        number: usize,
        score: f64,
        delta: f64,
        outcome: IterationOutcome,
    ) -> CgsrIteration {
        CgsrIteration {
            iteration_number: number,
            spec_proposed: simple_spec(),
            verification_result: outcome,
            counterexample_count: 0,
            score,
            delta_from_previous: delta,
            elapsed: Duration::from_millis(100),
        }
    }

    // ---- SpecSnapshot tests ----------------------------------------------

    #[test]
    fn test_spec_snapshot_clause_count_simple() {
        let spec = simple_spec();
        assert_eq!(spec.clause_count(), 2);
    }

    #[test]
    fn test_spec_snapshot_clause_count_with_invariants() {
        let spec = complex_spec();
        assert_eq!(spec.clause_count(), 3);
    }

    #[test]
    fn test_spec_snapshot_clause_count_empty() {
        let spec = SpecSnapshot {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
        };
        assert_eq!(spec.clause_count(), 0);
    }

    #[test]
    fn test_spec_snapshot_complexity_simple_less_than_complex() {
        let simple = simple_spec();
        let complex = complex_spec();
        assert!(
            simple.complexity_score() < complex.complexity_score(),
            "simple ({}) should be less complex than complex ({})",
            simple.complexity_score(),
            complex.complexity_score()
        );
    }

    #[test]
    fn test_spec_snapshot_complexity_empty_is_zero() {
        let spec = SpecSnapshot {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
        };
        assert!((spec.complexity_score() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_spec_snapshot_complexity_nesting_contributes() {
        // Same length but different nesting should yield different scores.
        let flat = SpecSnapshot {
            requires: vec!["xxxxxxxxxx".into()],
            ensures: vec![],
            invariants: vec![],
        };
        let nested = SpecSnapshot {
            requires: vec!["x((((()))))".into()], // 11 chars, depth 5
            ensures: vec![],
            invariants: vec![],
        };
        assert!(
            nested.complexity_score() > flat.complexity_score(),
            "nested ({}) should score higher than flat ({})",
            nested.complexity_score(),
            flat.complexity_score()
        );
    }

    // ---- CgsrScorer tests ------------------------------------------------

    #[test]
    fn test_scorer_verified_spec_gets_max() {
        let spec = simple_spec();
        let score = CgsrScorer::score_spec(&spec, &IterationOutcome::Verified, 0);
        assert!(
            (score - 1.0).abs() < f64::EPSILON,
            "verified simple spec should score 1.0, got {score}"
        );
    }

    #[test]
    fn test_scorer_counterexample_less_than_one() {
        let spec = simple_spec();
        let score = CgsrScorer::score_spec(&spec, &IterationOutcome::CounterexampleFound, 3);
        assert!(
            score < 1.0,
            "counterexample score should be < 1.0, got {score}"
        );
        assert!(
            score >= 0.0,
            "counterexample score should be >= 0.0, got {score}"
        );
    }

    #[test]
    fn test_scorer_fewer_counterexamples_higher_score() {
        let spec = simple_spec();
        let score_few = CgsrScorer::score_spec(&spec, &IterationOutcome::CounterexampleFound, 1);
        let score_many = CgsrScorer::score_spec(&spec, &IterationOutcome::CounterexampleFound, 10);
        assert!(
            score_few > score_many,
            "fewer cex ({score_few}) should beat more cex ({score_many})"
        );
    }

    #[test]
    fn test_scorer_unknown_gets_partial_credit() {
        let spec = simple_spec();
        let score = CgsrScorer::score_spec(&spec, &IterationOutcome::Unknown, 0);
        assert!(
            (score - 0.3).abs() < f64::EPSILON,
            "unknown simple spec should score 0.3, got {score}"
        );
    }

    #[test]
    fn test_scorer_error_gets_zero() {
        let spec = simple_spec();
        let score = CgsrScorer::score_spec(&spec, &IterationOutcome::Error, 0);
        assert!(
            score.abs() < f64::EPSILON,
            "error should score 0.0, got {score}"
        );
    }

    #[test]
    fn test_scorer_occam_penalty_for_verbose_specs() {
        let concise = simple_spec(); // 2 clauses
        let verbose = verbose_spec(); // 5 clauses
        let score_concise = CgsrScorer::score_spec(&concise, &IterationOutcome::Verified, 0);
        let score_verbose = CgsrScorer::score_spec(&verbose, &IterationOutcome::Verified, 0);
        assert!(
            score_concise > score_verbose,
            "concise ({score_concise}) should beat verbose ({score_verbose})"
        );
    }

    #[test]
    fn test_scorer_nesting_penalty() {
        let shallow = simple_spec();
        let deep = deeply_nested_spec();
        let score_shallow = CgsrScorer::score_spec(&shallow, &IterationOutcome::Verified, 0);
        let score_deep = CgsrScorer::score_spec(&deep, &IterationOutcome::Verified, 0);
        assert!(
            score_shallow > score_deep,
            "shallow ({score_shallow}) should beat deep ({score_deep})"
        );
    }

    #[test]
    fn test_scorer_floor_at_zero() {
        // Extremely verbose spec: 12 clauses → penalty 1.0, base 0.3 → 0.0 floor.
        let spec = SpecSnapshot {
            requires: (0..12).map(|i| format!("x{i} > 0")).collect(),
            ensures: vec![],
            invariants: vec![],
        };
        let score = CgsrScorer::score_spec(&spec, &IterationOutcome::Unknown, 0);
        assert!(score >= 0.0, "score should never go negative, got {score}");
    }

    // ---- ConvergenceAnalyzer tests ---------------------------------------

    #[test]
    fn test_analyzer_insufficient_data() {
        let analyzer = ConvergenceAnalyzer::new(5);
        assert_eq!(analyzer.trend(), ConvergenceTrend::Insufficient);
    }

    #[test]
    fn test_analyzer_insufficient_data_partial() {
        let mut analyzer = ConvergenceAnalyzer::new(5);
        analyzer.feed(&make_iteration(
            1,
            0.2,
            0.0,
            IterationOutcome::CounterexampleFound,
        ));
        analyzer.feed(&make_iteration(
            2,
            0.4,
            0.2,
            IterationOutcome::CounterexampleFound,
        ));
        assert_eq!(analyzer.trend(), ConvergenceTrend::Insufficient);
    }

    #[test]
    fn test_analyzer_detects_convergence() {
        let mut analyzer = ConvergenceAnalyzer::new(4);
        for i in 1..=4 {
            let score = 0.2 * i as f64;
            analyzer.feed(&make_iteration(
                i,
                score,
                0.2,
                IterationOutcome::CounterexampleFound,
            ));
        }
        assert!(
            analyzer.is_converging(),
            "monotonically increasing scores should be converging"
        );
        matches!(analyzer.trend(), ConvergenceTrend::Converging { .. });
    }

    #[test]
    fn test_analyzer_detects_stall() {
        let mut analyzer = ConvergenceAnalyzer::new(4);
        for i in 1..=4 {
            analyzer.feed(&make_iteration(
                i,
                0.5,
                0.0,
                IterationOutcome::CounterexampleFound,
            ));
        }
        assert!(
            analyzer.is_stalled(),
            "identical scores should register as stalled"
        );
        matches!(analyzer.trend(), ConvergenceTrend::Stalled { .. });
    }

    #[test]
    fn test_analyzer_detects_oscillation() {
        let mut analyzer = ConvergenceAnalyzer::new(5);
        let scores = [0.3, 0.6, 0.3, 0.6, 0.3];
        for (i, &s) in scores.iter().enumerate() {
            let delta = if i == 0 { 0.0 } else { s - scores[i - 1] };
            analyzer.feed(&make_iteration(
                i + 1,
                s,
                delta,
                IterationOutcome::CounterexampleFound,
            ));
        }
        assert!(
            analyzer.is_oscillating(),
            "alternating scores should register as oscillating"
        );
        matches!(analyzer.trend(), ConvergenceTrend::Oscillating { .. });
    }

    #[test]
    fn test_analyzer_detects_divergence() {
        let mut analyzer = ConvergenceAnalyzer::new(4);
        let scores = [0.8, 0.6, 0.4, 0.2];
        for (i, &s) in scores.iter().enumerate() {
            let delta = if i == 0 { 0.0 } else { s - scores[i - 1] };
            analyzer.feed(&make_iteration(
                i + 1,
                s,
                delta,
                IterationOutcome::CounterexampleFound,
            ));
        }
        assert!(
            !analyzer.is_converging(),
            "decreasing scores should not be converging"
        );
        let rate = analyzer.convergence_rate();
        assert!(rate < 0.0, "diverging rate should be negative, got {rate}");
        matches!(analyzer.trend(), ConvergenceTrend::Diverging { .. });
    }

    #[test]
    fn test_analyzer_convergence_rate() {
        let mut analyzer = ConvergenceAnalyzer::new(3);
        analyzer.feed(&make_iteration(
            1,
            0.1,
            0.0,
            IterationOutcome::CounterexampleFound,
        ));
        analyzer.feed(&make_iteration(
            2,
            0.3,
            0.2,
            IterationOutcome::CounterexampleFound,
        ));
        analyzer.feed(&make_iteration(
            3,
            0.5,
            0.2,
            IterationOutcome::CounterexampleFound,
        ));
        let rate = analyzer.convergence_rate();
        // (0.5 - 0.1) / 2 = 0.2
        assert!((rate - 0.2).abs() < 1e-9, "expected rate 0.2, got {rate}");
    }

    #[test]
    fn test_analyzer_estimated_iterations_remaining() {
        let mut analyzer = ConvergenceAnalyzer::new(3);
        // Use powers-of-two fractions to avoid f64 rounding surprises.
        analyzer.feed(&make_iteration(
            1,
            0.25,
            0.0,
            IterationOutcome::CounterexampleFound,
        ));
        analyzer.feed(&make_iteration(
            2,
            0.50,
            0.25,
            IterationOutcome::CounterexampleFound,
        ));
        analyzer.feed(&make_iteration(
            3,
            0.75,
            0.25,
            IterationOutcome::CounterexampleFound,
        ));
        // Rate = (0.75-0.25)/2 = 0.25. Remaining to 1.0: (1.0-0.75)/0.25 = 1.
        let est = analyzer.estimated_iterations_remaining(1.0);
        assert_eq!(est, Some(1));
    }

    #[test]
    fn test_analyzer_estimated_remaining_already_met() {
        let mut analyzer = ConvergenceAnalyzer::new(3);
        analyzer.feed(&make_iteration(1, 1.0, 0.0, IterationOutcome::Verified));
        let est = analyzer.estimated_iterations_remaining(1.0);
        assert_eq!(est, Some(0));
    }

    #[test]
    fn test_analyzer_estimated_remaining_stalled() {
        let mut analyzer = ConvergenceAnalyzer::new(3);
        for i in 1..=3 {
            analyzer.feed(&make_iteration(
                i,
                0.5,
                0.0,
                IterationOutcome::CounterexampleFound,
            ));
        }
        let est = analyzer.estimated_iterations_remaining(1.0);
        assert_eq!(est, None, "stalled should return None");
    }

    // ---- CgsrMetrics tests -----------------------------------------------

    #[test]
    fn test_metrics_iteration_tracking() {
        let mut metrics = CgsrMetrics::new("foo::bar".into());
        let iter1 = make_iteration(1, 0.3, 0.0, IterationOutcome::CounterexampleFound);
        let iter2 = make_iteration(2, 0.5, 0.2, IterationOutcome::CounterexampleFound);
        metrics.record_iteration(iter1);
        metrics.record_iteration(iter2);
        assert_eq!(metrics.iterations.len(), 2);
        assert_eq!(metrics.function_name, "foo::bar");
    }

    #[test]
    fn test_metrics_best_score_updates() {
        let mut metrics = CgsrMetrics::new("test_fn".into());
        metrics.record_iteration(make_iteration(
            1,
            0.3,
            0.0,
            IterationOutcome::CounterexampleFound,
        ));
        assert!((metrics.current_best_score - 0.3).abs() < f64::EPSILON);
        metrics.record_iteration(make_iteration(
            2,
            0.7,
            0.4,
            IterationOutcome::CounterexampleFound,
        ));
        assert!((metrics.current_best_score - 0.7).abs() < f64::EPSILON);
        // Regression should NOT lower best.
        metrics.record_iteration(make_iteration(
            3,
            0.4,
            -0.3,
            IterationOutcome::CounterexampleFound,
        ));
        assert!((metrics.current_best_score - 0.7).abs() < f64::EPSILON);
    }

    // ---- CgsrIteration delta test ----------------------------------------

    #[test]
    fn test_iteration_delta_computation() {
        let iter1 = make_iteration(1, 0.3, 0.0, IterationOutcome::CounterexampleFound);
        assert!((iter1.delta_from_previous - 0.0).abs() < f64::EPSILON);
        let iter2 = make_iteration(2, 0.5, 0.2, IterationOutcome::CounterexampleFound);
        assert!((iter2.delta_from_previous - 0.2).abs() < f64::EPSILON);
    }

    // ---- CgsrReport tests ------------------------------------------------

    #[test]
    fn test_report_render_includes_function_name() {
        let report = CgsrReport {
            function_name: "my_module::compute".into(),
            total_iterations: 5,
            final_score: 0.85,
            converged: true,
            trend: ConvergenceTrend::Converging { rate: 0.15 },
            best_spec: Some(simple_spec()),
            time_to_convergence: Some(Duration::from_secs(3)),
        };
        let rendered = report.render();
        assert!(
            rendered.contains("my_module::compute"),
            "report should include function name"
        );
    }

    #[test]
    fn test_report_render_includes_convergence_yes() {
        let report = CgsrReport {
            function_name: "f".into(),
            total_iterations: 3,
            final_score: 1.0,
            converged: true,
            trend: ConvergenceTrend::Converging { rate: 0.3 },
            best_spec: None,
            time_to_convergence: Some(Duration::from_millis(500)),
        };
        let rendered = report.render();
        assert!(rendered.contains("yes"), "converged report should say yes");
    }

    #[test]
    fn test_report_render_includes_convergence_no() {
        let report = CgsrReport {
            function_name: "g".into(),
            total_iterations: 10,
            final_score: 0.4,
            converged: false,
            trend: ConvergenceTrend::Stalled { since_iteration: 5 },
            best_spec: None,
            time_to_convergence: None,
        };
        let rendered = report.render();
        assert!(
            rendered.contains("no"),
            "non-converged report should say no"
        );
        assert!(rendered.contains("Stalled"), "report should include trend");
    }

    #[test]
    fn test_report_render_includes_iteration_count() {
        let report = CgsrReport {
            function_name: "h".into(),
            total_iterations: 7,
            final_score: 0.6,
            converged: false,
            trend: ConvergenceTrend::Oscillating { amplitude: 0.15 },
            best_spec: None,
            time_to_convergence: None,
        };
        let rendered = report.render();
        assert!(
            rendered.contains("7"),
            "report should include iteration count"
        );
    }

    // ---- Multiple iterations with improving scores -----------------------

    #[test]
    fn test_multiple_iterations_improving() {
        let mut metrics = CgsrMetrics::new("improving_fn".into());
        let mut analyzer = ConvergenceAnalyzer::new(5);
        let scores = [0.1, 0.25, 0.45, 0.7, 0.95];
        let mut prev = 0.0;
        for (i, &s) in scores.iter().enumerate() {
            let delta = s - prev;
            let iter = make_iteration(
                i + 1,
                s,
                delta,
                if s >= 0.95 {
                    IterationOutcome::Verified
                } else {
                    IterationOutcome::CounterexampleFound
                },
            );
            analyzer.feed(&iter);
            metrics.record_iteration(iter);
            prev = s;
        }
        assert!(analyzer.is_converging());
        assert!((metrics.current_best_score - 0.95).abs() < f64::EPSILON);
    }

    // ---- Multiple iterations with plateauing scores ----------------------

    #[test]
    fn test_multiple_iterations_plateauing() {
        let mut analyzer = ConvergenceAnalyzer::new(4);
        let scores = [0.1, 0.3, 0.5, 0.5, 0.5, 0.5];
        for (i, &s) in scores.iter().enumerate() {
            let delta = if i == 0 { 0.0 } else { s - scores[i - 1] };
            analyzer.feed(&make_iteration(
                i + 1,
                s,
                delta,
                IterationOutcome::CounterexampleFound,
            ));
        }
        // The last 4 scores are [0.5, 0.5, 0.5, 0.5] → stalled.
        assert!(analyzer.is_stalled());
    }

    // ---- Window size affects convergence detection -----------------------

    #[test]
    fn test_window_size_affects_detection() {
        // With window=3: [0.3, 0.5, 0.7] → converging.
        let mut small = ConvergenceAnalyzer::new(3);
        // With window=6: insufficient data for same 3 points.
        let mut large = ConvergenceAnalyzer::new(6);
        for i in 1..=3 {
            let s = 0.1 + 0.2 * i as f64;
            let iter = make_iteration(i, s, 0.2, IterationOutcome::CounterexampleFound);
            small.feed(&iter);
            large.feed(&iter);
        }
        assert!(
            small.is_converging(),
            "small window should detect convergence"
        );
        assert!(
            !large.is_converging(),
            "large window should not detect convergence with fewer data points"
        );
        assert_eq!(large.trend(), ConvergenceTrend::Insufficient);
    }

    // ---- Empty iteration history -----------------------------------------

    #[test]
    fn test_empty_iteration_history() {
        let metrics = CgsrMetrics::new("empty".into());
        assert!(metrics.iterations.is_empty());
        assert!((metrics.current_best_score - 0.0).abs() < f64::EPSILON);
    }

    // ---- Single iteration (edge case) ------------------------------------

    #[test]
    fn test_single_iteration_edge_case() {
        let mut metrics = CgsrMetrics::new("single".into());
        let iter = make_iteration(1, 0.5, 0.0, IterationOutcome::CounterexampleFound);
        metrics.record_iteration(iter);
        assert_eq!(metrics.iterations.len(), 1);
        assert!((metrics.current_best_score - 0.5).abs() < f64::EPSILON);

        let mut analyzer = ConvergenceAnalyzer::new(5);
        analyzer.feed(&metrics.iterations[0]);
        assert_eq!(analyzer.trend(), ConvergenceTrend::Insufficient);
        assert_eq!(analyzer.convergence_rate(), 0.0);
    }

    // ---- Full pipeline: create → feed → analyze → report -----------------

    #[test]
    fn test_full_pipeline() {
        let mut metrics = CgsrMetrics::new("pipeline::target".into());
        let mut analyzer = ConvergenceAnalyzer::new(3);

        // Iteration 1: poor start.
        let spec1 = SpecSnapshot {
            requires: vec!["true".into()],
            ensures: vec!["result > 0".into()],
            invariants: vec![],
        };
        let score1 = CgsrScorer::score_spec(&spec1, &IterationOutcome::CounterexampleFound, 5);
        let iter1 = CgsrIteration {
            iteration_number: 1,
            spec_proposed: spec1,
            verification_result: IterationOutcome::CounterexampleFound,
            counterexample_count: 5,
            score: score1,
            delta_from_previous: 0.0,
            elapsed: Duration::from_millis(200),
        };
        analyzer.feed(&iter1);
        metrics.record_iteration(iter1);

        // Iteration 2: improvement.
        let spec2 = SpecSnapshot {
            requires: vec!["x > 0".into()],
            ensures: vec!["result >= x".into()],
            invariants: vec![],
        };
        let score2 = CgsrScorer::score_spec(&spec2, &IterationOutcome::CounterexampleFound, 1);
        let delta2 = score2 - score1;
        let iter2 = CgsrIteration {
            iteration_number: 2,
            spec_proposed: spec2,
            verification_result: IterationOutcome::CounterexampleFound,
            counterexample_count: 1,
            score: score2,
            delta_from_previous: delta2,
            elapsed: Duration::from_millis(150),
        };
        analyzer.feed(&iter2);
        metrics.record_iteration(iter2);

        // Iteration 3: verified!
        let spec3 = SpecSnapshot {
            requires: vec!["x > 0".into()],
            ensures: vec!["result == x * 2".into()],
            invariants: vec![],
        };
        let score3 = CgsrScorer::score_spec(&spec3, &IterationOutcome::Verified, 0);
        let delta3 = score3 - score2;
        let iter3 = CgsrIteration {
            iteration_number: 3,
            spec_proposed: spec3.clone(),
            verification_result: IterationOutcome::Verified,
            counterexample_count: 0,
            score: score3,
            delta_from_previous: delta3,
            elapsed: Duration::from_millis(120),
        };
        analyzer.feed(&iter3);
        metrics.record_iteration(iter3);

        // Validate metrics.
        assert_eq!(metrics.iterations.len(), 3);
        assert!((metrics.current_best_score - score3).abs() < f64::EPSILON);

        // Validate analyzer.
        assert!(analyzer.is_converging());
        let rate = analyzer.convergence_rate();
        assert!(rate > 0.0);

        // Build report.
        let report = CgsrReport {
            function_name: metrics.function_name.clone(),
            total_iterations: metrics.iterations.len(),
            final_score: score3,
            converged: true,
            trend: analyzer.trend(),
            best_spec: Some(spec3),
            time_to_convergence: Some(Duration::from_millis(470)),
        };
        let rendered = report.render();
        assert!(rendered.contains("pipeline::target"));
        assert!(rendered.contains("yes"));
        assert!(rendered.contains("3"));
    }
}
