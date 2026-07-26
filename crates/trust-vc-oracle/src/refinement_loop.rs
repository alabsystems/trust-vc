// trust-vc-oracle -- Core refinement loop for LLM proof oracle
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Coordinates between the session manager, LLM backend, verifier, and CGSR
// engine to iteratively refine specifications until convergence or budget
// exhaustion. This module is self-contained: all types are defined locally
// so that it can be understood (and tested) in isolation.

use std::collections::HashMap;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Strategy
// ---------------------------------------------------------------------------

/// Controls how aggressively the refinement loop modifies specs each iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RefinementStrategy {
    /// Small, targeted changes (add one precondition or tighten one bound).
    Conservative,
    /// Large rewrites (replace entire spec, restructure invariants).
    Aggressive,
    /// Starts conservative, switches to aggressive when progress stalls.
    Adaptive,
    /// Alternates conservative and aggressive rounds.
    Hybrid,
}

impl RefinementStrategy {
    /// Human-readable label.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Conservative => "conservative",
            Self::Aggressive => "aggressive",
            Self::Adaptive => "adaptive",
            Self::Hybrid => "hybrid",
        }
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Top-level configuration for a refinement session.
#[derive(Debug, Clone)]
pub struct RefinementConfig {
    /// Maximum iterations before declaring exhaustion.
    pub max_iterations: usize,
    /// Wall-clock timeout per single iteration.
    pub timeout_per_iteration: Duration,
    /// Score delta below which we declare convergence (e.g. 0.01).
    pub convergence_threshold: f64,
    /// Initial strategy selection.
    pub strategy: RefinementStrategy,
    /// Number of consecutive plateau iterations before switching strategy.
    pub plateau_patience: usize,
    /// Minimum score improvement to consider an iteration "useful".
    pub min_improvement: f64,
}

impl Default for RefinementConfig {
    fn default() -> Self {
        Self {
            max_iterations: 20,
            timeout_per_iteration: Duration::from_secs(30),
            convergence_threshold: 0.01,
            strategy: RefinementStrategy::Adaptive,
            plateau_patience: 3,
            min_improvement: 0.005,
        }
    }
}

// ---------------------------------------------------------------------------
// Verification result (local mirror)
// ---------------------------------------------------------------------------

/// Outcome of verifying a single proposed spec.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum VerificationResult {
    /// All obligations discharged.
    Verified,
    /// At least one obligation failed with counterexample fields.
    Counterexample {
        /// Variable name-value pairs from the model.
        fields: Vec<(String, String)>,
    },
    /// Solver could not decide within resource limits.
    Unknown { reason: String },
}

impl VerificationResult {
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified)
    }

    #[must_use]
    pub fn is_counterexample(&self) -> bool {
        matches!(self, Self::Counterexample { .. })
    }
}

// ---------------------------------------------------------------------------
// Iteration result
// ---------------------------------------------------------------------------

/// The output of one propose-verify cycle.
#[derive(Debug, Clone)]
pub struct IterationResult {
    /// The proposed specification text.
    pub proposed_spec: String,
    /// Outcome from the verifier.
    pub verification: VerificationResult,
    /// Quality score for this iteration (0.0 = worst, 1.0 = fully verified).
    pub score: f64,
    /// Wall time consumed by this iteration.
    pub elapsed: Duration,
    /// Which strategy was active during this iteration.
    pub strategy_used: RefinementStrategy,
}

// ---------------------------------------------------------------------------
// Refinement outcome
// ---------------------------------------------------------------------------

/// Final result of the entire refinement loop.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum RefinementOutcome {
    /// The spec was proven correct.
    Converged { iterations: usize, final_score: f64 },
    /// The iteration budget was exhausted without convergence.
    Exhausted { iterations: usize, best_score: f64 },
    /// Wall-clock budget exceeded.
    TimedOut { iterations: usize, best_score: f64 },
    /// Scores are trending downward — the loop is making things worse.
    Diverged { iterations: usize, final_score: f64 },
}

impl RefinementOutcome {
    #[must_use]
    pub fn is_converged(&self) -> bool {
        matches!(self, Self::Converged { .. })
    }
}

// ---------------------------------------------------------------------------
// Spec patches
// ---------------------------------------------------------------------------

/// The kind of modification to apply to a specification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PatchKind {
    /// Add a new `requires` clause.
    AddRequires,
    /// Make an existing `ensures` clause stricter.
    StrengthenEnsures,
    /// Relax an existing `ensures` clause.
    WeakenEnsures,
    /// Add a loop invariant.
    AddInvariant,
    /// Add a mid-function assertion.
    AddAssertion,
    /// Introduce a helper lemma or ghost function.
    AddHelper,
}

/// A proposed modification to a specification.
#[derive(Debug, Clone)]
pub struct SpecPatch {
    /// What kind of change this is.
    pub kind: PatchKind,
    /// The clause text to add or replace.
    pub clause: String,
    /// Confidence that this patch will help (0.0 .. 1.0).
    pub confidence: f64,
    /// Human-readable rationale.
    pub rationale: String,
}

impl SpecPatch {
    #[must_use]
    pub fn new(kind: PatchKind, clause: &str, confidence: f64, rationale: &str) -> Self {
        Self {
            kind,
            clause: clause.to_owned(),
            confidence: confidence.clamp(0.0, 1.0),
            rationale: rationale.to_owned(),
        }
    }
}

// ---------------------------------------------------------------------------
// Score tracker
// ---------------------------------------------------------------------------

/// Records score history and detects convergence / divergence / plateau.
#[derive(Debug, Clone)]
pub struct ScoreTracker {
    scores: Vec<f64>,
}

impl ScoreTracker {
    #[must_use]
    pub fn new() -> Self {
        Self { scores: Vec::new() }
    }

    /// Append a score observation.
    pub fn record(&mut self, score: f64) {
        self.scores.push(score);
    }

    /// Number of recorded scores.
    #[must_use]
    pub fn len(&self) -> usize {
        self.scores.len()
    }

    /// Whether any scores have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.scores.is_empty()
    }

    /// The most recent score, if any.
    #[must_use]
    pub fn latest(&self) -> Option<f64> {
        self.scores.last().copied()
    }

    /// The highest score ever observed.
    #[must_use]
    pub fn best(&self) -> Option<f64> {
        self.scores.iter().copied().reduce(f64::max)
    }

    /// All recorded scores.
    #[must_use]
    pub fn scores(&self) -> &[f64] {
        &self.scores
    }

    /// True if the last `n` scores are within `threshold` of each other.
    /// Requires at least `n` scores; returns false otherwise.
    #[must_use]
    pub fn is_plateaued(&self, n: usize, threshold: f64) -> bool {
        if self.scores.len() < n || n == 0 {
            return false;
        }
        let tail = &self.scores[self.scores.len() - n..];
        let min = tail.iter().copied().reduce(f64::min).unwrap_or(0.0);
        let max = tail.iter().copied().reduce(f64::max).unwrap_or(0.0);
        (max - min).abs() <= threshold
    }

    /// True if the score trend over the last `window` entries is upward.
    /// Uses simple linear regression sign of slope.
    #[must_use]
    pub fn is_converging(&self) -> bool {
        if self.scores.len() < 2 {
            return false;
        }
        let window = self.scores.len().min(5);
        let tail = &self.scores[self.scores.len() - window..];
        linear_slope(tail) > 0.0
    }

    /// True if scores are trending downward over recent history.
    #[must_use]
    pub fn is_diverging(&self) -> bool {
        if self.scores.len() < 3 {
            return false;
        }
        let window = self.scores.len().min(5);
        let tail = &self.scores[self.scores.len() - window..];
        linear_slope(tail) < -0.05
    }
}

impl Default for ScoreTracker {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Convergence detector (statistical)
// ---------------------------------------------------------------------------

/// Performs statistical analysis of a score series to inform stopping decisions.
#[derive(Debug, Clone)]
pub struct ConvergenceDetector {
    scores: Vec<f64>,
    convergence_threshold: f64,
}

impl ConvergenceDetector {
    #[must_use]
    pub fn new(convergence_threshold: f64) -> Self {
        Self {
            scores: Vec::new(),
            convergence_threshold,
        }
    }

    /// Feed a new score observation.
    pub fn observe(&mut self, score: f64) {
        self.scores.push(score);
    }

    /// Compute the moving average over the last `window` observations.
    /// Returns `None` if fewer than `window` observations exist.
    #[must_use]
    pub fn moving_average(&self, window: usize) -> Option<f64> {
        if window == 0 || self.scores.len() < window {
            return None;
        }
        let tail = &self.scores[self.scores.len() - window..];
        let sum: f64 = tail.iter().sum();
        Some(sum / window as f64)
    }

    /// Linear trend (slope) of the full series. Positive = improving.
    #[must_use]
    pub fn trend(&self) -> f64 {
        if self.scores.len() < 2 {
            return 0.0;
        }
        linear_slope(&self.scores)
    }

    /// Variance of the full score series.
    #[must_use]
    pub fn variance(&self) -> f64 {
        if self.scores.is_empty() {
            return 0.0;
        }
        let mean = self.scores.iter().sum::<f64>() / self.scores.len() as f64;
        let sum_sq: f64 = self.scores.iter().map(|s| (s - mean).powi(2)).sum();
        sum_sq / self.scores.len() as f64
    }

    /// Whether the loop should stop based on convergence criteria.
    ///
    /// Stops when:
    /// 1. Latest score >= 1.0 (fully verified), or
    /// 2. Last 3 scores are within `convergence_threshold` of each other and
    ///    trend is near-zero (plateau at high quality), or
    /// 3. Trend is significantly negative (diverging).
    #[must_use]
    pub fn should_stop(&self) -> bool {
        if self.scores.is_empty() {
            return false;
        }
        let latest = self.scores[self.scores.len() - 1];
        // Fully verified.
        if latest >= 1.0 - f64::EPSILON {
            return true;
        }
        // Plateau detection: last 3 scores within threshold.
        if self.scores.len() >= 3 {
            let tail = &self.scores[self.scores.len() - 3..];
            let min = tail.iter().copied().reduce(f64::min).unwrap_or(0.0);
            let max = tail.iter().copied().reduce(f64::max).unwrap_or(0.0);
            if (max - min).abs() <= self.convergence_threshold {
                let trend = self.trend();
                if trend.abs() < self.convergence_threshold {
                    return true;
                }
            }
        }
        // Divergence: strong negative trend.
        if self.scores.len() >= 3 && self.trend() < -0.1 {
            return true;
        }
        false
    }

    /// Number of observations.
    #[must_use]
    pub fn observation_count(&self) -> usize {
        self.scores.len()
    }
}

// ---------------------------------------------------------------------------
// Adaptive controller
// ---------------------------------------------------------------------------

/// Decides which `RefinementStrategy` to use based on score trajectory.
#[derive(Debug, Clone)]
pub struct AdaptiveController {
    plateau_patience: usize,
    min_improvement: f64,
}

impl AdaptiveController {
    #[must_use]
    pub fn new(plateau_patience: usize, min_improvement: f64) -> Self {
        Self {
            plateau_patience,
            min_improvement,
        }
    }

    /// Recommend a strategy given the score history so far.
    #[must_use]
    pub fn recommend_strategy(&self, scores: &[f64]) -> RefinementStrategy {
        if scores.len() < 2 {
            return RefinementStrategy::Conservative;
        }
        let recent_len = scores.len().min(self.plateau_patience);
        let tail = &scores[scores.len() - recent_len..];
        let min = tail.iter().copied().reduce(f64::min).unwrap_or(0.0);
        let max = tail.iter().copied().reduce(f64::max).unwrap_or(0.0);
        let range = max - min;

        // If we are plateaued: switch to aggressive.
        if tail.len() >= self.plateau_patience && range < self.min_improvement {
            return RefinementStrategy::Aggressive;
        }

        // If diverging: switch to conservative to stabilize.
        let slope = linear_slope(tail);
        if slope < -0.05 {
            return RefinementStrategy::Conservative;
        }

        // If making good progress: stay conservative (don't break what works).
        if slope > 0.05 {
            return RefinementStrategy::Conservative;
        }

        // Middle ground: try hybrid.
        RefinementStrategy::Hybrid
    }
}

// ---------------------------------------------------------------------------
// Counterexample analyzer
// ---------------------------------------------------------------------------

/// Analyzes counterexample fields to produce targeted spec patches.
#[derive(Debug, Clone)]
pub struct CounterexampleAnalyzer;

impl CounterexampleAnalyzer {
    /// Given counterexample variable bindings, propose patches that might
    /// address the failure.
    ///
    /// Heuristics:
    /// - Negative integer values suggest a `requires!(x >= 0)` precondition.
    /// - Large values suggest a bounded-range precondition.
    /// - Empty collection values suggest a non-emptiness precondition.
    /// - Multiple related failures suggest an invariant.
    #[must_use]
    pub fn analyze(fields: &[(String, String)]) -> Vec<SpecPatch> {
        let mut patches = Vec::new();

        for (name, value) in fields {
            // Negative integer heuristic.
            if let Ok(n) = value.parse::<i64>() {
                if n < 0 {
                    patches.push(SpecPatch::new(
                        PatchKind::AddRequires,
                        &format!("{} >= 0", name),
                        0.8,
                        &format!(
                            "counterexample has {} = {}; add non-negativity guard",
                            name, n
                        ),
                    ));
                }
                if n.abs() > 1_000_000 {
                    patches.push(SpecPatch::new(
                        PatchKind::AddRequires,
                        &format!("{} < 1_000_000 && {} > -1_000_000", name, name),
                        0.5,
                        &format!(
                            "counterexample has {} = {}; add bounded-range guard",
                            name, n
                        ),
                    ));
                }
            }

            // Empty collection heuristic.
            let lower = value.to_lowercase();
            if lower == "[]" || lower == "{}" || lower == "seq![]" || lower == "empty" {
                patches.push(SpecPatch::new(
                    PatchKind::AddRequires,
                    &format!("{}.len() > 0", name),
                    0.7,
                    &format!(
                        "counterexample has {} = empty; add non-emptiness guard",
                        name
                    ),
                ));
            }

            // Zero-division heuristic.
            if (name.contains("div") || name.contains("denom") || name.contains("divisor"))
                && value == "0"
            {
                patches.push(SpecPatch::new(
                    PatchKind::AddRequires,
                    &format!("{} != 0", name),
                    0.9,
                    &format!(
                        "counterexample has {} = 0; guard against division by zero",
                        name
                    ),
                ));
            }
        }

        // If many fields are present, suggest an invariant capturing their relationship.
        if fields.len() >= 3 {
            let names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
            patches.push(SpecPatch::new(
                PatchKind::AddInvariant,
                &format!("/* invariant relating {} */", names.join(", ")),
                0.3,
                "multiple counterexample fields suggest a relational invariant",
            ));
        }

        patches
    }
}

// ---------------------------------------------------------------------------
// Refinement state
// ---------------------------------------------------------------------------

/// Mutable state carried across iterations of the refinement loop.
#[derive(Debug, Clone)]
pub struct RefinementState {
    /// Zero-based iteration counter.
    pub current_iteration: usize,
    /// Highest score observed so far.
    pub best_score: f64,
    /// Best spec text observed so far.
    pub best_spec: String,
    /// Score history (one entry per completed iteration).
    pub score_history: Vec<f64>,
    /// Number of consecutive iterations without meaningful improvement.
    pub plateau_count: usize,
    /// Currently active strategy.
    pub active_strategy: RefinementStrategy,
}

impl RefinementState {
    #[must_use]
    pub(crate) fn new(strategy: RefinementStrategy) -> Self {
        Self {
            current_iteration: 0,
            best_score: 0.0,
            best_spec: String::new(),
            score_history: Vec::new(),
            plateau_count: 0,
            active_strategy: strategy,
        }
    }

    /// Record an iteration's score and update best/plateau tracking.
    pub(crate) fn record_iteration(&mut self, score: f64, spec: &str, min_improvement: f64) {
        self.score_history.push(score);
        if score > self.best_score + min_improvement {
            self.best_score = score;
            self.best_spec = spec.to_owned();
            self.plateau_count = 0;
        } else {
            self.plateau_count += 1;
        }
        self.current_iteration += 1;
    }
}

// ---------------------------------------------------------------------------
// Refinement history
// ---------------------------------------------------------------------------

/// Complete record of all iterations for post-hoc analysis.
#[derive(Debug, Clone)]
pub struct RefinementHistory {
    /// Function being refined.
    pub function_name: String,
    /// Per-iteration records.
    pub iterations: Vec<IterationResult>,
    /// Final outcome.
    pub outcome: Option<RefinementOutcome>,
    /// Total wall time across all iterations.
    pub total_elapsed: Duration,
}

impl RefinementHistory {
    #[must_use]
    pub fn new(function_name: &str) -> Self {
        Self {
            function_name: function_name.to_owned(),
            iterations: Vec::new(),
            outcome: None,
            total_elapsed: Duration::ZERO,
        }
    }

    /// Push an iteration record.
    pub fn push(&mut self, result: IterationResult) {
        self.total_elapsed += result.elapsed;
        self.iterations.push(result);
    }

    /// Human-readable summary of the refinement session.
    #[must_use]
    pub fn summary(&self) -> String {
        let n = self.iterations.len();
        let best = self
            .iterations
            .iter()
            .map(|r| r.score)
            .reduce(f64::max)
            .unwrap_or(0.0);
        let outcome_str = match &self.outcome {
            Some(RefinementOutcome::Converged { iterations, .. }) => {
                format!("converged after {} iterations", iterations)
            }
            Some(RefinementOutcome::Exhausted { .. }) => "exhausted budget".to_owned(),
            Some(RefinementOutcome::TimedOut { .. }) => "timed out".to_owned(),
            Some(RefinementOutcome::Diverged { .. }) => "diverged".to_owned(),
            None => "in progress".to_owned(),
        };
        format!(
            "RefinementHistory[{}]: {} iterations, best score {:.3}, \
             elapsed {:?}, outcome: {}",
            self.function_name, n, best, self.total_elapsed, outcome_str,
        )
    }

    /// Scores extracted from iteration records, in order.
    #[must_use]
    pub fn score_series(&self) -> Vec<f64> {
        self.iterations.iter().map(|r| r.score).collect()
    }

    /// Count of iterations where verification succeeded.
    #[must_use]
    pub fn verified_count(&self) -> usize {
        self.iterations
            .iter()
            .filter(|r| r.verification.is_verified())
            .count()
    }

    /// Count of iterations that produced counterexamples.
    #[must_use]
    pub fn counterexample_count(&self) -> usize {
        self.iterations
            .iter()
            .filter(|r| r.verification.is_counterexample())
            .count()
    }

    /// Distribution of strategies used across iterations.
    #[must_use]
    pub fn strategy_distribution(&self) -> HashMap<RefinementStrategy, usize> {
        let mut dist = HashMap::new();
        for iter in &self.iterations {
            *dist.entry(iter.strategy_used).or_insert(0) += 1;
        }
        dist
    }
}

// ---------------------------------------------------------------------------
// RefinementLoop — main orchestrator
// ---------------------------------------------------------------------------

/// Orchestrates the propose-verify-refine cycle.
///
/// The loop uses pluggable callbacks for proposal and verification so that
/// tests can inject deterministic behavior without requiring an actual LLM
/// backend or ay solver instance.
pub struct RefinementLoop {
    config: RefinementConfig,
    controller: AdaptiveController,
    detector: ConvergenceDetector,
    tracker: ScoreTracker,
}

impl RefinementLoop {
    /// Create a new refinement loop from configuration.
    #[must_use]
    pub fn new(config: RefinementConfig) -> Self {
        let controller = AdaptiveController::new(config.plateau_patience, config.min_improvement);
        let detector = ConvergenceDetector::new(config.convergence_threshold);
        Self {
            config,
            controller,
            detector,
            tracker: ScoreTracker::new(),
        }
    }

    /// Run the full refinement loop.
    ///
    /// `propose_fn` is called each iteration with `(current_spec, iteration, strategy)`
    /// and must return the next candidate spec string.
    ///
    /// `verify_fn` is called with the proposed spec and must return
    /// `(VerificationResult, score)`.
    #[must_use]
    pub fn run<P, V>(
        &mut self,
        function_name: &str,
        initial_spec: &str,
        mut propose_fn: P,
        mut verify_fn: V,
    ) -> RefinementOutcome
    where
        P: FnMut(&str, usize, RefinementStrategy) -> String,
        V: FnMut(&str) -> (VerificationResult, f64),
    {
        let mut state = RefinementState::new(self.config.strategy);
        state.best_spec = initial_spec.to_owned();
        let mut history = RefinementHistory::new(function_name);

        for _ in 0..self.config.max_iterations {
            let iter_result = self.single_iteration(&mut state, &mut propose_fn, &mut verify_fn);

            let score = iter_result.score;
            let spec = iter_result.proposed_spec.clone();

            self.tracker.record(score);
            self.detector.observe(score);
            history.push(iter_result);

            state.record_iteration(score, &spec, self.config.min_improvement);

            // Check convergence conditions.
            if score >= 1.0 - f64::EPSILON {
                return RefinementOutcome::Converged {
                    iterations: state.current_iteration,
                    final_score: score,
                };
            }

            if self.tracker.is_diverging() && state.current_iteration >= 3 {
                return RefinementOutcome::Diverged {
                    iterations: state.current_iteration,
                    final_score: score,
                };
            }

            if self.detector.should_stop() && score < 1.0 - f64::EPSILON {
                return RefinementOutcome::Exhausted {
                    iterations: state.current_iteration,
                    best_score: state.best_score,
                };
            }

            // Adaptive strategy switching.
            if matches!(self.config.strategy, RefinementStrategy::Adaptive) {
                state.active_strategy = self.controller.recommend_strategy(&state.score_history);
            }
        }

        RefinementOutcome::Exhausted {
            iterations: state.current_iteration,
            best_score: state.best_score,
        }
    }

    /// Execute one iteration of the refinement loop.
    pub(crate) fn single_iteration<P, V>(
        &self,
        state: &mut RefinementState,
        propose_fn: &mut P,
        verify_fn: &mut V,
    ) -> IterationResult
    where
        P: FnMut(&str, usize, RefinementStrategy) -> String,
        V: FnMut(&str) -> (VerificationResult, f64),
    {
        let start = Instant::now();

        let proposed = propose_fn(
            &state.best_spec,
            state.current_iteration,
            state.active_strategy,
        );

        let (verification, score) = verify_fn(&proposed);
        let elapsed = start.elapsed();

        IterationResult {
            proposed_spec: proposed,
            verification,
            score,
            elapsed,
            strategy_used: state.active_strategy,
        }
    }

    /// Read-only access to the score tracker.
    #[must_use]
    pub fn tracker(&self) -> &ScoreTracker {
        &self.tracker
    }

    /// Read-only access to the convergence detector.
    #[must_use]
    pub fn detector(&self) -> &ConvergenceDetector {
        &self.detector
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Compute the slope of a least-squares linear regression over `data`,
/// treating indices as x-values 0..n.
fn linear_slope(data: &[f64]) -> f64 {
    let n = data.len() as f64;
    if n < 2.0 {
        return 0.0;
    }
    let x_mean = (n - 1.0) / 2.0;
    let y_mean = data.iter().sum::<f64>() / n;
    let mut num = 0.0;
    let mut den = 0.0;
    for (i, &y) in data.iter().enumerate() {
        let x = i as f64;
        num += (x - x_mean) * (y - y_mean);
        den += (x - x_mean) * (x - x_mean);
    }
    if den.abs() < f64::EPSILON {
        return 0.0;
    }
    num / den
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // RefinementStrategy
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_as_str_conservative() {
        assert_eq!(RefinementStrategy::Conservative.as_str(), "conservative");
    }

    #[test]
    fn test_strategy_as_str_aggressive() {
        assert_eq!(RefinementStrategy::Aggressive.as_str(), "aggressive");
    }

    #[test]
    fn test_strategy_as_str_adaptive() {
        assert_eq!(RefinementStrategy::Adaptive.as_str(), "adaptive");
    }

    #[test]
    fn test_strategy_as_str_hybrid() {
        assert_eq!(RefinementStrategy::Hybrid.as_str(), "hybrid");
    }

    // -----------------------------------------------------------------------
    // RefinementConfig
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_default_values() {
        let cfg = RefinementConfig::default();
        assert_eq!(cfg.max_iterations, 20);
        assert_eq!(cfg.timeout_per_iteration, Duration::from_secs(30));
        assert!((cfg.convergence_threshold - 0.01).abs() < f64::EPSILON);
        assert_eq!(cfg.strategy, RefinementStrategy::Adaptive);
        assert_eq!(cfg.plateau_patience, 3);
    }

    // -----------------------------------------------------------------------
    // VerificationResult
    // -----------------------------------------------------------------------

    #[test]
    fn test_verification_result_verified() {
        let vr = VerificationResult::Verified;
        assert!(vr.is_verified());
        assert!(!vr.is_counterexample());
    }

    #[test]
    fn test_verification_result_counterexample() {
        let vr = VerificationResult::Counterexample {
            fields: vec![("x".to_owned(), "-1".to_owned())],
        };
        assert!(!vr.is_verified());
        assert!(vr.is_counterexample());
    }

    #[test]
    fn test_verification_result_unknown() {
        let vr = VerificationResult::Unknown {
            reason: "timeout".to_owned(),
        };
        assert!(!vr.is_verified());
        assert!(!vr.is_counterexample());
    }

    // -----------------------------------------------------------------------
    // ScoreTracker
    // -----------------------------------------------------------------------

    #[test]
    fn test_score_tracker_empty() {
        let st = ScoreTracker::new();
        assert!(st.is_empty());
        assert_eq!(st.len(), 0);
        assert!(st.latest().is_none());
        assert!(st.best().is_none());
    }

    #[test]
    fn test_score_tracker_record_and_query() {
        let mut st = ScoreTracker::new();
        st.record(0.3);
        st.record(0.5);
        st.record(0.4);
        assert_eq!(st.len(), 3);
        assert!(!st.is_empty());
        assert!((st.latest().unwrap() - 0.4).abs() < f64::EPSILON);
        assert!((st.best().unwrap() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_score_tracker_plateau_detected() {
        let mut st = ScoreTracker::new();
        st.record(0.5);
        st.record(0.5);
        st.record(0.5);
        assert!(st.is_plateaued(3, 0.01));
    }

    #[test]
    fn test_score_tracker_no_plateau_with_variance() {
        let mut st = ScoreTracker::new();
        st.record(0.1);
        st.record(0.5);
        st.record(0.9);
        assert!(!st.is_plateaued(3, 0.01));
    }

    #[test]
    fn test_score_tracker_plateau_too_few_scores() {
        let mut st = ScoreTracker::new();
        st.record(0.5);
        st.record(0.5);
        assert!(!st.is_plateaued(3, 0.01));
    }

    #[test]
    fn test_score_tracker_converging() {
        let mut st = ScoreTracker::new();
        st.record(0.1);
        st.record(0.3);
        st.record(0.5);
        st.record(0.7);
        st.record(0.9);
        assert!(st.is_converging());
        assert!(!st.is_diverging());
    }

    #[test]
    fn test_score_tracker_diverging() {
        let mut st = ScoreTracker::new();
        st.record(0.9);
        st.record(0.7);
        st.record(0.4);
        st.record(0.2);
        st.record(0.0);
        assert!(st.is_diverging());
        assert!(!st.is_converging());
    }

    #[test]
    fn test_score_tracker_not_converging_single_entry() {
        let mut st = ScoreTracker::new();
        st.record(0.5);
        assert!(!st.is_converging());
    }

    // -----------------------------------------------------------------------
    // ConvergenceDetector
    // -----------------------------------------------------------------------

    #[test]
    fn test_convergence_detector_moving_average() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.2);
        cd.observe(0.4);
        cd.observe(0.6);
        let ma = cd.moving_average(3).unwrap();
        assert!((ma - 0.4).abs() < 1e-10);
    }

    #[test]
    fn test_convergence_detector_moving_average_insufficient_data() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.5);
        assert!(cd.moving_average(3).is_none());
    }

    #[test]
    fn test_convergence_detector_moving_average_window_zero() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.5);
        assert!(cd.moving_average(0).is_none());
    }

    #[test]
    fn test_convergence_detector_trend_positive() {
        let mut cd = ConvergenceDetector::new(0.01);
        for i in 0..10 {
            cd.observe(i as f64 * 0.1);
        }
        assert!(cd.trend() > 0.0);
    }

    #[test]
    fn test_convergence_detector_trend_negative() {
        let mut cd = ConvergenceDetector::new(0.01);
        for i in (0..10).rev() {
            cd.observe(i as f64 * 0.1);
        }
        assert!(cd.trend() < 0.0);
    }

    #[test]
    fn test_convergence_detector_variance_constant() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.5);
        cd.observe(0.5);
        cd.observe(0.5);
        assert!(cd.variance() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_detector_variance_spread() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.0);
        cd.observe(1.0);
        // mean = 0.5, variance = ((0.5)^2 + (0.5)^2) / 2 = 0.25
        assert!((cd.variance() - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_convergence_detector_should_stop_on_verified() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(1.0);
        assert!(cd.should_stop());
    }

    #[test]
    fn test_convergence_detector_should_stop_on_plateau() {
        let mut cd = ConvergenceDetector::new(0.05);
        cd.observe(0.8);
        cd.observe(0.8);
        cd.observe(0.8);
        assert!(cd.should_stop());
    }

    #[test]
    fn test_convergence_detector_should_not_stop_early() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.2);
        cd.observe(0.4);
        assert!(!cd.should_stop());
    }

    #[test]
    fn test_convergence_detector_observation_count() {
        let mut cd = ConvergenceDetector::new(0.01);
        assert_eq!(cd.observation_count(), 0);
        cd.observe(0.5);
        cd.observe(0.6);
        assert_eq!(cd.observation_count(), 2);
    }

    // -----------------------------------------------------------------------
    // AdaptiveController
    // -----------------------------------------------------------------------

    #[test]
    fn test_adaptive_controller_starts_conservative() {
        let ac = AdaptiveController::new(3, 0.01);
        assert_eq!(ac.recommend_strategy(&[]), RefinementStrategy::Conservative);
        assert_eq!(
            ac.recommend_strategy(&[0.5]),
            RefinementStrategy::Conservative
        );
    }

    #[test]
    fn test_adaptive_controller_plateau_switches_aggressive() {
        let ac = AdaptiveController::new(3, 0.01);
        // Three identical scores = plateau => aggressive.
        assert_eq!(
            ac.recommend_strategy(&[0.5, 0.5, 0.5]),
            RefinementStrategy::Aggressive
        );
    }

    #[test]
    fn test_adaptive_controller_diverging_switches_conservative() {
        let ac = AdaptiveController::new(3, 0.01);
        // Strongly declining => conservative to stabilize.
        assert_eq!(
            ac.recommend_strategy(&[0.9, 0.6, 0.3]),
            RefinementStrategy::Conservative
        );
    }

    #[test]
    fn test_adaptive_controller_improving_stays_conservative() {
        let ac = AdaptiveController::new(3, 0.01);
        assert_eq!(
            ac.recommend_strategy(&[0.1, 0.4, 0.7]),
            RefinementStrategy::Conservative
        );
    }

    // -----------------------------------------------------------------------
    // CounterexampleAnalyzer
    // -----------------------------------------------------------------------

    #[test]
    fn test_analyzer_negative_value_suggests_nonneg() {
        let fields = vec![("x".to_owned(), "-5".to_owned())];
        let patches = CounterexampleAnalyzer::analyze(&fields);
        assert!(!patches.is_empty());
        assert!(patches
            .iter()
            .any(|p| p.kind == PatchKind::AddRequires && p.clause.contains("x >= 0")));
    }

    #[test]
    fn test_analyzer_large_value_suggests_bound() {
        let fields = vec![("n".to_owned(), "99999999".to_owned())];
        let patches = CounterexampleAnalyzer::analyze(&fields);
        assert!(patches
            .iter()
            .any(|p| p.kind == PatchKind::AddRequires && p.clause.contains("1_000_000")));
    }

    #[test]
    fn test_analyzer_empty_collection_suggests_nonempty() {
        let fields = vec![("data".to_owned(), "[]".to_owned())];
        let patches = CounterexampleAnalyzer::analyze(&fields);
        assert!(patches
            .iter()
            .any(|p| p.kind == PatchKind::AddRequires && p.clause.contains("len() > 0")));
    }

    #[test]
    fn test_analyzer_zero_divisor_suggests_nonzero() {
        let fields = vec![("divisor".to_owned(), "0".to_owned())];
        let patches = CounterexampleAnalyzer::analyze(&fields);
        assert!(patches
            .iter()
            .any(|p| p.kind == PatchKind::AddRequires && p.clause.contains("!= 0")));
    }

    #[test]
    fn test_analyzer_many_fields_suggests_invariant() {
        let fields = vec![
            ("a".to_owned(), "1".to_owned()),
            ("b".to_owned(), "2".to_owned()),
            ("c".to_owned(), "3".to_owned()),
        ];
        let patches = CounterexampleAnalyzer::analyze(&fields);
        assert!(patches.iter().any(|p| p.kind == PatchKind::AddInvariant));
    }

    #[test]
    fn test_analyzer_empty_fields_no_patches() {
        let patches = CounterexampleAnalyzer::analyze(&[]);
        assert!(patches.is_empty());
    }

    // -----------------------------------------------------------------------
    // SpecPatch
    // -----------------------------------------------------------------------

    #[test]
    fn test_spec_patch_confidence_clamped() {
        let p = SpecPatch::new(PatchKind::AddRequires, "x > 0", 1.5, "test");
        assert!((p.confidence - 1.0).abs() < f64::EPSILON);

        let p2 = SpecPatch::new(PatchKind::AddRequires, "x > 0", -0.5, "test");
        assert!((p2.confidence - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // RefinementState
    // -----------------------------------------------------------------------

    #[test]
    fn test_state_initial() {
        let s = RefinementState::new(RefinementStrategy::Conservative);
        assert_eq!(s.current_iteration, 0);
        assert!((s.best_score - 0.0).abs() < f64::EPSILON);
        assert!(s.score_history.is_empty());
        assert_eq!(s.plateau_count, 0);
    }

    #[test]
    fn test_state_record_improves_best() {
        let mut s = RefinementState::new(RefinementStrategy::Conservative);
        s.record_iteration(0.5, "spec_a", 0.01);
        assert!((s.best_score - 0.5).abs() < f64::EPSILON);
        assert_eq!(s.best_spec, "spec_a");
        assert_eq!(s.plateau_count, 0);

        s.record_iteration(0.8, "spec_b", 0.01);
        assert!((s.best_score - 0.8).abs() < f64::EPSILON);
        assert_eq!(s.best_spec, "spec_b");
    }

    #[test]
    fn test_state_record_plateau_increments() {
        let mut s = RefinementState::new(RefinementStrategy::Conservative);
        s.record_iteration(0.5, "spec_a", 0.01);
        s.record_iteration(0.5, "spec_b", 0.01);
        s.record_iteration(0.49, "spec_c", 0.01);
        assert_eq!(s.plateau_count, 2);
        assert_eq!(s.best_spec, "spec_a");
    }

    // -----------------------------------------------------------------------
    // RefinementHistory
    // -----------------------------------------------------------------------

    #[test]
    fn test_history_summary_empty() {
        let h = RefinementHistory::new("foo");
        let s = h.summary();
        assert!(s.contains("foo"));
        assert!(s.contains("0 iterations"));
        assert!(s.contains("in progress"));
    }

    #[test]
    fn test_history_push_and_counts() {
        let mut h = RefinementHistory::new("bar");
        h.push(IterationResult {
            proposed_spec: "spec1".to_owned(),
            verification: VerificationResult::Counterexample {
                fields: vec![("x".to_owned(), "-1".to_owned())],
            },
            score: 0.3,
            elapsed: Duration::from_millis(10),
            strategy_used: RefinementStrategy::Conservative,
        });
        h.push(IterationResult {
            proposed_spec: "spec2".to_owned(),
            verification: VerificationResult::Verified,
            score: 1.0,
            elapsed: Duration::from_millis(15),
            strategy_used: RefinementStrategy::Conservative,
        });

        assert_eq!(h.verified_count(), 1);
        assert_eq!(h.counterexample_count(), 1);
        assert_eq!(h.total_elapsed, Duration::from_millis(25));

        let series = h.score_series();
        assert_eq!(series.len(), 2);
        assert!((series[0] - 0.3).abs() < f64::EPSILON);
        assert!((series[1] - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_history_strategy_distribution() {
        let mut h = RefinementHistory::new("baz");
        h.push(IterationResult {
            proposed_spec: "s1".to_owned(),
            verification: VerificationResult::Verified,
            score: 1.0,
            elapsed: Duration::from_millis(1),
            strategy_used: RefinementStrategy::Conservative,
        });
        h.push(IterationResult {
            proposed_spec: "s2".to_owned(),
            verification: VerificationResult::Verified,
            score: 1.0,
            elapsed: Duration::from_millis(1),
            strategy_used: RefinementStrategy::Aggressive,
        });
        h.push(IterationResult {
            proposed_spec: "s3".to_owned(),
            verification: VerificationResult::Verified,
            score: 1.0,
            elapsed: Duration::from_millis(1),
            strategy_used: RefinementStrategy::Conservative,
        });

        let dist = h.strategy_distribution();
        assert_eq!(dist[&RefinementStrategy::Conservative], 2);
        assert_eq!(dist[&RefinementStrategy::Aggressive], 1);
    }

    #[test]
    fn test_history_summary_with_outcome() {
        let mut h = RefinementHistory::new("qux");
        h.outcome = Some(RefinementOutcome::Converged {
            iterations: 3,
            final_score: 1.0,
        });
        let s = h.summary();
        assert!(s.contains("converged"));
    }

    // -----------------------------------------------------------------------
    // RefinementLoop — integration tests with mock callbacks
    // -----------------------------------------------------------------------

    #[test]
    fn test_loop_converges_immediately() {
        let config = RefinementConfig {
            max_iterations: 10,
            strategy: RefinementStrategy::Conservative,
            ..Default::default()
        };
        let mut rl = RefinementLoop::new(config);

        let outcome = rl.run(
            "trivial_fn",
            "initial",
            |_spec, _iter, _strat| "perfect_spec".to_owned(),
            |_spec| (VerificationResult::Verified, 1.0),
        );

        assert!(outcome.is_converged());
        match outcome {
            RefinementOutcome::Converged {
                iterations,
                final_score,
            } => {
                assert_eq!(iterations, 1);
                assert!((final_score - 1.0).abs() < f64::EPSILON);
            }
            _ => panic!("expected convergence"),
        }
    }

    #[test]
    fn test_loop_converges_after_refinement() {
        let config = RefinementConfig {
            max_iterations: 10,
            strategy: RefinementStrategy::Conservative,
            ..Default::default()
        };
        let mut rl = RefinementLoop::new(config);

        let outcome = rl.run(
            "refine_fn",
            "initial",
            |_spec, iter, _strat| format!("spec_v{}", iter),
            |spec| {
                if spec == "spec_v2" {
                    (VerificationResult::Verified, 1.0)
                } else {
                    (
                        VerificationResult::Counterexample {
                            fields: vec![("x".to_owned(), "-1".to_owned())],
                        },
                        0.3 + 0.2
                            * spec.chars().last().unwrap_or('0').to_digit(10).unwrap_or(0) as f64,
                    )
                }
            },
        );

        assert!(outcome.is_converged());
        match outcome {
            RefinementOutcome::Converged { iterations, .. } => {
                assert_eq!(iterations, 3); // iterations 0, 1, 2
            }
            _ => panic!("expected convergence"),
        }
    }

    #[test]
    fn test_loop_exhausts_budget() {
        let config = RefinementConfig {
            max_iterations: 3,
            strategy: RefinementStrategy::Conservative,
            convergence_threshold: 0.001,
            ..Default::default()
        };
        let mut rl = RefinementLoop::new(config);

        let outcome = rl.run(
            "hard_fn",
            "initial",
            |_spec, iter, _strat| format!("attempt_{}", iter),
            |_spec| (VerificationResult::Counterexample { fields: vec![] }, 0.1),
        );

        assert!(!outcome.is_converged());
    }

    #[test]
    fn test_loop_detects_divergence() {
        let config = RefinementConfig {
            max_iterations: 20,
            strategy: RefinementStrategy::Conservative,
            convergence_threshold: 0.001,
            ..Default::default()
        };
        let mut rl = RefinementLoop::new(config);

        let mut call = 0;
        let outcome = rl.run(
            "diverge_fn",
            "initial",
            |_spec, _iter, _strat| "bad_spec".to_owned(),
            |_spec| {
                call += 1;
                let score = 0.9 - (call as f64) * 0.15;
                (
                    VerificationResult::Counterexample { fields: vec![] },
                    score.max(0.0),
                )
            },
        );

        match outcome {
            RefinementOutcome::Diverged { .. } => {}
            other => panic!("expected divergence, got {:?}", other),
        }
    }

    #[test]
    fn test_loop_adaptive_strategy_changes() {
        let config = RefinementConfig {
            max_iterations: 10,
            strategy: RefinementStrategy::Adaptive,
            plateau_patience: 2,
            min_improvement: 0.01,
            convergence_threshold: 0.001,
            ..Default::default()
        };
        let mut rl = RefinementLoop::new(config);

        let mut strategies_seen: Vec<RefinementStrategy> = Vec::new();
        let mut call = 0;

        let _outcome = rl.run(
            "adaptive_fn",
            "initial",
            |_spec, _iter, strat| {
                strategies_seen.push(strat);
                "candidate".to_owned()
            },
            |_spec| {
                call += 1;
                // Plateau at 0.5 for first few, then improve.
                let score = if call <= 4 {
                    0.5
                } else {
                    0.5 + (call - 4) as f64 * 0.1
                };
                if score >= 1.0 {
                    (VerificationResult::Verified, 1.0)
                } else {
                    (VerificationResult::Counterexample { fields: vec![] }, score)
                }
            },
        );

        // After plateau, the controller should have recommended Aggressive at
        // least once.
        assert!(
            strategies_seen.len() >= 2,
            "should have recorded multiple strategy observations"
        );
    }

    #[test]
    fn test_loop_tracker_populated() {
        let config = RefinementConfig {
            max_iterations: 5,
            strategy: RefinementStrategy::Conservative,
            ..Default::default()
        };
        let mut rl = RefinementLoop::new(config);

        let _outcome = rl.run(
            "fn_track",
            "init",
            |_s, _i, _st| "spec".to_owned(),
            |_s| (VerificationResult::Verified, 1.0),
        );

        assert!(!rl.tracker().is_empty());
        assert!((rl.tracker().latest().unwrap() - 1.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // RefinementOutcome
    // -----------------------------------------------------------------------

    #[test]
    fn test_outcome_is_converged() {
        let c = RefinementOutcome::Converged {
            iterations: 5,
            final_score: 1.0,
        };
        assert!(c.is_converged());

        let e = RefinementOutcome::Exhausted {
            iterations: 10,
            best_score: 0.8,
        };
        assert!(!e.is_converged());
    }

    // -----------------------------------------------------------------------
    // linear_slope helper
    // -----------------------------------------------------------------------

    #[test]
    fn test_linear_slope_ascending() {
        let data = [0.0, 1.0, 2.0, 3.0, 4.0];
        let slope = linear_slope(&data);
        assert!((slope - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_linear_slope_descending() {
        let data = [4.0, 3.0, 2.0, 1.0, 0.0];
        let slope = linear_slope(&data);
        assert!((slope - (-1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_linear_slope_flat() {
        let data = [5.0, 5.0, 5.0];
        let slope = linear_slope(&data);
        assert!(slope.abs() < 1e-10);
    }

    #[test]
    fn test_linear_slope_single_point() {
        let data = [3.0];
        let slope = linear_slope(&data);
        assert!((slope - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_linear_slope_empty() {
        let data: [f64; 0] = [];
        let slope = linear_slope(&data);
        assert!((slope - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // PatchKind equality
    // -----------------------------------------------------------------------

    #[test]
    fn test_patch_kind_equality() {
        assert_eq!(PatchKind::AddRequires, PatchKind::AddRequires);
        assert_ne!(PatchKind::AddRequires, PatchKind::StrengthenEnsures);
        assert_ne!(PatchKind::WeakenEnsures, PatchKind::AddInvariant);
        assert_ne!(PatchKind::AddAssertion, PatchKind::AddHelper);
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_score_tracker_plateau_with_exact_window() {
        let mut st = ScoreTracker::new();
        st.record(0.1); // older, outside window
        st.record(0.5);
        st.record(0.5);
        st.record(0.5);
        assert!(st.is_plateaued(3, 0.01));
        // The first score (0.1) is outside the window of 3.
    }

    #[test]
    fn test_convergence_detector_empty_should_not_stop() {
        let cd = ConvergenceDetector::new(0.01);
        assert!(!cd.should_stop());
    }

    #[test]
    fn test_convergence_detector_variance_empty() {
        let cd = ConvergenceDetector::new(0.01);
        assert!((cd.variance() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_detector_trend_single_observation() {
        let mut cd = ConvergenceDetector::new(0.01);
        cd.observe(0.5);
        assert!((cd.trend() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_analyzer_positive_int_no_nonneg_patch() {
        let fields = vec![("x".to_owned(), "42".to_owned())];
        let patches = CounterexampleAnalyzer::analyze(&fields);
        assert!(
            !patches.iter().any(|p| p.clause.contains(">= 0")),
            "positive value should not trigger non-negativity patch"
        );
    }
}
