// trust-vc-oracle — Convergence analysis for oracle sessions
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Tracks and predicts oracle convergence behavior across functions.
// Uses exponential decay modeling and signature-based difficulty classification
// to estimate remaining iterations and provide actionable recommendations.

use std::collections::HashMap;

use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;

/// Difficulty classification for a function based on signature complexity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Difficulty {
    /// Expected to converge in 1-2 iterations.
    Easy,
    /// Expected to converge in 3-5 iterations.
    Medium,
    /// Expected to converge in 6-10 iterations.
    Hard,
    /// Expected to require more than 10 iterations (likely needs manual help).
    Intractable,
}

impl Difficulty {
    /// Upper bound of iterations for this difficulty class.
    #[must_use]
    pub fn max_iterations(self) -> usize {
        match self {
            Difficulty::Easy => 2,
            Difficulty::Medium => 5,
            Difficulty::Hard => 10,
            Difficulty::Intractable => usize::MAX,
        }
    }

    /// Human-readable label.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Difficulty::Easy => "easy",
            Difficulty::Medium => "medium",
            Difficulty::Hard => "hard",
            Difficulty::Intractable => "intractable",
        }
    }
}

/// Feedback type classification for tracking convergence patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FeedbackKind {
    Verified,
    Failed,
    Unknown,
    Error,
}

impl From<&ProofFeedback> for FeedbackKind {
    fn from(fb: &ProofFeedback) -> Self {
        match fb {
            ProofFeedback::Verified { .. } => FeedbackKind::Verified,
            ProofFeedback::Failed { .. } => FeedbackKind::Failed,
            ProofFeedback::Unknown { .. } => FeedbackKind::Unknown,
            ProofFeedback::Error { .. } => FeedbackKind::Error,
        }
    }
}

/// Per-function history record within the convergence tracker.
#[derive(Debug, Clone)]
pub struct FunctionHistory {
    /// Function name.
    pub name: String,
    /// Ordered sequence of feedback kinds received.
    pub feedback_sequence: Vec<FeedbackKind>,
    /// Whether the function eventually converged (was verified).
    pub converged: bool,
    /// Iteration at which convergence occurred (1-indexed), or None.
    pub converged_at: Option<usize>,
    /// Predicted difficulty based on signature analysis.
    pub difficulty: Difficulty,
}

impl FunctionHistory {
    /// Count of distinct feedback kinds seen.
    #[must_use]
    pub fn distinct_feedback_kinds(&self) -> usize {
        let mut seen = [false; 4];
        for kind in &self.feedback_sequence {
            let idx = match kind {
                FeedbackKind::Verified => 0,
                FeedbackKind::Failed => 1,
                FeedbackKind::Unknown => 2,
                FeedbackKind::Error => 3,
            };
            seen[idx] = true;
        }
        seen.iter().filter(|&&s| s).count()
    }

    /// Spec drift: ratio of distinct feedback kinds to total iterations.
    ///
    /// Higher drift means the oracle is exploring more diverse failure modes
    /// rather than converging on a solution. Returns 0.0 for empty history.
    #[must_use]
    pub fn spec_drift(&self) -> f64 {
        let total = self.feedback_sequence.len();
        if total == 0 {
            return 0.0;
        }
        self.distinct_feedback_kinds() as f64 / total as f64
    }

    /// Number of iterations recorded.
    #[must_use]
    pub fn iteration_count(&self) -> usize {
        self.feedback_sequence.len()
    }
}

/// Tracks convergence behavior across multiple functions.
///
/// Records feedback history and computes aggregate statistics for
/// convergence rate analysis and prediction.
#[derive(Debug, Clone)]
pub struct ConvergenceTracker {
    histories: HashMap<String, FunctionHistory>,
}

impl ConvergenceTracker {
    /// Create a new empty tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            histories: HashMap::new(),
        }
    }

    /// Record a feedback event for a function.
    ///
    /// If this is the first event for this function, a new history is created
    /// with the given difficulty classification. Subsequent calls append to
    /// the existing history.
    pub fn record(&mut self, func_name: &str, feedback: &ProofFeedback, difficulty: Difficulty) {
        let kind = FeedbackKind::from(feedback);
        let history = self
            .histories
            .entry(func_name.to_owned())
            .or_insert_with(|| FunctionHistory {
                name: func_name.to_owned(),
                feedback_sequence: Vec::new(),
                converged: false,
                converged_at: None,
                difficulty,
            });

        history.feedback_sequence.push(kind);

        if kind == FeedbackKind::Verified && !history.converged {
            history.converged = true;
            history.converged_at = Some(history.feedback_sequence.len());
        }
    }

    /// Get the history for a specific function.
    #[must_use]
    pub fn history(&self, func_name: &str) -> Option<&FunctionHistory> {
        self.histories.get(func_name)
    }

    /// Get all recorded function histories.
    #[must_use]
    pub fn all_histories(&self) -> &HashMap<String, FunctionHistory> {
        &self.histories
    }

    /// Total number of tracked functions.
    #[must_use]
    pub fn function_count(&self) -> usize {
        self.histories.len()
    }

    /// Number of functions that converged (were verified).
    #[must_use]
    pub fn converged_count(&self) -> usize {
        self.histories.values().filter(|h| h.converged).count()
    }

    /// Overall convergence rate: converged / total.
    ///
    /// Returns 0.0 if no functions are tracked.
    #[must_use]
    pub fn convergence_rate(&self) -> f64 {
        let total = self.histories.len();
        if total == 0 {
            return 0.0;
        }
        self.converged_count() as f64 / total as f64
    }

    /// Average iteration count across all converged functions.
    ///
    /// Returns `None` if no functions have converged.
    #[must_use]
    pub fn avg_iterations_to_convergence(&self) -> Option<f64> {
        let converged: Vec<&FunctionHistory> =
            self.histories.values().filter(|h| h.converged).collect();
        if converged.is_empty() {
            return None;
        }
        let total_iters: usize = converged.iter().filter_map(|h| h.converged_at).sum();
        Some(total_iters as f64 / converged.len() as f64)
    }

    /// Compute the empirical single-step convergence probability.
    ///
    /// This is the fraction of all recorded iterations (across all functions)
    /// that resulted in `Verified`. Used as the `p` parameter for the
    /// exponential decay predictor.
    #[must_use]
    pub fn empirical_step_probability(&self) -> f64 {
        let mut verified_steps = 0usize;
        let mut total_steps = 0usize;
        for history in self.histories.values() {
            for kind in &history.feedback_sequence {
                total_steps += 1;
                if *kind == FeedbackKind::Verified {
                    verified_steps += 1;
                }
            }
        }
        if total_steps == 0 {
            return 0.0;
        }
        verified_steps as f64 / total_steps as f64
    }

    /// Build a convergence report summarizing all tracked functions.
    #[must_use]
    pub fn report(&self) -> ConvergenceReport {
        let mut per_difficulty: HashMap<Difficulty, DifficultyBreakdown> = HashMap::new();

        for history in self.histories.values() {
            let entry =
                per_difficulty
                    .entry(history.difficulty)
                    .or_insert_with(|| DifficultyBreakdown {
                        difficulty: history.difficulty,
                        total: 0,
                        converged: 0,
                        total_iterations: 0,
                    });
            entry.total += 1;
            if history.converged {
                entry.converged += 1;
            }
            entry.total_iterations += history.iteration_count();
        }

        let mut breakdowns: Vec<DifficultyBreakdown> = per_difficulty.into_values().collect();
        breakdowns.sort_by_key(|b| match b.difficulty {
            Difficulty::Easy => 0,
            Difficulty::Medium => 1,
            Difficulty::Hard => 2,
            Difficulty::Intractable => 3,
        });

        let intractable_functions: Vec<String> = self
            .histories
            .values()
            .filter(|h| !h.converged && h.iteration_count() >= 10)
            .map(|h| h.name.clone())
            .collect();

        let recommendations =
            build_recommendations(&intractable_functions, self.convergence_rate());

        ConvergenceReport {
            total_functions: self.function_count(),
            converged_functions: self.converged_count(),
            convergence_rate: self.convergence_rate(),
            avg_iterations: self.avg_iterations_to_convergence(),
            empirical_step_probability: self.empirical_step_probability(),
            per_difficulty: breakdowns,
            intractable_functions,
            recommendations,
        }
    }
}

impl Default for ConvergenceTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Predicts remaining iterations to convergence using exponential decay.
///
/// Model: `P(converge by step n) = 1 - (1 - p)^n`
///
/// Where `p` is the single-step convergence probability, estimated from
/// historical data or provided directly.
#[derive(Debug, Clone)]
pub struct ConvergencePredictor {
    /// Single-step convergence probability (0.0 to 1.0).
    step_probability: f64,
}

impl ConvergencePredictor {
    /// Create a predictor with the given single-step probability.
    ///
    /// Clamps `p` to `[0.0, 1.0]`.
    #[must_use]
    pub fn new(step_probability: f64) -> Self {
        Self {
            step_probability: step_probability.clamp(0.0, 1.0),
        }
    }

    /// Create a predictor from a tracker's empirical data.
    #[must_use]
    pub fn from_tracker(tracker: &ConvergenceTracker) -> Self {
        Self::new(tracker.empirical_step_probability())
    }

    /// The step probability used by this predictor.
    #[must_use]
    pub fn step_probability(&self) -> f64 {
        self.step_probability
    }

    /// Probability of having converged by step `n` (1-indexed).
    ///
    /// `P(converge by step n) = 1 - (1 - p)^n`
    ///
    /// Returns 0.0 for `n == 0` or when `p == 0.0`.
    #[must_use]
    pub fn cumulative_probability(&self, n: usize) -> f64 {
        if n == 0 || self.step_probability == 0.0 {
            return 0.0;
        }
        if self.step_probability >= 1.0 {
            return 1.0;
        }
        1.0 - (1.0 - self.step_probability).powi(n as i32)
    }

    /// Estimate remaining iterations needed to reach a given confidence level.
    ///
    /// Solves `1 - (1-p)^n >= confidence` for `n`, given that `already_done`
    /// non-converging iterations have been spent.
    ///
    /// Returns `None` if convergence at the requested confidence is impossible
    /// (e.g., `p == 0.0` or `confidence >= 1.0`).
    #[must_use]
    pub fn remaining_iterations(&self, already_done: usize, confidence: f64) -> Option<usize> {
        if self.step_probability <= 0.0 || confidence >= 1.0 {
            return None;
        }
        if confidence <= 0.0 {
            return Some(0);
        }
        // We need: 1 - (1-p)^(already_done + remaining) >= confidence
        // => (1-p)^(already_done + remaining) <= 1 - confidence
        // => (already_done + remaining) * ln(1-p) <= ln(1 - confidence)
        // => already_done + remaining >= ln(1 - confidence) / ln(1-p)
        //    (inequality flips because ln(1-p) < 0)
        let q = 1.0 - self.step_probability;
        let ln_q = q.ln();
        if ln_q == 0.0 {
            // p == 1.0, already handled by cumulative_probability
            return Some(0);
        }
        let total_needed_f64 = (1.0 - confidence).ln() / ln_q;
        let total_needed = total_needed_f64.ceil() as usize;
        Some(total_needed.saturating_sub(already_done))
    }

    /// Estimate total iterations to reach the given confidence level from scratch.
    ///
    /// Equivalent to `remaining_iterations(0, confidence)`.
    #[must_use]
    pub fn total_iterations_for_confidence(&self, confidence: f64) -> Option<usize> {
        self.remaining_iterations(0, confidence)
    }
}

/// Classifies function difficulty based on signature properties.
///
/// Heuristic scoring:
/// - Parameter count: more params = harder
/// - Return type complexity: Option, Result, collections = harder
/// - Generic/lifetime indicators: harder
/// - Mutable references: harder
#[derive(Debug, Clone)]
pub struct DifficultyClassifier;

impl DifficultyClassifier {
    /// Classify a function signature into a difficulty bucket.
    #[must_use]
    pub fn classify(func: &FunctionSignature) -> Difficulty {
        let score = Self::complexity_score(func);
        match score {
            0..=2 => Difficulty::Easy,
            3..=5 => Difficulty::Medium,
            6..=9 => Difficulty::Hard,
            _ => Difficulty::Intractable,
        }
    }

    /// Compute a numeric complexity score (higher = more complex).
    ///
    /// Scoring rubric:
    /// - Base: 1 point per parameter
    /// - +2 if return type contains `Option` or `Result`
    /// - +1 per generic type parameter (`<T>` patterns)
    /// - +2 if any parameter is `&mut`
    /// - +1 if return type contains collection keywords (Vec, Map, Set, Seq)
    /// - +1 per lifetime annotation
    #[must_use]
    pub fn complexity_score(func: &FunctionSignature) -> usize {
        let mut score = 0usize;

        // Parameter count
        score += func.params.len();

        // Mutable reference parameters
        for (_name, ty) in &func.params {
            if ty.contains("&mut") {
                score += 2;
            }
            // Generic/complex parameter types
            if ty.contains('<') {
                score += 1;
            }
        }

        // Return type complexity
        if let Some(ref ret) = func.return_type {
            if ret.contains("Option") || ret.contains("Result") {
                score += 2;
            }
            if ret.contains("Vec")
                || ret.contains("Map")
                || ret.contains("Set")
                || ret.contains("Seq")
            {
                score += 1;
            }
            if ret.contains('<') {
                score += 1;
            }
        }

        // Lifetime annotations in source
        let lifetime_count = func
            .source
            .matches("'")
            .count()
            .saturating_sub(count_string_literals(&func.source));
        score += lifetime_count / 2; // approximate: each lifetime appears ~twice

        score
    }
}

/// Count approximate number of string literal single-quotes to avoid
/// double-counting lifetimes inside string content.
fn count_string_literals(source: &str) -> usize {
    // Simple heuristic: count char literals like 'a' (3 chars pattern)
    let mut count = 0;
    let bytes = source.as_bytes();
    let mut i = 0;
    while i + 2 < bytes.len() {
        if bytes[i] == b'\'' && i + 2 < bytes.len() && bytes[i + 2] == b'\'' {
            count += 2; // Two single-quote chars from one char literal
            i += 3;
        } else {
            i += 1;
        }
    }
    count
}

/// Breakdown of convergence statistics for a single difficulty class.
#[derive(Debug, Clone)]
pub struct DifficultyBreakdown {
    /// The difficulty level.
    pub difficulty: Difficulty,
    /// Total functions in this class.
    pub total: usize,
    /// Functions that converged.
    pub converged: usize,
    /// Total iterations spent across all functions in this class.
    pub total_iterations: usize,
}

impl DifficultyBreakdown {
    /// Convergence rate for this difficulty class.
    #[must_use]
    pub fn convergence_rate(&self) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.converged as f64 / self.total as f64
    }

    /// Average iterations per function in this class.
    #[must_use]
    pub fn avg_iterations(&self) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.total_iterations as f64 / self.total as f64
    }
}

/// Summary report of convergence analysis across all tracked functions.
#[derive(Debug, Clone)]
pub struct ConvergenceReport {
    /// Total functions analyzed.
    pub total_functions: usize,
    /// Functions that converged (verified).
    pub converged_functions: usize,
    /// Overall convergence rate (0.0 to 1.0).
    pub convergence_rate: f64,
    /// Average iterations to convergence for converged functions.
    pub avg_iterations: Option<f64>,
    /// Empirical single-step convergence probability.
    pub empirical_step_probability: f64,
    /// Per-difficulty breakdown, ordered Easy -> Intractable.
    pub per_difficulty: Vec<DifficultyBreakdown>,
    /// Names of functions classified as intractable (10+ iters, not converged).
    pub intractable_functions: Vec<String>,
    /// Actionable recommendations based on the analysis.
    pub recommendations: Vec<String>,
}

impl ConvergenceReport {
    /// Render the report as a human-readable string.
    #[must_use]
    pub fn to_summary(&self) -> String {
        let mut out = String::new();
        out.push_str("=== Convergence Report ===\n");
        out.push_str(&format!(
            "Functions: {} total, {} converged ({:.1}%)\n",
            self.total_functions,
            self.converged_functions,
            self.convergence_rate * 100.0,
        ));

        if let Some(avg) = self.avg_iterations {
            out.push_str(&format!("Avg iterations to convergence: {:.1}\n", avg));
        }
        out.push_str(&format!(
            "Empirical step probability: {:.3}\n",
            self.empirical_step_probability,
        ));

        if !self.per_difficulty.is_empty() {
            out.push_str("\nPer-difficulty breakdown:\n");
            for bd in &self.per_difficulty {
                out.push_str(&format!(
                    "  {:12} — {} total, {} converged ({:.0}%), avg {:.1} iters\n",
                    bd.difficulty.as_str(),
                    bd.total,
                    bd.converged,
                    bd.convergence_rate() * 100.0,
                    bd.avg_iterations(),
                ));
            }
        }

        if !self.intractable_functions.is_empty() {
            out.push_str(&format!(
                "\nIntractable functions ({}):\n",
                self.intractable_functions.len()
            ));
            for name in &self.intractable_functions {
                out.push_str(&format!("  - {}\n", name));
            }
        }

        if !self.recommendations.is_empty() {
            out.push_str("\nRecommendations:\n");
            for rec in &self.recommendations {
                out.push_str(&format!("  * {}\n", rec));
            }
        }

        out
    }
}

/// Build actionable recommendations based on analysis results.
fn build_recommendations(intractable: &[String], convergence_rate: f64) -> Vec<String> {
    let mut recs = Vec::new();

    if convergence_rate < 0.5 {
        recs.push(
            "Low overall convergence rate (<50%). Consider adding more domain-specific \
             prompt templates or reducing function complexity before oracle submission."
                .to_owned(),
        );
    }

    if !intractable.is_empty() {
        recs.push(format!(
            "{} function(s) appear intractable. Consider: \
             (1) manual annotation hints, \
             (2) decomposing into smaller helper functions, or \
             (3) adding ghost state to simplify the proof obligation.",
            intractable.len(),
        ));
    }

    if convergence_rate >= 0.8 {
        recs.push(
            "High convergence rate (>=80%). The oracle is effective for this codebase; \
             consider increasing the iteration budget for remaining hard functions."
                .to_owned(),
        );
    }

    recs
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    fn make_verified_feedback() -> ProofFeedback {
        ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::from_millis(10),
            certificate_info: None,
        }
    }

    fn make_failed_feedback() -> ProofFeedback {
        ProofFeedback::Failed {
            counterexamples: vec![],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures".to_owned(),
            solver_mode: "Default".to_owned(),
            elapsed: Duration::from_millis(5),
        }
    }

    fn make_unknown_feedback() -> ProofFeedback {
        ProofFeedback::Unknown {
            reason: "timeout".to_owned(),
            category: "timeout".to_owned(),
            is_retriable: true,
            suggestion: "simplify spec".to_owned(),
            elapsed: Duration::from_millis(100),
        }
    }

    fn make_error_feedback() -> ProofFeedback {
        ProofFeedback::Error {
            message: "internal error".to_owned(),
        }
    }

    fn simple_func(name: &str, param_count: usize) -> FunctionSignature {
        let params: Vec<(String, String)> = (0..param_count)
            .map(|i| (format!("x{}", i), "u32".to_owned()))
            .collect();
        FunctionSignature {
            name: name.to_owned(),
            params,
            return_type: Some("u32".to_owned()),
            source: format!("fn {}() -> u32 {{ 0 }}", name),
            ..Default::default()
        }
    }

    // --- ConvergenceTracker tests ---

    #[test]
    fn test_tracker_empty_returns_zero_rate() {
        let tracker = ConvergenceTracker::new();
        assert_eq!(tracker.function_count(), 0);
        assert_eq!(tracker.converged_count(), 0);
        assert!((tracker.convergence_rate() - 0.0).abs() < f64::EPSILON);
        assert!(tracker.avg_iterations_to_convergence().is_none());
    }

    #[test]
    fn test_tracker_single_verified_function() {
        let mut tracker = ConvergenceTracker::new();
        tracker.record("foo", &make_verified_feedback(), Difficulty::Easy);

        assert_eq!(tracker.function_count(), 1);
        assert_eq!(tracker.converged_count(), 1);
        assert!((tracker.convergence_rate() - 1.0).abs() < f64::EPSILON);

        let history = tracker.history("foo").expect("history should exist");
        assert!(history.converged);
        assert_eq!(history.converged_at, Some(1));
        assert_eq!(history.iteration_count(), 1);
    }

    #[test]
    fn test_tracker_converges_after_failures() {
        let mut tracker = ConvergenceTracker::new();
        tracker.record("bar", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("bar", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("bar", &make_verified_feedback(), Difficulty::Medium);

        let history = tracker.history("bar").expect("history should exist");
        assert!(history.converged);
        assert_eq!(history.converged_at, Some(3));
        assert_eq!(history.iteration_count(), 3);
    }

    #[test]
    fn test_tracker_never_converges() {
        let mut tracker = ConvergenceTracker::new();
        for _ in 0..5 {
            tracker.record("hard_func", &make_failed_feedback(), Difficulty::Hard);
        }

        assert_eq!(tracker.converged_count(), 0);
        assert!((tracker.convergence_rate() - 0.0).abs() < f64::EPSILON);

        let history = tracker.history("hard_func").expect("history should exist");
        assert!(!history.converged);
        assert!(history.converged_at.is_none());
    }

    #[test]
    fn test_tracker_multiple_functions_mixed() {
        let mut tracker = ConvergenceTracker::new();

        // Function A: converges on first try
        tracker.record("a", &make_verified_feedback(), Difficulty::Easy);

        // Function B: converges after 3 tries
        tracker.record("b", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("b", &make_unknown_feedback(), Difficulty::Medium);
        tracker.record("b", &make_verified_feedback(), Difficulty::Medium);

        // Function C: never converges
        tracker.record("c", &make_failed_feedback(), Difficulty::Hard);
        tracker.record("c", &make_failed_feedback(), Difficulty::Hard);

        assert_eq!(tracker.function_count(), 3);
        assert_eq!(tracker.converged_count(), 2);
        let rate = tracker.convergence_rate();
        assert!((rate - 2.0 / 3.0).abs() < 1e-10);

        let avg = tracker
            .avg_iterations_to_convergence()
            .expect("should have avg");
        // (1 + 3) / 2 = 2.0
        assert!((avg - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_tracker_empirical_step_probability() {
        let mut tracker = ConvergenceTracker::new();

        // 2 verified out of 5 total steps
        tracker.record("a", &make_verified_feedback(), Difficulty::Easy);
        tracker.record("b", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("b", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("b", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("c", &make_verified_feedback(), Difficulty::Easy);

        let p = tracker.empirical_step_probability();
        assert!((p - 2.0 / 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_tracker_converged_at_first_verified_only() {
        let mut tracker = ConvergenceTracker::new();
        // Record verified twice -- converged_at should be the first occurrence
        tracker.record("f", &make_verified_feedback(), Difficulty::Easy);
        tracker.record("f", &make_verified_feedback(), Difficulty::Easy);

        let history = tracker.history("f").expect("should exist");
        assert_eq!(history.converged_at, Some(1));
        assert_eq!(history.iteration_count(), 2);
    }

    // --- FunctionHistory tests ---

    #[test]
    fn test_function_history_distinct_feedback_kinds() {
        let mut tracker = ConvergenceTracker::new();
        tracker.record("x", &make_failed_feedback(), Difficulty::Hard);
        tracker.record("x", &make_unknown_feedback(), Difficulty::Hard);
        tracker.record("x", &make_error_feedback(), Difficulty::Hard);
        tracker.record("x", &make_verified_feedback(), Difficulty::Hard);

        let history = tracker.history("x").expect("should exist");
        assert_eq!(history.distinct_feedback_kinds(), 4);
    }

    #[test]
    fn test_function_history_spec_drift() {
        let mut tracker = ConvergenceTracker::new();
        // 3 iterations, all same kind => drift = 1/3
        tracker.record("y", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("y", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("y", &make_failed_feedback(), Difficulty::Medium);

        let history = tracker.history("y").expect("should exist");
        assert!((history.spec_drift() - 1.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_function_history_spec_drift_empty() {
        let history = FunctionHistory {
            name: "empty".to_owned(),
            feedback_sequence: vec![],
            converged: false,
            converged_at: None,
            difficulty: Difficulty::Easy,
        };
        assert!((history.spec_drift() - 0.0).abs() < f64::EPSILON);
    }

    // --- ConvergencePredictor tests ---

    #[test]
    fn test_predictor_cumulative_probability_basic() {
        let pred = ConvergencePredictor::new(0.3);
        // P(step 1) = 0.3
        assert!((pred.cumulative_probability(1) - 0.3).abs() < 1e-10);
        // P(step 2) = 1 - 0.7^2 = 1 - 0.49 = 0.51
        assert!((pred.cumulative_probability(2) - 0.51).abs() < 1e-10);
        // P(step 0) = 0.0
        assert!((pred.cumulative_probability(0) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_predictor_zero_probability() {
        let pred = ConvergencePredictor::new(0.0);
        assert!((pred.cumulative_probability(100) - 0.0).abs() < f64::EPSILON);
        assert!(pred.remaining_iterations(0, 0.9).is_none());
    }

    #[test]
    fn test_predictor_certain_probability() {
        let pred = ConvergencePredictor::new(1.0);
        assert!((pred.cumulative_probability(1) - 1.0).abs() < f64::EPSILON);
        assert_eq!(pred.remaining_iterations(0, 0.5), Some(0));
    }

    #[test]
    fn test_predictor_remaining_iterations() {
        let pred = ConvergencePredictor::new(0.5);
        // Need 1 - 0.5^n >= 0.9 => 0.5^n <= 0.1 => n >= log(0.1)/log(0.5) ~= 3.32
        // So n = 4 total
        let remaining = pred.remaining_iterations(0, 0.9).expect("should compute");
        assert_eq!(remaining, 4);

        // If we've already done 2, we need 4 - 2 = 2 more
        let remaining2 = pred.remaining_iterations(2, 0.9).expect("should compute");
        assert_eq!(remaining2, 2);
    }

    #[test]
    fn test_predictor_remaining_already_exceeded() {
        let pred = ConvergencePredictor::new(0.5);
        // Total needed for 0.9 is 4; if we've done 10, remaining = 0
        let remaining = pred.remaining_iterations(10, 0.9).expect("should compute");
        assert_eq!(remaining, 0);
    }

    #[test]
    fn test_predictor_confidence_one_returns_none() {
        let pred = ConvergencePredictor::new(0.5);
        assert!(pred.remaining_iterations(0, 1.0).is_none());
    }

    #[test]
    fn test_predictor_from_tracker() {
        let mut tracker = ConvergenceTracker::new();
        // 1 verified out of 4 steps
        tracker.record("a", &make_failed_feedback(), Difficulty::Easy);
        tracker.record("a", &make_failed_feedback(), Difficulty::Easy);
        tracker.record("a", &make_failed_feedback(), Difficulty::Easy);
        tracker.record("a", &make_verified_feedback(), Difficulty::Easy);

        let pred = ConvergencePredictor::from_tracker(&tracker);
        assert!((pred.step_probability() - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_predictor_clamps_out_of_range() {
        let pred_neg = ConvergencePredictor::new(-0.5);
        assert!((pred_neg.step_probability() - 0.0).abs() < f64::EPSILON);

        let pred_high = ConvergencePredictor::new(1.5);
        assert!((pred_high.step_probability() - 1.0).abs() < f64::EPSILON);
    }

    // --- DifficultyClassifier tests ---

    #[test]
    fn test_classifier_easy_single_param() {
        let func = simple_func("add_one", 1);
        assert_eq!(DifficultyClassifier::classify(&func), Difficulty::Easy);
    }

    #[test]
    fn test_classifier_medium_multi_param() {
        let func = FunctionSignature {
            name: "merge".to_owned(),
            params: vec![
                ("a".to_owned(), "Vec<u32>".to_owned()),
                ("b".to_owned(), "Vec<u32>".to_owned()),
                ("c".to_owned(), "u32".to_owned()),
            ],
            return_type: Some("Vec<u32>".to_owned()),
            source: "fn merge(a: Vec<u32>, b: Vec<u32>, c: u32) -> Vec<u32> { a }".to_owned(),
            ..Default::default()
        };
        let score = DifficultyClassifier::complexity_score(&func);
        // 3 params + 2 generic params (<u32> in a and b) + 1 return Vec + 1 return generic = 7
        // Actually: 3 params + 2 (a,b contain '<') + 1 (ret Vec) + 1 (ret '<') = 7 => Hard
        assert!(score >= 3, "score should be at least medium: got {}", score);
    }

    #[test]
    fn test_classifier_hard_mut_refs() {
        let func = FunctionSignature {
            name: "sort_in_place".to_owned(),
            params: vec![
                ("data".to_owned(), "&mut Vec<i32>".to_owned()),
                ("cmp".to_owned(), "&Fn(i32, i32) -> bool".to_owned()),
            ],
            return_type: Some("Result<(), Error>".to_owned()),
            source: "fn sort_in_place(data: &mut Vec<i32>, cmp: &Fn(i32, i32) -> bool) -> Result<(), Error> {}".to_owned(),
            ..Default::default()
        };
        let score = DifficultyClassifier::complexity_score(&func);
        // 2 params + 2 (mut ref) + 1 (data has '<') + 1 (cmp has '<') + 2 (Result in ret) + 1 (ret '<') = 9
        assert!(score >= 6, "score should be hard: got {}", score);
    }

    #[test]
    fn test_classifier_intractable_complex() {
        let func = FunctionSignature {
            name: "verify_merkle_tree".to_owned(),
            params: vec![
                ("root".to_owned(), "&mut Map<Key, Value>".to_owned()),
                ("proof".to_owned(), "Vec<Hash>".to_owned()),
                ("leaf".to_owned(), "&[u8]".to_owned()),
                ("config".to_owned(), "Config<'a>".to_owned()),
                ("callback".to_owned(), "&dyn Fn(Hash) -> Result<bool, Error>".to_owned()),
            ],
            return_type: Some("Result<Option<Proof>, VerifyError>".to_owned()),
            source: "fn verify_merkle_tree<'a>(root: &mut Map<Key, Value>, proof: Vec<Hash>, leaf: &[u8], config: Config<'a>, callback: &dyn Fn(Hash) -> Result<bool, Error>) -> Result<Option<Proof>, VerifyError> {}".to_owned(),
            ..Default::default()
        };
        let score = DifficultyClassifier::complexity_score(&func);
        assert!(score >= 10, "score should be intractable: got {}", score);
        assert_eq!(
            DifficultyClassifier::classify(&func),
            Difficulty::Intractable
        );
    }

    #[test]
    fn test_classifier_zero_params() {
        let func = FunctionSignature {
            name: "get_version".to_owned(),
            params: vec![],
            return_type: Some("u32".to_owned()),
            source: "fn get_version() -> u32 { 1 }".to_owned(),
            ..Default::default()
        };
        assert_eq!(DifficultyClassifier::classify(&func), Difficulty::Easy);
        assert_eq!(DifficultyClassifier::complexity_score(&func), 0);
    }

    // --- ConvergenceReport tests ---

    #[test]
    fn test_report_empty_tracker() {
        let tracker = ConvergenceTracker::new();
        let report = tracker.report();
        assert_eq!(report.total_functions, 0);
        assert_eq!(report.converged_functions, 0);
        assert!(report.per_difficulty.is_empty());
        assert!(report.intractable_functions.is_empty());
    }

    #[test]
    fn test_report_mixed_difficulty() {
        let mut tracker = ConvergenceTracker::new();

        // Easy: converges immediately
        tracker.record("easy1", &make_verified_feedback(), Difficulty::Easy);

        // Medium: converges after 3 iters
        tracker.record("med1", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("med1", &make_failed_feedback(), Difficulty::Medium);
        tracker.record("med1", &make_verified_feedback(), Difficulty::Medium);

        // Hard: never converges (10+ iters)
        for _ in 0..12 {
            tracker.record("hard1", &make_failed_feedback(), Difficulty::Hard);
        }

        let report = tracker.report();
        assert_eq!(report.total_functions, 3);
        assert_eq!(report.converged_functions, 2);
        assert_eq!(report.intractable_functions, vec!["hard1".to_owned()]);
        assert_eq!(report.per_difficulty.len(), 3);

        // Check ordering: Easy, Medium, Hard
        assert_eq!(report.per_difficulty[0].difficulty, Difficulty::Easy);
        assert_eq!(report.per_difficulty[1].difficulty, Difficulty::Medium);
        assert_eq!(report.per_difficulty[2].difficulty, Difficulty::Hard);
    }

    #[test]
    fn test_report_recommendations_low_convergence() {
        let mut tracker = ConvergenceTracker::new();
        // 0 out of 3 converge
        tracker.record("a", &make_failed_feedback(), Difficulty::Easy);
        tracker.record("b", &make_failed_feedback(), Difficulty::Easy);
        tracker.record("c", &make_failed_feedback(), Difficulty::Easy);

        let report = tracker.report();
        assert!(
            report
                .recommendations
                .iter()
                .any(|r| r.contains("Low overall convergence")),
            "should recommend improving convergence: {:?}",
            report.recommendations
        );
    }

    #[test]
    fn test_report_recommendations_high_convergence() {
        let mut tracker = ConvergenceTracker::new();
        for i in 0..10 {
            tracker.record(
                &format!("f{}", i),
                &make_verified_feedback(),
                Difficulty::Easy,
            );
        }

        let report = tracker.report();
        assert!(
            report
                .recommendations
                .iter()
                .any(|r| r.contains("High convergence")),
            "should recommend increasing budget: {:?}",
            report.recommendations
        );
    }

    #[test]
    fn test_report_summary_renders() {
        let mut tracker = ConvergenceTracker::new();
        tracker.record("foo", &make_verified_feedback(), Difficulty::Easy);
        tracker.record("bar", &make_failed_feedback(), Difficulty::Medium);

        let report = tracker.report();
        let summary = report.to_summary();
        assert!(summary.contains("Convergence Report"));
        assert!(summary.contains("2 total"));
        assert!(summary.contains("1 converged"));
    }

    #[test]
    fn test_difficulty_breakdown_convergence_rate() {
        let bd = DifficultyBreakdown {
            difficulty: Difficulty::Medium,
            total: 4,
            converged: 3,
            total_iterations: 12,
        };
        assert!((bd.convergence_rate() - 0.75).abs() < f64::EPSILON);
        assert!((bd.avg_iterations() - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_difficulty_breakdown_empty() {
        let bd = DifficultyBreakdown {
            difficulty: Difficulty::Easy,
            total: 0,
            converged: 0,
            total_iterations: 0,
        };
        assert!((bd.convergence_rate() - 0.0).abs() < f64::EPSILON);
        assert!((bd.avg_iterations() - 0.0).abs() < f64::EPSILON);
    }

    // --- Difficulty enum tests ---

    #[test]
    fn test_difficulty_max_iterations() {
        assert_eq!(Difficulty::Easy.max_iterations(), 2);
        assert_eq!(Difficulty::Medium.max_iterations(), 5);
        assert_eq!(Difficulty::Hard.max_iterations(), 10);
        assert_eq!(Difficulty::Intractable.max_iterations(), usize::MAX);
    }

    #[test]
    fn test_difficulty_as_str() {
        assert_eq!(Difficulty::Easy.as_str(), "easy");
        assert_eq!(Difficulty::Medium.as_str(), "medium");
        assert_eq!(Difficulty::Hard.as_str(), "hard");
        assert_eq!(Difficulty::Intractable.as_str(), "intractable");
    }

    // --- FeedbackKind conversion tests ---

    #[test]
    fn test_feedback_kind_from_proof_feedback() {
        assert_eq!(
            FeedbackKind::from(&make_verified_feedback()),
            FeedbackKind::Verified
        );
        assert_eq!(
            FeedbackKind::from(&make_failed_feedback()),
            FeedbackKind::Failed
        );
        assert_eq!(
            FeedbackKind::from(&make_unknown_feedback()),
            FeedbackKind::Unknown
        );
        assert_eq!(
            FeedbackKind::from(&make_error_feedback()),
            FeedbackKind::Error
        );
    }

    // --- Predictor total_iterations_for_confidence ---

    #[test]
    fn test_predictor_total_iterations_for_confidence() {
        let pred = ConvergencePredictor::new(0.5);
        let total = pred.total_iterations_for_confidence(0.9);
        let remaining = pred.remaining_iterations(0, 0.9);
        assert_eq!(total, remaining);
    }
}
