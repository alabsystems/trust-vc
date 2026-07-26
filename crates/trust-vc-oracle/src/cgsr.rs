// trust-vc-oracle — Counterexample-Guided Specification Refinement engine
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Implements the full CGSR loop: start with template-based candidate specs,
// verify each against the ay backend, collect counterexamples on failure,
// and iteratively refine (strengthen, weaken, split, or discard) until all
// specs are proven or the iteration budget is exhausted.

use crate::feedback::ProofFeedback;
use crate::mining::MinedSpec;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Strategy for how the CGSR engine responds to counterexamples.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum RefinementStrategy {
    /// Add preconditions that exclude the counterexample.
    Strengthen,
    /// Relax postconditions to accommodate the counterexample.
    Weaken,
    /// Split the spec into multiple disjoint specs.
    Split,
}

/// Configuration for the CGSR engine.
#[derive(Debug, Clone)]
pub struct CgsrConfig {
    /// Maximum refinement iterations before giving up.
    pub max_iterations: usize,
    /// Default refinement strategy.
    pub strategy: RefinementStrategy,
    /// Maximum counterexamples to collect before stopping.
    pub max_counterexamples: usize,
    /// Whether to emit progress to stderr.
    pub verbose: bool,
}

impl Default for CgsrConfig {
    fn default() -> Self {
        Self {
            max_iterations: 10,
            strategy: RefinementStrategy::Strengthen,
            max_counterexamples: 50,
            verbose: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Counterexample
// ---------------------------------------------------------------------------

/// A counterexample extracted from a failed verification attempt.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Counterexample {
    /// Variable name-value pairs from the ay model.
    pub variable_bindings: Vec<(String, String)>,
    /// Which clause (requires/ensures) was violated.
    pub violated_clause: String,
    /// The CGSR iteration that produced this counterexample.
    pub iteration: usize,
}

impl Counterexample {
    /// Construct a new `Counterexample`.
    #[must_use]
    pub fn new(
        variable_bindings: Vec<(String, String)>,
        violated_clause: String,
        iteration: usize,
    ) -> Self {
        Self {
            variable_bindings,
            violated_clause,
            iteration,
        }
    }

    /// Extract a `Counterexample` from `ProofFeedback::Failed`.
    ///
    /// Returns `None` if the feedback is not a failure.
    #[must_use]
    pub fn from_feedback(feedback: &ProofFeedback, iteration: usize) -> Option<Self> {
        match feedback {
            ProofFeedback::Failed {
                counterexamples,
                obligation_name,
                ..
            } => {
                let bindings = counterexamples
                    .iter()
                    .map(|cx| (cx.name.clone(), cx.value.clone()))
                    .collect();
                Some(Self {
                    variable_bindings: bindings,
                    violated_clause: obligation_name.clone(),
                    iteration,
                })
            }
            _ => None,
        }
    }

    /// Check whether this counterexample has a binding for `name`.
    #[must_use]
    pub fn has_binding(&self, name: &str) -> bool {
        self.variable_bindings.iter().any(|(n, _)| n == name)
    }

    /// Get the value for a variable name, if present.
    #[must_use]
    pub fn get_value(&self, name: &str) -> Option<&str> {
        self.variable_bindings
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v.as_str())
    }
}

// ---------------------------------------------------------------------------
// Refinement steps (audit trail)
// ---------------------------------------------------------------------------

/// A single refinement action applied during the CGSR loop.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum RefinementStep {
    /// Strengthen: add a precondition to exclude the counterexample.
    Strengthen {
        /// Index of the spec in the candidate list.
        spec_idx: usize,
        /// The precondition clause that was added.
        added_precondition: String,
    },

    /// Weaken: relax a postcondition to accommodate the counterexample.
    Weaken {
        /// Index of the spec in the candidate list.
        spec_idx: usize,
        /// The relaxed postcondition replacing the original.
        relaxed_postcondition: String,
    },

    /// Split: decompose one spec into multiple disjoint specs.
    Split {
        /// Index of the original spec.
        spec_idx: usize,
        /// The resulting specs after splitting.
        into: Vec<MinedSpec>,
    },

    /// Discard: remove a spec that cannot be refined further.
    Discard {
        /// Index of the spec that was removed.
        spec_idx: usize,
        /// Reason for discarding.
        reason: String,
    },
}

// ---------------------------------------------------------------------------
// CGSR result
// ---------------------------------------------------------------------------

/// Result of a complete CGSR session.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CgsrResult {
    /// Final set of verified specs.
    pub verified_specs: Vec<MinedSpec>,
    /// Specs that could not be verified within the budget.
    pub unverified_specs: Vec<MinedSpec>,
    /// Total iterations consumed.
    pub iterations_used: usize,
    /// Total counterexamples collected.
    pub counterexample_count: usize,
    /// Full audit trail of refinement steps.
    pub history: Vec<RefinementStep>,
}

impl CgsrResult {
    /// Whether all initial specs were verified (or refined to verified).
    #[must_use]
    pub fn all_verified(&self) -> bool {
        self.unverified_specs.is_empty() && !self.verified_specs.is_empty()
    }

    /// Total number of specs (verified + unverified).
    #[must_use]
    pub fn total_specs(&self) -> usize {
        self.verified_specs.len() + self.unverified_specs.len()
    }
}

// ---------------------------------------------------------------------------
// Verification adapter (injectable for testing)
// ---------------------------------------------------------------------------

/// Abstraction over the verification step so tests can inject a mock.
pub(crate) trait CgsrVerifyAdapter: Send + Sync {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback;
}

// ---------------------------------------------------------------------------
// CgsrEngine
// ---------------------------------------------------------------------------

/// The Counterexample-Guided Specification Refinement engine.
///
/// Drives the full refinement loop: verify candidate specs, collect
/// counterexamples on failure, apply refinement strategies, repeat.
pub struct CgsrEngine {
    config: CgsrConfig,
    specs: Vec<MinedSpec>,
    counterexamples: Vec<Counterexample>,
    history: Vec<RefinementStep>,
}

impl CgsrEngine {
    /// Create a new engine with the given config and initial candidate specs.
    #[must_use]
    pub fn new(config: CgsrConfig, initial_specs: Vec<MinedSpec>) -> Self {
        Self {
            config,
            specs: initial_specs,
            counterexamples: Vec::new(),
            history: Vec::new(),
        }
    }

    /// Read-only access to the current spec candidates.
    #[must_use]
    pub fn specs(&self) -> &[MinedSpec] {
        &self.specs
    }

    /// Read-only access to collected counterexamples.
    #[must_use]
    pub fn counterexamples(&self) -> &[Counterexample] {
        &self.counterexamples
    }

    /// Read-only access to the refinement audit trail.
    #[must_use]
    pub fn history(&self) -> &[RefinementStep] {
        &self.history
    }

    /// Current configuration.
    #[must_use]
    pub fn config(&self) -> &CgsrConfig {
        &self.config
    }

    // -----------------------------------------------------------------------
    // Refinement from a single counterexample
    // -----------------------------------------------------------------------

    /// Refine specs in response to a single counterexample.
    ///
    /// Identifies which spec the counterexample violates (by matching
    /// `violated_clause` against ensures clauses), then applies the
    /// configured refinement strategy.
    ///
    /// Returns the indices of specs that were modified.
    pub fn refine_from_counterexample(&mut self, cex: &Counterexample) -> Vec<usize> {
        let violated_indices = find_violated_specs(&self.specs, cex);

        if violated_indices.is_empty() {
            return Vec::new();
        }

        let strategy = choose_strategy(&self.config, cex, &violated_indices);
        let mut modified = Vec::new();

        for &idx in &violated_indices {
            if idx >= self.specs.len() {
                continue;
            }

            match strategy {
                RefinementStrategy::Strengthen => {
                    let precondition = synthesize_precondition(cex);
                    self.specs[idx].requires.push(precondition.clone());
                    self.history.push(RefinementStep::Strengthen {
                        spec_idx: idx,
                        added_precondition: precondition,
                    });
                    modified.push(idx);
                }

                RefinementStrategy::Weaken => {
                    if let Some(relaxed) = weaken_postcondition(&self.specs[idx].ensures, cex) {
                        let old_len = self.specs[idx].ensures.len();
                        self.specs[idx].ensures = relaxed.clone();
                        let relaxed_desc = if self.specs[idx].ensures.len() < old_len {
                            "removed violated clause".to_string()
                        } else {
                            self.specs[idx].ensures.last().cloned().unwrap_or_default()
                        };
                        self.history.push(RefinementStep::Weaken {
                            spec_idx: idx,
                            relaxed_postcondition: relaxed_desc,
                        });
                        modified.push(idx);
                    }
                }

                RefinementStrategy::Split => {
                    let (positive, negative) = split_spec(&self.specs[idx], cex);
                    let into = vec![positive.clone(), negative.clone()];
                    self.history.push(RefinementStep::Split {
                        spec_idx: idx,
                        into: into.clone(),
                    });
                    // Replace the original with the positive half; append the
                    // negative half.
                    self.specs[idx] = positive;
                    self.specs.push(negative);
                    modified.push(idx);
                    modified.push(self.specs.len() - 1);
                }
            }
        }

        self.counterexamples.push(cex.clone());
        modified
    }

    // -----------------------------------------------------------------------
    // Full CGSR loop
    // -----------------------------------------------------------------------

    /// Run the full CGSR loop with an injectable verifier.
    ///
    /// For each iteration:
    /// 1. Verify each unverified spec.
    /// 2. Collect counterexamples.
    /// 3. Refine failing specs.
    /// 4. Stop when all verified or budget exhausted.
    pub(crate) fn run_loop(&mut self, adapter: &dyn CgsrVerifyAdapter) -> CgsrResult {
        let mut iteration = 0;

        while iteration < self.config.max_iterations
            && self.counterexamples.len() < self.config.max_counterexamples
        {
            let unverified_indices: Vec<usize> = self
                .specs
                .iter()
                .enumerate()
                .filter(|(_, s)| !s.verified)
                .map(|(i, _)| i)
                .collect();

            if unverified_indices.is_empty() {
                break;
            }

            let mut any_refined = false;

            for idx in unverified_indices {
                let spec = &self.specs[idx];
                let feedback = adapter.verify(
                    &spec.function_name,
                    &[], // variables inferred by verifier
                    &spec.requires,
                    &spec.ensures,
                );

                if self.config.verbose {
                    eprintln!(
                        "[cgsr] iter={} spec={} template={} => {}",
                        iteration,
                        spec.function_name,
                        spec.template_name,
                        feedback_tag(&feedback),
                    );
                }

                if feedback.is_verified() {
                    self.specs[idx].verified = true;
                    self.specs[idx].iterations = iteration;
                } else if feedback.is_failed() {
                    let cex = Counterexample::from_feedback(&feedback, iteration);
                    if let Some(cex) = cex {
                        let modified = self.refine_from_counterexample(&cex);
                        if !modified.is_empty() {
                            any_refined = true;
                        }
                    }
                } else {
                    // Unknown or Error: discard the spec.
                    let reason = match &feedback {
                        ProofFeedback::Unknown { reason, .. } => {
                            format!("solver unknown: {}", reason)
                        }
                        ProofFeedback::Error { message } => {
                            format!("verification error: {}", message)
                        }
                        _ => "non-actionable feedback".to_string(),
                    };
                    self.history.push(RefinementStep::Discard {
                        spec_idx: idx,
                        reason: reason.clone(),
                    });
                    // Mark as verified=false but remove from active set by
                    // clearing ensures (empty spec = nothing to verify).
                    self.specs[idx].ensures.clear();
                }
            }

            iteration += 1;

            if !any_refined
                && self
                    .specs
                    .iter()
                    .all(|s| s.verified || s.ensures.is_empty())
            {
                break;
            }
        }

        let (verified, unverified): (Vec<_>, Vec<_>) = self
            .specs
            .iter()
            .filter(|s| !s.ensures.is_empty())
            .cloned()
            .partition(|s| s.verified);

        CgsrResult {
            verified_specs: verified,
            unverified_specs: unverified,
            iterations_used: iteration,
            counterexample_count: self.counterexamples.len(),
            history: self.history.clone(),
        }
    }
}

/// Public convenience function: run the full CGSR loop.
///
/// Creates a `CgsrEngine`, injects a real verifier, and returns the result.
#[must_use]
pub fn run_cgsr_loop(config: &CgsrConfig, initial_specs: Vec<MinedSpec>) -> CgsrResult {
    let mut engine = CgsrEngine::new(config.clone(), initial_specs);
    engine.run_loop(&RealCgsrVerifier)
}

// ---------------------------------------------------------------------------
// Real verifier adapter
// ---------------------------------------------------------------------------

struct RealCgsrVerifier;

impl CgsrVerifyAdapter for RealCgsrVerifier {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback {
        crate::verify::verify_with_annotations(function_name, variables, requires, ensures)
    }
}

// ---------------------------------------------------------------------------
// Refinement helpers
// ---------------------------------------------------------------------------

/// Find which specs are violated by a counterexample.
///
/// Matches the counterexample's `violated_clause` against each spec's
/// ensures clauses. If the violated clause is a substring of any ensures
/// clause, or if the obligation name matches the template name, the spec
/// is considered violated.
fn find_violated_specs(specs: &[MinedSpec], cex: &Counterexample) -> Vec<usize> {
    let mut indices = Vec::new();
    let clause = &cex.violated_clause;

    for (i, spec) in specs.iter().enumerate() {
        if spec.verified || spec.ensures.is_empty() {
            continue;
        }

        // Direct match: the violated clause is one of the ensures.
        let direct_match = spec
            .ensures
            .iter()
            .any(|e| e == clause || clause.contains(e.as_str()));

        // Obligation-name match: the obligation contains the template name.
        let name_match =
            clause.contains(&spec.template_name) || clause.contains(&spec.function_name);

        // Fallback: if the spec is unverified, it is a candidate.
        let fallback = !spec.verified;

        if direct_match || name_match || fallback {
            indices.push(i);
        }
    }

    indices
}

/// Choose the best refinement strategy given the counterexample.
///
/// Heuristic:
/// - If the counterexample has bindings that look like edge cases (zero,
///   negative, boundary values), prefer Strengthen (add precondition).
/// - If multiple specs are violated, prefer Split.
/// - Otherwise, use the configured default.
fn choose_strategy(
    config: &CgsrConfig,
    cex: &Counterexample,
    violated: &[usize],
) -> RefinementStrategy {
    // Multiple violations → split.
    if violated.len() > 1 {
        return RefinementStrategy::Split;
    }

    // Edge-case heuristic: if any value is 0, negative, or a boundary,
    // strengthen by adding a precondition.
    let is_edge_case = cex.variable_bindings.iter().any(|(_, v)| {
        v == "0"
            || v.starts_with('-')
            || v == "2147483647"
            || v == "-2147483648"
            || v == "4294967295"
            || v == "255"
            || v == "127"
            || v == "-128"
    });

    if is_edge_case {
        return RefinementStrategy::Strengthen;
    }

    config.strategy
}

/// Synthesize a precondition that excludes the given counterexample.
///
/// Generates a conjunction of `var != value` clauses for every binding.
fn synthesize_precondition(cex: &Counterexample) -> String {
    if cex.variable_bindings.len() == 1 {
        let (name, value) = &cex.variable_bindings[0];
        // Try to parse as integer for nicer output.
        if let Ok(v) = value.parse::<i128>() {
            if v < 0 {
                return format!("{} >= 0", name);
            }
            return format!("{} != {}", name, value);
        }
        return format!("{} != {}", name, value);
    }

    let clauses: Vec<String> = cex
        .variable_bindings
        .iter()
        .map(|(name, value)| format!("{} != {}", name, value))
        .collect();
    clauses.join(" && ")
}

/// Weaken postconditions to accommodate a counterexample.
///
/// Removes the violated clause from ensures, or if the clause is a strict
/// inequality, relaxes it to a non-strict one.
fn weaken_postcondition(ensures: &[String], cex: &Counterexample) -> Option<Vec<String>> {
    let clause = &cex.violated_clause;
    let mut result: Vec<String> = ensures.to_vec();

    // Try to relax a strict inequality to non-strict.
    for ens in &mut result {
        if ens.contains(clause.as_str()) || clause.contains(ens.as_str()) {
            // Relax > to >=, < to <=.
            if ens.contains(" > ") && !ens.contains(" >= ") {
                *ens = ens.replace(" > ", " >= ");
                return Some(result);
            }
            if ens.contains(" < ") && !ens.contains(" <= ") {
                *ens = ens.replace(" < ", " <= ");
                return Some(result);
            }
        }
    }

    // Fallback: remove the violated clause entirely.
    let before = result.len();
    result.retain(|e| !clause.contains(e.as_str()) && !e.contains(clause.as_str()));
    if result.len() < before {
        return Some(result);
    }

    // If we could not identify which clause to weaken, remove the last one.
    if !result.is_empty() {
        result.pop();
        return Some(result);
    }

    None
}

/// Split a spec into two disjoint specs around a counterexample.
///
/// The positive half adds a precondition excluding the counterexample.
/// The negative half adds a precondition matching the counterexample and
/// drops the violated ensures clause.
fn split_spec(spec: &MinedSpec, cex: &Counterexample) -> (MinedSpec, MinedSpec) {
    let precondition = synthesize_precondition(cex);
    let negated = negate_precondition(&precondition);

    let positive = MinedSpec::new(
        spec.function_name.clone(),
        format!("{}_pos", spec.template_name),
        {
            let mut r = spec.requires.clone();
            r.push(precondition);
            r
        },
        spec.ensures.clone(),
        false,
        0,
    );

    let negative = MinedSpec::new(
        spec.function_name.clone(),
        format!("{}_neg", spec.template_name),
        {
            let mut r = spec.requires.clone();
            r.push(negated);
            r
        },
        spec.ensures
            .iter()
            .filter(|e| !cex.violated_clause.contains(e.as_str()))
            .cloned()
            .collect(),
        false,
        0,
    );

    (positive, negative)
}

/// Simple precondition negation (best-effort for common patterns).
fn negate_precondition(precondition: &str) -> String {
    if let Some(rest) = precondition.strip_prefix('!') {
        return rest.to_string();
    }
    if precondition.contains(" != ") {
        return precondition.replace(" != ", " == ");
    }
    if precondition.contains(" >= ") {
        return precondition.replace(" >= ", " < ");
    }
    if precondition.contains(" <= ") {
        return precondition.replace(" <= ", " > ");
    }
    if precondition.contains(" > ") {
        return precondition.replace(" > ", " <= ");
    }
    if precondition.contains(" < ") {
        return precondition.replace(" < ", " >= ");
    }
    if precondition.contains(" == ") {
        return precondition.replace(" == ", " != ");
    }
    format!("!({})", precondition)
}

/// Short tag for feedback variant (logging).
fn feedback_tag(feedback: &ProofFeedback) -> &'static str {
    match feedback {
        ProofFeedback::Verified { .. } => "VERIFIED",
        ProofFeedback::Failed { .. } => "FAILED",
        ProofFeedback::Unknown { .. } => "UNKNOWN",
        ProofFeedback::Error { .. } => "ERROR",
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::feedback::{CounterexampleField, FailureLocalization};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    // -----------------------------------------------------------------------
    // Mock verifier
    // -----------------------------------------------------------------------

    struct ScriptedCgsrVerifier {
        responses: Vec<ProofFeedback>,
        call_count: AtomicUsize,
    }

    impl ScriptedCgsrVerifier {
        fn new(responses: Vec<ProofFeedback>) -> Self {
            Self {
                responses,
                call_count: AtomicUsize::new(0),
            }
        }
    }

    impl CgsrVerifyAdapter for ScriptedCgsrVerifier {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            let idx = self.call_count.fetch_add(1, Ordering::SeqCst);
            if idx < self.responses.len() {
                self.responses[idx].clone()
            } else {
                self.responses
                    .last()
                    .cloned()
                    .unwrap_or(ProofFeedback::Error {
                        message: "scripted verifier exhausted".to_string(),
                    })
            }
        }
    }

    struct AlwaysVerifiedAdapter;

    impl CgsrVerifyAdapter for AlwaysVerifiedAdapter {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            ProofFeedback::Verified {
                steps: vec![],
                elapsed: Duration::from_millis(1),
                certificate_info: None,
            }
        }
    }

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

    fn make_verified_feedback() -> ProofFeedback {
        ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::from_millis(1),
            certificate_info: None,
        }
    }

    fn make_failed_feedback(name: &str, value: &str, clause: &str) -> ProofFeedback {
        ProofFeedback::Failed {
            counterexamples: vec![CounterexampleField {
                name: name.to_string(),
                ty: "i32".to_string(),
                value: value.to_string(),
            }],
            localization: FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: clause.to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::from_millis(1),
        }
    }

    fn make_unknown_feedback() -> ProofFeedback {
        ProofFeedback::Unknown {
            reason: "timeout".to_string(),
            category: "Timeout".to_string(),
            is_retriable: false,
            suggestion: "simplify".to_string(),
            elapsed: Duration::from_millis(100),
        }
    }

    fn make_spec(func: &str, template: &str, requires: Vec<&str>, ensures: Vec<&str>) -> MinedSpec {
        MinedSpec::new(
            func.to_string(),
            template.to_string(),
            requires.into_iter().map(String::from).collect(),
            ensures.into_iter().map(String::from).collect(),
            false,
            0,
        )
    }

    fn default_config() -> CgsrConfig {
        CgsrConfig {
            max_iterations: 5,
            strategy: RefinementStrategy::Strengthen,
            max_counterexamples: 20,
            verbose: false,
        }
    }

    // -----------------------------------------------------------------------
    // Tests: Counterexample construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_counterexample_new_fields() {
        let cex = Counterexample::new(
            vec![("x".to_string(), "-5".to_string())],
            "result >= 0".to_string(),
            3,
        );
        assert_eq!(cex.variable_bindings.len(), 1);
        assert_eq!(cex.violated_clause, "result >= 0");
        assert_eq!(cex.iteration, 3);
    }

    #[test]
    fn test_counterexample_from_feedback_success() {
        let feedback = make_failed_feedback("x", "-3", "ensures_positive");
        let cex = Counterexample::from_feedback(&feedback, 2);
        assert!(cex.is_some());
        let cex = cex.unwrap();
        assert_eq!(
            cex.variable_bindings,
            vec![("x".to_string(), "-3".to_string())]
        );
        assert_eq!(cex.violated_clause, "ensures_positive");
        assert_eq!(cex.iteration, 2);
    }

    #[test]
    fn test_counterexample_from_feedback_not_failed() {
        let feedback = make_verified_feedback();
        assert!(Counterexample::from_feedback(&feedback, 0).is_none());

        let unknown = make_unknown_feedback();
        assert!(Counterexample::from_feedback(&unknown, 0).is_none());
    }

    #[test]
    fn test_counterexample_has_binding() {
        let cex = Counterexample::new(
            vec![
                ("x".to_string(), "10".to_string()),
                ("y".to_string(), "20".to_string()),
            ],
            "ensures".to_string(),
            0,
        );
        assert!(cex.has_binding("x"));
        assert!(cex.has_binding("y"));
        assert!(!cex.has_binding("z"));
    }

    #[test]
    fn test_counterexample_get_value() {
        let cex = Counterexample::new(
            vec![("result".to_string(), "-42".to_string())],
            "ensures".to_string(),
            0,
        );
        assert_eq!(cex.get_value("result"), Some("-42"));
        assert_eq!(cex.get_value("missing"), None);
    }

    // -----------------------------------------------------------------------
    // Tests: Refinement helpers
    // -----------------------------------------------------------------------

    #[test]
    fn test_synthesize_precondition_negative_value() {
        let cex = Counterexample::new(
            vec![("x".to_string(), "-5".to_string())],
            "ensures".to_string(),
            0,
        );
        let precond = synthesize_precondition(&cex);
        assert_eq!(precond, "x >= 0");
    }

    #[test]
    fn test_synthesize_precondition_specific_value() {
        let cex = Counterexample::new(
            vec![("x".to_string(), "42".to_string())],
            "ensures".to_string(),
            0,
        );
        let precond = synthesize_precondition(&cex);
        assert_eq!(precond, "x != 42");
    }

    #[test]
    fn test_synthesize_precondition_multiple_bindings() {
        let cex = Counterexample::new(
            vec![
                ("a".to_string(), "1".to_string()),
                ("b".to_string(), "2".to_string()),
            ],
            "ensures".to_string(),
            0,
        );
        let precond = synthesize_precondition(&cex);
        assert_eq!(precond, "a != 1 && b != 2");
    }

    #[test]
    fn test_negate_precondition_neq() {
        assert_eq!(negate_precondition("x != 5"), "x == 5");
    }

    #[test]
    fn test_negate_precondition_gte() {
        assert_eq!(negate_precondition("x >= 0"), "x < 0");
    }

    #[test]
    fn test_negate_precondition_gt() {
        assert_eq!(negate_precondition("x > 0"), "x <= 0");
    }

    #[test]
    fn test_negate_precondition_fallback() {
        assert_eq!(negate_precondition("is_valid(x)"), "!(is_valid(x))");
    }

    #[test]
    fn test_weaken_postcondition_strict_to_nonstrict() {
        let ensures = vec!["result > 0".to_string()];
        let cex = Counterexample::new(
            vec![("result".to_string(), "0".to_string())],
            "result > 0".to_string(),
            0,
        );
        let weakened = weaken_postcondition(&ensures, &cex);
        assert!(weakened.is_some());
        assert_eq!(weakened.unwrap(), vec!["result >= 0".to_string()]);
    }

    #[test]
    fn test_weaken_postcondition_removes_violated() {
        let ensures = vec!["result >= 0".to_string(), "result < 100".to_string()];
        let cex = Counterexample::new(
            vec![("result".to_string(), "200".to_string())],
            "result < 100".to_string(),
            0,
        );
        let weakened = weaken_postcondition(&ensures, &cex);
        assert!(weakened.is_some());
        let result = weakened.unwrap();
        // Should relax < to <=.
        assert_eq!(
            result,
            vec!["result >= 0".to_string(), "result <= 100".to_string()]
        );
    }

    // -----------------------------------------------------------------------
    // Tests: CgsrEngine — refine_from_counterexample
    // -----------------------------------------------------------------------

    #[test]
    fn test_refine_strengthen_adds_precondition() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        let mut engine = CgsrEngine::new(
            CgsrConfig {
                strategy: RefinementStrategy::Strengthen,
                ..default_config()
            },
            vec![spec],
        );

        let cex = Counterexample::new(
            vec![("x".to_string(), "-3".to_string())],
            "result >= 0".to_string(),
            0,
        );

        let modified = engine.refine_from_counterexample(&cex);
        assert!(!modified.is_empty());
        assert!(
            engine.specs()[0]
                .requires
                .iter()
                .any(|r| r.contains("x >= 0")),
            "should have added x >= 0 precondition, got: {:?}",
            engine.specs()[0].requires,
        );
        assert_eq!(engine.counterexamples().len(), 1);
        assert!(matches!(
            engine.history()[0],
            RefinementStep::Strengthen { .. }
        ));
    }

    #[test]
    fn test_refine_weaken_relaxes_postcondition() {
        let spec = make_spec("f", "range", vec![], vec!["result > 5"]);
        let mut engine = CgsrEngine::new(
            CgsrConfig {
                strategy: RefinementStrategy::Weaken,
                ..default_config()
            },
            vec![spec],
        );

        // Use a non-edge-case value (not 0/-1/MAX) to avoid the
        // choose_strategy heuristic overriding Weaken → Strengthen.
        let cex = Counterexample::new(
            vec![("result".to_string(), "3".to_string())],
            "result > 5".to_string(),
            0,
        );

        let modified = engine.refine_from_counterexample(&cex);
        assert!(!modified.is_empty());
        assert!(
            engine.specs()[0]
                .ensures
                .contains(&"result >= 5".to_string()),
            "should have relaxed > to >=, got: {:?}",
            engine.specs()[0].ensures,
        );
        assert!(matches!(engine.history()[0], RefinementStep::Weaken { .. }));
    }

    #[test]
    fn test_refine_split_produces_two_specs() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        let mut engine = CgsrEngine::new(
            CgsrConfig {
                strategy: RefinementStrategy::Split,
                ..default_config()
            },
            vec![spec],
        );

        let cex = Counterexample::new(
            vec![("x".to_string(), "5".to_string())],
            "result >= 0".to_string(),
            0,
        );

        let modified = engine.refine_from_counterexample(&cex);
        assert_eq!(engine.specs().len(), 2, "split should produce two specs");
        assert!(modified.len() >= 2);
        assert!(matches!(engine.history()[0], RefinementStep::Split { .. }));

        // One should be _pos, one _neg.
        let names: Vec<&str> = engine
            .specs()
            .iter()
            .map(|s| s.template_name.as_str())
            .collect();
        assert!(names.contains(&"range_pos"));
        assert!(names.contains(&"range_neg"));
    }

    #[test]
    fn test_refine_no_match_returns_empty() {
        // A spec that is already verified should not be refined.
        let mut spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        spec.verified = true;
        let mut engine = CgsrEngine::new(default_config(), vec![spec]);

        let cex = Counterexample::new(
            vec![("x".to_string(), "-1".to_string())],
            "result >= 0".to_string(),
            0,
        );

        let modified = engine.refine_from_counterexample(&cex);
        assert!(modified.is_empty(), "verified spec should not be refined");
    }

    // -----------------------------------------------------------------------
    // Tests: CgsrEngine — run_loop
    // -----------------------------------------------------------------------

    #[test]
    fn test_run_loop_all_verified_immediately() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        let mut engine = CgsrEngine::new(default_config(), vec![spec]);

        let result = engine.run_loop(&AlwaysVerifiedAdapter);

        assert!(result.all_verified());
        assert_eq!(result.verified_specs.len(), 1);
        assert_eq!(result.unverified_specs.len(), 0);
        assert_eq!(result.counterexample_count, 0);
        assert_eq!(result.iterations_used, 1);
    }

    #[test]
    fn test_run_loop_refines_then_verifies() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        let verifier = ScriptedCgsrVerifier::new(vec![
            make_failed_feedback("x", "-3", "result >= 0"),
            make_verified_feedback(),
        ]);

        let mut engine = CgsrEngine::new(default_config(), vec![spec]);
        let result = engine.run_loop(&verifier);

        assert_eq!(result.verified_specs.len(), 1);
        assert_eq!(result.counterexample_count, 1);
        assert!(result.iterations_used >= 1);
        assert!(!result.history.is_empty());
    }

    #[test]
    fn test_run_loop_budget_exhausted() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        let verifier = ScriptedCgsrVerifier::new(vec![
            make_failed_feedback("x", "-1", "result >= 0"),
            make_failed_feedback("x", "-2", "result >= 0"),
            make_failed_feedback("x", "-3", "result >= 0"),
        ]);

        let config = CgsrConfig {
            max_iterations: 2,
            ..default_config()
        };

        let mut engine = CgsrEngine::new(config, vec![spec]);
        let result = engine.run_loop(&verifier);

        assert!(!result.all_verified());
        assert_eq!(result.iterations_used, 2);
    }

    #[test]
    fn test_run_loop_unknown_discards_spec() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        let verifier = ScriptedCgsrVerifier::new(vec![make_unknown_feedback()]);

        let mut engine = CgsrEngine::new(default_config(), vec![spec]);
        let result = engine.run_loop(&verifier);

        // Discarded specs have empty ensures and are filtered out.
        assert_eq!(result.verified_specs.len(), 0);
        assert_eq!(result.unverified_specs.len(), 0);
        assert!(
            result
                .history
                .iter()
                .any(|s| matches!(s, RefinementStep::Discard { .. })),
            "should record a Discard step",
        );
    }

    #[test]
    fn test_run_loop_multiple_specs_partial_verification() {
        let specs = vec![
            make_spec("f", "range", vec![], vec!["result >= 0"]),
            make_spec("f", "non_negative", vec![], vec!["result > 100"]),
        ];

        // First spec verifies, second always fails.
        let verifier = ScriptedCgsrVerifier::new(vec![
            make_verified_feedback(),
            make_failed_feedback("result", "50", "result > 100"),
            // Second iteration for spec 2: still fails.
            make_failed_feedback("result", "30", "result > 100"),
            make_failed_feedback("result", "10", "result > 100"),
            make_failed_feedback("result", "5", "result > 100"),
            make_failed_feedback("result", "1", "result > 100"),
        ]);

        let mut engine = CgsrEngine::new(default_config(), specs);
        let result = engine.run_loop(&verifier);

        assert_eq!(result.verified_specs.len(), 1);
        assert_eq!(result.verified_specs[0].template_name, "range");
        assert!(!result.all_verified());
    }

    #[test]
    fn test_run_loop_empty_specs() {
        let mut engine = CgsrEngine::new(default_config(), vec![]);
        let result = engine.run_loop(&AlwaysVerifiedAdapter);

        assert_eq!(result.verified_specs.len(), 0);
        assert_eq!(result.unverified_specs.len(), 0);
        assert_eq!(result.iterations_used, 0);
        assert!(!result.all_verified());
    }

    #[test]
    fn test_run_loop_max_counterexamples_stops_early() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"]);

        // Generate many failures.
        let responses: Vec<ProofFeedback> = (0..30)
            .map(|i| make_failed_feedback("x", &format!("-{}", i + 1), "result >= 0"))
            .collect();

        let verifier = ScriptedCgsrVerifier::new(responses);
        let config = CgsrConfig {
            max_iterations: 100,
            max_counterexamples: 3,
            ..default_config()
        };

        let mut engine = CgsrEngine::new(config, vec![spec]);
        let result = engine.run_loop(&verifier);

        assert!(
            result.counterexample_count <= 3,
            "should stop at max_counterexamples, got {}",
            result.counterexample_count,
        );
    }

    // -----------------------------------------------------------------------
    // Tests: CgsrResult
    // -----------------------------------------------------------------------

    #[test]
    fn test_cgsr_result_all_verified() {
        let result = CgsrResult {
            verified_specs: vec![make_spec("f", "range", vec![], vec!["x >= 0"])],
            unverified_specs: vec![],
            iterations_used: 1,
            counterexample_count: 0,
            history: vec![],
        };
        assert!(result.all_verified());
        assert_eq!(result.total_specs(), 1);
    }

    #[test]
    fn test_cgsr_result_not_all_verified() {
        let result = CgsrResult {
            verified_specs: vec![],
            unverified_specs: vec![make_spec("f", "range", vec![], vec!["x >= 0"])],
            iterations_used: 5,
            counterexample_count: 3,
            history: vec![],
        };
        assert!(!result.all_verified());
        assert_eq!(result.total_specs(), 1);
    }

    #[test]
    fn test_cgsr_result_empty_is_not_all_verified() {
        let result = CgsrResult {
            verified_specs: vec![],
            unverified_specs: vec![],
            iterations_used: 0,
            counterexample_count: 0,
            history: vec![],
        };
        assert!(!result.all_verified());
        assert_eq!(result.total_specs(), 0);
    }

    // -----------------------------------------------------------------------
    // Tests: Strategy selection
    // -----------------------------------------------------------------------

    #[test]
    fn test_choose_strategy_edge_case_strengthens() {
        let config = CgsrConfig {
            strategy: RefinementStrategy::Weaken,
            ..default_config()
        };
        let cex = Counterexample::new(
            vec![("x".to_string(), "0".to_string())],
            "ensures".to_string(),
            0,
        );
        let strategy = choose_strategy(&config, &cex, &[0]);
        assert_eq!(strategy, RefinementStrategy::Strengthen);
    }

    #[test]
    fn test_choose_strategy_multiple_violations_splits() {
        let config = CgsrConfig {
            strategy: RefinementStrategy::Strengthen,
            ..default_config()
        };
        let cex = Counterexample::new(
            vec![("x".to_string(), "42".to_string())],
            "ensures".to_string(),
            0,
        );
        let strategy = choose_strategy(&config, &cex, &[0, 1]);
        assert_eq!(strategy, RefinementStrategy::Split);
    }

    #[test]
    fn test_choose_strategy_default_fallback() {
        let config = CgsrConfig {
            strategy: RefinementStrategy::Weaken,
            ..default_config()
        };
        let cex = Counterexample::new(
            vec![("x".to_string(), "42".to_string())],
            "ensures".to_string(),
            0,
        );
        let strategy = choose_strategy(&config, &cex, &[0]);
        assert_eq!(strategy, RefinementStrategy::Weaken);
    }

    #[test]
    fn test_choose_strategy_negative_value_strengthens() {
        let config = CgsrConfig {
            strategy: RefinementStrategy::Weaken,
            ..default_config()
        };
        let cex = Counterexample::new(
            vec![("x".to_string(), "-100".to_string())],
            "ensures".to_string(),
            0,
        );
        let strategy = choose_strategy(&config, &cex, &[0]);
        assert_eq!(strategy, RefinementStrategy::Strengthen);
    }

    // -----------------------------------------------------------------------
    // Tests: Config defaults
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_default_values() {
        let config = CgsrConfig::default();
        assert_eq!(config.max_iterations, 10);
        assert_eq!(config.strategy, RefinementStrategy::Strengthen);
        assert_eq!(config.max_counterexamples, 50);
        assert!(!config.verbose);
    }

    // -----------------------------------------------------------------------
    // Tests: find_violated_specs
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_violated_specs_direct_match() {
        let specs = vec![
            make_spec("f", "range", vec![], vec!["result >= 0"]),
            make_spec("f", "non_neg", vec![], vec!["result > 10"]),
        ];
        let cex = Counterexample::new(vec![], "result >= 0".to_string(), 0);
        let violated = find_violated_specs(&specs, &cex);
        // Both are unverified, so both match via fallback.
        assert!(violated.contains(&0));
    }

    #[test]
    fn test_find_violated_specs_skips_verified() {
        let mut spec = make_spec("f", "range", vec![], vec!["result >= 0"]);
        spec.verified = true;
        let specs = vec![spec];
        let cex = Counterexample::new(vec![], "result >= 0".to_string(), 0);
        let violated = find_violated_specs(&specs, &cex);
        assert!(violated.is_empty());
    }
}
