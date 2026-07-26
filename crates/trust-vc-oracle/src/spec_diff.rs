// trust-vc-oracle — Specification diffing across mining runs
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Computes differences between mined spec sets across successive mining
// runs and tracks convergence metrics to determine when the mining loop
// has stabilized.

use std::collections::HashMap;
use std::fmt;

use crate::mining::MinedSpec;

// ---------------------------------------------------------------------------
// Spec identity key
// ---------------------------------------------------------------------------

/// Deduplication/matching key for a mined spec: `(function_name, template_name)`.
type SpecKey = (String, String);

/// Extract the matching key from a `MinedSpec`.
fn spec_key(spec: &MinedSpec) -> SpecKey {
    (spec.function_name.clone(), spec.template_name.clone())
}

// ---------------------------------------------------------------------------
// SpecDiff
// ---------------------------------------------------------------------------

/// The result of comparing two sets of mined specs (old vs new).
///
/// Specs are matched by `(function_name, template_name)`. Matched pairs are
/// classified as unchanged, strengthened, or weakened based on their requires
/// and ensures clauses. Unmatched specs appear in `added` or `removed`.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SpecDiff {
    /// Specs present in new but not in old.
    pub added: Vec<MinedSpec>,
    /// Specs present in old but not in new.
    pub removed: Vec<MinedSpec>,
    /// Specs that gained preconditions (old, new). More requires = stronger guard.
    pub strengthened: Vec<(MinedSpec, MinedSpec)>,
    /// Specs that lost postconditions (old, new). Fewer ensures = weaker guarantee.
    pub weakened: Vec<(MinedSpec, MinedSpec)>,
    /// Specs that are identical across old and new.
    pub unchanged: Vec<MinedSpec>,
    /// Specs whose verification status changed from unverified to verified.
    pub newly_verified: Vec<(MinedSpec, MinedSpec)>,
    /// Specs whose verification status changed from verified to unverified.
    pub newly_unverified: Vec<(MinedSpec, MinedSpec)>,
}

impl SpecDiff {
    /// Total number of specs that changed in any way.
    #[must_use]
    pub fn total_changed(&self) -> usize {
        self.added.len()
            + self.removed.len()
            + self.strengthened.len()
            + self.weakened.len()
            + self.newly_verified.len()
            + self.newly_unverified.len()
    }

    /// Total number of specs considered (changed + unchanged).
    #[must_use]
    pub fn total_specs(&self) -> usize {
        self.total_changed() + self.unchanged.len()
    }

    /// Whether the two spec sets are identical.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.total_changed() == 0
    }

    /// Generate a human-readable summary report.
    #[must_use]
    pub fn report(&self) -> DiffReport<'_> {
        DiffReport { diff: self }
    }
}

// ---------------------------------------------------------------------------
// Clause comparison helpers
// ---------------------------------------------------------------------------

/// Returns true if two clause vectors contain exactly the same elements
/// (order-independent).
fn clauses_equal(a: &[String], b: &[String]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut a_sorted: Vec<&str> = a.iter().map(String::as_str).collect();
    let mut b_sorted: Vec<&str> = b.iter().map(String::as_str).collect();
    a_sorted.sort_unstable();
    b_sorted.sort_unstable();
    a_sorted == b_sorted
}

/// Classify how a matched pair of specs changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ChangeKind {
    Unchanged,
    Strengthened,
    Weakened,
    /// Both strengthened (gained requires) and weakened (lost ensures).
    Mixed,
}

/// Compare old and new specs to determine the nature of the change.
fn classify_change(old: &MinedSpec, new: &MinedSpec) -> ChangeKind {
    let requires_same = clauses_equal(&old.requires, &new.requires);
    let ensures_same = clauses_equal(&old.ensures, &new.ensures);

    if requires_same && ensures_same {
        return ChangeKind::Unchanged;
    }

    // Strengthened: gained new requires (more preconditions) OR gained new ensures
    let gained_requires = new.requires.len() > old.requires.len()
        || (!requires_same && new.requires.len() >= old.requires.len());
    // Weakened: lost ensures (fewer postconditions) OR lost requires
    let lost_ensures = new.ensures.len() < old.ensures.len()
        || (!ensures_same && new.ensures.len() <= old.ensures.len());

    match (gained_requires, lost_ensures) {
        (true, true) => ChangeKind::Mixed,
        (true, false) => ChangeKind::Strengthened,
        (false, true) => ChangeKind::Weakened,
        // Clauses changed but don't fit a simple pattern — treat as strengthened
        // (the spec is different, and we bias toward "gained information").
        (false, false) => ChangeKind::Strengthened,
    }
}

// ---------------------------------------------------------------------------
// Core diff function
// ---------------------------------------------------------------------------

/// Compute the diff between two sets of mined specs.
///
/// Specs are matched by `(function_name, template_name)`. Matched pairs are
/// classified as unchanged, strengthened, or weakened. Unmatched specs are
/// reported as added or removed.
#[must_use]
pub fn diff_spec_sets(old: &[MinedSpec], new: &[MinedSpec]) -> SpecDiff {
    let mut old_map: HashMap<SpecKey, &MinedSpec> = HashMap::new();
    for spec in old {
        old_map.insert(spec_key(spec), spec);
    }

    let mut new_map: HashMap<SpecKey, &MinedSpec> = HashMap::new();
    for spec in new {
        new_map.insert(spec_key(spec), spec);
    }

    let mut added = Vec::new();
    let mut removed = Vec::new();
    let mut strengthened = Vec::new();
    let mut weakened = Vec::new();
    let mut unchanged = Vec::new();
    let mut newly_verified = Vec::new();
    let mut newly_unverified = Vec::new();

    // Process specs present in new
    for (key, new_spec) in &new_map {
        if let Some(old_spec) = old_map.get(key) {
            // Check verification status change first
            if !old_spec.verified && new_spec.verified {
                newly_verified.push(((*old_spec).clone(), (*new_spec).clone()));
            } else if old_spec.verified && !new_spec.verified {
                newly_unverified.push(((*old_spec).clone(), (*new_spec).clone()));
            } else {
                // Same verification status — classify clause changes
                match classify_change(old_spec, new_spec) {
                    ChangeKind::Unchanged => unchanged.push((*new_spec).clone()),
                    ChangeKind::Strengthened | ChangeKind::Mixed => {
                        strengthened.push(((*old_spec).clone(), (*new_spec).clone()));
                    }
                    ChangeKind::Weakened => {
                        weakened.push(((*old_spec).clone(), (*new_spec).clone()));
                    }
                }
            }
        } else {
            added.push((*new_spec).clone());
        }
    }

    // Specs in old but not in new
    for (key, old_spec) in &old_map {
        if !new_map.contains_key(key) {
            removed.push((*old_spec).clone());
        }
    }

    SpecDiff {
        added,
        removed,
        strengthened,
        weakened,
        unchanged,
        newly_verified,
        newly_unverified,
    }
}

// ---------------------------------------------------------------------------
// DiffReport
// ---------------------------------------------------------------------------

/// Human-readable report for a `SpecDiff`.
///
/// Implements `Display` for convenient printing.
pub struct DiffReport<'a> {
    diff: &'a SpecDiff,
}

impl<'a> DiffReport<'a> {
    /// One-line summary.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "{} added, {} removed, {} strengthened, {} weakened, \
             {} newly verified, {} newly unverified, {} unchanged",
            self.diff.added.len(),
            self.diff.removed.len(),
            self.diff.strengthened.len(),
            self.diff.weakened.len(),
            self.diff.newly_verified.len(),
            self.diff.newly_unverified.len(),
            self.diff.unchanged.len(),
        )
    }

    /// Detailed multi-line report showing specific clause changes.
    #[must_use]
    pub fn detailed(&self) -> String {
        let mut lines = Vec::new();
        lines.push(format!("Spec Diff Report: {}", self.summary()));
        lines.push(String::new());

        if !self.diff.added.is_empty() {
            lines.push("Added:".to_string());
            for spec in &self.diff.added {
                lines.push(format!(
                    "  + {}::{} (verified={})",
                    spec.function_name, spec.template_name, spec.verified
                ));
            }
            lines.push(String::new());
        }

        if !self.diff.removed.is_empty() {
            lines.push("Removed:".to_string());
            for spec in &self.diff.removed {
                lines.push(format!(
                    "  - {}::{} (verified={})",
                    spec.function_name, spec.template_name, spec.verified
                ));
            }
            lines.push(String::new());
        }

        if !self.diff.strengthened.is_empty() {
            lines.push("Strengthened:".to_string());
            for (old, new) in &self.diff.strengthened {
                lines.push(format!(
                    "  ~ {}::{}: requires {} -> {}, ensures {} -> {}",
                    old.function_name,
                    old.template_name,
                    old.requires.len(),
                    new.requires.len(),
                    old.ensures.len(),
                    new.ensures.len(),
                ));
            }
            lines.push(String::new());
        }

        if !self.diff.weakened.is_empty() {
            lines.push("Weakened:".to_string());
            for (old, new) in &self.diff.weakened {
                lines.push(format!(
                    "  ~ {}::{}: requires {} -> {}, ensures {} -> {}",
                    old.function_name,
                    old.template_name,
                    old.requires.len(),
                    new.requires.len(),
                    old.ensures.len(),
                    new.ensures.len(),
                ));
            }
            lines.push(String::new());
        }

        if !self.diff.newly_verified.is_empty() {
            lines.push("Newly verified:".to_string());
            for (_, new) in &self.diff.newly_verified {
                lines.push(format!(
                    "  * {}::{} (was unverified, now verified)",
                    new.function_name, new.template_name,
                ));
            }
            lines.push(String::new());
        }

        if !self.diff.newly_unverified.is_empty() {
            lines.push("Newly unverified:".to_string());
            for (_, new) in &self.diff.newly_unverified {
                lines.push(format!(
                    "  ! {}::{} (was verified, now unverified)",
                    new.function_name, new.template_name,
                ));
            }
            lines.push(String::new());
        }

        lines.join("\n")
    }
}

impl fmt::Display for DiffReport<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.detailed())
    }
}

// ---------------------------------------------------------------------------
// Spec evolution across multiple runs
// ---------------------------------------------------------------------------

/// Compute successive diffs across a series of mining runs.
///
/// Given a history of spec sets (one per run, in chronological order),
/// produces `history.len() - 1` diffs representing the changes between
/// each consecutive pair of runs.
///
/// Returns an empty vec if fewer than 2 runs are provided.
#[must_use]
pub fn spec_evolution(history: &[Vec<MinedSpec>]) -> Vec<SpecDiff> {
    if history.len() < 2 {
        return Vec::new();
    }
    history
        .windows(2)
        .map(|pair| diff_spec_sets(&pair[0], &pair[1]))
        .collect()
}

// ---------------------------------------------------------------------------
// ConvergenceMetric
// ---------------------------------------------------------------------------

/// Metrics for tracking whether mined specs are converging (stabilizing)
/// across successive runs.
pub struct ConvergenceMetric;

impl ConvergenceMetric {
    /// Fraction of specs that changed between consecutive runs.
    ///
    /// A churn rate of 0.0 means no specs changed; 1.0 means every spec
    /// changed. Returns 0.0 for empty diffs.
    #[must_use]
    pub fn churn_rate(diffs: &[SpecDiff]) -> f64 {
        if diffs.is_empty() {
            return 0.0;
        }
        let total_changed: usize = diffs.iter().map(SpecDiff::total_changed).sum();
        let total_specs: usize = diffs.iter().map(SpecDiff::total_specs).sum();
        if total_specs == 0 {
            return 0.0;
        }
        total_changed as f64 / total_specs as f64
    }

    /// Stability index: `1.0 - churn_rate`.
    ///
    /// 1.0 means fully stable (no churn); 0.0 means complete churn.
    #[must_use]
    pub fn stability_index(diffs: &[SpecDiff]) -> f64 {
        1.0 - Self::churn_rate(diffs)
    }

    /// Estimated number of additional runs needed to reach <5% churn.
    ///
    /// Uses a simple exponential-decay model fitted to the per-diff churn
    /// rates. Returns `None` if:
    /// - There are fewer than 2 diffs (insufficient data)
    /// - The churn rate is not decreasing (non-convergent)
    /// - The specs are already stable (churn < 5%)
    ///
    /// Returns `Some(0)` when the latest diff already has <5% churn.
    #[must_use]
    pub fn time_to_stability(diffs: &[SpecDiff]) -> Option<usize> {
        if diffs.is_empty() {
            return None;
        }

        let per_diff_churn: Vec<f64> = diffs
            .iter()
            .map(|d| {
                let total = d.total_specs();
                if total == 0 {
                    0.0
                } else {
                    d.total_changed() as f64 / total as f64
                }
            })
            .collect();

        // If the latest churn is already below threshold, we are stable.
        let threshold = 0.05;
        if let Some(&latest) = per_diff_churn.last() {
            if latest < threshold {
                return Some(0);
            }
        }

        if per_diff_churn.len() < 2 {
            return None;
        }

        // Fit exponential decay: churn(t) = c0 * r^t
        // Use last two data points to estimate decay rate.
        let n = per_diff_churn.len();
        let prev = per_diff_churn[n - 2];
        let curr = per_diff_churn[n - 1];

        if prev <= 0.0 || curr <= 0.0 || curr >= prev {
            // Not decreasing — cannot extrapolate convergence.
            return None;
        }

        let decay_rate = curr / prev;
        // Solve: curr * decay_rate^k < threshold
        // k > ln(threshold / curr) / ln(decay_rate)
        let k = (threshold / curr).ln() / decay_rate.ln();
        let runs_needed = k.ceil() as usize;
        Some(runs_needed)
    }

    /// Per-diff churn rates for the entire history.
    ///
    /// Returns one churn rate per diff (same length as input).
    #[must_use]
    pub fn churn_history(diffs: &[SpecDiff]) -> Vec<f64> {
        diffs
            .iter()
            .map(|d| {
                let total = d.total_specs();
                if total == 0 {
                    0.0
                } else {
                    d.total_changed() as f64 / total as f64
                }
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn make_spec(
        func: &str,
        template: &str,
        requires: Vec<&str>,
        ensures: Vec<&str>,
        verified: bool,
    ) -> MinedSpec {
        MinedSpec::new(
            func.to_string(),
            template.to_string(),
            requires.iter().map(|s| s.to_string()).collect(),
            ensures.iter().map(|s| s.to_string()).collect(),
            verified,
            0,
        )
    }

    fn make_spec_with_iters(
        func: &str,
        template: &str,
        requires: Vec<&str>,
        ensures: Vec<&str>,
        verified: bool,
        iterations: usize,
    ) -> MinedSpec {
        MinedSpec::new(
            func.to_string(),
            template.to_string(),
            requires.iter().map(|s| s.to_string()).collect(),
            ensures.iter().map(|s| s.to_string()).collect(),
            verified,
            iterations,
        )
    }

    // -----------------------------------------------------------------------
    // diff_spec_sets: basic cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_diff_both_empty() {
        let diff = diff_spec_sets(&[], &[]);
        assert!(diff.is_empty());
        assert_eq!(diff.total_changed(), 0);
        assert_eq!(diff.total_specs(), 0);
    }

    #[test]
    fn test_diff_all_added() {
        let new = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(result)"], true),
        ];
        let diff = diff_spec_sets(&[], &new);
        assert_eq!(diff.added.len(), 2);
        assert!(diff.removed.is_empty());
        assert!(diff.unchanged.is_empty());
        assert_eq!(diff.total_changed(), 2);
    }

    #[test]
    fn test_diff_all_removed() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&old, &[]);
        assert!(diff.added.is_empty());
        assert_eq!(diff.removed.len(), 1);
        assert_eq!(diff.removed[0].function_name, "f");
    }

    #[test]
    fn test_diff_identical_specs_unchanged() {
        let specs = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&specs, &specs);
        assert!(diff.is_empty());
        assert_eq!(diff.unchanged.len(), 1);
        assert_eq!(diff.unchanged[0].function_name, "f");
    }

    #[test]
    fn test_diff_strengthened_gained_requires() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let new = vec![make_spec(
            "f",
            "range",
            vec!["x > 0", "x < 100"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(diff.strengthened.len(), 1);
        assert_eq!(diff.strengthened[0].0.requires.len(), 1);
        assert_eq!(diff.strengthened[0].1.requires.len(), 2);
    }

    #[test]
    fn test_diff_weakened_lost_ensures() {
        let old = vec![make_spec(
            "f",
            "range",
            vec![],
            vec!["result >= 0", "result < 100"],
            true,
        )];
        let new = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(diff.weakened.len(), 1);
        assert_eq!(diff.weakened[0].0.ensures.len(), 2);
        assert_eq!(diff.weakened[0].1.ensures.len(), 1);
    }

    #[test]
    fn test_diff_newly_verified() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            false,
        )];
        let new = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(diff.newly_verified.len(), 1);
        assert!(!diff.newly_verified[0].0.verified);
        assert!(diff.newly_verified[0].1.verified);
    }

    #[test]
    fn test_diff_newly_unverified() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let new = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            false,
        )];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(diff.newly_unverified.len(), 1);
        assert!(diff.newly_unverified[0].0.verified);
        assert!(!diff.newly_unverified[0].1.verified);
    }

    #[test]
    fn test_diff_mixed_add_remove_change() {
        let old = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(result)"], true),
        ];
        let new = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true),
            make_spec("h", "identity", vec![], vec!["result == x"], true),
        ];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(diff.unchanged.len(), 1, "f::range should be unchanged");
        assert_eq!(diff.removed.len(), 1, "g::sorted should be removed");
        assert_eq!(diff.removed[0].function_name, "g");
        assert_eq!(diff.added.len(), 1, "h::identity should be added");
        assert_eq!(diff.added[0].function_name, "h");
    }

    #[test]
    fn test_diff_matching_by_function_and_template() {
        // Same function, different templates should NOT match
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let new = vec![make_spec(
            "f",
            "sorted",
            vec![],
            vec!["sorted(result)"],
            true,
        )];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(diff.removed.len(), 1, "f::range removed");
        assert_eq!(diff.added.len(), 1, "f::sorted added");
        assert!(diff.unchanged.is_empty());
    }

    #[test]
    fn test_diff_clause_order_independence() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["a > 0", "b > 0"],
            vec!["r1", "r2"],
            true,
        )];
        let new = vec![make_spec(
            "f",
            "range",
            vec!["b > 0", "a > 0"],
            vec!["r2", "r1"],
            true,
        )];
        let diff = diff_spec_sets(&old, &new);
        assert_eq!(
            diff.unchanged.len(),
            1,
            "reordered clauses should be considered identical"
        );
    }

    // -----------------------------------------------------------------------
    // DiffReport
    // -----------------------------------------------------------------------

    #[test]
    fn test_report_summary_format() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let new = vec![
            make_spec(
                "f",
                "range",
                vec!["x > 0", "x < 100"],
                vec!["result >= 0"],
                true,
            ),
            make_spec("g", "sorted", vec![], vec!["sorted(result)"], true),
        ];
        let diff = diff_spec_sets(&old, &new);
        let report = diff.report();
        let summary = report.summary();
        assert!(summary.contains("1 added"), "summary: {summary}");
        assert!(summary.contains("1 strengthened"), "summary: {summary}");
        assert!(summary.contains("0 removed"), "summary: {summary}");
        assert!(summary.contains("0 unchanged"), "summary: {summary}");
    }

    #[test]
    fn test_report_detailed_contains_sections() {
        let old = vec![make_spec(
            "f",
            "range",
            vec![],
            vec!["result >= 0", "result < 100"],
            true,
        )];
        let new = vec![
            make_spec("f", "range", vec![], vec!["result >= 0"], true),
            make_spec("g", "identity", vec![], vec!["result == x"], true),
        ];
        let diff = diff_spec_sets(&old, &new);
        let detailed = diff.report().detailed();
        assert!(detailed.contains("Added:"), "detailed: {detailed}");
        assert!(detailed.contains("g::identity"), "detailed: {detailed}");
        assert!(detailed.contains("Weakened:"), "detailed: {detailed}");
        assert!(detailed.contains("f::range"), "detailed: {detailed}");
    }

    #[test]
    fn test_report_display_trait() {
        let diff = diff_spec_sets(&[], &[]);
        let report = diff.report();
        let display = format!("{report}");
        assert!(display.contains("Spec Diff Report:"));
    }

    // -----------------------------------------------------------------------
    // spec_evolution
    // -----------------------------------------------------------------------

    #[test]
    fn test_evolution_empty_history() {
        let diffs = spec_evolution(&[]);
        assert!(diffs.is_empty());
    }

    #[test]
    fn test_evolution_single_run() {
        let history = vec![vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )]];
        let diffs = spec_evolution(&history);
        assert!(diffs.is_empty(), "need at least 2 runs to produce diffs");
    }

    #[test]
    fn test_evolution_two_runs() {
        let run1 = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let run2 = vec![make_spec(
            "f",
            "range",
            vec!["x > 0", "x < 100"],
            vec!["result >= 0"],
            true,
        )];
        let diffs = spec_evolution(&[run1, run2]);
        assert_eq!(diffs.len(), 1);
        assert_eq!(diffs[0].strengthened.len(), 1);
    }

    #[test]
    fn test_evolution_three_runs_produces_two_diffs() {
        let run1 = vec![make_spec("f", "range", vec![], vec!["result >= 0"], false)];
        let run2 = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let run3 = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diffs = spec_evolution(&[run1, run2, run3]);
        assert_eq!(diffs.len(), 2);
        // First diff: newly verified + strengthened
        assert_eq!(diffs[0].newly_verified.len(), 1);
        // Second diff: unchanged
        assert_eq!(diffs[1].unchanged.len(), 1);
        assert!(diffs[1].is_empty());
    }

    // -----------------------------------------------------------------------
    // ConvergenceMetric
    // -----------------------------------------------------------------------

    #[test]
    fn test_churn_rate_empty() {
        assert_eq!(ConvergenceMetric::churn_rate(&[]), 0.0);
    }

    #[test]
    fn test_churn_rate_no_changes() {
        let specs = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&specs, &specs);
        assert_eq!(ConvergenceMetric::churn_rate(&[diff]), 0.0);
    }

    #[test]
    fn test_churn_rate_all_changes() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&old, &[]);
        let rate = ConvergenceMetric::churn_rate(&[diff]);
        assert!(
            (rate - 1.0).abs() < f64::EPSILON,
            "all removed = 100% churn, got {rate}"
        );
    }

    #[test]
    fn test_stability_index_complement_of_churn() {
        let specs = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&specs, &specs);
        let stability = ConvergenceMetric::stability_index(&[diff]);
        assert!(
            (stability - 1.0).abs() < f64::EPSILON,
            "no churn = stability 1.0, got {stability}"
        );
    }

    #[test]
    fn test_stability_index_partial_churn() {
        let old = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(result)"], true),
        ];
        let new = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true),
            make_spec("g", "sorted", vec!["len > 0"], vec!["sorted(result)"], true),
        ];
        let diff = diff_spec_sets(&old, &new);
        let stability = ConvergenceMetric::stability_index(&[diff]);
        assert!(
            stability > 0.0 && stability < 1.0,
            "partial churn should give stability between 0 and 1, got {stability}"
        );
    }

    #[test]
    fn test_time_to_stability_already_stable() {
        let specs = vec![make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0"],
            true,
        )];
        let diff = diff_spec_sets(&specs, &specs);
        let result = ConvergenceMetric::time_to_stability(&[diff]);
        assert_eq!(result, Some(0), "already stable should return Some(0)");
    }

    #[test]
    fn test_time_to_stability_insufficient_data() {
        assert_eq!(ConvergenceMetric::time_to_stability(&[]), None);
    }

    #[test]
    fn test_time_to_stability_decreasing_churn() {
        // Simulate decreasing churn: run1->run2 has 50% churn, run2->run3 has 25%
        let run1 = vec![
            make_spec("f", "range", vec![], vec!["r >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(r)"], true),
        ];
        let run2 = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(r)"], true),
        ];
        let run3 = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(r)"], true),
            make_spec("h", "identity", vec![], vec!["r == x"], true),
        ];
        // run2 has some changes but run3 adds one — this is decreasing in ratio
        // because the total set grows.
        // Instead, let's construct diffs directly for clarity.
        let diff1 = diff_spec_sets(&run1, &run2);
        let diff2 = diff_spec_sets(&run2, &run3);

        // diff1: 1 strengthened, 1 unchanged => churn = 1/2 = 0.5
        // diff2: 1 added, 2 unchanged => churn = 1/3 ~= 0.33
        let diffs = vec![diff1, diff2];
        let result = ConvergenceMetric::time_to_stability(&diffs);
        assert!(
            result.is_some(),
            "decreasing churn should produce a stability estimate"
        );
        let runs = result.unwrap();
        assert!(
            runs > 0,
            "should need at least 1 more run to reach <5% churn"
        );
    }

    #[test]
    fn test_time_to_stability_non_decreasing_returns_none() {
        // Churn is increasing — should not converge
        let run1 = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(r)"], true),
        ];
        let run2 = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true),
            make_spec("g", "sorted", vec![], vec!["sorted(r)"], true),
        ];
        let run3 = vec![
            make_spec("f", "range", vec!["x > 0", "x < 100"], vec!["r >= 0"], true),
            make_spec("g", "sorted", vec!["len > 0"], vec!["sorted(r)"], true),
        ];
        let diff1 = diff_spec_sets(&run1, &run2); // 0 churn
        let diff2 = diff_spec_sets(&run2, &run3); // high churn
        let result = ConvergenceMetric::time_to_stability(&[diff1, diff2]);
        // First diff has 0 churn, second has high churn — not decreasing.
        // The function should return None since churn is not decreasing between
        // the last two data points.
        assert_eq!(result, None, "increasing churn should return None");
    }

    #[test]
    fn test_churn_history_matches_diffs() {
        let run1 = vec![make_spec("f", "range", vec![], vec!["r >= 0"], true)];
        let run2 = vec![make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true)];
        let run3 = vec![make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true)];
        let diffs = spec_evolution(&[run1, run2, run3]);
        let history = ConvergenceMetric::churn_history(&diffs);
        assert_eq!(history.len(), 2);
        assert!(history[0] > 0.0, "first diff has changes");
        assert!(
            history[1] < f64::EPSILON,
            "second diff has no changes, got {}",
            history[1]
        );
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_diff_duplicate_keys_in_new_last_wins() {
        // If new contains duplicates, HashMap will keep the last one.
        // This matches the expected behavior since mining shouldn't produce
        // duplicates, but we test robustness.
        let old: Vec<MinedSpec> = vec![];
        let new = vec![
            make_spec("f", "range", vec!["x > 0"], vec!["r >= 0"], true),
            make_spec("f", "range", vec!["x > 5"], vec!["r >= 5"], true),
        ];
        let diff = diff_spec_sets(&old, &new);
        // One of the two should be added (HashMap dedup)
        assert_eq!(diff.added.len(), 1);
    }

    #[test]
    fn test_diff_with_iterations_field_ignored_for_matching() {
        // Iterations don't affect matching — only (function_name, template_name)
        let old = vec![make_spec_with_iters(
            "f",
            "range",
            vec!["x > 0"],
            vec!["r >= 0"],
            true,
            0,
        )];
        let new = vec![make_spec_with_iters(
            "f",
            "range",
            vec!["x > 0"],
            vec!["r >= 0"],
            true,
            3,
        )];
        let diff = diff_spec_sets(&old, &new);
        // Clauses are identical, so unchanged
        assert_eq!(diff.unchanged.len(), 1);
    }

    #[test]
    fn test_clauses_equal_empty() {
        assert!(clauses_equal(&[], &[]));
    }

    #[test]
    fn test_clauses_equal_different_lengths() {
        let a = vec!["x > 0".to_string()];
        let b = vec!["x > 0".to_string(), "x < 10".to_string()];
        assert!(!clauses_equal(&a, &b));
    }
}
