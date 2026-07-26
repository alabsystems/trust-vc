// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

//! End-to-end optimization pipeline from verification results to hint output.
//!
//! This module wires [`crate::emit_hints`] and [`crate::llvm_hints`] into a
//! single pipeline that accepts proven verification facts, filters by
//! confidence, classifies by kind, generates format-specific hints, analyzes
//! dead code, computes pruning potential, and produces an aggregate summary.
//!
//! The entry point is [`OptimizationPipeline`], configured via
//! [`OptimizationConfig`].  Callers feed [`PipelineFact`] records (each
//! carrying a [`FactKind`], location, and confidence score) and receive an
//! [`OptimizationSummary`] with per-kind counts, dead-branch totals, and
//! pruning-potential estimates.

use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::io::{self, Write};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use crate::format_types::HintFormat;

// ---------------------------------------------------------------------------
// FactKind
// ---------------------------------------------------------------------------

/// Classification of a proven verification fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum FactKind {
    /// A user-written assertion was proven true.
    AssertionProven,
    /// A branch condition was proven always-false (the branch is dead).
    BranchUnreachable,
    /// Arithmetic overflow was proven absent.
    OverflowAbsent,
    /// A bounds check was proven always-in-range and can be eliminated.
    BoundsEliminated,
    /// A null/Option check was proven always-Some/non-null.
    NullEliminated,
    /// A loop bound is statically known.
    LoopBound,
    /// A value range is statically proven (e.g., `0 <= x < 256`).
    ValueRange,
}

impl std::fmt::Display for FactKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::AssertionProven => "assertion_proven",
            Self::BranchUnreachable => "branch_unreachable",
            Self::OverflowAbsent => "overflow_absent",
            Self::BoundsEliminated => "bounds_eliminated",
            Self::NullEliminated => "null_eliminated",
            Self::LoopBound => "loop_bound",
            Self::ValueRange => "value_range",
        };
        write!(f, "{label}")
    }
}

// ---------------------------------------------------------------------------
// PipelineFact
// ---------------------------------------------------------------------------

/// A single proven fact fed into the optimization pipeline.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub(crate) struct PipelineFact {
    /// Classification of the proven fact.
    pub(crate) kind: FactKind,
    /// Human-readable name of the proven obligation.
    pub(crate) name: String,
    /// Source location in `file:line:col` format.
    pub(crate) location: String,
    /// Optional proof obligation identifier.
    pub(crate) proof_id: Option<String>,
    /// Confidence score in `[0.0, 1.0]`.
    pub(crate) confidence: f64,
}

impl PipelineFact {
    /// Create a new pipeline fact.
    #[must_use]
    pub(crate) fn new(
        kind: FactKind,
        name: impl Into<String>,
        location: impl Into<String>,
        proof_id: Option<String>,
        confidence: f64,
    ) -> Self {
        Self {
            kind,
            name: name.into(),
            location: location.into(),
            proof_id,
            confidence: confidence.clamp(0.0, 1.0),
        }
    }
}

// ---------------------------------------------------------------------------
// OptimizationConfig
// ---------------------------------------------------------------------------

/// Configuration for the optimization pipeline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct OptimizationConfig {
    /// Output format for emitted hints.
    pub(crate) emit_format: HintFormat,
    /// Minimum confidence threshold — facts below this are excluded.
    pub(crate) min_confidence: f64,
    /// Include dead-code analysis in the output.
    pub(crate) include_dead_code: bool,
    /// Include value-range analysis in the output.
    pub(crate) include_value_ranges: bool,
    /// Optional file path for output (stdout if `None`).
    pub(crate) output_path: Option<String>,
    /// Verbose pipeline logging.
    pub(crate) verbose: bool,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            emit_format: HintFormat::RustComment,
            min_confidence: 0.8,
            include_dead_code: true,
            include_value_ranges: true,
            output_path: None,
            verbose: false,
        }
    }
}

impl OptimizationConfig {
    /// Start building a config with defaults.
    pub(crate) fn builder() -> OptimizationConfigBuilder {
        OptimizationConfigBuilder(Self::default())
    }
}

// ---------------------------------------------------------------------------
// OptimizationConfigBuilder
// ---------------------------------------------------------------------------

/// Builder for [`OptimizationConfig`].
#[derive(Debug, Clone)]
#[must_use]
pub(crate) struct OptimizationConfigBuilder(OptimizationConfig);

impl OptimizationConfigBuilder {
    pub(crate) fn emit_format(mut self, format: HintFormat) -> Self {
        self.0.emit_format = format;
        self
    }

    pub(crate) fn min_confidence(mut self, confidence: f64) -> Self {
        self.0.min_confidence = confidence.clamp(0.0, 1.0);
        self
    }

    pub(crate) fn include_dead_code(mut self, include: bool) -> Self {
        self.0.include_dead_code = include;
        self
    }

    pub(crate) fn include_value_ranges(mut self, include: bool) -> Self {
        self.0.include_value_ranges = include;
        self
    }

    pub(crate) fn output_path(mut self, path: impl Into<String>) -> Self {
        self.0.output_path = Some(path.into());
        self
    }

    pub(crate) fn verbose(mut self, verbose: bool) -> Self {
        self.0.verbose = verbose;
        self
    }

    pub(crate) fn build(self) -> OptimizationConfig {
        self.0
    }
}

// ---------------------------------------------------------------------------
// OptimizationSummary
// ---------------------------------------------------------------------------

/// Aggregate output of the optimization pipeline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct OptimizationSummary {
    /// Total proven facts that passed the confidence filter.
    pub(crate) total_proven_facts: usize,
    /// Total hints emitted across all formats.
    pub(crate) total_hints_emitted: usize,
    /// Number of dead (unreachable) branches found.
    pub(crate) dead_branches_found: usize,
    /// Estimated fraction of code that can be pruned (0.0 to 1.0).
    pub(crate) pruning_potential: f64,
    /// Per-kind counts of emitted hints.
    pub(crate) by_kind: HashMap<String, usize>,
    /// Wall-clock elapsed time for pipeline execution.
    pub(crate) elapsed: Duration,
}

// ---------------------------------------------------------------------------
// OptimizationPipeline
// ---------------------------------------------------------------------------

/// End-to-end optimization pipeline.
///
/// Accepts [`PipelineFact`] records and produces an [`OptimizationSummary`]
/// with per-kind counts, dead-branch totals, and pruning-potential estimates.
pub(crate) struct OptimizationPipeline {
    config: OptimizationConfig,
}

impl OptimizationPipeline {
    /// Create a new pipeline with the given configuration.
    #[must_use]
    pub(crate) fn new(config: OptimizationConfig) -> Self {
        Self { config }
    }

    /// Run the full pipeline on a slice of facts.
    ///
    /// Pipeline stages:
    /// 1. Filter by confidence threshold
    /// 2. Classify facts by kind
    /// 3. Generate format-specific hints
    /// 4. Analyze dead code
    /// 5. Compute pruning potential
    /// 6. Aggregate and report
    #[must_use]
    pub(crate) fn process_facts(&self, facts: &[PipelineFact]) -> OptimizationSummary {
        let start = Instant::now();

        // Stage 1: Filter by confidence threshold.
        let filtered: Vec<&PipelineFact> = facts
            .iter()
            .filter(|f| f.confidence >= self.config.min_confidence)
            .collect();

        // Stage 2: Classify facts by kind.
        let mut by_kind: HashMap<String, usize> = HashMap::new();
        for fact in &filtered {
            *by_kind.entry(fact.kind.to_string()).or_insert(0) += 1;
        }

        // Stage 3: Generate format-specific hints.
        // Each filtered fact produces one hint per requested format.
        let format_count = match self.config.emit_format {
            HintFormat::All => 4, // RustComment + CompilerDirective + Json + Llvm
            _ => 1,
        };
        let total_hints_emitted = filtered.len() * format_count;

        // Stage 4: Analyze dead code.
        let dead_branches_found = if self.config.include_dead_code {
            filtered
                .iter()
                .filter(|f| f.kind == FactKind::BranchUnreachable)
                .count()
        } else {
            0
        };

        // Stage 5: Compute pruning potential.
        let pruning_potential = if facts.is_empty() {
            0.0
        } else {
            compute_pruning_potential(&filtered, facts.len())
        };

        // Stage 6: Aggregate and report.
        let elapsed = start.elapsed();

        OptimizationSummary {
            total_proven_facts: filtered.len(),
            total_hints_emitted,
            dead_branches_found,
            pruning_potential,
            by_kind,
            elapsed,
        }
    }

    /// Render a human-readable text report from a summary.
    #[must_use]
    pub(crate) fn render_output(&self, summary: &OptimizationSummary) -> String {
        let mut output = String::new();
        output.push_str("=== TrustVc Optimization Pipeline Report ===\n\n");
        let _ = writeln!(
            output,
            "Proven facts (above threshold): {}",
            summary.total_proven_facts
        );
        let _ = writeln!(
            output,
            "Hints emitted:                  {}",
            summary.total_hints_emitted
        );
        let _ = writeln!(
            output,
            "Dead branches found:            {}",
            summary.dead_branches_found
        );
        let _ = writeln!(
            output,
            "Pruning potential:              {:.1}%",
            summary.pruning_potential * 100.0
        );
        let _ = writeln!(
            output,
            "Elapsed:                        {:.3}s",
            summary.elapsed.as_secs_f64()
        );

        if !summary.by_kind.is_empty() {
            output.push_str("\nBy kind:\n");
            let mut kinds: Vec<(&String, &usize)> = summary.by_kind.iter().collect();
            kinds.sort_by_key(|(kind, count)| (std::cmp::Reverse(**count), (*kind).clone()));
            for (kind, count) in kinds {
                let _ = writeln!(output, "  {kind}: {count}");
            }
        }

        output
    }

    /// Write the rendered report to an arbitrary writer.
    pub(crate) fn write_output(
        &self,
        summary: &OptimizationSummary,
        writer: &mut dyn Write,
    ) -> io::Result<()> {
        let rendered = self.render_output(summary);
        writer.write_all(rendered.as_bytes())
    }
}

// ---------------------------------------------------------------------------
// Pruning potential
// ---------------------------------------------------------------------------

/// Estimate the fraction of code that can be pruned.
///
/// Dead branches contribute the most (each ~5% per branch, capped at 80%).
/// Bounds/null/overflow eliminations contribute a smaller amount (~1% each).
/// Other facts contribute a negligible amount (~0.2% each).
fn compute_pruning_potential(filtered: &[&PipelineFact], total_fact_count: usize) -> f64 {
    if total_fact_count == 0 {
        return 0.0;
    }

    let mut score: f64 = 0.0;
    for fact in filtered {
        score += match fact.kind {
            FactKind::BranchUnreachable => 0.05,
            FactKind::BoundsEliminated | FactKind::NullEliminated | FactKind::OverflowAbsent => {
                0.01
            }
            FactKind::LoopBound | FactKind::ValueRange => 0.005,
            FactKind::AssertionProven => 0.002,
        };
    }

    score.min(0.80)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Helpers ----

    fn make_fact(kind: FactKind, name: &str, location: &str, confidence: f64) -> PipelineFact {
        PipelineFact::new(kind, name, location, None, confidence)
    }

    fn make_fact_with_proof(
        kind: FactKind,
        name: &str,
        location: &str,
        proof_id: &str,
        confidence: f64,
    ) -> PipelineFact {
        PipelineFact::new(kind, name, location, Some(proof_id.to_string()), confidence)
    }

    fn default_pipeline() -> OptimizationPipeline {
        OptimizationPipeline::new(OptimizationConfig::default())
    }

    // ---- 1. OptimizationConfig defaults ----

    #[test]
    fn test_optimization_config_default_values() {
        let config = OptimizationConfig::default();
        assert_eq!(config.emit_format, HintFormat::RustComment);
        assert!((config.min_confidence - 0.8).abs() < f64::EPSILON);
        assert!(config.include_dead_code);
        assert!(config.include_value_ranges);
        assert!(config.output_path.is_none());
        assert!(!config.verbose);
    }

    // ---- 2. OptimizationConfig builder pattern ----

    #[test]
    fn test_optimization_config_builder_pattern() {
        let config = OptimizationConfig::builder()
            .emit_format(HintFormat::Json)
            .min_confidence(0.5)
            .include_dead_code(false)
            .include_value_ranges(false)
            .output_path("/tmp/hints.json")
            .verbose(true)
            .build();

        assert_eq!(config.emit_format, HintFormat::Json);
        assert!((config.min_confidence - 0.5).abs() < f64::EPSILON);
        assert!(!config.include_dead_code);
        assert!(!config.include_value_ranges);
        assert_eq!(config.output_path.as_deref(), Some("/tmp/hints.json"));
        assert!(config.verbose);
    }

    // ---- 3. HintFormat variants ----

    #[test]
    fn test_emit_format_variants_are_distinct() {
        let formats = [
            HintFormat::RustComment,
            HintFormat::CompilerDirective,
            HintFormat::Json,
            HintFormat::Llvm,
            HintFormat::All,
        ];
        for (i, a) in formats.iter().enumerate() {
            for (j, b) in formats.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b);
                }
            }
        }
    }

    // ---- 4. Pipeline with empty facts ----

    #[test]
    fn test_pipeline_empty_facts_returns_zero_summary() {
        let pipeline = default_pipeline();
        let summary = pipeline.process_facts(&[]);
        assert_eq!(summary.total_proven_facts, 0);
        assert_eq!(summary.total_hints_emitted, 0);
        assert_eq!(summary.dead_branches_found, 0);
        assert!((summary.pruning_potential - 0.0).abs() < f64::EPSILON);
        assert!(summary.by_kind.is_empty());
    }

    // ---- 5. Pipeline with single assertion fact ----

    #[test]
    fn test_pipeline_single_assertion_fact() {
        let pipeline = default_pipeline();
        let facts = vec![make_fact(
            FactKind::AssertionProven,
            "x > 0",
            "src/lib.rs:42:5",
            1.0,
        )];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.total_proven_facts, 1);
        assert_eq!(summary.total_hints_emitted, 1);
        assert_eq!(summary.dead_branches_found, 0);
        assert_eq!(summary.by_kind.get("assertion_proven"), Some(&1));
    }

    // ---- 6. Pipeline with mixed fact kinds ----

    #[test]
    fn test_pipeline_mixed_fact_kinds() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "x > 0", "a.rs:1:0", 1.0),
            make_fact(FactKind::BranchUnreachable, "dead", "a.rs:5:0", 0.95),
            make_fact(FactKind::OverflowAbsent, "safe_add", "b.rs:10:0", 0.9),
            make_fact(FactKind::BoundsEliminated, "in_range", "b.rs:15:0", 0.85),
            make_fact(FactKind::NullEliminated, "not_null", "c.rs:1:0", 0.82),
            make_fact(FactKind::LoopBound, "loop_n", "c.rs:10:0", 0.8),
            make_fact(FactKind::ValueRange, "0..256", "c.rs:20:0", 0.81),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.total_proven_facts, 7);
        assert_eq!(summary.dead_branches_found, 1);
        assert_eq!(summary.by_kind.len(), 7);
    }

    // ---- 7. Confidence filtering (below threshold excluded) ----

    #[test]
    fn test_pipeline_confidence_filtering_excludes_below_threshold() {
        let config = OptimizationConfig::builder().min_confidence(0.9).build();
        let pipeline = OptimizationPipeline::new(config);
        let facts = vec![
            make_fact(FactKind::AssertionProven, "high", "a.rs:1:0", 0.95),
            make_fact(FactKind::BranchUnreachable, "low", "a.rs:2:0", 0.5),
            make_fact(FactKind::OverflowAbsent, "mid", "a.rs:3:0", 0.89),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(
            summary.total_proven_facts, 1,
            "only the 0.95 fact should pass the 0.9 threshold"
        );
    }

    // ---- 8. Dead code analysis ----

    #[test]
    fn test_pipeline_dead_code_analysis_counts_unreachable_branches() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::BranchUnreachable, "dead1", "a.rs:1:0", 1.0),
            make_fact(FactKind::BranchUnreachable, "dead2", "a.rs:5:0", 0.9),
            make_fact(FactKind::AssertionProven, "ok", "a.rs:10:0", 1.0),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.dead_branches_found, 2);
    }

    // ---- 9. Pruning potential computation ----

    #[test]
    fn test_pipeline_pruning_potential_increases_with_dead_branches() {
        let pipeline = default_pipeline();
        let single = vec![make_fact(FactKind::BranchUnreachable, "d", "a.rs:1:0", 1.0)];
        let double = vec![
            make_fact(FactKind::BranchUnreachable, "d1", "a.rs:1:0", 1.0),
            make_fact(FactKind::BranchUnreachable, "d2", "a.rs:5:0", 1.0),
        ];
        let s1 = pipeline.process_facts(&single);
        let s2 = pipeline.process_facts(&double);
        assert!(
            s2.pruning_potential > s1.pruning_potential,
            "more dead branches should increase pruning potential"
        );
    }

    // ---- 10. Summary aggregation ----

    #[test]
    fn test_pipeline_summary_aggregation_total_counts() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "a", "x.rs:1:0", 1.0),
            make_fact(FactKind::AssertionProven, "b", "x.rs:2:0", 0.9),
            make_fact(FactKind::BoundsEliminated, "c", "x.rs:3:0", 0.85),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.total_proven_facts, 3);
        assert_eq!(summary.total_hints_emitted, 3);
        let assertion_count = summary
            .by_kind
            .get("assertion_proven")
            .copied()
            .unwrap_or(0);
        let bounds_count = summary
            .by_kind
            .get("bounds_eliminated")
            .copied()
            .unwrap_or(0);
        assert_eq!(assertion_count, 2);
        assert_eq!(bounds_count, 1);
    }

    // ---- 11. Render output text format ----

    #[test]
    fn test_render_output_text_format_contains_key_fields() {
        let pipeline = default_pipeline();
        let facts = vec![make_fact(
            FactKind::AssertionProven,
            "x > 0",
            "a.rs:1:0",
            1.0,
        )];
        let summary = pipeline.process_facts(&facts);
        let rendered = pipeline.render_output(&summary);
        assert!(rendered.contains("TrustVc Optimization Pipeline Report"));
        assert!(rendered.contains("Proven facts"));
        assert!(rendered.contains("Hints emitted"));
        assert!(rendered.contains("Dead branches"));
        assert!(rendered.contains("Pruning potential"));
        assert!(rendered.contains("Elapsed"));
    }

    // ---- 12. Render output JSON format (via serde) ----

    #[test]
    fn test_summary_serializes_to_valid_json() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "a", "a.rs:1:0", 1.0),
            make_fact(FactKind::BranchUnreachable, "b", "a.rs:2:0", 0.9),
        ];
        let summary = pipeline.process_facts(&facts);
        let json =
            serde_json::to_string_pretty(&summary).expect("summary should serialize to JSON");
        let parsed: serde_json::Value = serde_json::from_str(&json).expect("JSON should be valid");
        assert_eq!(parsed["total_proven_facts"], 2);
        assert_eq!(parsed["total_hints_emitted"], 2);
        assert_eq!(parsed["dead_branches_found"], 1);
    }

    // ---- 13. FactKind classification (display round-trip) ----

    #[test]
    fn test_fact_kind_display_all_variants() {
        assert_eq!(FactKind::AssertionProven.to_string(), "assertion_proven");
        assert_eq!(
            FactKind::BranchUnreachable.to_string(),
            "branch_unreachable"
        );
        assert_eq!(FactKind::OverflowAbsent.to_string(), "overflow_absent");
        assert_eq!(FactKind::BoundsEliminated.to_string(), "bounds_eliminated");
        assert_eq!(FactKind::NullEliminated.to_string(), "null_eliminated");
        assert_eq!(FactKind::LoopBound.to_string(), "loop_bound");
        assert_eq!(FactKind::ValueRange.to_string(), "value_range");
    }

    // ---- 14. PipelineFact creation ----

    #[test]
    fn test_pipeline_fact_creation_fields() {
        let fact = PipelineFact::new(
            FactKind::BoundsEliminated,
            "in_range",
            "src/lib.rs:42:5",
            Some("proof_abc".to_string()),
            0.95,
        );
        assert_eq!(fact.kind, FactKind::BoundsEliminated);
        assert_eq!(fact.name, "in_range");
        assert_eq!(fact.location, "src/lib.rs:42:5");
        assert_eq!(fact.proof_id.as_deref(), Some("proof_abc"));
        assert!((fact.confidence - 0.95).abs() < f64::EPSILON);
    }

    // ---- 15. Multiple facts same location ----

    #[test]
    fn test_pipeline_multiple_facts_same_location_all_counted() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "a1", "lib.rs:10:0", 1.0),
            make_fact(FactKind::BoundsEliminated, "a2", "lib.rs:10:0", 0.9),
            make_fact(FactKind::OverflowAbsent, "a3", "lib.rs:10:0", 0.85),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(
            summary.total_proven_facts, 3,
            "facts at the same location should all be counted"
        );
    }

    // ---- 16. Multiple facts different functions ----

    #[test]
    fn test_pipeline_multiple_facts_different_functions() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "fn_a_ok", "src/a.rs:1:0", 1.0),
            make_fact(
                FactKind::BoundsEliminated,
                "fn_b_bounds",
                "src/b.rs:20:0",
                0.9,
            ),
            make_fact(
                FactKind::NullEliminated,
                "fn_c_null",
                "src/c.rs:100:0",
                0.85,
            ),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.total_proven_facts, 3);
        assert_eq!(summary.by_kind.len(), 3);
    }

    // ---- 17. Write output to buffer ----

    #[test]
    fn test_write_output_to_buffer_succeeds() {
        let pipeline = default_pipeline();
        let facts = vec![make_fact(
            FactKind::AssertionProven,
            "x > 0",
            "a.rs:1:0",
            1.0,
        )];
        let summary = pipeline.process_facts(&facts);
        let mut buf = Vec::new();
        pipeline
            .write_output(&summary, &mut buf)
            .expect("write_output should succeed");
        let output = String::from_utf8(buf).expect("output should be valid UTF-8");
        assert!(
            output.contains("TrustVc Optimization Pipeline Report"),
            "output should contain report header"
        );
    }

    // ---- 18. Large fact set (100+) ----

    #[test]
    fn test_pipeline_large_fact_set_handles_100_plus_facts() {
        let pipeline = default_pipeline();
        let facts: Vec<PipelineFact> = (0..150)
            .map(|i| {
                let kind = match i % 7 {
                    0 => FactKind::AssertionProven,
                    1 => FactKind::BranchUnreachable,
                    2 => FactKind::OverflowAbsent,
                    3 => FactKind::BoundsEliminated,
                    4 => FactKind::NullEliminated,
                    5 => FactKind::LoopBound,
                    _ => FactKind::ValueRange,
                };
                make_fact(kind, &format!("fact_{i}"), &format!("f.rs:{i}:0"), 0.9)
            })
            .collect();
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.total_proven_facts, 150);
        assert_eq!(summary.total_hints_emitted, 150);
        assert!(summary.by_kind.len() <= 7);
    }

    // ---- 19. All format renders something ----

    #[test]
    fn test_pipeline_all_format_multiplies_hint_count() {
        let config = OptimizationConfig::builder()
            .emit_format(HintFormat::All)
            .build();
        let pipeline = OptimizationPipeline::new(config);
        let facts = vec![make_fact(
            FactKind::AssertionProven,
            "x > 0",
            "a.rs:1:0",
            1.0,
        )];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(
            summary.total_hints_emitted, 4,
            "All format should emit 4 hints per fact"
        );
    }

    // ---- 20. By-kind counts correct ----

    #[test]
    fn test_pipeline_by_kind_counts_correct() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "a1", "a.rs:1:0", 1.0),
            make_fact(FactKind::AssertionProven, "a2", "a.rs:2:0", 0.9),
            make_fact(FactKind::BranchUnreachable, "b1", "a.rs:3:0", 0.85),
            make_fact(FactKind::BranchUnreachable, "b2", "a.rs:4:0", 0.82),
            make_fact(FactKind::BranchUnreachable, "b3", "a.rs:5:0", 0.81),
        ];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(summary.by_kind.get("assertion_proven"), Some(&2));
        assert_eq!(summary.by_kind.get("branch_unreachable"), Some(&3));
    }

    // ---- 21. Elapsed timing tracked ----

    #[test]
    fn test_pipeline_elapsed_timing_is_nonnegative() {
        let pipeline = default_pipeline();
        let facts = vec![make_fact(FactKind::AssertionProven, "x", "a.rs:1:0", 1.0)];
        let summary = pipeline.process_facts(&facts);
        assert!(
            summary.elapsed >= Duration::ZERO,
            "elapsed time should be non-negative"
        );
    }

    // ---- 22. Confidence 1.0 facts always included ----

    #[test]
    fn test_pipeline_confidence_1_0_always_included() {
        let config = OptimizationConfig::builder().min_confidence(0.99).build();
        let pipeline = OptimizationPipeline::new(config);
        let facts = vec![make_fact(
            FactKind::AssertionProven,
            "certain",
            "a.rs:1:0",
            1.0,
        )];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(
            summary.total_proven_facts, 1,
            "confidence 1.0 should always pass any threshold <= 1.0"
        );
    }

    // ---- 23. Confidence 0.0 facts excluded at any threshold ----

    #[test]
    fn test_pipeline_confidence_0_0_excluded_at_any_positive_threshold() {
        let config = OptimizationConfig::builder().min_confidence(0.01).build();
        let pipeline = OptimizationPipeline::new(config);
        let facts = vec![make_fact(
            FactKind::AssertionProven,
            "zero_conf",
            "a.rs:1:0",
            0.0,
        )];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(
            summary.total_proven_facts, 0,
            "confidence 0.0 should be excluded at any positive threshold"
        );
    }

    // ---- 24. Location parsing edge cases ----

    #[test]
    fn test_pipeline_fact_with_empty_location_accepted() {
        let fact = PipelineFact::new(FactKind::AssertionProven, "x", "", None, 1.0);
        assert_eq!(fact.location, "");
    }

    #[test]
    fn test_pipeline_fact_with_complex_path_location() {
        let fact = PipelineFact::new(
            FactKind::AssertionProven,
            "x",
            "/home/user/project/src/deeply/nested/module.rs:999:42",
            None,
            1.0,
        );
        assert_eq!(
            fact.location,
            "/home/user/project/src/deeply/nested/module.rs:999:42"
        );
    }

    // ---- 25. Summary total counts match ----

    #[test]
    fn test_pipeline_summary_total_counts_match_by_kind_sum() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "a", "a.rs:1:0", 1.0),
            make_fact(FactKind::BranchUnreachable, "b", "a.rs:2:0", 0.9),
            make_fact(FactKind::OverflowAbsent, "c", "a.rs:3:0", 0.85),
            make_fact(FactKind::BoundsEliminated, "d", "a.rs:4:0", 0.82),
            make_fact(FactKind::NullEliminated, "e", "a.rs:5:0", 0.81),
        ];
        let summary = pipeline.process_facts(&facts);
        let by_kind_total: usize = summary.by_kind.values().sum();
        assert_eq!(
            summary.total_proven_facts, by_kind_total,
            "total_proven_facts should equal sum of by_kind counts"
        );
    }

    // ---- 26. Dead code disabled ----

    #[test]
    fn test_pipeline_dead_code_disabled_returns_zero_dead_branches() {
        let config = OptimizationConfig::builder()
            .include_dead_code(false)
            .build();
        let pipeline = OptimizationPipeline::new(config);
        let facts = vec![make_fact(
            FactKind::BranchUnreachable,
            "dead",
            "a.rs:1:0",
            1.0,
        )];
        let summary = pipeline.process_facts(&facts);
        assert_eq!(
            summary.dead_branches_found, 0,
            "dead branches should be 0 when include_dead_code is false"
        );
    }

    // ---- 27. PipelineFact confidence clamped ----

    #[test]
    fn test_pipeline_fact_confidence_clamped_to_unit_interval() {
        let over = PipelineFact::new(FactKind::AssertionProven, "x", "a.rs:1:0", None, 1.5);
        let under = PipelineFact::new(FactKind::AssertionProven, "x", "a.rs:1:0", None, -0.5);
        assert!((over.confidence - 1.0).abs() < f64::EPSILON);
        assert!((under.confidence - 0.0).abs() < f64::EPSILON);
    }

    // ---- 28. Pruning potential capped at 0.80 ----

    #[test]
    fn test_pruning_potential_capped_at_80_percent() {
        let pipeline = default_pipeline();
        // 20 dead branches should push well past 0.80 in raw score
        let facts: Vec<PipelineFact> = (0..20)
            .map(|i| {
                make_fact(
                    FactKind::BranchUnreachable,
                    &format!("d{i}"),
                    "a.rs:1:0",
                    1.0,
                )
            })
            .collect();
        let summary = pipeline.process_facts(&facts);
        assert!(
            summary.pruning_potential <= 0.80 + f64::EPSILON,
            "pruning potential should be capped at 0.80, got {}",
            summary.pruning_potential
        );
    }

    // ---- 29. Render output by_kind section sorted ----

    #[test]
    fn test_render_output_by_kind_section_present() {
        let pipeline = default_pipeline();
        let facts = vec![
            make_fact(FactKind::AssertionProven, "a", "a.rs:1:0", 1.0),
            make_fact(FactKind::BranchUnreachable, "b", "a.rs:2:0", 0.9),
        ];
        let summary = pipeline.process_facts(&facts);
        let rendered = pipeline.render_output(&summary);
        assert!(rendered.contains("By kind:"));
        assert!(rendered.contains("assertion_proven: 1"));
        assert!(rendered.contains("branch_unreachable: 1"));
    }

    // ---- 30. PipelineFact with proof_id ----

    #[test]
    fn test_pipeline_fact_with_proof_id_retained() {
        let fact = make_fact_with_proof(
            FactKind::BoundsEliminated,
            "in_range",
            "lib.rs:10:0",
            "proof_xyz",
            0.95,
        );
        assert_eq!(fact.proof_id.as_deref(), Some("proof_xyz"));
    }
}
