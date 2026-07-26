// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

//! LLVM metadata generation and dead-code elimination hints from proven facts.
//!
//! When trust_vc proves assertions, branch conditions, overflow absence, or
//! bounds-check validity, this module translates those proofs into LLVM IR
//! metadata strings and dead-code analysis reports.  A downstream LLVM pass can
//! consume these metadata nodes to eliminate redundant checks, mark cold paths,
//! or insert `__builtin_unreachable()` on provably-dead branches.

use std::collections::HashMap;
use std::fmt::{self, Write as _};

use serde::{Deserialize, Serialize};
use trust_vc_core::proven_facts::ProvenFact;

// ---------------------------------------------------------------------------
// LlvmMetadataKind
// ---------------------------------------------------------------------------

/// Classification of an LLVM metadata node derived from a proven fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum LlvmMetadataKind {
    /// A user-written assertion was proven true.
    AssertionProven,
    /// A branch condition was proven always-false (the branch is dead).
    BranchUnreachable,
    /// Arithmetic overflow was proven absent for the given operation.
    OverflowAbsent,
    /// A bounds check was proven always-in-range and can be eliminated.
    BoundsCheckEliminated,
    /// A null/Option check was proven always-Some/non-null.
    NullCheckEliminated,
    /// A loop bound is statically known.
    LoopBoundKnown,
    /// A value range is statically proven (e.g., `0 <= x < 256`).
    ValueRangeKnown,
}

impl fmt::Display for LlvmMetadataKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::AssertionProven => "assertion_proven",
            Self::BranchUnreachable => "branch_unreachable",
            Self::OverflowAbsent => "overflow_absent",
            Self::BoundsCheckEliminated => "bounds_check_eliminated",
            Self::NullCheckEliminated => "null_check_eliminated",
            Self::LoopBoundKnown => "loop_bound_known",
            Self::ValueRangeKnown => "value_range_known",
        };
        write!(f, "{label}")
    }
}

impl LlvmMetadataKind {
    /// Parse from the Display string representation.
    #[must_use]
    fn from_str_repr(s: &str) -> Option<Self> {
        match s {
            "assertion_proven" => Some(Self::AssertionProven),
            "branch_unreachable" => Some(Self::BranchUnreachable),
            "overflow_absent" => Some(Self::OverflowAbsent),
            "bounds_check_eliminated" => Some(Self::BoundsCheckEliminated),
            "null_check_eliminated" => Some(Self::NullCheckEliminated),
            "loop_bound_known" => Some(Self::LoopBoundKnown),
            "value_range_known" => Some(Self::ValueRangeKnown),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// SourceLoc
// ---------------------------------------------------------------------------

/// Source location: file path, line number, column number.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct SourceLoc {
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) column: usize,
}

impl SourceLoc {
    /// Creates a new source location.
    #[must_use]
    pub(crate) fn new(file: impl Into<String>, line: usize, column: usize) -> Self {
        Self {
            file: file.into(),
            line,
            column,
        }
    }

    /// Parse a location string like `"src/lib.rs:42:5"`.
    ///
    /// Returns `None` if the string does not match the expected `file:line:col`
    /// pattern.
    #[must_use]
    pub(crate) fn parse(s: &str) -> Option<Self> {
        let trimmed = s.trim();
        let last_colon = trimmed.rfind(':')?;
        let column: usize = trimmed[last_colon + 1..].parse().ok()?;
        let rest = &trimmed[..last_colon];
        let second_colon = rest.rfind(':')?;
        let line: usize = rest[second_colon + 1..].parse().ok()?;
        let file = rest[..second_colon].to_string();
        if file.is_empty() {
            return None;
        }
        Some(Self { file, line, column })
    }
}

impl fmt::Display for SourceLoc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

// ---------------------------------------------------------------------------
// LlvmMetadata
// ---------------------------------------------------------------------------

/// A single LLVM metadata node derived from a proven verification fact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) struct LlvmMetadata {
    /// The kind of metadata (what was proven).
    pub(crate) kind: LlvmMetadataKind,
    /// The function this metadata applies to.
    pub(crate) function_name: String,
    /// Source location in the original Rust code.
    pub(crate) location: SourceLoc,
    /// Optional proof identifier for traceability.
    pub(crate) proof_id: Option<String>,
    /// The rendered LLVM IR metadata string.
    pub(crate) metadata_string: String,
}

// ---------------------------------------------------------------------------
// GeneratorStats
// ---------------------------------------------------------------------------

/// Statistics tracked by the hint generator.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub(crate) struct GeneratorStats {
    /// Total number of input facts.
    pub(crate) total_facts: usize,
    /// Number of facts that were successfully classified.
    pub(crate) classified: usize,
    /// Number of facts that could not be classified (missing location, etc.).
    pub(crate) unclassifiable: usize,
}

// ---------------------------------------------------------------------------
// LlvmHintGenerator
// ---------------------------------------------------------------------------

/// Translates proven verification facts into LLVM metadata nodes.
///
/// The generator classifies each [`ProvenFact`] into an [`LlvmMetadataKind`]
/// using heuristic pattern matching on the expression string, then renders the
/// corresponding LLVM IR metadata string.
pub(crate) struct LlvmHintGenerator {
    facts: Vec<ProvenFact>,
}

impl LlvmHintGenerator {
    /// Creates a new generator from a list of proven facts.
    #[must_use]
    pub(crate) fn new(facts: Vec<ProvenFact>) -> Self {
        Self { facts }
    }

    /// Classify a proven fact expression into an [`LlvmMetadataKind`].
    #[must_use]
    fn classify(fact: &ProvenFact) -> LlvmMetadataKind {
        let expr = fact.expression().trim();

        // Overflow-related patterns.
        if Self::is_overflow_expression(expr) {
            return LlvmMetadataKind::OverflowAbsent;
        }

        // Loop bound patterns.
        if Self::is_loop_bound_expression(expr) {
            return LlvmMetadataKind::LoopBoundKnown;
        }

        // Value range patterns.
        if Self::is_value_range_expression(expr) {
            return LlvmMetadataKind::ValueRangeKnown;
        }

        // Bounds check patterns.
        if Self::is_bounds_expression(expr) {
            return LlvmMetadataKind::BoundsCheckEliminated;
        }

        // Null/Option check patterns.
        if Self::is_null_check_expression(expr) {
            return LlvmMetadataKind::NullCheckEliminated;
        }

        // Invariant with a "false" branch or "unreachable" token.
        if Self::is_branch_unreachable_expression(expr) {
            return LlvmMetadataKind::BranchUnreachable;
        }

        // Default: assertion proven.
        LlvmMetadataKind::AssertionProven
    }

    fn is_overflow_expression(expr: &str) -> bool {
        let keywords = [
            "no_overflow",
            "overflow",
            "wrapping",
            "saturating",
            "checked_add",
            "checked_sub",
            "checked_mul",
        ];
        keywords.iter().any(|kw| expr.contains(kw))
    }

    fn is_loop_bound_expression(expr: &str) -> bool {
        let has_loop_keyword = expr.contains("loop_bound")
            || expr.contains("iteration")
            || expr.contains("trip_count");
        let has_range_syntax =
            expr.contains("..") && (expr.contains("for") || expr.contains("while"));
        has_loop_keyword || has_range_syntax
    }

    fn is_value_range_expression(expr: &str) -> bool {
        // Patterns like `0 <= x && x < 256` or `x in 0..N`.
        let has_range = expr.contains("..") && !expr.contains("for") && !expr.contains("while");
        let has_double_bound = (expr.contains("<=") || expr.contains(">=")) && expr.contains("&&");
        has_range || has_double_bound
    }

    fn is_bounds_expression(expr: &str) -> bool {
        let keywords = [".len()", "index", "offset", "capacity", "bound", "size"];
        let has_keyword = keywords.iter().any(|kw| expr.contains(kw));
        let has_comparison = expr.contains('<') || expr.contains("<=") || expr.contains(">=");
        has_keyword && has_comparison
    }

    fn is_null_check_expression(expr: &str) -> bool {
        let patterns = [
            "is_some()",
            "is_none()",
            "!= None",
            "!= null",
            "is_null()",
            "is_ok()",
        ];
        patterns.iter().any(|p| expr.contains(p))
    }

    fn is_branch_unreachable_expression(expr: &str) -> bool {
        expr.contains("unreachable")
            || expr.contains("false_branch")
            || expr == "false"
            || expr.contains("dead_code")
    }

    /// Extract a function name from the step label or fall back to `"<unknown>"`.
    fn extract_function_name(fact: &ProvenFact) -> String {
        let label = fact.step_label();
        // Convention: step labels often look like `fn_name::assertion_name` or
        // `fn_name.assertion_name`.
        if let Some(idx) = label.find("::") {
            return label[..idx].to_string();
        }
        if let Some(idx) = label.find('.') {
            return label[..idx].to_string();
        }
        label.to_string()
    }

    /// Generate the LLVM IR metadata string for a classified fact.
    #[must_use]
    fn render_metadata_string(kind: LlvmMetadataKind, fact: &ProvenFact) -> String {
        let kind_str = kind.to_string();
        let expr = fact.expression();
        match kind {
            LlvmMetadataKind::ValueRangeKnown => {
                format!("!{{!\"trust_vc.proven\", !\"value_range\", !\"{expr}\", i32 1}}")
            }
            LlvmMetadataKind::LoopBoundKnown => {
                format!("!{{!\"trust_vc.proven\", !\"loop_bound\", !\"{expr}\", i32 1}}")
            }
            _ => {
                format!("!{{!\"trust_vc.proven\", !\"{kind_str}\", i32 1}}")
            }
        }
    }

    /// Generate an `__builtin_unreachable()` stub annotation for a proven
    /// unreachable branch.
    #[must_use]
    fn render_unreachable_stub(loc: &SourceLoc, expr: &str) -> String {
        format!(
            "// At {loc}\n\
             // SAFETY: trust_vc proved branch `{expr}` is unreachable.\n\
             __builtin_unreachable();"
        )
    }

    /// Run the full generation pipeline, producing metadata nodes and stats.
    #[must_use]
    pub(crate) fn generate(&self) -> (Vec<LlvmMetadata>, GeneratorStats) {
        let mut nodes = Vec::new();
        let mut stats = GeneratorStats {
            total_facts: self.facts.len(),
            ..Default::default()
        };

        for fact in &self.facts {
            let loc_str = match fact.source_location() {
                Some(s) => s,
                None => {
                    stats.unclassifiable += 1;
                    continue;
                }
            };

            let location = match SourceLoc::parse(loc_str) {
                Some(l) => l,
                None => {
                    stats.unclassifiable += 1;
                    continue;
                }
            };

            let kind = Self::classify(fact);
            let function_name = Self::extract_function_name(fact);
            let metadata_string = Self::render_metadata_string(kind, fact);

            nodes.push(LlvmMetadata {
                kind,
                function_name,
                location,
                proof_id: Some(fact.step_label().to_string()),
                metadata_string,
            });

            stats.classified += 1;
        }

        (nodes, stats)
    }
}

// ---------------------------------------------------------------------------
// DeadCodeAnalysis
// ---------------------------------------------------------------------------

/// Analysis of dead (provably unreachable) branches.
///
/// Given proven branch facts, identifies which branches are dead and computes
/// a pruning potential score indicating how much code can be eliminated.
pub(crate) struct DeadCodeAnalysis {
    dead_branches: Vec<DeadBranch>,
    total_branch_facts: usize,
}

/// A single dead branch identified by the analysis.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DeadBranch {
    pub(crate) location: SourceLoc,
    pub(crate) expression: String,
    pub(crate) suggestion: DeadBranchSuggestion,
}

/// Suggested action for a dead branch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) enum DeadBranchSuggestion {
    /// Mark the function/block as `#[cold]`.
    Cold,
    /// Replace with `unsafe { core::hint::unreachable_unchecked() }`.
    UnreachableUnchecked,
}

impl fmt::Display for DeadBranchSuggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cold => write!(f, "#[cold]"),
            Self::UnreachableUnchecked => {
                write!(f, "unsafe {{ core::hint::unreachable_unchecked() }}")
            }
        }
    }
}

impl DeadCodeAnalysis {
    /// Creates a new dead-code analysis from a set of metadata nodes.
    ///
    /// Only nodes classified as `BranchUnreachable` or `AssertionProven` (whose
    /// expression is `"false"`) contribute to dead branches.
    #[must_use]
    pub(crate) fn new(nodes: &[LlvmMetadata]) -> Self {
        let branch_nodes: Vec<&LlvmMetadata> = nodes
            .iter()
            .filter(|n| {
                n.kind == LlvmMetadataKind::BranchUnreachable
                    || (n.kind == LlvmMetadataKind::AssertionProven && Self::is_false_assertion(n))
            })
            .collect();

        let total_branch_facts = branch_nodes.len();

        let dead_branches = branch_nodes
            .iter()
            .map(|node| {
                let suggestion = if node.metadata_string.contains("branch_unreachable") {
                    DeadBranchSuggestion::UnreachableUnchecked
                } else {
                    DeadBranchSuggestion::Cold
                };
                DeadBranch {
                    location: node.location.clone(),
                    expression: Self::extract_expression_from_metadata(node),
                    suggestion,
                }
            })
            .collect();

        Self {
            dead_branches,
            total_branch_facts,
        }
    }

    fn is_false_assertion(node: &LlvmMetadata) -> bool {
        node.metadata_string.contains("false")
    }

    fn extract_expression_from_metadata(node: &LlvmMetadata) -> String {
        // The proof_id typically carries the step label which encodes the
        // expression context.
        node.proof_id
            .clone()
            .unwrap_or_else(|| "<unknown>".to_string())
    }

    /// Returns the list of identified dead branches.
    #[must_use]
    pub(crate) fn dead_branches(&self) -> &[DeadBranch] {
        &self.dead_branches
    }

    /// Number of dead branches found.
    #[must_use]
    pub(crate) fn dead_branch_count(&self) -> usize {
        self.dead_branches.len()
    }

    /// Compute the pruning potential score in the range `[0.0, 1.0]`.
    ///
    /// The score represents the fraction of analyzed branch facts that are
    /// provably dead.  Returns `0.0` when there are no branch facts (avoids
    /// division by zero).
    #[must_use]
    pub(crate) fn pruning_potential(&self, total_nodes: usize) -> f64 {
        if total_nodes == 0 {
            return 0.0;
        }
        self.dead_branches.len() as f64 / total_nodes as f64
    }

    /// Generate cold-path suggestions as human-readable strings.
    #[must_use]
    pub(crate) fn cold_path_suggestions(&self) -> Vec<String> {
        self.dead_branches
            .iter()
            .filter(|b| b.suggestion == DeadBranchSuggestion::Cold)
            .map(|b| format!("At {}: suggest {}", b.location, b.suggestion))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// HintReport
// ---------------------------------------------------------------------------

/// Aggregated report of LLVM hints and dead-code analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct HintReport {
    /// Total number of LLVM metadata hints generated.
    pub(crate) total_hints: usize,
    /// Count of hints by kind.
    pub(crate) by_kind: HashMap<String, usize>,
    /// Number of dead branches identified.
    pub(crate) dead_branches: usize,
    /// Pruning potential score (0.0 to 1.0).
    pub(crate) pruning_potential: f64,
}

impl HintReport {
    /// Build a report from generated metadata nodes and a dead-code analysis.
    #[must_use]
    pub(crate) fn from_parts(nodes: &[LlvmMetadata], analysis: &DeadCodeAnalysis) -> Self {
        let mut by_kind: HashMap<String, usize> = HashMap::new();
        for node in nodes {
            *by_kind.entry(node.kind.to_string()).or_insert(0) += 1;
        }

        Self {
            total_hints: nodes.len(),
            by_kind,
            dead_branches: analysis.dead_branch_count(),
            pruning_potential: analysis.pruning_potential(nodes.len()),
        }
    }

    /// Render a human-readable summary of the report.
    #[must_use]
    pub(crate) fn render_summary(&self) -> String {
        let mut out = String::new();
        out.push_str("LLVM Hint Report\n");
        out.push_str("================\n");
        let _ = writeln!(out, "Total hints:       {}", self.total_hints);
        let _ = writeln!(out, "Dead branches:     {}", self.dead_branches);
        let _ = writeln!(
            out,
            "Pruning potential: {:.1}%",
            self.pruning_potential * 100.0
        );

        if !self.by_kind.is_empty() {
            out.push_str("\nBy kind:\n");
            let mut sorted: Vec<_> = self.by_kind.iter().collect();
            sorted.sort_by_key(|(k, _)| *k);
            for (kind, count) in sorted {
                let _ = writeln!(out, "  {kind}: {count}");
            }
        }

        out
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_core::proven_facts::{ProvenFact, ProvenFactKind};

    // -- LlvmMetadataKind display and round-trip --

    #[test]
    fn test_metadata_kind_display_all_variants() {
        assert_eq!(
            LlvmMetadataKind::AssertionProven.to_string(),
            "assertion_proven"
        );
        assert_eq!(
            LlvmMetadataKind::BranchUnreachable.to_string(),
            "branch_unreachable"
        );
        assert_eq!(
            LlvmMetadataKind::OverflowAbsent.to_string(),
            "overflow_absent"
        );
        assert_eq!(
            LlvmMetadataKind::BoundsCheckEliminated.to_string(),
            "bounds_check_eliminated"
        );
        assert_eq!(
            LlvmMetadataKind::NullCheckEliminated.to_string(),
            "null_check_eliminated"
        );
        assert_eq!(
            LlvmMetadataKind::LoopBoundKnown.to_string(),
            "loop_bound_known"
        );
        assert_eq!(
            LlvmMetadataKind::ValueRangeKnown.to_string(),
            "value_range_known"
        );
    }

    #[test]
    fn test_metadata_kind_round_trip_via_string() {
        let kinds = [
            LlvmMetadataKind::AssertionProven,
            LlvmMetadataKind::BranchUnreachable,
            LlvmMetadataKind::OverflowAbsent,
            LlvmMetadataKind::BoundsCheckEliminated,
            LlvmMetadataKind::NullCheckEliminated,
            LlvmMetadataKind::LoopBoundKnown,
            LlvmMetadataKind::ValueRangeKnown,
        ];
        for kind in &kinds {
            let s = kind.to_string();
            let back = LlvmMetadataKind::from_str_repr(&s)
                .unwrap_or_else(|| panic!("failed to round-trip {kind}"));
            assert_eq!(*kind, back);
        }
    }

    // -- SourceLoc parsing --

    #[test]
    fn test_source_loc_parse_valid() {
        let loc = SourceLoc::parse("src/lib.rs:42:5").unwrap();
        assert_eq!(loc.file, "src/lib.rs");
        assert_eq!(loc.line, 42);
        assert_eq!(loc.column, 5);
    }

    #[test]
    fn test_source_loc_parse_trims_whitespace() {
        let loc = SourceLoc::parse("  src/main.rs:10:1  ").unwrap();
        assert_eq!(loc.file, "src/main.rs");
        assert_eq!(loc.line, 10);
        assert_eq!(loc.column, 1);
    }

    #[test]
    fn test_source_loc_parse_invalid_no_colons() {
        assert!(SourceLoc::parse("no_colons_here").is_none());
    }

    #[test]
    fn test_source_loc_parse_invalid_non_numeric_line() {
        assert!(SourceLoc::parse("file.rs:abc:5").is_none());
    }

    #[test]
    fn test_source_loc_parse_invalid_empty_file() {
        assert!(SourceLoc::parse(":10:5").is_none());
    }

    #[test]
    fn test_source_loc_display_round_trip() {
        let loc = SourceLoc::new("src/lib.rs", 42, 5);
        assert_eq!(loc.to_string(), "src/lib.rs:42:5");
        let reparsed = SourceLoc::parse(&loc.to_string()).unwrap();
        assert_eq!(loc, reparsed);
    }

    #[test]
    fn test_source_loc_ordering() {
        let a = SourceLoc::new("a.rs", 1, 1);
        let b = SourceLoc::new("a.rs", 1, 5);
        let c = SourceLoc::new("a.rs", 10, 1);
        let d = SourceLoc::new("b.rs", 1, 1);
        assert!(a < b);
        assert!(b < c);
        assert!(c < d);
    }

    // -- Generator with empty facts --

    #[test]
    fn test_generator_empty_facts() {
        let generator = LlvmHintGenerator::new(vec![]);
        let (nodes, stats) = generator.generate();
        assert!(nodes.is_empty());
        assert_eq!(stats.total_facts, 0);
        assert_eq!(stats.classified, 0);
        assert_eq!(stats.unclassifiable, 0);
    }

    // -- Generator classifying assertion-proven facts --

    #[test]
    fn test_generator_classifies_assertion_proven() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:10:5".to_string()),
            "positive_guard",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, stats) = generator.generate();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].kind, LlvmMetadataKind::AssertionProven);
        assert_eq!(nodes[0].function_name, "positive_guard");
        assert_eq!(stats.classified, 1);
        assert_eq!(stats.unclassifiable, 0);
    }

    // -- Generator classifying overflow-absent facts --

    #[test]
    fn test_generator_classifies_overflow_absent() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "no_overflow(a + b)",
            Some("src/arith.rs:5:1".to_string()),
            "add_check",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].kind, LlvmMetadataKind::OverflowAbsent);
    }

    // -- Generator classifying bounds-check facts --

    #[test]
    fn test_generator_classifies_bounds_check() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/loop.rs:20:9".to_string()),
            "loop_idx",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].kind, LlvmMetadataKind::BoundsCheckEliminated);
    }

    // -- Metadata string format correctness --

    #[test]
    fn test_metadata_string_format_assertion() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:1:1".to_string()),
            "step1",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(
            nodes[0].metadata_string,
            "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}"
        );
    }

    #[test]
    fn test_metadata_string_format_value_range() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "0 <= x && x < 256",
            Some("src/lib.rs:5:1".to_string()),
            "range_check",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes[0].kind, LlvmMetadataKind::ValueRangeKnown);
        assert!(nodes[0].metadata_string.contains("value_range"));
        assert!(nodes[0].metadata_string.contains("0 <= x && x < 256"));
    }

    #[test]
    fn test_metadata_string_format_loop_bound() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Invariant,
            "loop_bound <= 100",
            Some("src/lib.rs:3:1".to_string()),
            "bound_step",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes[0].kind, LlvmMetadataKind::LoopBoundKnown);
        assert!(nodes[0].metadata_string.contains("loop_bound"));
    }

    // -- DeadCodeAnalysis with no dead branches --

    #[test]
    fn test_dead_code_analysis_no_dead_branches() {
        let nodes = vec![LlvmMetadata {
            kind: LlvmMetadataKind::AssertionProven,
            function_name: "foo".to_string(),
            location: SourceLoc::new("a.rs", 1, 1),
            proof_id: Some("step1".to_string()),
            metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}".to_string(),
        }];
        let analysis = DeadCodeAnalysis::new(&nodes);
        assert_eq!(analysis.dead_branch_count(), 0);
        assert!(analysis.dead_branches().is_empty());
    }

    // -- DeadCodeAnalysis with proven false branches --

    #[test]
    fn test_dead_code_analysis_unreachable_branches() {
        let nodes = vec![
            LlvmMetadata {
                kind: LlvmMetadataKind::BranchUnreachable,
                function_name: "foo".to_string(),
                location: SourceLoc::new("a.rs", 10, 1),
                proof_id: Some("dead_branch".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"branch_unreachable\", i32 1}"
                    .to_string(),
            },
            LlvmMetadata {
                kind: LlvmMetadataKind::AssertionProven,
                function_name: "bar".to_string(),
                location: SourceLoc::new("b.rs", 5, 1),
                proof_id: Some("ok_assert".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}"
                    .to_string(),
            },
        ];
        let analysis = DeadCodeAnalysis::new(&nodes);
        assert_eq!(analysis.dead_branch_count(), 1);
        assert_eq!(
            analysis.dead_branches()[0].suggestion,
            DeadBranchSuggestion::UnreachableUnchecked
        );
    }

    // -- DeadCodeAnalysis pruning potential calculation --

    #[test]
    fn test_dead_code_pruning_potential_zero_when_no_nodes() {
        let analysis = DeadCodeAnalysis::new(&[]);
        assert!((analysis.pruning_potential(0) - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_dead_code_pruning_potential_half() {
        let nodes = vec![
            LlvmMetadata {
                kind: LlvmMetadataKind::BranchUnreachable,
                function_name: "f".to_string(),
                location: SourceLoc::new("a.rs", 1, 1),
                proof_id: Some("dead".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"branch_unreachable\", i32 1}"
                    .to_string(),
            },
            LlvmMetadata {
                kind: LlvmMetadataKind::AssertionProven,
                function_name: "g".to_string(),
                location: SourceLoc::new("a.rs", 5, 1),
                proof_id: Some("ok".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}"
                    .to_string(),
            },
        ];
        let analysis = DeadCodeAnalysis::new(&nodes);
        // 1 dead out of 2 total nodes.
        let potential = analysis.pruning_potential(nodes.len());
        assert!((potential - 0.5).abs() < f64::EPSILON);
    }

    // -- HintReport aggregation --

    #[test]
    fn test_hint_report_aggregation() {
        let nodes = vec![
            LlvmMetadata {
                kind: LlvmMetadataKind::AssertionProven,
                function_name: "f".to_string(),
                location: SourceLoc::new("a.rs", 1, 1),
                proof_id: Some("s1".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}"
                    .to_string(),
            },
            LlvmMetadata {
                kind: LlvmMetadataKind::BoundsCheckEliminated,
                function_name: "f".to_string(),
                location: SourceLoc::new("a.rs", 5, 1),
                proof_id: Some("s2".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"bounds_check_eliminated\", i32 1}"
                    .to_string(),
            },
            LlvmMetadata {
                kind: LlvmMetadataKind::AssertionProven,
                function_name: "g".to_string(),
                location: SourceLoc::new("b.rs", 1, 1),
                proof_id: Some("s3".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}"
                    .to_string(),
            },
        ];
        let analysis = DeadCodeAnalysis::new(&nodes);
        let report = HintReport::from_parts(&nodes, &analysis);
        assert_eq!(report.total_hints, 3);
        assert_eq!(*report.by_kind.get("assertion_proven").unwrap(), 2);
        assert_eq!(*report.by_kind.get("bounds_check_eliminated").unwrap(), 1);
        assert_eq!(report.dead_branches, 0);
    }

    // -- HintReport summary rendering --

    #[test]
    fn test_hint_report_render_summary() {
        let nodes = vec![LlvmMetadata {
            kind: LlvmMetadataKind::AssertionProven,
            function_name: "f".to_string(),
            location: SourceLoc::new("a.rs", 1, 1),
            proof_id: Some("s1".to_string()),
            metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}".to_string(),
        }];
        let analysis = DeadCodeAnalysis::new(&nodes);
        let report = HintReport::from_parts(&nodes, &analysis);
        let summary = report.render_summary();
        assert!(summary.contains("LLVM Hint Report"));
        assert!(summary.contains("Total hints:       1"));
        assert!(summary.contains("Dead branches:     0"));
        assert!(summary.contains("Pruning potential:"));
        assert!(summary.contains("assertion_proven: 1"));
    }

    // -- Generator statistics tracking --

    #[test]
    fn test_generator_stats_tracking_mixed() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("a.rs:1:1".to_string()),
                "s1",
            ),
            // No location -> unclassifiable.
            ProvenFact::new(ProvenFactKind::Assertion, "y > 0", None, "s2"),
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "i < arr.len()",
                Some("a.rs:5:1".to_string()),
                "s3",
            ),
        ];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, stats) = generator.generate();
        assert_eq!(stats.total_facts, 3);
        assert_eq!(stats.classified, 2);
        assert_eq!(stats.unclassifiable, 1);
        assert_eq!(nodes.len(), 2);
    }

    // -- Multiple facts same function --

    #[test]
    fn test_generator_multiple_facts_same_function() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("a.rs:1:1".to_string()),
                "foo::guard1",
            ),
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "y > 0",
                Some("a.rs:2:1".to_string()),
                "foo::guard2",
            ),
        ];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes.len(), 2);
        assert_eq!(nodes[0].function_name, "foo");
        assert_eq!(nodes[1].function_name, "foo");
    }

    // -- Facts across different functions --

    #[test]
    fn test_generator_facts_across_different_functions() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "a > 0",
                Some("a.rs:1:1".to_string()),
                "alpha::check",
            ),
            ProvenFact::new(
                ProvenFactKind::Postcondition,
                "result == 42",
                Some("b.rs:10:1".to_string()),
                "beta::ensure",
            ),
        ];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes.len(), 2);
        assert_eq!(nodes[0].function_name, "alpha");
        assert_eq!(nodes[1].function_name, "beta");
    }

    // -- Unknown fact kinds handled gracefully --

    #[test]
    fn test_generator_unknown_expression_defaults_to_assertion() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Postcondition,
            "some_complex_expression(a, b, c)",
            Some("src/lib.rs:50:1".to_string()),
            "complex_step",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, stats) = generator.generate();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].kind, LlvmMetadataKind::AssertionProven);
        assert_eq!(stats.classified, 1);
    }

    // -- NullCheckEliminated metadata --

    #[test]
    fn test_generator_classifies_null_check() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Precondition,
            "arg.is_some()",
            Some("src/api.rs:3:1".to_string()),
            "notnull_pre",
        )];
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, _) = generator.generate();
        assert_eq!(nodes.len(), 1);
        assert_eq!(nodes[0].kind, LlvmMetadataKind::NullCheckEliminated);
    }

    // -- Cold path suggestion generation --

    #[test]
    fn test_cold_path_suggestions_generated() {
        // An AssertionProven with "false" in metadata triggers Cold suggestion.
        let nodes = vec![LlvmMetadata {
            kind: LlvmMetadataKind::AssertionProven,
            function_name: "f".to_string(),
            location: SourceLoc::new("a.rs", 10, 1),
            proof_id: Some("dead_path".to_string()),
            metadata_string: "!{!\"trust_vc.proven\", !\"false\", i32 1}".to_string(),
        }];
        let analysis = DeadCodeAnalysis::new(&nodes);
        assert_eq!(analysis.dead_branch_count(), 1);
        let suggestions = analysis.cold_path_suggestions();
        assert_eq!(suggestions.len(), 1);
        assert!(suggestions[0].contains("#[cold]"));
        assert!(suggestions[0].contains("a.rs:10:1"));
    }

    // -- Large batch processing (100+ facts) --

    #[test]
    fn test_generator_large_batch_processing() {
        let facts: Vec<ProvenFact> = (0..150)
            .map(|i| {
                ProvenFact::new(
                    ProvenFactKind::Assertion,
                    format!("x_{i} > 0"),
                    Some(format!("src/batch.rs:{i}:1")),
                    format!("batch_step_{i}"),
                )
            })
            .collect();
        let generator = LlvmHintGenerator::new(facts);
        let (nodes, stats) = generator.generate();
        assert_eq!(nodes.len(), 150);
        assert_eq!(stats.total_facts, 150);
        assert_eq!(stats.classified, 150);
        assert_eq!(stats.unclassifiable, 0);
    }

    // -- Idempotent regeneration --

    #[test]
    fn test_generator_idempotent_regeneration() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("a.rs:1:1".to_string()),
                "s1",
            ),
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "i < arr.len()",
                Some("a.rs:5:1".to_string()),
                "s2",
            ),
        ];
        let generator = LlvmHintGenerator::new(facts.clone());
        let (nodes1, stats1) = generator.generate();
        let gen2 = LlvmHintGenerator::new(facts);
        let (nodes2, stats2) = gen2.generate();
        assert_eq!(nodes1, nodes2);
        assert_eq!(stats1, stats2);
    }

    // -- Report JSON serialization --

    #[test]
    fn test_hint_report_json_serialization() {
        let nodes = vec![
            LlvmMetadata {
                kind: LlvmMetadataKind::AssertionProven,
                function_name: "f".to_string(),
                location: SourceLoc::new("a.rs", 1, 1),
                proof_id: Some("s1".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"assertion_proven\", i32 1}"
                    .to_string(),
            },
            LlvmMetadata {
                kind: LlvmMetadataKind::BoundsCheckEliminated,
                function_name: "f".to_string(),
                location: SourceLoc::new("a.rs", 5, 1),
                proof_id: Some("s2".to_string()),
                metadata_string: "!{!\"trust_vc.proven\", !\"bounds_check_eliminated\", i32 1}"
                    .to_string(),
            },
        ];
        let analysis = DeadCodeAnalysis::new(&nodes);
        let report = HintReport::from_parts(&nodes, &analysis);
        let json = serde_json::to_string(&report).expect("serialize report");
        let back: HintReport = serde_json::from_str(&json).expect("deserialize report");
        assert_eq!(back.total_hints, report.total_hints);
        assert_eq!(back.dead_branches, report.dead_branches);
        assert_eq!(back.by_kind, report.by_kind);
    }

    // -- Integration: facts -> generator -> report pipeline --

    #[test]
    fn test_full_pipeline_facts_to_report() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("src/lib.rs:10:5".to_string()),
                "fn_a::guard",
            ),
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "i < buf.len()",
                Some("src/lib.rs:20:9".to_string()),
                "fn_a::loop_bound",
            ),
            ProvenFact::new(
                ProvenFactKind::Precondition,
                "val.is_some()",
                Some("src/api.rs:5:1".to_string()),
                "fn_b::notnull",
            ),
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "no_overflow(a + b)",
                Some("src/arith.rs:3:1".to_string()),
                "fn_c::overflow",
            ),
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "unreachable",
                Some("src/lib.rs:30:1".to_string()),
                "fn_a::dead",
            ),
            // No location -> will be unclassifiable.
            ProvenFact::new(ProvenFactKind::Assertion, "y > 0", None, "fn_d::check"),
        ];

        let generator = LlvmHintGenerator::new(facts);
        let (nodes, stats) = generator.generate();

        assert_eq!(stats.total_facts, 6);
        assert_eq!(stats.classified, 5);
        assert_eq!(stats.unclassifiable, 1);

        let analysis = DeadCodeAnalysis::new(&nodes);
        let report = HintReport::from_parts(&nodes, &analysis);

        assert_eq!(report.total_hints, 5);
        assert!(report.by_kind.contains_key("assertion_proven"));
        assert!(report.by_kind.contains_key("bounds_check_eliminated"));
        assert!(report.by_kind.contains_key("null_check_eliminated"));
        assert!(report.by_kind.contains_key("overflow_absent"));
        assert!(report.by_kind.contains_key("branch_unreachable"));

        // At least one dead branch (the "unreachable" one).
        assert!(report.dead_branches >= 1);
        assert!(report.pruning_potential > 0.0);
        assert!(report.pruning_potential <= 1.0);

        // Summary renders without panic.
        let summary = report.render_summary();
        assert!(summary.contains("LLVM Hint Report"));
        assert!(summary.contains("Total hints:       5"));
    }

    // -- Metadata kind serde round-trip --

    #[test]
    fn test_metadata_kind_serde_round_trip() {
        let kinds = [
            LlvmMetadataKind::AssertionProven,
            LlvmMetadataKind::BranchUnreachable,
            LlvmMetadataKind::OverflowAbsent,
            LlvmMetadataKind::BoundsCheckEliminated,
            LlvmMetadataKind::NullCheckEliminated,
            LlvmMetadataKind::LoopBoundKnown,
            LlvmMetadataKind::ValueRangeKnown,
        ];
        for kind in &kinds {
            let json = serde_json::to_string(kind).expect("serialize kind");
            let back: LlvmMetadataKind = serde_json::from_str(&json).expect("deserialize kind");
            assert_eq!(*kind, back);
        }
    }

    // -- Unreachable stub rendering --

    #[test]
    fn test_unreachable_stub_rendering() {
        let loc = SourceLoc::new("src/lib.rs", 42, 5);
        let stub = LlvmHintGenerator::render_unreachable_stub(&loc, "false_branch == true");
        assert!(stub.contains("src/lib.rs:42:5"));
        assert!(stub.contains("__builtin_unreachable()"));
        assert!(stub.contains("false_branch == true"));
    }
}
