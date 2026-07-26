//! Reporting module for proven facts and their optimization potential.
//!
//! Provides both human-readable and JSON output for integration with tooling
//! pipelines. The JSON output uses manual formatting to avoid requiring
//! `serde_json` as a runtime dependency.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::fmt::{self, Write as _};

use serde::{Deserialize, Serialize};

use super::hints::{generate_hints, OptimizationHintKind};
use super::{ProvenFact, ProvenFactKind};
use crate::json_escape;

/// Summary statistics for a collection of proven facts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ProvenFactsReport {
    /// Total number of proven facts.
    total_facts: usize,
    /// Number of proven assertions.
    assertions: usize,
    /// Number of proven preconditions.
    preconditions: usize,
    /// Number of proven postconditions.
    postconditions: usize,
    /// Number of proven invariants.
    invariants: usize,
    /// Number of hints classified as unreachable branches.
    unreachable_branch_hints: usize,
    /// Number of hints classified as bounds eliminations.
    bounds_elimination_hints: usize,
    /// Number of hints classified as null check eliminations.
    null_check_elimination_hints: usize,
}

impl ProvenFactsReport {
    /// Builds a report from a slice of proven facts.
    #[must_use]
    pub fn from_facts(facts: &[ProvenFact]) -> Self {
        let mut assertions = 0;
        let mut preconditions = 0;
        let mut postconditions = 0;
        let mut invariants = 0;

        for fact in facts {
            match fact.kind() {
                ProvenFactKind::Assertion => assertions += 1,
                ProvenFactKind::Precondition => preconditions += 1,
                ProvenFactKind::Postcondition => postconditions += 1,
                ProvenFactKind::Invariant => invariants += 1,
            }
        }

        let hints = generate_hints(facts);
        let mut unreachable_branch_hints = 0;
        let mut bounds_elimination_hints = 0;
        let mut null_check_elimination_hints = 0;

        for hint in &hints {
            match hint.hint_kind() {
                OptimizationHintKind::UnreachableBranch => unreachable_branch_hints += 1,
                OptimizationHintKind::BoundsElimination => bounds_elimination_hints += 1,
                OptimizationHintKind::NullCheckElimination => null_check_elimination_hints += 1,
            }
        }

        Self {
            total_facts: facts.len(),
            assertions,
            preconditions,
            postconditions,
            invariants,
            unreachable_branch_hints,
            bounds_elimination_hints,
            null_check_elimination_hints,
        }
    }

    /// Total number of proven facts.
    #[must_use]
    pub const fn total_facts(&self) -> usize {
        self.total_facts
    }

    /// Number of proven assertions.
    #[must_use]
    pub const fn assertions(&self) -> usize {
        self.assertions
    }

    /// Number of proven preconditions.
    #[must_use]
    pub const fn preconditions(&self) -> usize {
        self.preconditions
    }

    /// Number of proven postconditions.
    #[must_use]
    pub const fn postconditions(&self) -> usize {
        self.postconditions
    }

    /// Number of proven invariants.
    #[must_use]
    pub const fn invariants(&self) -> usize {
        self.invariants
    }

    /// Number of unreachable-branch optimization hints.
    #[must_use]
    pub const fn unreachable_branch_hints(&self) -> usize {
        self.unreachable_branch_hints
    }

    /// Number of bounds-elimination optimization hints.
    #[must_use]
    pub const fn bounds_elimination_hints(&self) -> usize {
        self.bounds_elimination_hints
    }

    /// Number of null-check-elimination optimization hints.
    #[must_use]
    pub const fn null_check_elimination_hints(&self) -> usize {
        self.null_check_elimination_hints
    }
}

impl fmt::Display for ProvenFactsReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", format_report_from_summary(self))
    }
}

/// Produces a human-readable summary of proven facts and their optimization
/// potential.
///
/// The output includes per-kind counts, optimization hint breakdown, and a
/// per-fact detail listing with source locations.
///
/// # Examples
///
/// ```
/// use trust_vc_core::proven_facts::{ProvenFact, ProvenFactKind, format_report};
///
/// let facts = vec![
///     ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s1"),
/// ];
/// let report = format_report(&facts);
/// assert!(report.contains("Proven Facts Summary"));
/// ```
#[must_use]
pub fn format_report(facts: &[ProvenFact]) -> String {
    let summary = ProvenFactsReport::from_facts(facts);
    let mut output = format_report_from_summary(&summary);

    // Detail section: per-fact listing
    if !facts.is_empty() {
        output.push_str("\nDetails:\n");
        for (i, fact) in facts.iter().enumerate() {
            let loc = fact.source_location().unwrap_or("<unknown>");
            let _ = writeln!(
                output,
                "  {idx}. [{kind}] `{expr}` at {loc} (step: {step})",
                idx = i + 1,
                kind = fact.kind(),
                expr = fact.expression(),
                loc = loc,
                step = fact.step_label(),
            );
        }
    }

    output
}

/// Renders the summary portion of the report from pre-computed statistics.
fn format_report_from_summary(summary: &ProvenFactsReport) -> String {
    let mut output = String::new();
    output.push_str("Proven Facts Summary\n");
    output.push_str("====================\n");
    let _ = writeln!(output, "Total proven facts: {}", summary.total_facts);
    let _ = writeln!(
        output,
        "  Assertions:     {}\n\
         \x20 Preconditions:  {}\n\
         \x20 Postconditions: {}\n\
         \x20 Invariants:     {}",
        summary.assertions, summary.preconditions, summary.postconditions, summary.invariants,
    );
    output.push_str("\nOptimization Hints:\n");
    let _ = writeln!(
        output,
        "  Unreachable branches:     {}\n\
         \x20 Bounds eliminations:      {}\n\
         \x20 Null check eliminations:  {}",
        summary.unreachable_branch_hints,
        summary.bounds_elimination_hints,
        summary.null_check_elimination_hints,
    );
    output
}

/// Produces a JSON representation of the proven facts for tooling consumption.
///
/// The output is a JSON object with `summary` and `facts` fields.
/// Uses manual formatting to avoid requiring `serde_json` as a runtime
/// dependency (it is only available as a dev-dependency).
///
/// # Examples
///
/// ```
/// use trust_vc_core::proven_facts::{ProvenFact, ProvenFactKind, to_json};
///
/// let facts = vec![
///     ProvenFact::new(
///         ProvenFactKind::Assertion,
///         "x > 0",
///         Some("src/lib.rs:42:5".to_string()),
///         "guard",
///     ),
/// ];
/// let json = to_json(&facts);
/// assert!(json.contains("\"total_facts\": 1"));
/// ```
#[must_use]
pub fn to_json(facts: &[ProvenFact]) -> String {
    let summary = ProvenFactsReport::from_facts(facts);
    let hints = generate_hints(facts);

    let mut out = String::new();
    out.push_str("{\n");

    // Summary object
    out.push_str("  \"summary\": {\n");
    let _ = writeln!(out, "    \"total_facts\": {},", summary.total_facts);
    let _ = writeln!(out, "    \"assertions\": {},", summary.assertions);
    let _ = writeln!(out, "    \"preconditions\": {},", summary.preconditions);
    let _ = writeln!(out, "    \"postconditions\": {},", summary.postconditions);
    let _ = writeln!(out, "    \"invariants\": {},", summary.invariants);
    let _ = writeln!(
        out,
        "    \"unreachable_branch_hints\": {},",
        summary.unreachable_branch_hints
    );
    let _ = writeln!(
        out,
        "    \"bounds_elimination_hints\": {},",
        summary.bounds_elimination_hints
    );
    let _ = writeln!(
        out,
        "    \"null_check_elimination_hints\": {}",
        summary.null_check_elimination_hints
    );
    out.push_str("  },\n");

    // Facts array
    out.push_str("  \"facts\": [\n");
    for (i, fact) in facts.iter().enumerate() {
        out.push_str("    {\n");
        let _ = writeln!(
            out,
            "      \"kind\": \"{}\",",
            json_escape(&fact.kind().to_string())
        );
        let _ = writeln!(
            out,
            "      \"expression\": \"{}\",",
            json_escape(fact.expression())
        );
        match fact.source_location() {
            Some(loc) => {
                let _ = writeln!(out, "      \"source_location\": \"{}\",", json_escape(loc));
            }
            None => {
                out.push_str("      \"source_location\": null,\n");
            }
        }
        let _ = writeln!(
            out,
            "      \"step_label\": \"{}\"",
            json_escape(fact.step_label())
        );
        if i + 1 < facts.len() {
            out.push_str("    },\n");
        } else {
            out.push_str("    }\n");
        }
    }
    out.push_str("  ],\n");

    // Hints array
    out.push_str("  \"hints\": [\n");
    for (i, hint) in hints.iter().enumerate() {
        out.push_str("    {\n");
        match hint.source_location() {
            Some(loc) => {
                let _ = writeln!(out, "      \"source_location\": \"{}\",", json_escape(loc));
            }
            None => {
                out.push_str("      \"source_location\": null,\n");
            }
        }
        let _ = writeln!(
            out,
            "      \"hint_kind\": \"{}\",",
            json_escape(&hint.hint_kind().to_string())
        );
        let _ = writeln!(
            out,
            "      \"expression\": \"{}\",",
            json_escape(hint.expression())
        );
        let _ = writeln!(
            out,
            "      \"safety_justification\": \"{}\"",
            json_escape(hint.safety_justification())
        );
        if i + 1 < hints.len() {
            out.push_str("    },\n");
        } else {
            out.push_str("    }\n");
        }
    }
    out.push_str("  ]\n");

    out.push_str("}\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- ProvenFactsReport tests --

    #[test]
    fn test_report_from_empty_facts() {
        let report = ProvenFactsReport::from_facts(&[]);
        assert_eq!(report.total_facts(), 0);
        assert_eq!(report.assertions(), 0);
        assert_eq!(report.preconditions(), 0);
        assert_eq!(report.postconditions(), 0);
        assert_eq!(report.invariants(), 0);
        assert_eq!(report.unreachable_branch_hints(), 0);
        assert_eq!(report.bounds_elimination_hints(), 0);
        assert_eq!(report.null_check_elimination_hints(), 0);
    }

    #[test]
    fn test_report_counts_by_kind() {
        let facts = vec![
            ProvenFact::new(ProvenFactKind::Assertion, "a", None, "s1"),
            ProvenFact::new(ProvenFactKind::Assertion, "b", None, "s2"),
            ProvenFact::new(ProvenFactKind::Precondition, "c", None, "s3"),
            ProvenFact::new(ProvenFactKind::Postcondition, "d", None, "s4"),
            ProvenFact::new(ProvenFactKind::Invariant, "e", None, "s5"),
            ProvenFact::new(ProvenFactKind::Invariant, "f", None, "s6"),
            ProvenFact::new(ProvenFactKind::Invariant, "g", None, "s7"),
        ];
        let report = ProvenFactsReport::from_facts(&facts);
        assert_eq!(report.total_facts(), 7);
        assert_eq!(report.assertions(), 2);
        assert_eq!(report.preconditions(), 1);
        assert_eq!(report.postconditions(), 1);
        assert_eq!(report.invariants(), 3);
    }

    #[test]
    fn test_report_hint_counts_mixed() {
        let facts = vec![
            // unreachable branch (plain comparison)
            ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s1"),
            // bounds elimination
            ProvenFact::new(ProvenFactKind::Invariant, "i < arr.len()", None, "s2"),
            // null check elimination
            ProvenFact::new(ProvenFactKind::Precondition, "val.is_some()", None, "s3"),
        ];
        let report = ProvenFactsReport::from_facts(&facts);
        assert_eq!(report.unreachable_branch_hints(), 1);
        assert_eq!(report.bounds_elimination_hints(), 1);
        assert_eq!(report.null_check_elimination_hints(), 1);
    }

    #[test]
    fn test_report_display_impl() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            None,
            "s1",
        )];
        let report = ProvenFactsReport::from_facts(&facts);
        let display = report.to_string();
        assert!(display.contains("Total proven facts: 1"));
        assert!(display.contains("Assertions:"));
    }

    #[test]
    fn test_report_serde_round_trip() {
        let facts = vec![
            ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s1"),
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "i < n",
                Some("a.rs:1:1".to_string()),
                "s2",
            ),
        ];
        let report = ProvenFactsReport::from_facts(&facts);
        let json = serde_json::to_string(&report).expect("serialize report");
        let back: ProvenFactsReport = serde_json::from_str(&json).expect("deserialize report");
        assert_eq!(report, back);
    }

    // -- format_report tests --

    #[test]
    fn test_format_report_empty() {
        let output = format_report(&[]);
        assert!(output.contains("Proven Facts Summary"));
        assert!(output.contains("Total proven facts: 0"));
        // No details section for empty
        assert!(!output.contains("Details:"));
    }

    #[test]
    fn test_format_report_single_fact_with_location() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "nonneg",
        )];
        let output = format_report(&facts);
        assert!(output.contains("Total proven facts: 1"));
        assert!(output.contains("Assertions:     1"));
        assert!(output.contains("Details:"));
        assert!(output.contains("[assertion]"));
        assert!(output.contains("`x > 0`"));
        assert!(output.contains("src/lib.rs:42:5"));
        assert!(output.contains("(step: nonneg)"));
    }

    #[test]
    fn test_format_report_fact_without_location() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Postcondition,
            "result == 42",
            None,
            "answer",
        )];
        let output = format_report(&facts);
        assert!(output.contains("<unknown>"));
    }

    #[test]
    fn test_format_report_multiple_facts() {
        let facts = vec![
            ProvenFact::new(ProvenFactKind::Assertion, "a", None, "s1"),
            ProvenFact::new(ProvenFactKind::Precondition, "b", None, "s2"),
            ProvenFact::new(ProvenFactKind::Invariant, "c", None, "s3"),
        ];
        let output = format_report(&facts);
        assert!(output.contains("Total proven facts: 3"));
        assert!(output.contains("1. [assertion]"));
        assert!(output.contains("2. [precondition]"));
        assert!(output.contains("3. [invariant]"));
    }

    #[test]
    fn test_format_report_optimization_hints_section() {
        let facts = vec![
            ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s1"),
            ProvenFact::new(ProvenFactKind::Invariant, "i < arr.len()", None, "s2"),
        ];
        let output = format_report(&facts);
        assert!(output.contains("Optimization Hints:"));
        assert!(output.contains("Unreachable branches:     1"));
        assert!(output.contains("Bounds eliminations:      1"));
    }

    // -- json_escape tests --

    #[test]
    fn test_json_escape_plain_string() {
        assert_eq!(json_escape("hello"), "hello");
    }

    #[test]
    fn test_json_escape_quotes() {
        assert_eq!(json_escape("say \"hi\""), "say \\\"hi\\\"");
    }

    #[test]
    fn test_json_escape_backslash() {
        assert_eq!(json_escape("a\\b"), "a\\\\b");
    }

    #[test]
    fn test_json_escape_newline() {
        assert_eq!(json_escape("a\nb"), "a\\nb");
    }

    #[test]
    fn test_json_escape_tab() {
        assert_eq!(json_escape("a\tb"), "a\\tb");
    }

    #[test]
    fn test_json_escape_control_char() {
        // ASCII bell (0x07)
        assert_eq!(json_escape("\x07"), "\\u0007");
    }

    // -- to_json tests --

    #[test]
    fn test_to_json_empty() {
        let output = to_json(&[]);
        assert!(output.contains("\"total_facts\": 0"));
        assert!(output.contains("\"facts\": ["));
        assert!(output.contains("\"hints\": ["));
    }

    #[test]
    fn test_to_json_single_fact() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "guard",
        )];
        let output = to_json(&facts);
        assert!(output.contains("\"total_facts\": 1"));
        assert!(output.contains("\"assertions\": 1"));
        assert!(output.contains("\"kind\": \"assertion\""));
        assert!(output.contains("\"expression\": \"x > 0\""));
        assert!(output.contains("\"source_location\": \"src/lib.rs:42:5\""));
        assert!(output.contains("\"step_label\": \"guard\""));
    }

    #[test]
    fn test_to_json_null_location() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Postcondition,
            "result == 0",
            None,
            "ret",
        )];
        let output = to_json(&facts);
        assert!(output.contains("\"source_location\": null"));
    }

    #[test]
    fn test_to_json_includes_hints() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < buf.len()",
            Some("loop.rs:5:1".to_string()),
            "bound",
        )];
        let output = to_json(&facts);
        assert!(output.contains("\"hints\": ["));
        assert!(output.contains("\"hint_kind\": \"bounds_elimination\""));
        assert!(output.contains("\"safety_justification\":"));
    }

    #[test]
    fn test_to_json_multiple_facts() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("a.rs:1:1".to_string()),
                "s1",
            ),
            ProvenFact::new(
                ProvenFactKind::Precondition,
                "opt.is_some()",
                Some("a.rs:2:1".to_string()),
                "s2",
            ),
        ];
        let output = to_json(&facts);
        assert!(output.contains("\"total_facts\": 2"));
        // Both facts present
        assert!(output.contains("\"kind\": \"assertion\""));
        assert!(output.contains("\"kind\": \"precondition\""));
    }

    #[test]
    fn test_to_json_special_chars_in_expression() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "msg == \"hello\\nworld\"",
            None,
            "str_check",
        )];
        let output = to_json(&facts);
        // Quotes and backslash should be escaped
        assert!(output.contains("\\\"hello"));
        assert!(output.contains("\\\\n"));
    }

    #[test]
    fn test_to_json_is_valid_json() {
        // Use serde_json (dev-dep) to parse and verify the output is valid JSON
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("a.rs:1:1".to_string()),
                "s1",
            ),
            ProvenFact::new(ProvenFactKind::Invariant, "i < arr.len()", None, "s2"),
            ProvenFact::new(
                ProvenFactKind::Precondition,
                "v.is_some()",
                Some("b.rs:5:1".to_string()),
                "s3",
            ),
        ];
        let output = to_json(&facts);
        let parsed: serde_json::Value =
            serde_json::from_str(&output).expect("to_json output must be valid JSON");
        assert!(parsed.is_object());
        assert!(parsed["summary"].is_object());
        assert!(parsed["facts"].is_array());
        assert!(parsed["hints"].is_array());
        assert_eq!(parsed["summary"]["total_facts"], 3);
        assert_eq!(parsed["facts"].as_array().unwrap().len(), 3);
        assert_eq!(parsed["hints"].as_array().unwrap().len(), 3);
    }
}
