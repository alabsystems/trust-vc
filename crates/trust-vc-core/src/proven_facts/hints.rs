// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Codegen module that transforms `ProvenFact`s into Rust optimization hints.
//!
//! When the trust_vc verifier proves a fact (e.g., `x > 0`), a downstream
//! compiler backend can leverage that proof to emit
//! `unsafe { std::hint::unreachable_unchecked() }` on the provably-false
//! branch, eliminate redundant bounds checks, or remove null/option checks.
//!
//! This module is advisory: it produces annotations and reports but does not
//! modify source code directly.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::fmt::{self, Write as _};

use serde::{Deserialize, Serialize};

use super::ProvenFact;

/// Classification of the optimization hint that can be derived from a proven fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OptimizationHintKind {
    /// The negation branch of a conditional is provably unreachable.
    /// Allows `unsafe { std::hint::unreachable_unchecked() }` on the dead branch.
    UnreachableBranch,
    /// A bounds check (e.g., array index) is provably within range.
    /// Allows the compiler to eliminate the bounds check entirely.
    BoundsElimination,
    /// A null/Option check is provably non-null/Some.
    /// Allows replacing `if let Some(x) = val` with `unsafe { val.unwrap_unchecked() }`.
    NullCheckElimination,
}

impl fmt::Display for OptimizationHintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::UnreachableBranch => "unreachable_branch",
            Self::BoundsElimination => "bounds_elimination",
            Self::NullCheckElimination => "null_check_elimination",
        };
        write!(f, "{label}")
    }
}

/// An optimization hint derived from a proven fact.
///
/// Each hint carries enough context for a code generator to emit the
/// appropriate unsafe optimization at the right source location, along
/// with a safety justification that documents why the optimization is
/// sound (traceable back to the trust_vc proof).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct OptimizationHint {
    /// Source location where the hint applies (e.g., `"src/lib.rs:42:5"`).
    source_location: Option<String>,
    /// What kind of optimization this hint enables.
    hint_kind: OptimizationHintKind,
    /// The proven expression (e.g., `"x > 0"`).
    expression: String,
    /// Human-readable explanation of why the optimization is sound,
    /// citing the verification step that proved the underlying fact.
    safety_justification: String,
}

impl OptimizationHint {
    /// Creates a new optimization hint.
    #[must_use]
    pub fn new(
        source_location: Option<String>,
        hint_kind: OptimizationHintKind,
        expression: impl Into<String>,
        safety_justification: impl Into<String>,
    ) -> Self {
        Self {
            source_location,
            hint_kind,
            expression: expression.into(),
            safety_justification: safety_justification.into(),
        }
    }

    /// Source location where this hint applies, if known.
    #[must_use]
    pub fn source_location(&self) -> Option<&str> {
        self.source_location.as_deref()
    }

    /// The kind of optimization enabled.
    #[must_use]
    pub const fn hint_kind(&self) -> OptimizationHintKind {
        self.hint_kind
    }

    /// The proven expression.
    #[must_use]
    pub fn expression(&self) -> &str {
        &self.expression
    }

    /// Safety justification for the optimization.
    #[must_use]
    pub fn safety_justification(&self) -> &str {
        &self.safety_justification
    }
}

/// Heuristically classifies a proven expression into an optimization hint kind.
///
/// This uses simple pattern matching on the expression string. A more
/// sophisticated implementation would operate on the AST, but for the
/// advisory hint layer string heuristics are sufficient.
fn classify_expression(expr: &str) -> OptimizationHintKind {
    let normalized = expr.trim();

    // Bounds-related patterns: index < len, i < n, offset <= capacity, etc.
    if is_bounds_expression(normalized) {
        return OptimizationHintKind::BoundsElimination;
    }

    // Null/Option-related patterns: x.is_some(), ptr != null, x != None, etc.
    if is_null_check_expression(normalized) {
        return OptimizationHintKind::NullCheckElimination;
    }

    // Default: any proven conditional implies its negation branch is unreachable.
    OptimizationHintKind::UnreachableBranch
}

/// Returns `true` if the expression looks like a bounds/index check.
fn is_bounds_expression(expr: &str) -> bool {
    let bounds_keywords = [
        ".len()", "index", "offset", "capacity", "bound", "range", "size",
    ];
    let has_bounds_keyword = bounds_keywords.iter().any(|kw| expr.contains(kw));
    let has_comparison = expr.contains('<') || expr.contains("<=") || expr.contains(">=");
    has_bounds_keyword && has_comparison
}

/// Returns `true` if the expression looks like a null/option check.
fn is_null_check_expression(expr: &str) -> bool {
    let null_patterns = [
        "is_some()",
        "is_none()",
        "!= None",
        "!= null",
        "!= std::ptr::null",
        ".is_null()",
        "!is_null()",
    ];
    null_patterns.iter().any(|pat| expr.contains(pat))
}

/// Builds the safety justification string for a given fact.
fn build_safety_justification(fact: &ProvenFact) -> String {
    format!(
        "SAFETY: trust_vc proved {kind} `{expr}` at step `{step}`. \
         The negation of this condition is unreachable.",
        kind = fact.kind(),
        expr = fact.expression(),
        step = fact.step_label(),
    )
}

/// Generates optimization hints from a slice of proven facts.
///
/// Each proven fact is mapped to an [`OptimizationHint`] based on heuristic
/// classification of the proven expression. The resulting hints are advisory
/// and can be consumed by a code generator or reported to the user.
///
/// # Examples
///
/// ```
/// use trust_vc_core::proven_facts::{ProvenFact, ProvenFactKind, generate_hints};
///
/// let facts = vec![
///     ProvenFact::new(
///         ProvenFactKind::Assertion,
///         "x > 0",
///         Some("src/lib.rs:42:5".to_string()),
///         "positive_guard",
///     ),
/// ];
/// let hints = generate_hints(&facts);
/// assert_eq!(hints.len(), 1);
/// ```
#[must_use]
pub fn generate_hints(facts: &[ProvenFact]) -> Vec<OptimizationHint> {
    facts
        .iter()
        .map(|fact| {
            let hint_kind = classify_expression(fact.expression());
            let safety = build_safety_justification(fact);
            OptimizationHint {
                source_location: fact.source_location().map(str::to_string),
                hint_kind,
                expression: fact.expression().to_string(),
                safety_justification: safety,
            }
        })
        .collect()
}

/// Emits Rust-style annotation comments for a slice of optimization hints.
///
/// The output is intended for human review or for pasting into generated code.
/// Each hint is rendered as a block of `//` comments followed by the
/// corresponding `unsafe` hint annotation.
///
/// # Examples
///
/// ```
/// use trust_vc_core::proven_facts::{ProvenFact, ProvenFactKind, generate_hints, emit_hint_annotations};
///
/// let facts = vec![
///     ProvenFact::new(
///         ProvenFactKind::Assertion,
///         "x > 0",
///         Some("src/lib.rs:42:5".to_string()),
///         "nonneg",
///     ),
/// ];
/// let hints = generate_hints(&facts);
/// let output = emit_hint_annotations(&hints);
/// assert!(output.contains("unreachable_unchecked"));
/// ```
#[must_use]
pub fn emit_hint_annotations(hints: &[OptimizationHint]) -> String {
    let mut output = String::new();

    for (i, hint) in hints.iter().enumerate() {
        if i > 0 {
            output.push('\n');
        }

        // Location header
        if let Some(loc) = hint.source_location() {
            let _ = writeln!(output, "// At {loc}");
        }

        // Safety justification comment
        let _ = writeln!(output, "// {}", hint.safety_justification());

        // Emit the appropriate annotation based on hint kind
        match hint.hint_kind() {
            OptimizationHintKind::UnreachableBranch => {
                let _ = write!(
                    output,
                    "// Proven: `{expr}` -- else branch is dead code.\n\
                     // unsafe {{ std::hint::unreachable_unchecked() }}\n",
                    expr = hint.expression(),
                );
            }
            OptimizationHintKind::BoundsElimination => {
                let _ = write!(
                    output,
                    "// Proven: `{expr}` -- bounds check can be elided.\n\
                     // unsafe {{ slice.get_unchecked(index) }}\n",
                    expr = hint.expression(),
                );
            }
            OptimizationHintKind::NullCheckElimination => {
                let _ = write!(
                    output,
                    "// Proven: `{expr}` -- null/Option check can be elided.\n\
                     // unsafe {{ option.unwrap_unchecked() }}\n",
                    expr = hint.expression(),
                );
            }
        }
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proven_facts::ProvenFactKind;

    // -- OptimizationHintKind tests --

    #[test]
    fn test_hint_kind_display_unreachable_branch() {
        assert_eq!(
            OptimizationHintKind::UnreachableBranch.to_string(),
            "unreachable_branch"
        );
    }

    #[test]
    fn test_hint_kind_display_bounds_elimination() {
        assert_eq!(
            OptimizationHintKind::BoundsElimination.to_string(),
            "bounds_elimination"
        );
    }

    #[test]
    fn test_hint_kind_display_null_check_elimination() {
        assert_eq!(
            OptimizationHintKind::NullCheckElimination.to_string(),
            "null_check_elimination"
        );
    }

    // -- OptimizationHint constructor and accessor tests --

    #[test]
    fn test_hint_new_with_location() {
        let hint = OptimizationHint::new(
            Some("src/lib.rs:10:5".to_string()),
            OptimizationHintKind::UnreachableBranch,
            "x > 0",
            "SAFETY: proven by trust_vc",
        );
        assert_eq!(hint.source_location(), Some("src/lib.rs:10:5"));
        assert_eq!(hint.hint_kind(), OptimizationHintKind::UnreachableBranch);
        assert_eq!(hint.expression(), "x > 0");
        assert_eq!(hint.safety_justification(), "SAFETY: proven by trust_vc");
    }

    #[test]
    fn test_hint_new_without_location() {
        let hint = OptimizationHint::new(
            None,
            OptimizationHintKind::BoundsElimination,
            "i < arr.len()",
            "safe",
        );
        assert!(hint.source_location().is_none());
        assert_eq!(hint.hint_kind(), OptimizationHintKind::BoundsElimination);
    }

    // -- classify_expression tests --

    #[test]
    fn test_classify_simple_comparison_as_unreachable() {
        assert_eq!(
            classify_expression("x > 0"),
            OptimizationHintKind::UnreachableBranch
        );
    }

    #[test]
    fn test_classify_bounds_check_with_len() {
        assert_eq!(
            classify_expression("i < arr.len()"),
            OptimizationHintKind::BoundsElimination
        );
    }

    #[test]
    fn test_classify_bounds_check_with_index() {
        assert_eq!(
            classify_expression("index < capacity"),
            OptimizationHintKind::BoundsElimination
        );
    }

    #[test]
    fn test_classify_bounds_check_with_offset() {
        assert_eq!(
            classify_expression("offset <= size"),
            OptimizationHintKind::BoundsElimination
        );
    }

    #[test]
    fn test_classify_null_check_is_some() {
        assert_eq!(
            classify_expression("value.is_some()"),
            OptimizationHintKind::NullCheckElimination
        );
    }

    #[test]
    fn test_classify_null_check_not_none() {
        assert_eq!(
            classify_expression("ptr != None"),
            OptimizationHintKind::NullCheckElimination
        );
    }

    #[test]
    fn test_classify_null_check_not_null() {
        assert_eq!(
            classify_expression("ptr != null"),
            OptimizationHintKind::NullCheckElimination
        );
    }

    #[test]
    fn test_classify_postcondition_as_unreachable() {
        assert_eq!(
            classify_expression("result == old(x) + 1"),
            OptimizationHintKind::UnreachableBranch
        );
    }

    #[test]
    fn test_classify_whitespace_trimmed() {
        assert_eq!(
            classify_expression("  i < arr.len()  "),
            OptimizationHintKind::BoundsElimination
        );
    }

    // -- is_bounds_expression tests --

    #[test]
    fn test_is_bounds_len_comparison() {
        assert!(is_bounds_expression("i < vec.len()"));
    }

    #[test]
    fn test_is_bounds_needs_comparison_operator() {
        // Has keyword but no comparison operator
        assert!(!is_bounds_expression("arr.len()"));
    }

    #[test]
    fn test_is_bounds_needs_keyword() {
        // Has comparison but no bounds keyword
        assert!(!is_bounds_expression("x < y"));
    }

    // -- is_null_check_expression tests --

    #[test]
    fn test_is_null_check_is_some() {
        assert!(is_null_check_expression("val.is_some()"));
    }

    #[test]
    fn test_is_null_check_is_none() {
        assert!(is_null_check_expression("!val.is_none()"));
    }

    #[test]
    fn test_is_null_check_not_null() {
        assert!(is_null_check_expression("ptr != null"));
    }

    #[test]
    fn test_is_null_check_plain_comparison_is_not_null() {
        assert!(!is_null_check_expression("x > 0"));
    }

    // -- build_safety_justification tests --

    #[test]
    fn test_safety_justification_format() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "positive_check",
        );
        let justification = build_safety_justification(&fact);
        assert!(justification.contains("assertion"));
        assert!(justification.contains("x > 0"));
        assert!(justification.contains("positive_check"));
        assert!(justification.contains("SAFETY"));
    }

    // -- generate_hints tests --

    #[test]
    fn test_generate_hints_empty_input() {
        let hints = generate_hints(&[]);
        assert!(hints.is_empty());
    }

    #[test]
    fn test_generate_hints_single_fact() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "nonneg",
        )];
        let hints = generate_hints(&facts);
        assert_eq!(hints.len(), 1);
        assert_eq!(
            hints[0].hint_kind(),
            OptimizationHintKind::UnreachableBranch
        );
        assert_eq!(hints[0].expression(), "x > 0");
        assert_eq!(hints[0].source_location(), Some("src/lib.rs:42:5"));
        assert!(hints[0].safety_justification().contains("SAFETY"));
    }

    #[test]
    fn test_generate_hints_bounds_classification() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/loop.rs:5:1".to_string()),
            "loop_bound",
        )];
        let hints = generate_hints(&facts);
        assert_eq!(hints.len(), 1);
        assert_eq!(
            hints[0].hint_kind(),
            OptimizationHintKind::BoundsElimination
        );
    }

    #[test]
    fn test_generate_hints_null_check_classification() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Precondition,
            "arg.is_some()",
            None,
            "notnull_pre",
        )];
        let hints = generate_hints(&facts);
        assert_eq!(hints.len(), 1);
        assert_eq!(
            hints[0].hint_kind(),
            OptimizationHintKind::NullCheckElimination
        );
    }

    #[test]
    fn test_generate_hints_preserves_location_none() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Postcondition,
            "result == 42",
            None,
            "answer",
        )];
        let hints = generate_hints(&facts);
        assert_eq!(hints.len(), 1);
        assert!(hints[0].source_location().is_none());
    }

    #[test]
    fn test_generate_hints_multiple_facts_mixed_kinds() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "x > 0",
                Some("a.rs:1:1".to_string()),
                "s1",
            ),
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "index < buf.len()",
                Some("a.rs:10:5".to_string()),
                "s2",
            ),
            ProvenFact::new(
                ProvenFactKind::Precondition,
                "opt.is_some()",
                Some("a.rs:20:1".to_string()),
                "s3",
            ),
        ];
        let hints = generate_hints(&facts);
        assert_eq!(hints.len(), 3);
        assert_eq!(
            hints[0].hint_kind(),
            OptimizationHintKind::UnreachableBranch
        );
        assert_eq!(
            hints[1].hint_kind(),
            OptimizationHintKind::BoundsElimination
        );
        assert_eq!(
            hints[2].hint_kind(),
            OptimizationHintKind::NullCheckElimination
        );
    }

    // -- emit_hint_annotations tests --

    #[test]
    fn test_emit_annotations_empty() {
        let output = emit_hint_annotations(&[]);
        assert!(output.is_empty());
    }

    #[test]
    fn test_emit_annotations_unreachable_branch() {
        let hints = vec![OptimizationHint::new(
            Some("src/lib.rs:42:5".to_string()),
            OptimizationHintKind::UnreachableBranch,
            "x > 0",
            "SAFETY: proven by trust_vc",
        )];
        let output = emit_hint_annotations(&hints);
        assert!(output.contains("At src/lib.rs:42:5"));
        assert!(output.contains("SAFETY: proven by trust_vc"));
        assert!(output.contains("unreachable_unchecked"));
        assert!(output.contains("else branch is dead code"));
    }

    #[test]
    fn test_emit_annotations_bounds_elimination() {
        let hints = vec![OptimizationHint::new(
            Some("src/buf.rs:10:1".to_string()),
            OptimizationHintKind::BoundsElimination,
            "i < buf.len()",
            "SAFETY: loop invariant proven",
        )];
        let output = emit_hint_annotations(&hints);
        assert!(output.contains("bounds check can be elided"));
        assert!(output.contains("get_unchecked"));
    }

    #[test]
    fn test_emit_annotations_null_check_elimination() {
        let hints = vec![OptimizationHint::new(
            Some("src/opt.rs:5:1".to_string()),
            OptimizationHintKind::NullCheckElimination,
            "val.is_some()",
            "SAFETY: precondition proven",
        )];
        let output = emit_hint_annotations(&hints);
        assert!(output.contains("null/Option check can be elided"));
        assert!(output.contains("unwrap_unchecked"));
    }

    #[test]
    fn test_emit_annotations_no_location() {
        let hints = vec![OptimizationHint::new(
            None,
            OptimizationHintKind::UnreachableBranch,
            "x > 0",
            "SAFETY: proven",
        )];
        let output = emit_hint_annotations(&hints);
        // Should NOT contain "At " line when location is None
        assert!(!output.contains("At "));
        assert!(output.contains("unreachable_unchecked"));
    }

    #[test]
    fn test_emit_annotations_multiple_hints_separated() {
        let hints = vec![
            OptimizationHint::new(
                Some("a.rs:1:1".to_string()),
                OptimizationHintKind::UnreachableBranch,
                "x > 0",
                "SAFETY: s1",
            ),
            OptimizationHint::new(
                Some("a.rs:10:1".to_string()),
                OptimizationHintKind::BoundsElimination,
                "i < len",
                "SAFETY: s2",
            ),
        ];
        let output = emit_hint_annotations(&hints);
        assert!(output.contains("At a.rs:1:1"));
        assert!(output.contains("At a.rs:10:1"));
        // Multiple hints produce multiple blocks
        assert!(output.contains("unreachable_unchecked"));
        assert!(output.contains("get_unchecked"));
    }

    // -- Serde round-trip tests --

    #[test]
    fn test_hint_kind_serde_round_trip() {
        let kinds = [
            OptimizationHintKind::UnreachableBranch,
            OptimizationHintKind::BoundsElimination,
            OptimizationHintKind::NullCheckElimination,
        ];
        for kind in &kinds {
            let json = serde_json::to_string(kind).expect("serialize hint kind");
            let back: OptimizationHintKind =
                serde_json::from_str(&json).expect("deserialize hint kind");
            assert_eq!(*kind, back);
        }
    }

    #[test]
    fn test_hint_serde_round_trip_with_location() {
        let hint = OptimizationHint::new(
            Some("src/lib.rs:1:1".to_string()),
            OptimizationHintKind::BoundsElimination,
            "i < n",
            "SAFETY: proven",
        );
        let json = serde_json::to_string(&hint).expect("serialize hint");
        let back: OptimizationHint = serde_json::from_str(&json).expect("deserialize hint");
        assert_eq!(hint, back);
    }

    #[test]
    fn test_hint_serde_round_trip_without_location() {
        let hint = OptimizationHint::new(
            None,
            OptimizationHintKind::NullCheckElimination,
            "x.is_some()",
            "SAFETY: pre",
        );
        let json = serde_json::to_string(&hint).expect("serialize hint");
        let back: OptimizationHint = serde_json::from_str(&json).expect("deserialize hint");
        assert_eq!(hint, back);
    }
}
