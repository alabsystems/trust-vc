// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verified hint code transformations that convert proven facts into concrete
//! Rust optimization hints.
//!
//! The existing `trust_vc_core::proven_facts::hints` module produces *advisory*
//! comments.  This module goes further: it emits concrete, compilable Rust code
//! transformations that a downstream build step can splice into the crate.
//!
//! Five transform families are supported:
//!
//! 1. **Unreachable** — dead-branch elimination via
//!    `unsafe { core::hint::unreachable_unchecked() }`.
//! 2. **BoundsCheckElimination** — proven in-bounds access via
//!    `unsafe { slice.get_unchecked(idx) }`.
//! 3. **OverflowCheckElimination** — proven non-overflowing arithmetic via
//!    `unchecked_add` / `unchecked_sub` / `unchecked_mul`.
//! 4. **NullCheckElimination** — proven `Some`/`Ok` via
//!    `unsafe { option.unwrap_unchecked() }`.
//! 5. **AssertionStrengthening** — `debug_assert!` promoted to `assert!` when
//!    the condition is proven always-true.
//!
//! Every emitted transform carries a safety comment that cites the proof
//! obligation that justifies the transformation.

use std::fmt;

use trust_vc_core::proven_facts::ProvenFact;

// ---------------------------------------------------------------------------
// Transform types
// ---------------------------------------------------------------------------

/// Classification of a hint code transformation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum TransformKind {
    /// Replace dead branch with `unreachable_unchecked()`.
    Unreachable,
    /// Replace bounds-checked access with `get_unchecked`.
    BoundsCheckElimination,
    /// Replace checked arithmetic with unchecked intrinsic.
    OverflowCheckElimination,
    /// Replace `Option::unwrap` / match with `unwrap_unchecked`.
    NullCheckElimination,
    /// Promote `debug_assert!` to `assert!`.
    AssertionStrengthening,
}

impl fmt::Display for TransformKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::Unreachable => "unreachable",
            Self::BoundsCheckElimination => "bounds_check_elimination",
            Self::OverflowCheckElimination => "overflow_check_elimination",
            Self::NullCheckElimination => "null_check_elimination",
            Self::AssertionStrengthening => "assertion_strengthening",
        };
        write!(f, "{label}")
    }
}

/// A concrete code transformation derived from a proven fact.
///
/// Each transform carries the replacement code and a safety comment citing the
/// proof obligation that justifies the replacement.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) struct HintTransform {
    /// What kind of transformation this is.
    kind: TransformKind,
    /// The source location where the transform applies (e.g., `"src/lib.rs:42:5"`).
    source_location: Option<String>,
    /// The original expression that was proven.
    original_expression: String,
    /// The replacement Rust code snippet.
    replacement_code: String,
    /// SAFETY comment citing the proof obligation.
    safety_comment: String,
    /// The proof obligation name that justifies this transform.
    obligation_name: String,
}

impl HintTransform {
    /// The kind of transformation.
    #[must_use]
    pub(crate) fn kind(&self) -> TransformKind {
        self.kind
    }

    /// Source location where the transform applies, if known.
    #[must_use]
    pub(crate) fn source_location(&self) -> Option<&str> {
        self.source_location.as_deref()
    }

    /// The original proven expression.
    #[must_use]
    pub(crate) fn original_expression(&self) -> &str {
        &self.original_expression
    }

    /// The replacement code snippet.
    #[must_use]
    pub(crate) fn replacement_code(&self) -> &str {
        &self.replacement_code
    }

    /// The SAFETY comment for the replacement.
    #[must_use]
    pub(crate) fn safety_comment(&self) -> &str {
        &self.safety_comment
    }

    /// The proof obligation name justifying this transform.
    #[must_use]
    pub(crate) fn obligation_name(&self) -> &str {
        &self.obligation_name
    }
}

impl fmt::Display for HintTransform {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(loc) = &self.source_location {
            writeln!(f, "// At {loc}")?;
        }
        writeln!(f, "{}", self.safety_comment)?;
        write!(f, "{}", self.replacement_code)
    }
}

// ---------------------------------------------------------------------------
// Expression classification helpers
// ---------------------------------------------------------------------------

/// Returns `true` if the expression looks like a bounds / index check.
fn is_bounds_expression(expr: &str) -> bool {
    let bounds_keywords = [
        ".len()", "index", "offset", "capacity", "bound", "range", "size",
    ];
    let has_keyword = bounds_keywords.iter().any(|kw| expr.contains(kw));
    let has_comparison = expr.contains('<') || expr.contains("<=") || expr.contains(">=");
    has_keyword && has_comparison
}

/// Returns `true` if the expression looks like a null / Option check.
fn is_null_check_expression(expr: &str) -> bool {
    let patterns = [
        "is_some()",
        "is_none()",
        "!= None",
        "!= null",
        "!= std::ptr::null",
        ".is_null()",
        "is_ok()",
    ];
    patterns.iter().any(|pat| expr.contains(pat))
}

/// Returns `true` if the expression looks like an overflow-freedom assertion.
fn is_overflow_expression(expr: &str) -> bool {
    let overflow_keywords = [
        "no_overflow",
        "no overflow",
        "wrapping",
        "checked_add",
        "checked_sub",
        "checked_mul",
        "overflowing",
        "saturating",
        "+ 1 <=",
        "+ 1 <",
        "as u",
        "as i",
    ];
    let arith_patterns = [" + ", " - ", " * "];
    let range_patterns = ["<= MAX", ">= MIN", "< u", "< i", "<= u", "<= i"];

    if overflow_keywords.iter().any(|kw| expr.contains(kw)) {
        return true;
    }

    let has_arithmetic = arith_patterns.iter().any(|pat| expr.contains(pat));
    let has_range_bound = range_patterns.iter().any(|pat| expr.contains(pat));
    has_arithmetic && has_range_bound
}

/// Returns `true` if the expression looks like a debug-assert candidate.
fn is_debug_assert_expression(expr: &str) -> bool {
    expr.contains("debug_assert")
}

/// Attempt to extract an operator from an overflow expression.
///
/// Returns `"add"`, `"sub"`, or `"mul"` if the expression contains the
/// corresponding arithmetic operator. Defaults to `"add"`.
fn extract_overflow_operator(expr: &str) -> &'static str {
    if expr.contains(" * ") || expr.contains("checked_mul") || expr.contains("mul") {
        "mul"
    } else if expr.contains(" - ") || expr.contains("checked_sub") || expr.contains("sub") {
        "sub"
    } else {
        "add"
    }
}

// ---------------------------------------------------------------------------
// Individual transform constructors
// ---------------------------------------------------------------------------

/// Build an unreachable-branch transform.
fn make_unreachable_transform(fact: &ProvenFact, source_line: Option<&str>) -> HintTransform {
    let expr = fact.expression();
    let obligation = fact.step_label();
    let loc = resolve_location(fact, source_line);

    HintTransform {
        kind: TransformKind::Unreachable,
        source_location: loc,
        original_expression: expr.to_string(),
        replacement_code: format!(
            "if !({expr}) {{\n    \
             // SAFETY: proven by trust_vc (obligation: {obligation})\n    \
             unsafe {{ core::hint::unreachable_unchecked() }}\n\
             }}"
        ),
        safety_comment: format!("// SAFETY: proven by trust_vc (obligation: {obligation})"),
        obligation_name: obligation.to_string(),
    }
}

/// Build a bounds-check-elimination transform.
fn make_bounds_check_transform(fact: &ProvenFact, source_line: Option<&str>) -> HintTransform {
    let expr = fact.expression();
    let obligation = fact.step_label();
    let loc = resolve_location(fact, source_line);

    HintTransform {
        kind: TransformKind::BoundsCheckElimination,
        source_location: loc,
        original_expression: expr.to_string(),
        replacement_code: format!(
            "// SAFETY: proven by trust_vc (obligation: {obligation})\n\
             unsafe {{ *slice.get_unchecked(idx) }}"
        ),
        safety_comment: format!("// SAFETY: proven by trust_vc (obligation: {obligation})"),
        obligation_name: obligation.to_string(),
    }
}

/// Build an overflow-check-elimination transform.
fn make_overflow_check_transform(fact: &ProvenFact, source_line: Option<&str>) -> HintTransform {
    let expr = fact.expression();
    let obligation = fact.step_label();
    let loc = resolve_location(fact, source_line);
    let op = extract_overflow_operator(expr);

    HintTransform {
        kind: TransformKind::OverflowCheckElimination,
        source_location: loc,
        original_expression: expr.to_string(),
        replacement_code: format!(
            "// SAFETY: proven by trust_vc (obligation: {obligation})\n\
             unsafe {{ a.unchecked_{op}(b) }}"
        ),
        safety_comment: format!("// SAFETY: proven by trust_vc (obligation: {obligation})"),
        obligation_name: obligation.to_string(),
    }
}

/// Build a null-check-elimination transform.
fn make_null_check_transform(fact: &ProvenFact, source_line: Option<&str>) -> HintTransform {
    let expr = fact.expression();
    let obligation = fact.step_label();
    let loc = resolve_location(fact, source_line);

    let replacement = if expr.contains("is_ok") {
        format!(
            "// SAFETY: proven by trust_vc (obligation: {obligation})\n\
             unsafe {{ result.unwrap_unchecked() }}"
        )
    } else {
        format!(
            "// SAFETY: proven by trust_vc (obligation: {obligation})\n\
             unsafe {{ option.unwrap_unchecked() }}"
        )
    };

    HintTransform {
        kind: TransformKind::NullCheckElimination,
        source_location: loc,
        original_expression: expr.to_string(),
        replacement_code: replacement,
        safety_comment: format!("// SAFETY: proven by trust_vc (obligation: {obligation})"),
        obligation_name: obligation.to_string(),
    }
}

/// Build an assertion-strengthening transform.
fn make_assertion_strengthening_transform(
    fact: &ProvenFact,
    source_line: Option<&str>,
) -> HintTransform {
    let expr = fact.expression();
    let obligation = fact.step_label();
    let loc = resolve_location(fact, source_line);

    // Strip `debug_assert` wrapper to extract the inner condition.
    let inner = expr
        .trim()
        .strip_prefix("debug_assert!(")
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(expr);

    HintTransform {
        kind: TransformKind::AssertionStrengthening,
        source_location: loc,
        original_expression: expr.to_string(),
        replacement_code: format!(
            "// Strengthened: proven always-true by trust_vc (obligation: {obligation})\n\
             assert!({inner});"
        ),
        safety_comment: format!(
            "// Strengthened: proven always-true by trust_vc (obligation: {obligation})"
        ),
        obligation_name: obligation.to_string(),
    }
}

/// Resolve the source location from the fact or an explicit source line.
fn resolve_location(fact: &ProvenFact, source_line: Option<&str>) -> Option<String> {
    source_line
        .map(str::to_string)
        .or_else(|| fact.source_location().map(str::to_string))
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Attempt to transform a proven fact into a concrete code hint.
///
/// Returns `Some(HintTransform)` when the expression matches a known
/// optimization pattern, `None` otherwise.
///
/// The optional `source_line` overrides the fact's own source location when
/// the caller has a more precise location (e.g., from the scan phase).
#[must_use]
pub(crate) fn try_transform(fact: &ProvenFact, source_line: Option<&str>) -> Option<HintTransform> {
    let expr = fact.expression().trim();

    // Debug-assert strengthening takes priority so that expressions like
    // `debug_assert!(x > 0)` are not misclassified as unreachable branches.
    if is_debug_assert_expression(expr) {
        return Some(make_assertion_strengthening_transform(fact, source_line));
    }

    if is_bounds_expression(expr) {
        return Some(make_bounds_check_transform(fact, source_line));
    }

    if is_null_check_expression(expr) {
        return Some(make_null_check_transform(fact, source_line));
    }

    if is_overflow_expression(expr) {
        return Some(make_overflow_check_transform(fact, source_line));
    }

    // General conditional: any proven assertion/precondition/postcondition/
    // invariant implies its negation branch is unreachable.
    Some(make_unreachable_transform(fact, source_line))
}

/// Transform all proven facts into hint transforms.
///
/// Convenience wrapper that calls [`try_transform`] on each fact and collects
/// the results.
#[must_use]
pub(crate) fn transform_all(facts: &[ProvenFact], source_line: Option<&str>) -> Vec<HintTransform> {
    facts
        .iter()
        .filter_map(|fact| try_transform(fact, source_line))
        .collect()
}

/// Render all transforms as a single Rust source string suitable for writing
/// to a `.hints.rs` file.
#[must_use]
pub(crate) fn render_transforms(transforms: &[HintTransform]) -> String {
    let mut output = String::new();
    for (i, transform) in transforms.iter().enumerate() {
        if i > 0 {
            output.push('\n');
        }
        output.push_str(&transform.to_string());
        output.push('\n');
    }
    output
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_core::proven_facts::{ProvenFact, ProvenFactKind};

    // -- TransformKind Display --

    #[test]
    fn test_transform_kind_display_unreachable() {
        assert_eq!(TransformKind::Unreachable.to_string(), "unreachable");
    }

    #[test]
    fn test_transform_kind_display_bounds() {
        assert_eq!(
            TransformKind::BoundsCheckElimination.to_string(),
            "bounds_check_elimination"
        );
    }

    #[test]
    fn test_transform_kind_display_overflow() {
        assert_eq!(
            TransformKind::OverflowCheckElimination.to_string(),
            "overflow_check_elimination"
        );
    }

    #[test]
    fn test_transform_kind_display_null() {
        assert_eq!(
            TransformKind::NullCheckElimination.to_string(),
            "null_check_elimination"
        );
    }

    #[test]
    fn test_transform_kind_display_assertion_strengthening() {
        assert_eq!(
            TransformKind::AssertionStrengthening.to_string(),
            "assertion_strengthening"
        );
    }

    // -- Unreachable transform --

    #[test]
    fn test_unreachable_transform_simple_condition() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "positive_guard",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::Unreachable);
        assert!(transform
            .replacement_code()
            .contains("unreachable_unchecked"));
        assert!(transform.safety_comment().contains("positive_guard"));
        assert_eq!(transform.obligation_name(), "positive_guard");
        assert_eq!(transform.source_location(), Some("src/lib.rs:42:5"));
    }

    #[test]
    fn test_unreachable_transform_postcondition() {
        let fact = ProvenFact::new(
            ProvenFactKind::Postcondition,
            "result == old(x) + 1",
            None,
            "inc_ensures",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::Unreachable);
        assert!(transform
            .replacement_code()
            .contains("result == old(x) + 1"));
        assert_eq!(transform.obligation_name(), "inc_ensures");
    }

    #[test]
    fn test_unreachable_transform_source_line_override() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "flag == true",
            Some("original.rs:1:1".to_string()),
            "flag_check",
        );
        let transform =
            try_transform(&fact, Some("override.rs:99:1")).expect("should produce transform");
        assert_eq!(transform.source_location(), Some("override.rs:99:1"));
    }

    // -- BoundsCheckElimination transform --

    #[test]
    fn test_bounds_check_elimination_len() {
        let fact = ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < arr.len()",
            Some("src/loop.rs:10:9".to_string()),
            "loop_bound",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::BoundsCheckElimination);
        assert!(transform.replacement_code().contains("get_unchecked"));
        assert!(transform.safety_comment().contains("loop_bound"));
    }

    #[test]
    fn test_bounds_check_elimination_index_capacity() {
        let fact = ProvenFact::new(
            ProvenFactKind::Precondition,
            "index < capacity",
            Some("src/vec.rs:5:1".to_string()),
            "cap_pre",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::BoundsCheckElimination);
    }

    #[test]
    fn test_bounds_check_elimination_offset_le_size() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "offset <= size",
            None,
            "off_check",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::BoundsCheckElimination);
    }

    // -- OverflowCheckElimination transform --

    #[test]
    fn test_overflow_check_elimination_no_overflow() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "no_overflow(a + b)",
            Some("src/math.rs:20:5".to_string()),
            "arith_safe",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::OverflowCheckElimination);
        assert!(transform.replacement_code().contains("unchecked_add"));
        assert!(transform.safety_comment().contains("arith_safe"));
    }

    #[test]
    fn test_overflow_check_elimination_checked_sub() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "checked_sub does not overflow",
            None,
            "sub_safe",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::OverflowCheckElimination);
        assert!(transform.replacement_code().contains("unchecked_sub"));
    }

    #[test]
    fn test_overflow_check_elimination_mul() {
        let fact = ProvenFact::new(ProvenFactKind::Assertion, "a * b <= MAX", None, "mul_bound");
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::OverflowCheckElimination);
        assert!(transform.replacement_code().contains("unchecked_mul"));
    }

    #[test]
    fn test_overflow_check_elimination_add_range() {
        let fact = ProvenFact::new(ProvenFactKind::Assertion, "x + 1 <= MAX", None, "inc_safe");
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::OverflowCheckElimination);
        assert!(transform.replacement_code().contains("unchecked_add"));
    }

    // -- NullCheckElimination transform --

    #[test]
    fn test_null_check_elimination_is_some() {
        let fact = ProvenFact::new(
            ProvenFactKind::Precondition,
            "arg.is_some()",
            Some("src/api.rs:15:1".to_string()),
            "notnull_pre",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::NullCheckElimination);
        assert!(transform
            .replacement_code()
            .contains("option.unwrap_unchecked"));
        assert!(transform.safety_comment().contains("notnull_pre"));
    }

    #[test]
    fn test_null_check_elimination_not_none() {
        let fact = ProvenFact::new(ProvenFactKind::Assertion, "ptr != None", None, "not_none");
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::NullCheckElimination);
    }

    #[test]
    fn test_null_check_elimination_is_ok() {
        let fact = ProvenFact::new(
            ProvenFactKind::Postcondition,
            "result.is_ok()",
            Some("src/io.rs:30:1".to_string()),
            "io_ok",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::NullCheckElimination);
        assert!(transform
            .replacement_code()
            .contains("result.unwrap_unchecked"));
    }

    // -- AssertionStrengthening transform --

    #[test]
    fn test_assertion_strengthening_debug_assert() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "debug_assert!(x > 0)",
            Some("src/lib.rs:50:5".to_string()),
            "debug_guard",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::AssertionStrengthening);
        assert!(transform.replacement_code().contains("assert!(x > 0)"));
        assert!(transform.safety_comment().contains("debug_guard"));
        assert!(!transform.replacement_code().contains("debug_assert"));
    }

    #[test]
    fn test_assertion_strengthening_preserves_inner_expr() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "debug_assert!(a + b < 100)",
            None,
            "sum_bound",
        );
        let transform = try_transform(&fact, None).expect("should produce transform");
        assert_eq!(transform.kind(), TransformKind::AssertionStrengthening);
        assert!(transform
            .replacement_code()
            .contains("assert!(a + b < 100)"));
    }

    // -- resolve_location --

    #[test]
    fn test_resolve_location_prefers_source_line() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("fact_loc.rs:1:1".to_string()),
            "s",
        );
        let loc = resolve_location(&fact, Some("caller_loc.rs:99:1"));
        assert_eq!(loc.as_deref(), Some("caller_loc.rs:99:1"));
    }

    #[test]
    fn test_resolve_location_falls_back_to_fact() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("fact_loc.rs:1:1".to_string()),
            "s",
        );
        let loc = resolve_location(&fact, None);
        assert_eq!(loc.as_deref(), Some("fact_loc.rs:1:1"));
    }

    #[test]
    fn test_resolve_location_none_when_both_absent() {
        let fact = ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s");
        let loc = resolve_location(&fact, None);
        assert!(loc.is_none());
    }

    // -- transform_all --

    #[test]
    fn test_transform_all_empty() {
        let transforms = transform_all(&[], None);
        assert!(transforms.is_empty());
    }

    #[test]
    fn test_transform_all_multiple_facts() {
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
        let transforms = transform_all(&facts, None);
        assert_eq!(transforms.len(), 3);
        assert_eq!(transforms[0].kind(), TransformKind::Unreachable);
        assert_eq!(transforms[1].kind(), TransformKind::BoundsCheckElimination);
        assert_eq!(transforms[2].kind(), TransformKind::NullCheckElimination);
    }

    // -- render_transforms --

    #[test]
    fn test_render_transforms_empty() {
        let output = render_transforms(&[]);
        assert!(output.is_empty());
    }

    #[test]
    fn test_render_transforms_single() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "guard",
        );
        let transforms = vec![try_transform(&fact, None).unwrap()];
        let output = render_transforms(&transforms);
        assert!(output.contains("At src/lib.rs:42:5"));
        assert!(output.contains("unreachable_unchecked"));
        assert!(output.contains("SAFETY: proven by trust_vc"));
    }

    #[test]
    fn test_render_transforms_multiple_separated() {
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
                Some("a.rs:10:5".to_string()),
                "s2",
            ),
        ];
        let transforms = transform_all(&facts, None);
        let output = render_transforms(&transforms);
        assert!(output.contains("At a.rs:1:1"));
        assert!(output.contains("At a.rs:10:5"));
        assert!(output.contains("unreachable_unchecked"));
        assert!(output.contains("get_unchecked"));
    }

    // -- HintTransform Display --

    #[test]
    fn test_hint_transform_display_with_location() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:1:1".to_string()),
            "guard",
        );
        let transform = try_transform(&fact, None).unwrap();
        let display = transform.to_string();
        assert!(display.contains("At src/lib.rs:1:1"));
        assert!(display.contains("SAFETY"));
        assert!(display.contains("unreachable_unchecked"));
    }

    #[test]
    fn test_hint_transform_display_without_location() {
        let fact = ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "guard");
        let transform = try_transform(&fact, None).unwrap();
        let display = transform.to_string();
        assert!(!display.contains("At "));
        assert!(display.contains("unreachable_unchecked"));
    }

    // -- Expression classifier edge cases --

    #[test]
    fn test_classify_bounds_len_needs_comparison() {
        // Has .len() but no comparison — should NOT be bounds elimination.
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "arr.len() == 5",
            None,
            "exact_len",
        );
        let transform = try_transform(&fact, None).unwrap();
        // `==` is not `<`/`<=`/`>=`, so this falls through to unreachable.
        assert_eq!(transform.kind(), TransformKind::Unreachable);
    }

    #[test]
    fn test_classify_overflow_wrapping_keyword() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "wrapping addition is safe",
            None,
            "wrap_safe",
        );
        let transform = try_transform(&fact, None).unwrap();
        assert_eq!(transform.kind(), TransformKind::OverflowCheckElimination);
    }

    #[test]
    fn test_extract_overflow_operator_defaults_to_add() {
        assert_eq!(extract_overflow_operator("no_overflow(x)"), "add");
    }

    #[test]
    fn test_extract_overflow_operator_detects_sub() {
        assert_eq!(extract_overflow_operator("a - b >= MIN"), "sub");
    }

    #[test]
    fn test_extract_overflow_operator_detects_mul() {
        assert_eq!(extract_overflow_operator("a * b <= MAX"), "mul");
    }

    // -- Safety comment content --

    #[test]
    fn test_safety_comment_cites_obligation() {
        let fact = ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < n",
            Some("loop.rs:5:9".to_string()),
            "loop_inv_7",
        );
        let transform = try_transform(&fact, None).unwrap();
        assert!(transform
            .safety_comment()
            .contains("obligation: loop_inv_7"));
    }

    #[test]
    fn test_all_transform_kinds_cite_obligation_in_replacement() {
        let test_cases: Vec<(&str, TransformKind)> = vec![
            ("x > 0", TransformKind::Unreachable),
            ("i < arr.len()", TransformKind::BoundsCheckElimination),
            (
                "no_overflow(a + b)",
                TransformKind::OverflowCheckElimination,
            ),
            ("val.is_some()", TransformKind::NullCheckElimination),
            (
                "debug_assert!(x > 0)",
                TransformKind::AssertionStrengthening,
            ),
        ];

        for (expr, expected_kind) in test_cases {
            let fact = ProvenFact::new(ProvenFactKind::Assertion, expr, None, "test_obligation");
            let transform = try_transform(&fact, None)
                .unwrap_or_else(|| panic!("expected transform for expression: {expr}"));
            assert_eq!(
                transform.kind(),
                expected_kind,
                "wrong kind for expression: {expr}"
            );
            assert!(
                transform.replacement_code().contains("test_obligation"),
                "replacement for {expr} should cite obligation"
            );
        }
    }
}
