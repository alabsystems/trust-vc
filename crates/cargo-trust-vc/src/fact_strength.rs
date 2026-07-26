// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Fact strength analyzer: classifies proven facts by optimization potential.
//!
//! When trust_vc proves a fact, the optimization value of that proof varies
//! significantly. A proven bounds check (`i < arr.len()`) enables
//! `get_unchecked` and eliminates a branch -- high value. A proven general
//! assertion (`x == old(x) + 1`) documents correctness but does not directly
//! enable a code transformation -- low value.
//!
//! This module provides [`FactStrength`] classification, cycle-savings
//! estimation via [`OptimizationBudget`], and [`StrengthReport`] for
//! summarizing the optimization potential of a collection of proven facts.

use std::fmt;

use trust_vc_core::proven_facts::ProvenFact;

// ---------------------------------------------------------------------------
// FactStrength enum
// ---------------------------------------------------------------------------

/// Classification of a proven fact by its optimization potential.
///
/// Ordered from highest to lowest optimization value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub(crate) enum FactStrength {
    /// No direct optimization; useful for documentation or proof tracing.
    Informational,
    /// Assertion strengthening only (e.g., `debug_assert!` to `assert!`).
    Weak,
    /// Enables constant folding or dead code elimination.
    Moderate,
    /// Eliminates overflow or null/Option check.
    Strong,
    /// Eliminates a branch or bounds check (highest optimization value).
    Critical,
}

impl fmt::Display for FactStrength {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::Critical => "critical",
            Self::Strong => "strong",
            Self::Moderate => "moderate",
            Self::Weak => "weak",
            Self::Informational => "informational",
        };
        write!(f, "{label}")
    }
}

// ---------------------------------------------------------------------------
// Expression classification
// ---------------------------------------------------------------------------

/// Parse the fact expression and classify based on optimization-relevant
/// patterns.
///
/// Classification precedence (first match wins):
///
/// - **Critical**: bounds checks (`x < len`, `index < capacity`, etc.)
/// - **Strong**: null/Option checks (`is_some()`, `!= None`) or overflow
///   freedom (`x + y < MAX`, `no_overflow`, `checked_add`)
/// - **Moderate**: range info (`x > 0`, `x >= 0`) or constant folding
///   (`x == <const>`)
/// - **Weak**: debug-assert candidates
/// - **Informational**: everything else
#[must_use]
pub(crate) fn classify_fact(fact: &str) -> FactStrength {
    let expr = fact.trim();

    if is_bounds_check(expr) {
        return FactStrength::Critical;
    }

    if is_null_check(expr) || is_overflow_check(expr) {
        return FactStrength::Strong;
    }

    if is_range_info(expr) || is_constant_fold(expr) {
        return FactStrength::Moderate;
    }

    if is_debug_assert(expr) {
        return FactStrength::Weak;
    }

    FactStrength::Informational
}

/// Returns `true` for bounds-check patterns: `x < len`, `x < arr.len()`,
/// `index < capacity`, `offset <= size`, etc.
fn is_bounds_check(expr: &str) -> bool {
    let bounds_keywords = [
        ".len()", "index", "offset", "capacity", "bound", "range", "size",
    ];
    let has_keyword = bounds_keywords.iter().any(|kw| expr.contains(kw));
    let has_comparison = expr.contains('<') || expr.contains("<=") || expr.contains(">=");
    // Also match compound patterns like `x >= 0 && x < len`
    if has_keyword && has_comparison {
        return true;
    }
    // Match `x >= 0 && x < <something>.len()` compound form
    if expr.contains("&&") && has_comparison && has_keyword {
        return true;
    }
    false
}

/// Returns `true` for null/Option check patterns.
fn is_null_check(expr: &str) -> bool {
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

/// Returns `true` for overflow-freedom patterns.
fn is_overflow_check(expr: &str) -> bool {
    let overflow_keywords = [
        "no_overflow",
        "no overflow",
        "wrapping",
        "checked_add",
        "checked_sub",
        "checked_mul",
        "overflowing",
        "saturating",
    ];

    if overflow_keywords.iter().any(|kw| expr.contains(kw)) {
        return true;
    }

    // Arithmetic + range bound: `x + y < MAX`, `a * b <= MAX`
    let arith_patterns = [" + ", " - ", " * "];
    let range_patterns = [
        "<= MAX", ">= MIN", "< MAX", "< u", "< i", "<= u", "<= i", "< U", "< I", "<= U", "<= I",
    ];

    let has_arithmetic = arith_patterns.iter().any(|pat| expr.contains(pat));
    let has_range_bound = range_patterns.iter().any(|pat| expr.contains(pat));
    has_arithmetic && has_range_bound
}

/// Returns `true` for simple range-info patterns that enable constant
/// propagation or dead-code elimination: `x > 0`, `x >= 0`, `x >= 1`.
fn is_range_info(expr: &str) -> bool {
    let trimmed = expr.trim();

    // Match patterns like `x > 0`, `x >= 0`, `x >= 1`, `y > 0`
    // but NOT compound expressions (those are handled by bounds/overflow).
    if trimmed.contains("&&") || trimmed.contains("||") {
        return false;
    }

    // Already classified as bounds/overflow? Skip.
    if is_bounds_check(trimmed) || is_overflow_check(trimmed) || is_null_check(trimmed) {
        return false;
    }

    // Simple non-negative or positive patterns
    let range_patterns = ["> 0", ">= 0", ">= 1", "> 1", "< 0", "<= 0"];
    if range_patterns.iter().any(|pat| trimmed.ends_with(pat)) {
        return true;
    }
    // Also match `0 < x`, `0 <= x`
    if trimmed.starts_with("0 < ") || trimmed.starts_with("0 <= ") {
        return true;
    }

    false
}

/// Returns `true` for constant-equality patterns: `x == <literal>`.
fn is_constant_fold(expr: &str) -> bool {
    let trimmed = expr.trim();

    // Already classified by a higher-priority classifier? Skip.
    if is_bounds_check(trimmed) || is_overflow_check(trimmed) || is_null_check(trimmed) {
        return false;
    }

    if !trimmed.contains("==") {
        return false;
    }

    // Split on `==` and check if one side looks like a constant.
    let parts: Vec<&str> = trimmed.splitn(2, "==").collect();
    if parts.len() != 2 {
        return false;
    }

    let lhs = parts[0].trim();
    let rhs = parts[1].trim();

    is_constant_like(lhs) || is_constant_like(rhs)
}

/// Returns `true` if the token looks like a compile-time constant:
/// integer literal, `true`/`false`, quoted string, or ALL_CAPS identifier.
fn is_constant_like(token: &str) -> bool {
    let t = token.trim();
    if t.is_empty() {
        return false;
    }
    // Integer literal (possibly negative)
    let numeric = t.strip_prefix('-').unwrap_or(t);
    if numeric.chars().all(|c| c.is_ascii_digit() || c == '_') && !numeric.is_empty() {
        return true;
    }
    // Boolean literals
    if t == "true" || t == "false" {
        return true;
    }
    // String literal
    if t.starts_with('"') && t.ends_with('"') {
        return true;
    }
    // ALL_CAPS constant (at least 2 chars)
    if t.len() >= 2 && t.chars().all(|c| c.is_ascii_uppercase() || c == '_') {
        return true;
    }
    false
}

/// Returns `true` for debug-assert patterns.
fn is_debug_assert(expr: &str) -> bool {
    expr.contains("debug_assert")
}

// ---------------------------------------------------------------------------
// OptimizationBudget
// ---------------------------------------------------------------------------

/// Estimates runtime savings from applying proven-fact optimizations.
///
/// The cycle estimates are deliberately rough order-of-magnitude numbers
/// based on typical x86-64 branch misprediction, bounds-check, and
/// null-check costs.
pub(crate) struct OptimizationBudget;

impl OptimizationBudget {
    /// Rough per-instance cycle savings for a given fact strength.
    ///
    /// These are single-execution estimates; in a hot loop the savings
    /// multiply by the iteration count.
    #[must_use]
    pub(crate) fn estimate_cycles_saved(strength: FactStrength) -> u64 {
        match strength {
            // Bounds check: branch + comparison + possible panic call
            FactStrength::Critical => 15,
            // Overflow/null check: branch + comparison
            FactStrength::Strong => 10,
            // Range info / constant fold: enables further LLVM passes
            FactStrength::Moderate => 5,
            // debug_assert -> assert promotion: no runtime gain in release
            FactStrength::Weak => 1,
            // Documentation only
            FactStrength::Informational => 0,
        }
    }

    /// Rank facts by optimization value (descending).
    ///
    /// Returns tuples of (fact, strength, estimated cycles saved). The
    /// caller receives a cloned `ProvenFact` because we need to sort
    /// independently of the input slice's order.
    #[must_use]
    pub(crate) fn rank_by_value(facts: &[ProvenFact]) -> Vec<(ProvenFact, FactStrength, u64)> {
        let mut ranked: Vec<(ProvenFact, FactStrength, u64)> = facts
            .iter()
            .map(|fact| {
                let strength = classify_fact(fact.expression());
                let cycles = Self::estimate_cycles_saved(strength);
                (fact.clone(), strength, cycles)
            })
            .collect();

        // Sort descending by cycles (primary), then by strength (secondary).
        ranked.sort_by_key(|(_, strength, cycles)| {
            (std::cmp::Reverse(*cycles), std::cmp::Reverse(*strength))
        });

        ranked
    }
}

// ---------------------------------------------------------------------------
// StrengthReport
// ---------------------------------------------------------------------------

/// Summary report of fact strengths across a collection of proven facts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StrengthReport {
    /// Count per strength category.
    critical: usize,
    strong: usize,
    moderate: usize,
    weak: usize,
    informational: usize,
    /// Total estimated cycle savings.
    total_cycles: u64,
    /// Top-N most valuable optimizations (fact expression, strength, cycles).
    top_optimizations: Vec<(String, FactStrength, u64)>,
}

impl StrengthReport {
    /// Build a report from a slice of proven facts.
    ///
    /// `top_n` controls how many of the highest-value facts appear in the
    /// `top_optimizations` list.
    #[must_use]
    pub(crate) fn from_facts(facts: &[ProvenFact], top_n: usize) -> Self {
        let mut critical = 0usize;
        let mut strong = 0usize;
        let mut moderate = 0usize;
        let mut weak = 0usize;
        let mut informational = 0usize;
        let mut total_cycles = 0u64;

        let ranked = OptimizationBudget::rank_by_value(facts);

        for (_, strength, cycles) in &ranked {
            match strength {
                FactStrength::Critical => critical += 1,
                FactStrength::Strong => strong += 1,
                FactStrength::Moderate => moderate += 1,
                FactStrength::Weak => weak += 1,
                FactStrength::Informational => informational += 1,
            }
            total_cycles += cycles;
        }

        let top_optimizations: Vec<(String, FactStrength, u64)> = ranked
            .iter()
            .take(top_n)
            .map(|(fact, strength, cycles)| (fact.expression().to_string(), *strength, *cycles))
            .collect();

        Self {
            critical,
            strong,
            moderate,
            weak,
            informational,
            total_cycles,
            top_optimizations,
        }
    }

    /// Number of Critical-strength facts.
    #[must_use]
    pub(crate) fn critical(&self) -> usize {
        self.critical
    }

    /// Number of Strong-strength facts.
    #[must_use]
    pub(crate) fn strong(&self) -> usize {
        self.strong
    }

    /// Number of Moderate-strength facts.
    #[must_use]
    pub(crate) fn moderate(&self) -> usize {
        self.moderate
    }

    /// Number of Weak-strength facts.
    #[must_use]
    pub(crate) fn weak(&self) -> usize {
        self.weak
    }

    /// Number of Informational-strength facts.
    #[must_use]
    pub(crate) fn informational(&self) -> usize {
        self.informational
    }

    /// Total estimated cycle savings across all facts.
    #[must_use]
    pub(crate) fn total_cycles(&self) -> u64 {
        self.total_cycles
    }

    /// Top-N most valuable optimizations by estimated cycle savings.
    #[must_use]
    pub(crate) fn top_optimizations(&self) -> &[(String, FactStrength, u64)] {
        &self.top_optimizations
    }
}

impl fmt::Display for StrengthReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Fact Strength Report")?;
        writeln!(f, "===================")?;
        writeln!(f, "  Critical:      {}", self.critical)?;
        writeln!(f, "  Strong:        {}", self.strong)?;
        writeln!(f, "  Moderate:      {}", self.moderate)?;
        writeln!(f, "  Weak:          {}", self.weak)?;
        writeln!(f, "  Informational: {}", self.informational)?;
        writeln!(f)?;
        writeln!(f, "Estimated total cycle savings: {}", self.total_cycles)?;

        if !self.top_optimizations.is_empty() {
            writeln!(f)?;
            writeln!(f, "Top optimizations:")?;
            for (i, (expr, strength, cycles)) in self.top_optimizations.iter().enumerate() {
                writeln!(
                    f,
                    "  {}. [{}] `{}` (~{} cycles)",
                    i + 1,
                    strength,
                    expr,
                    cycles,
                )?;
            }
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_core::proven_facts::ProvenFactKind;

    // ---- FactStrength Display ----

    #[test]
    fn test_fact_strength_display_critical() {
        assert_eq!(FactStrength::Critical.to_string(), "critical");
    }

    #[test]
    fn test_fact_strength_display_strong() {
        assert_eq!(FactStrength::Strong.to_string(), "strong");
    }

    #[test]
    fn test_fact_strength_display_moderate() {
        assert_eq!(FactStrength::Moderate.to_string(), "moderate");
    }

    #[test]
    fn test_fact_strength_display_weak() {
        assert_eq!(FactStrength::Weak.to_string(), "weak");
    }

    #[test]
    fn test_fact_strength_display_informational() {
        assert_eq!(FactStrength::Informational.to_string(), "informational");
    }

    // ---- FactStrength ordering ----

    #[test]
    fn test_fact_strength_ord_critical_is_highest() {
        assert!(FactStrength::Critical > FactStrength::Strong);
        assert!(FactStrength::Strong > FactStrength::Moderate);
        assert!(FactStrength::Moderate > FactStrength::Weak);
        assert!(FactStrength::Weak > FactStrength::Informational);
    }

    // ---- classify_fact: Critical (bounds checks) ----

    #[test]
    fn test_classify_bounds_check_len() {
        assert_eq!(classify_fact("i < arr.len()"), FactStrength::Critical);
    }

    #[test]
    fn test_classify_bounds_check_index_capacity() {
        assert_eq!(classify_fact("index < capacity"), FactStrength::Critical);
    }

    #[test]
    fn test_classify_bounds_check_offset_le_size() {
        assert_eq!(classify_fact("offset <= size"), FactStrength::Critical);
    }

    #[test]
    fn test_classify_bounds_compound_range() {
        assert_eq!(
            classify_fact("x >= 0 && x < arr.len()"),
            FactStrength::Critical,
        );
    }

    // ---- classify_fact: Strong (null checks) ----

    #[test]
    fn test_classify_null_is_some() {
        assert_eq!(classify_fact("x.is_some()"), FactStrength::Strong);
    }

    #[test]
    fn test_classify_null_not_none() {
        assert_eq!(classify_fact("x != None"), FactStrength::Strong);
    }

    #[test]
    fn test_classify_null_is_ok() {
        assert_eq!(classify_fact("result.is_ok()"), FactStrength::Strong);
    }

    // ---- classify_fact: Strong (overflow) ----

    #[test]
    fn test_classify_overflow_arith_max() {
        assert_eq!(classify_fact("x + y < MAX"), FactStrength::Strong);
    }

    #[test]
    fn test_classify_overflow_mul_max() {
        assert_eq!(classify_fact("a * b <= MAX"), FactStrength::Strong);
    }

    #[test]
    fn test_classify_overflow_no_overflow_keyword() {
        assert_eq!(classify_fact("no_overflow(a + b)"), FactStrength::Strong);
    }

    #[test]
    fn test_classify_overflow_checked_add() {
        assert_eq!(classify_fact("checked_add is safe"), FactStrength::Strong);
    }

    // ---- classify_fact: Moderate (range info) ----

    #[test]
    fn test_classify_range_positive() {
        assert_eq!(classify_fact("x > 0"), FactStrength::Moderate);
    }

    #[test]
    fn test_classify_range_nonneg() {
        assert_eq!(classify_fact("x >= 0"), FactStrength::Moderate);
    }

    // ---- classify_fact: Moderate (constant folding) ----

    #[test]
    fn test_classify_constant_eq_int() {
        assert_eq!(classify_fact("x == 42"), FactStrength::Moderate);
    }

    #[test]
    fn test_classify_constant_eq_bool() {
        assert_eq!(classify_fact("flag == true"), FactStrength::Moderate);
    }

    // ---- classify_fact: Weak ----

    #[test]
    fn test_classify_debug_assert() {
        assert_eq!(classify_fact("debug_assert!(x > 0)"), FactStrength::Weak,);
    }

    // ---- classify_fact: Informational ----

    #[test]
    fn test_classify_informational_postcondition() {
        assert_eq!(
            classify_fact("result == old(x) + 1"),
            FactStrength::Informational,
        );
    }

    #[test]
    fn test_classify_informational_equality_no_const() {
        assert_eq!(
            classify_fact("result == old(seq).push(val)"),
            FactStrength::Informational,
        );
    }

    // ---- classify_fact: whitespace handling ----

    #[test]
    fn test_classify_trims_whitespace() {
        assert_eq!(classify_fact("  i < arr.len()  "), FactStrength::Critical);
    }

    // ---- OptimizationBudget::estimate_cycles_saved ----

    #[test]
    fn test_cycles_critical() {
        assert_eq!(
            OptimizationBudget::estimate_cycles_saved(FactStrength::Critical),
            15
        );
    }

    #[test]
    fn test_cycles_strong() {
        assert_eq!(
            OptimizationBudget::estimate_cycles_saved(FactStrength::Strong),
            10
        );
    }

    #[test]
    fn test_cycles_moderate() {
        assert_eq!(
            OptimizationBudget::estimate_cycles_saved(FactStrength::Moderate),
            5
        );
    }

    #[test]
    fn test_cycles_weak() {
        assert_eq!(
            OptimizationBudget::estimate_cycles_saved(FactStrength::Weak),
            1
        );
    }

    #[test]
    fn test_cycles_informational() {
        assert_eq!(
            OptimizationBudget::estimate_cycles_saved(FactStrength::Informational),
            0
        );
    }

    // ---- OptimizationBudget::rank_by_value ----

    #[test]
    fn test_rank_by_value_empty() {
        let ranked = OptimizationBudget::rank_by_value(&[]);
        assert!(ranked.is_empty());
    }

    #[test]
    fn test_rank_by_value_ordering() {
        let facts = vec![
            ProvenFact::new(
                ProvenFactKind::Assertion,
                "result == old(x) + 1",
                None,
                "informational_fact",
            ),
            ProvenFact::new(
                ProvenFactKind::Invariant,
                "i < arr.len()",
                None,
                "critical_fact",
            ),
            ProvenFact::new(
                ProvenFactKind::Precondition,
                "arg.is_some()",
                None,
                "strong_fact",
            ),
        ];
        let ranked = OptimizationBudget::rank_by_value(&facts);
        assert_eq!(ranked.len(), 3);
        // Critical first, then Strong, then Informational
        assert_eq!(ranked[0].1, FactStrength::Critical);
        assert_eq!(ranked[1].1, FactStrength::Strong);
        assert_eq!(ranked[2].1, FactStrength::Informational);
    }

    #[test]
    fn test_rank_by_value_preserves_fact_data() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < buf.len()",
            Some("loop.rs:5:1".to_string()),
            "loop_bound",
        )];
        let ranked = OptimizationBudget::rank_by_value(&facts);
        assert_eq!(ranked.len(), 1);
        assert_eq!(ranked[0].0.expression(), "i < buf.len()");
        assert_eq!(ranked[0].0.source_location(), Some("loop.rs:5:1"));
        assert_eq!(ranked[0].0.step_label(), "loop_bound");
    }

    // ---- StrengthReport ----

    #[test]
    fn test_strength_report_empty() {
        let report = StrengthReport::from_facts(&[], 5);
        assert_eq!(report.critical(), 0);
        assert_eq!(report.strong(), 0);
        assert_eq!(report.moderate(), 0);
        assert_eq!(report.weak(), 0);
        assert_eq!(report.informational(), 0);
        assert_eq!(report.total_cycles(), 0);
        assert!(report.top_optimizations().is_empty());
    }

    #[test]
    fn test_strength_report_mixed_facts() {
        let facts = vec![
            // Critical: bounds
            ProvenFact::new(ProvenFactKind::Invariant, "i < arr.len()", None, "s1"),
            // Strong: null check
            ProvenFact::new(ProvenFactKind::Precondition, "v.is_some()", None, "s2"),
            // Moderate: range
            ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s3"),
            // Weak: debug_assert
            ProvenFact::new(ProvenFactKind::Assertion, "debug_assert!(flag)", None, "s4"),
            // Informational: general postcondition
            ProvenFact::new(
                ProvenFactKind::Postcondition,
                "result == old(seq).push(val)",
                None,
                "s5",
            ),
        ];
        let report = StrengthReport::from_facts(&facts, 3);
        assert_eq!(report.critical(), 1);
        assert_eq!(report.strong(), 1);
        assert_eq!(report.moderate(), 1);
        assert_eq!(report.weak(), 1);
        assert_eq!(report.informational(), 1);
        // 15 + 10 + 5 + 1 + 0 = 31
        assert_eq!(report.total_cycles(), 31);
    }

    #[test]
    fn test_strength_report_top_n_limits() {
        let facts = vec![
            ProvenFact::new(ProvenFactKind::Invariant, "i < arr.len()", None, "s1"),
            ProvenFact::new(ProvenFactKind::Precondition, "v.is_some()", None, "s2"),
            ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s3"),
            ProvenFact::new(
                ProvenFactKind::Postcondition,
                "result == old(x)",
                None,
                "s4",
            ),
        ];
        let report = StrengthReport::from_facts(&facts, 2);
        assert_eq!(report.top_optimizations().len(), 2);
        // Top 2 should be Critical and Strong
        assert_eq!(report.top_optimizations()[0].1, FactStrength::Critical);
        assert_eq!(report.top_optimizations()[1].1, FactStrength::Strong);
    }

    #[test]
    fn test_strength_report_top_n_exceeds_count() {
        let facts = vec![ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            None,
            "s1",
        )];
        let report = StrengthReport::from_facts(&facts, 100);
        // Should only have as many as there are facts
        assert_eq!(report.top_optimizations().len(), 1);
    }

    #[test]
    fn test_strength_report_display_output() {
        let facts = vec![
            ProvenFact::new(ProvenFactKind::Invariant, "i < arr.len()", None, "s1"),
            ProvenFact::new(ProvenFactKind::Assertion, "x > 0", None, "s2"),
        ];
        let report = StrengthReport::from_facts(&facts, 5);
        let display = report.to_string();
        assert!(display.contains("Fact Strength Report"));
        assert!(display.contains("Critical:"));
        assert!(display.contains("Estimated total cycle savings:"));
        assert!(display.contains("Top optimizations:"));
        assert!(display.contains("[critical]"));
    }

    // ---- Edge cases ----

    #[test]
    fn test_classify_empty_string() {
        assert_eq!(classify_fact(""), FactStrength::Informational);
    }

    #[test]
    fn test_classify_only_whitespace() {
        assert_eq!(classify_fact("   "), FactStrength::Informational);
    }

    #[test]
    fn test_classify_negative_constant() {
        assert_eq!(classify_fact("x == -1"), FactStrength::Moderate);
    }

    #[test]
    fn test_classify_all_caps_constant() {
        assert_eq!(
            classify_fact("mode == DEFAULT_MODE"),
            FactStrength::Moderate
        );
    }
}
