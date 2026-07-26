// trust-vc-oracle — Spec quality metrics and analysis
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Comprehensive quality analysis for mined specifications: completeness,
// precision, robustness, composability, coverage estimation, per-function
// reports, and quality comparisons across mining iterations.

use std::collections::HashMap;

use crate::mining::MinedSpec;

// ---------------------------------------------------------------------------
// Standard types referenced in specs
// ---------------------------------------------------------------------------

/// Primitive types that compose well across function boundaries.
const STANDARD_TYPES: &[&str] = &[
    "bool", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
    "f32", "f64", "String", "&str", "Option", "Result", "Vec", "Seq", "Set", "Map",
];

/// Keywords that indicate branch-sensitive postconditions.
const BRANCH_KEYWORDS: &[&str] = &[
    "if", "else", "match", "=>", "||", "&&", "==", "!=", ">=", "<=",
];

// ---------------------------------------------------------------------------
// SpecQuality
// ---------------------------------------------------------------------------

/// Quality metrics for a single mined specification.
///
/// Each dimension is normalised to `[0.0, 1.0]`.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct SpecQuality {
    /// Fraction of function behaviors covered (0.0-1.0).
    ///
    /// Estimated by comparing the number of ensures clauses against
    /// the number of observable output paths in the function source.
    pub completeness: f64,

    /// How tight the spec is — absence of spurious constraints (0.0-1.0).
    ///
    /// A precise spec has few preconditions (it applies broadly).
    /// More requires clauses reduce precision.
    pub precision: f64,

    /// Resilience to input perturbation (0.0-1.0).
    ///
    /// Measured by how many ensures clauses reference relational
    /// comparisons (>=, <=, !=) vs. exact equality. Relational specs
    /// are more robust to small input changes.
    pub robustness: f64,

    /// How well the spec composes with callers (0.0-1.0).
    ///
    /// Higher when the types mentioned in requires/ensures are standard
    /// (primitive, Option, Result, collections) vs. opaque/custom types.
    pub composability: f64,
}

impl SpecQuality {
    /// Aggregate quality as the weighted geometric mean of all four
    /// dimensions. Returns 0.0 if any dimension is 0.0.
    #[must_use]
    pub fn aggregate(&self) -> f64 {
        // Weighted geometric mean: completeness and precision are most
        // important, robustness and composability are secondary.
        let weights = [0.35, 0.30, 0.15, 0.20];
        let values = [
            self.completeness,
            self.precision,
            self.robustness,
            self.composability,
        ];

        let total_weight: f64 = weights.iter().sum();
        let log_sum: f64 = values
            .iter()
            .zip(weights.iter())
            .map(|(&v, &w)| {
                if v <= 0.0 {
                    return f64::NEG_INFINITY;
                }
                w * v.ln()
            })
            .sum();

        if log_sum == f64::NEG_INFINITY {
            return 0.0;
        }

        (log_sum / total_weight).exp()
    }
}

// ---------------------------------------------------------------------------
// Path counting heuristics
// ---------------------------------------------------------------------------

/// Count approximate output paths in function source.
///
/// Heuristic: count `if`, `match` arms, `else`, `?` (early return),
/// `return` statements. Minimum is 1 (single path).
fn count_output_paths(source: &str) -> usize {
    let mut paths = 1usize;

    // Each `if` adds one path (the else branch is implicit).
    paths += source.matches("if ").count();
    // Each explicit `else` confirms a second branch (already counted by `if`
    // but nested else adds more).
    // Match arms: count `=>`
    let match_arms = source.matches("=>").count();
    if match_arms > 0 {
        // match arms are counted as additional paths beyond the first
        paths += match_arms.saturating_sub(1);
    }
    // Early returns add paths.
    let explicit_returns = source
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            trimmed.starts_with("return ") || trimmed == "return;" || trimmed.ends_with('?')
        })
        .count();
    paths += explicit_returns;

    paths.max(1)
}

/// Count the number of branch-sensitive tokens in spec clauses.
fn count_branch_tokens(clauses: &[String]) -> usize {
    clauses
        .iter()
        .flat_map(|clause| {
            BRANCH_KEYWORDS
                .iter()
                .map(move |kw| clause.matches(kw).count())
        })
        .sum()
}

// ---------------------------------------------------------------------------
// Core analysis
// ---------------------------------------------------------------------------

/// Analyse the quality of a mined specification against its function source.
///
/// # Arguments
///
/// * `spec` - The mined specification to analyse.
/// * `func_source` - The full source code of the function this spec applies to.
///
/// # Returns
///
/// A `SpecQuality` with all four dimensions normalised to `[0.0, 1.0]`.
#[must_use]
pub fn analyze_quality(spec: &MinedSpec, func_source: &str) -> SpecQuality {
    let completeness = compute_completeness(spec, func_source);
    let precision = compute_precision(spec);
    let robustness = compute_robustness(spec);
    let composability = compute_composability(spec);

    SpecQuality {
        completeness,
        precision,
        robustness,
        composability,
    }
}

/// Completeness: fraction of function output paths covered by ensures.
fn compute_completeness(spec: &MinedSpec, func_source: &str) -> f64 {
    if spec.ensures.is_empty() {
        return 0.0;
    }
    let output_paths = count_output_paths(func_source);
    // Each ensures clause can cover at most one path; more clauses relative
    // to paths means better coverage. Cap at 1.0.
    let branch_tokens = count_branch_tokens(&spec.ensures);
    // An ensures with branch tokens (e.g., "if x > 0 then result >= 0")
    // can cover multiple paths. Give each branch token +0.5 path credit.
    let effective_coverage = spec.ensures.len() as f64 + branch_tokens as f64 * 0.5;
    (effective_coverage / output_paths as f64).min(1.0)
}

/// Precision: fewer preconditions = more general = more precise.
fn compute_precision(spec: &MinedSpec) -> f64 {
    // 0 requires = 1.0 precision (no constraints on callers).
    // Exponential decay: each requires halves the precision.
    let decay = 0.5_f64;
    decay.powf(spec.requires.len() as f64).clamp(0.0, 1.0)
}

/// Robustness: relational comparisons are more robust than exact equality.
fn compute_robustness(spec: &MinedSpec) -> f64 {
    let all_clauses: Vec<&String> = spec.requires.iter().chain(spec.ensures.iter()).collect();

    if all_clauses.is_empty() {
        return 0.0;
    }

    let relational_keywords = [">=", "<=", ">", "<", "!="];
    let exact_keywords = ["=="];

    let mut relational_count = 0usize;
    let mut exact_count = 0usize;

    for clause in &all_clauses {
        for kw in &relational_keywords {
            relational_count += clause.matches(kw).count();
        }
        for kw in &exact_keywords {
            exact_count += clause.matches(kw).count();
        }
    }

    let total = relational_count + exact_count;
    if total == 0 {
        // No comparisons at all — neutral robustness.
        return 0.5;
    }

    // More relational = more robust.
    relational_count as f64 / total as f64
}

/// Composability: standard types in clauses compose better.
fn compute_composability(spec: &MinedSpec) -> f64 {
    let all_clauses: Vec<&String> = spec.requires.iter().chain(spec.ensures.iter()).collect();

    if all_clauses.is_empty() {
        return 0.0;
    }

    // Extract all identifiers that look like type names (capitalized or
    // primitive) and check how many are standard.
    let joined = all_clauses
        .iter()
        .map(|s| s.as_str())
        .collect::<Vec<_>>()
        .join(" ");

    let tokens: Vec<&str> = joined
        .split(|c: char| !c.is_alphanumeric() && c != '_')
        .filter(|t| !t.is_empty())
        .collect();

    if tokens.is_empty() {
        return 0.5;
    }

    // Count tokens that reference standard types.
    let standard_refs: usize = tokens
        .iter()
        .filter(|t| {
            STANDARD_TYPES
                .iter()
                .any(|st| t.starts_with(st) || *t == st)
        })
        .count();

    // Also give credit for common spec patterns: result, old, self.
    let spec_builtin_count: usize = tokens
        .iter()
        .filter(|t| matches!(**t, "result" | "old" | "self" | "true" | "false"))
        .count();

    let familiar = standard_refs + spec_builtin_count;
    // Ratio of familiar tokens; boost toward 1.0 since most clauses
    // are expressions with operators and literals (not type names).
    let ratio = familiar as f64 / tokens.len() as f64;

    // Scale so even 30% familiar tokens gives composability near 1.0.
    (ratio * 3.0).min(1.0)
}

// ---------------------------------------------------------------------------
// SpecCoverage
// ---------------------------------------------------------------------------

/// Coverage analysis for a set of mined specs over a function.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct SpecCoverage {
    /// Function name.
    pub function_name: String,

    /// Estimated number of output paths.
    pub estimated_paths: usize,

    /// Number of ensures clauses across all specs for this function.
    pub ensures_count: usize,

    /// Estimated branch coverage in `[0.0, 1.0]`.
    pub branch_coverage: f64,

    /// Template names that contributed specs.
    pub contributing_templates: Vec<String>,

    /// Paths not covered — suggested areas for additional specs.
    pub uncovered_suggestions: Vec<String>,
}

/// Analyse coverage across all specs for a single function.
#[must_use]
pub fn analyze_coverage(specs: &[MinedSpec], func_name: &str, func_source: &str) -> SpecCoverage {
    let func_specs: Vec<&MinedSpec> = specs
        .iter()
        .filter(|s| s.function_name == func_name && s.verified)
        .collect();

    let estimated_paths = count_output_paths(func_source);

    let ensures_count: usize = func_specs.iter().map(|s| s.ensures.len()).sum();

    let branch_tokens: usize = func_specs
        .iter()
        .map(|s| count_branch_tokens(&s.ensures))
        .sum();

    let effective = ensures_count as f64 + branch_tokens as f64 * 0.5;
    let branch_coverage = (effective / estimated_paths as f64).min(1.0);

    let contributing_templates: Vec<String> = func_specs
        .iter()
        .map(|s| s.template_name.clone())
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();

    let uncovered_suggestions = suggest_uncovered(func_source, &func_specs);

    SpecCoverage {
        function_name: func_name.to_string(),
        estimated_paths,
        ensures_count,
        branch_coverage,
        contributing_templates,
        uncovered_suggestions,
    }
}

/// Suggest areas where additional specs might help.
fn suggest_uncovered(source: &str, specs: &[&MinedSpec]) -> Vec<String> {
    let mut suggestions = Vec::new();
    let all_ensures: Vec<&str> = specs
        .iter()
        .flat_map(|s| s.ensures.iter().map(String::as_str))
        .collect();

    // Check for match arms without corresponding spec clauses.
    if source.contains("match ")
        && !all_ensures
            .iter()
            .any(|e| e.contains("match") || e.contains("=>"))
    {
        suggestions.push("Consider specs for individual match arms".to_string());
    }

    // Check for error/None paths.
    if (source.contains("None") || source.contains("Err("))
        && !all_ensures
            .iter()
            .any(|e| e.contains("None") || e.contains("Err"))
    {
        suggestions.push("Consider specs for error/None return paths".to_string());
    }

    // Check for overflow-sensitive arithmetic.
    if (source.contains(" + ") || source.contains(" * ") || source.contains(" - "))
        && !all_ensures
            .iter()
            .any(|e| e.contains("overflow") || e.contains("wrapping"))
    {
        suggestions.push("Consider overflow boundary conditions".to_string());
    }

    // Check for early returns (keyword anywhere in source, not just line-start).
    let has_early_return = source.contains("return ");
    if has_early_return && all_ensures.len() < 2 {
        suggestions.push("Consider separate specs for early-return paths".to_string());
    }

    suggestions
}

// ---------------------------------------------------------------------------
// QualityReport
// ---------------------------------------------------------------------------

/// Per-function quality entry in a report.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct FunctionQualityEntry {
    /// Function name.
    pub function_name: String,
    /// Quality metrics (averaged across all specs for this function).
    pub quality: SpecQuality,
    /// Number of specs analysed.
    pub spec_count: usize,
    /// Coverage analysis.
    pub coverage: SpecCoverage,
}

/// Recommendation generated by quality analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Recommendation {
    /// This function needs stronger specs.
    NeedsStrongerSpec {
        function_name: String,
        reason: String,
    },
    /// A redundant spec can be removed.
    RedundantSpec {
        function_name: String,
        template_name: String,
    },
    /// Coverage is low — consider additional templates.
    LowCoverage {
        function_name: String,
        current_coverage: String,
    },
}

/// Aggregate quality report across all mined specs.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct QualityReport {
    /// Per-function quality entries.
    pub entries: Vec<FunctionQualityEntry>,

    /// Aggregate completeness across all functions.
    pub aggregate_completeness: f64,
    /// Aggregate precision across all functions.
    pub aggregate_precision: f64,
    /// Aggregate robustness across all functions.
    pub aggregate_robustness: f64,
    /// Aggregate composability across all functions.
    pub aggregate_composability: f64,

    /// Actionable recommendations.
    pub recommendations: Vec<Recommendation>,
}

/// Build a quality report for a set of mined specs.
///
/// `func_sources` maps function name to source code. Functions not found
/// in the map are analysed with an empty source string.
#[must_use]
pub fn build_quality_report(
    specs: &[MinedSpec],
    func_sources: &HashMap<String, String>,
) -> QualityReport {
    // Group specs by function name.
    let mut by_function: HashMap<String, Vec<&MinedSpec>> = HashMap::new();
    for spec in specs {
        by_function
            .entry(spec.function_name.clone())
            .or_default()
            .push(spec);
    }

    let mut entries = Vec::new();
    let mut recommendations = Vec::new();
    let mut total_completeness = 0.0;
    let mut total_precision = 0.0;
    let mut total_robustness = 0.0;
    let mut total_composability = 0.0;

    for (func_name, func_specs) in &by_function {
        let source = func_sources
            .get(func_name)
            .map(String::as_str)
            .unwrap_or("");

        // Analyse quality for each spec and average.
        let qualities: Vec<SpecQuality> = func_specs
            .iter()
            .map(|s| analyze_quality(s, source))
            .collect();

        let n = qualities.len() as f64;
        let avg_quality = SpecQuality {
            completeness: qualities.iter().map(|q| q.completeness).sum::<f64>() / n,
            precision: qualities.iter().map(|q| q.precision).sum::<f64>() / n,
            robustness: qualities.iter().map(|q| q.robustness).sum::<f64>() / n,
            composability: qualities.iter().map(|q| q.composability).sum::<f64>() / n,
        };

        let coverage = analyze_coverage(specs, func_name, source);

        // Generate recommendations.
        if avg_quality.completeness < 0.3 {
            recommendations.push(Recommendation::NeedsStrongerSpec {
                function_name: func_name.clone(),
                reason: format!(
                    "completeness {:.2} below 0.30 threshold",
                    avg_quality.completeness
                ),
            });
        }

        if coverage.branch_coverage < 0.5 {
            recommendations.push(Recommendation::LowCoverage {
                function_name: func_name.clone(),
                current_coverage: format!("{:.0}%", coverage.branch_coverage * 100.0),
            });
        }

        // Detect redundant specs: multiple specs from the same template.
        let mut template_counts: HashMap<&str, usize> = HashMap::new();
        for s in func_specs {
            *template_counts.entry(&s.template_name).or_insert(0) += 1;
        }
        for (tmpl, count) in &template_counts {
            if *count > 1 {
                recommendations.push(Recommendation::RedundantSpec {
                    function_name: func_name.clone(),
                    template_name: tmpl.to_string(),
                });
            }
        }

        total_completeness += avg_quality.completeness;
        total_precision += avg_quality.precision;
        total_robustness += avg_quality.robustness;
        total_composability += avg_quality.composability;

        entries.push(FunctionQualityEntry {
            function_name: func_name.clone(),
            quality: avg_quality,
            spec_count: func_specs.len(),
            coverage,
        });
    }

    // Sort entries by function name for deterministic output.
    entries.sort_by_key(|entry| entry.function_name.clone());

    let func_count = by_function.len() as f64;
    let (agg_c, agg_p, agg_r, agg_co) = if func_count > 0.0 {
        (
            total_completeness / func_count,
            total_precision / func_count,
            total_robustness / func_count,
            total_composability / func_count,
        )
    } else {
        (0.0, 0.0, 0.0, 0.0)
    };

    QualityReport {
        entries,
        aggregate_completeness: agg_c,
        aggregate_precision: agg_p,
        aggregate_robustness: agg_r,
        aggregate_composability: agg_co,
        recommendations,
    }
}

// ---------------------------------------------------------------------------
// QualityComparison
// ---------------------------------------------------------------------------

/// Per-function delta in quality scores.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct FunctionQualityDelta {
    /// Function name.
    pub function_name: String,
    /// Old aggregate quality.
    pub old_aggregate: f64,
    /// New aggregate quality.
    pub new_aggregate: f64,
    /// Change (new - old). Positive = improvement.
    pub delta: f64,
}

/// Comparison of quality between two sets of mined specs.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct QualityComparison {
    /// Per-function quality deltas.
    pub function_deltas: Vec<FunctionQualityDelta>,
    /// Functions whose quality improved.
    pub improved: Vec<String>,
    /// Functions whose quality degraded.
    pub degraded: Vec<String>,
    /// Functions unchanged or not comparable.
    pub unchanged: Vec<String>,
    /// Overall quality change (positive = improvement).
    pub overall_delta: f64,
}

/// Compare quality between two sets of mined specs.
///
/// Uses empty source strings for analysis (source-independent metrics).
/// For source-dependent comparison, use `compare_quality_with_sources`.
#[must_use]
pub fn compare_quality(old: &[MinedSpec], new: &[MinedSpec]) -> QualityComparison {
    compare_quality_with_sources(old, new, &HashMap::new())
}

/// Compare quality with function source context.
#[must_use]
pub fn compare_quality_with_sources(
    old: &[MinedSpec],
    new: &[MinedSpec],
    func_sources: &HashMap<String, String>,
) -> QualityComparison {
    let old_report = build_quality_report(old, func_sources);
    let new_report = build_quality_report(new, func_sources);

    // Index old entries by function name.
    let old_by_name: HashMap<&str, &FunctionQualityEntry> = old_report
        .entries
        .iter()
        .map(|e| (e.function_name.as_str(), e))
        .collect();

    let new_by_name: HashMap<&str, &FunctionQualityEntry> = new_report
        .entries
        .iter()
        .map(|e| (e.function_name.as_str(), e))
        .collect();

    // Collect all function names.
    let mut all_functions: Vec<String> = old_by_name
        .keys()
        .chain(new_by_name.keys())
        .map(|s| s.to_string())
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    all_functions.sort();

    let mut function_deltas = Vec::new();
    let mut improved = Vec::new();
    let mut degraded = Vec::new();
    let mut unchanged = Vec::new();

    let threshold = 0.01; // Minimum change to count as improvement/degradation.

    for func in &all_functions {
        let old_agg = old_by_name
            .get(func.as_str())
            .map(|e| e.quality.aggregate())
            .unwrap_or(0.0);
        let new_agg = new_by_name
            .get(func.as_str())
            .map(|e| e.quality.aggregate())
            .unwrap_or(0.0);
        let delta = new_agg - old_agg;

        function_deltas.push(FunctionQualityDelta {
            function_name: func.clone(),
            old_aggregate: old_agg,
            new_aggregate: new_agg,
            delta,
        });

        if delta > threshold {
            improved.push(func.clone());
        } else if delta < -threshold {
            degraded.push(func.clone());
        } else {
            unchanged.push(func.clone());
        }
    }

    let overall_delta = if function_deltas.is_empty() {
        0.0
    } else {
        function_deltas.iter().map(|d| d.delta).sum::<f64>() / function_deltas.len() as f64
    };

    QualityComparison {
        function_deltas,
        improved,
        degraded,
        unchanged,
        overall_delta,
    }
}

// ---------------------------------------------------------------------------
// Quality trend
// ---------------------------------------------------------------------------

/// A single data point in a quality trend.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct QualitySnapshot {
    /// Iteration index (0-based).
    pub iteration: usize,
    /// Aggregate quality at this iteration.
    pub aggregate_quality: f64,
    /// Number of verified specs.
    pub verified_count: usize,
    /// Total spec count.
    pub total_count: usize,
}

/// Compute quality trend across mining iterations.
///
/// Each element of `history` is the set of mined specs from one iteration.
#[must_use]
pub fn quality_trend(
    history: &[Vec<MinedSpec>],
    func_sources: &HashMap<String, String>,
) -> Vec<QualitySnapshot> {
    history
        .iter()
        .enumerate()
        .map(|(i, specs)| {
            let report = build_quality_report(specs, func_sources);
            let agg = if report.entries.is_empty() {
                0.0
            } else {
                report
                    .entries
                    .iter()
                    .map(|e| e.quality.aggregate())
                    .sum::<f64>()
                    / report.entries.len() as f64
            };
            let verified_count = specs.iter().filter(|s| s.verified).count();

            QualitySnapshot {
                iteration: i,
                aggregate_quality: agg,
                verified_count,
                total_count: specs.len(),
            }
        })
        .collect()
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

    fn simple_source() -> &'static str {
        "fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }"
    }

    fn complex_source() -> &'static str {
        r#"fn classify(x: i32) -> &str {
            match x {
                0 => "zero",
                1..=10 => "small",
                11..=100 => "medium",
                _ => "large",
            }
        }"#
    }

    // -----------------------------------------------------------------------
    // SpecQuality — aggregate
    // -----------------------------------------------------------------------

    #[test]
    fn test_spec_quality_aggregate_all_ones() {
        let q = SpecQuality {
            completeness: 1.0,
            precision: 1.0,
            robustness: 1.0,
            composability: 1.0,
        };
        let agg = q.aggregate();
        assert!(
            (agg - 1.0).abs() < 0.01,
            "all-1.0 should aggregate to ~1.0, got {agg}"
        );
    }

    #[test]
    fn test_spec_quality_aggregate_with_zero() {
        let q = SpecQuality {
            completeness: 0.0,
            precision: 1.0,
            robustness: 1.0,
            composability: 1.0,
        };
        assert_eq!(q.aggregate(), 0.0, "any zero dimension should yield 0");
    }

    #[test]
    fn test_spec_quality_aggregate_partial_values() {
        let q = SpecQuality {
            completeness: 0.5,
            precision: 0.8,
            robustness: 0.6,
            composability: 0.7,
        };
        let agg = q.aggregate();
        assert!(agg > 0.0 && agg < 1.0, "partial should be in (0, 1): {agg}");
        // Geometric mean should be less than arithmetic mean.
        let arith = (0.5 + 0.8 + 0.6 + 0.7) / 4.0;
        assert!(
            agg <= arith,
            "geometric mean {agg} should be <= arithmetic {arith}"
        );
    }

    // -----------------------------------------------------------------------
    // analyze_quality — completeness
    // -----------------------------------------------------------------------

    #[test]
    fn test_completeness_no_ensures_is_zero() {
        let spec = make_spec("f", "range", vec![], vec![], true);
        let q = analyze_quality(&spec, simple_source());
        assert_eq!(q.completeness, 0.0, "no ensures should give 0 completeness");
    }

    #[test]
    fn test_completeness_single_ensures_simple_function() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"], true);
        let q = analyze_quality(&spec, "fn id(x: u32) -> u32 { x }");
        assert!(
            q.completeness > 0.0,
            "single ensures on single-path function should be > 0"
        );
    }

    #[test]
    fn test_completeness_branch_tokens_boost_coverage() {
        let spec_plain = make_spec("f", "range", vec![], vec!["result >= 0"], true);
        let spec_branchy = make_spec(
            "f",
            "range",
            vec![],
            vec!["if x >= 0 then result == x else result == -x"],
            true,
        );
        let q_plain = analyze_quality(&spec_plain, simple_source());
        let q_branchy = analyze_quality(&spec_branchy, simple_source());
        assert!(
            q_branchy.completeness >= q_plain.completeness,
            "branch-aware ensures should have >= completeness"
        );
    }

    // -----------------------------------------------------------------------
    // analyze_quality — precision
    // -----------------------------------------------------------------------

    #[test]
    fn test_precision_no_requires_is_high() {
        let spec = make_spec("f", "range", vec![], vec!["result >= 0"], true);
        let q = analyze_quality(&spec, simple_source());
        assert!(
            (q.precision - 1.0).abs() < f64::EPSILON,
            "0 requires should give precision 1.0, got {}",
            q.precision
        );
    }

    #[test]
    fn test_precision_decreases_with_requires() {
        let spec_0 = make_spec("f", "range", vec![], vec!["result >= 0"], true);
        let spec_1 = make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true);
        let spec_2 = make_spec(
            "f",
            "range",
            vec!["x > 0", "x < 100"],
            vec!["result >= 0"],
            true,
        );

        let q0 = analyze_quality(&spec_0, simple_source());
        let q1 = analyze_quality(&spec_1, simple_source());
        let q2 = analyze_quality(&spec_2, simple_source());

        assert!(
            q0.precision > q1.precision,
            "0 requires should have higher precision than 1: {} vs {}",
            q0.precision,
            q1.precision
        );
        assert!(
            q1.precision > q2.precision,
            "1 requires should have higher precision than 2: {} vs {}",
            q1.precision,
            q2.precision
        );
    }

    // -----------------------------------------------------------------------
    // analyze_quality — robustness
    // -----------------------------------------------------------------------

    #[test]
    fn test_robustness_relational_high() {
        let spec = make_spec("f", "range", vec!["x >= 0"], vec!["result >= 0"], true);
        let q = analyze_quality(&spec, simple_source());
        assert!(
            q.robustness > 0.5,
            "relational-only spec should have robustness > 0.5, got {}",
            q.robustness
        );
    }

    #[test]
    fn test_robustness_exact_equality_lower() {
        let spec = make_spec("f", "identity", vec![], vec!["result == x"], true);
        let q = analyze_quality(&spec, simple_source());
        // Exact equality only — should be low robustness.
        assert!(
            q.robustness < 0.5,
            "exact-equality-only should have robustness < 0.5, got {}",
            q.robustness
        );
    }

    #[test]
    fn test_robustness_empty_clauses_zero() {
        let spec = make_spec("f", "range", vec![], vec![], true);
        let q = analyze_quality(&spec, simple_source());
        assert_eq!(q.robustness, 0.0, "empty clauses should give 0 robustness");
    }

    // -----------------------------------------------------------------------
    // analyze_quality — composability
    // -----------------------------------------------------------------------

    #[test]
    fn test_composability_standard_types_high() {
        let spec = make_spec("f", "range", vec!["x > 0"], vec!["result >= 0"], true);
        let q = analyze_quality(&spec, simple_source());
        assert!(
            q.composability > 0.0,
            "spec with standard tokens should have positive composability"
        );
    }

    #[test]
    fn test_composability_empty_clauses_zero() {
        let spec = make_spec("f", "range", vec![], vec![], true);
        let q = analyze_quality(&spec, simple_source());
        assert_eq!(
            q.composability, 0.0,
            "empty clauses should give 0 composability"
        );
    }

    // -----------------------------------------------------------------------
    // count_output_paths
    // -----------------------------------------------------------------------

    #[test]
    fn test_output_paths_simple_function() {
        let paths = count_output_paths("fn id(x: u32) -> u32 { x }");
        assert_eq!(paths, 1, "identity function has 1 path");
    }

    #[test]
    fn test_output_paths_if_else() {
        let paths = count_output_paths(simple_source());
        assert!(
            paths >= 2,
            "if-else should have at least 2 paths, got {paths}"
        );
    }

    #[test]
    fn test_output_paths_match() {
        let paths = count_output_paths(complex_source());
        // 4 match arms: "zero", "small", "medium", "large"
        assert!(
            paths >= 4,
            "4-arm match should have >= 4 paths, got {paths}"
        );
    }

    #[test]
    fn test_output_paths_empty_string() {
        let paths = count_output_paths("");
        assert_eq!(paths, 1, "empty source should count as 1 path");
    }

    // -----------------------------------------------------------------------
    // SpecCoverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_coverage_single_verified_spec() {
        let specs = vec![make_spec("abs", "range", vec![], vec!["result >= 0"], true)];
        let cov = analyze_coverage(&specs, "abs", simple_source());
        assert_eq!(cov.function_name, "abs");
        assert!(cov.estimated_paths >= 2);
        assert_eq!(cov.ensures_count, 1);
        assert!(cov.branch_coverage > 0.0 && cov.branch_coverage <= 1.0);
    }

    #[test]
    fn test_coverage_no_specs_for_function() {
        let specs = vec![make_spec(
            "other",
            "range",
            vec![],
            vec!["result >= 0"],
            true,
        )];
        let cov = analyze_coverage(&specs, "abs", simple_source());
        assert_eq!(cov.ensures_count, 0);
        assert_eq!(cov.branch_coverage, 0.0);
    }

    #[test]
    fn test_coverage_unverified_specs_excluded() {
        let specs = vec![make_spec(
            "abs",
            "range",
            vec![],
            vec!["result >= 0"],
            false,
        )];
        let cov = analyze_coverage(&specs, "abs", simple_source());
        assert_eq!(
            cov.ensures_count, 0,
            "unverified specs should be excluded from coverage"
        );
    }

    #[test]
    fn test_coverage_suggestions_for_match() {
        let specs = vec![make_spec(
            "classify",
            "range",
            vec![],
            vec!["result >= 0"],
            true,
        )];
        let cov = analyze_coverage(&specs, "classify", complex_source());
        assert!(
            !cov.uncovered_suggestions.is_empty(),
            "match source should produce coverage suggestions"
        );
    }

    // -----------------------------------------------------------------------
    // QualityReport
    // -----------------------------------------------------------------------

    #[test]
    fn test_quality_report_empty_specs() {
        let report = build_quality_report(&[], &HashMap::new());
        assert!(report.entries.is_empty());
        assert_eq!(report.aggregate_completeness, 0.0);
        assert!(report.recommendations.is_empty());
    }

    #[test]
    fn test_quality_report_single_function() {
        let specs = vec![make_spec("abs", "range", vec![], vec!["result >= 0"], true)];
        let mut sources = HashMap::new();
        sources.insert("abs".to_string(), simple_source().to_string());

        let report = build_quality_report(&specs, &sources);
        assert_eq!(report.entries.len(), 1);
        assert_eq!(report.entries[0].function_name, "abs");
        assert_eq!(report.entries[0].spec_count, 1);
        assert!(report.aggregate_completeness > 0.0);
    }

    #[test]
    fn test_quality_report_multiple_functions() {
        let specs = vec![
            make_spec("abs", "range", vec![], vec!["result >= 0"], true),
            make_spec("inc", "range", vec![], vec!["result > x"], true),
        ];
        let report = build_quality_report(&specs, &HashMap::new());
        assert_eq!(report.entries.len(), 2);
    }

    #[test]
    fn test_quality_report_recommends_low_completeness() {
        // A spec with no ensures has 0 completeness.
        let specs = vec![make_spec("f", "range", vec!["x > 0"], vec![], true)];
        let report = build_quality_report(&specs, &HashMap::new());
        let has_needs_stronger = report.recommendations.iter().any(|r| {
            matches!(r, Recommendation::NeedsStrongerSpec { function_name, .. } if function_name == "f")
        });
        assert!(
            has_needs_stronger,
            "should recommend stronger spec for 0-ensures function"
        );
    }

    #[test]
    fn test_quality_report_detects_redundant_specs() {
        let specs = vec![
            make_spec("f", "range", vec![], vec!["result >= 0"], true),
            make_spec("f", "range", vec!["x > 0"], vec!["result >= 1"], true),
        ];
        let report = build_quality_report(&specs, &HashMap::new());
        let has_redundant = report.recommendations.iter().any(|r| {
            matches!(r, Recommendation::RedundantSpec { function_name, template_name }
                if function_name == "f" && template_name == "range")
        });
        assert!(has_redundant, "duplicate template usage should be flagged");
    }

    // -----------------------------------------------------------------------
    // QualityComparison
    // -----------------------------------------------------------------------

    #[test]
    fn test_compare_quality_identical() {
        let specs = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let cmp = compare_quality(&specs, &specs);
        assert!(cmp.improved.is_empty());
        assert!(cmp.degraded.is_empty());
        assert_eq!(cmp.unchanged.len(), 1);
        assert!(
            cmp.overall_delta.abs() < 0.01,
            "identical specs should have ~0 delta, got {}",
            cmp.overall_delta
        );
    }

    #[test]
    fn test_compare_quality_improvement() {
        let old = vec![make_spec(
            "f",
            "range",
            vec!["x > 0", "x < 100", "x != 50"],
            vec![],
            true,
        )];
        let new = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let cmp = compare_quality(&old, &new);
        assert!(
            cmp.overall_delta > 0.0,
            "adding ensures + removing requires should improve quality, got {}",
            cmp.overall_delta
        );
    }

    #[test]
    fn test_compare_quality_degradation() {
        let old = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let new = vec![make_spec(
            "f",
            "range",
            vec!["x > 0", "x < 100", "x != 50"],
            vec![],
            true,
        )];
        let cmp = compare_quality(&old, &new);
        assert!(
            cmp.overall_delta < 0.0,
            "removing ensures + adding requires should degrade quality, got {}",
            cmp.overall_delta
        );
    }

    #[test]
    fn test_compare_quality_new_function_added() {
        let old: Vec<MinedSpec> = vec![];
        let new = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let cmp = compare_quality(&old, &new);
        assert_eq!(cmp.improved.len(), 1);
        assert_eq!(cmp.improved[0], "f");
    }

    #[test]
    fn test_compare_quality_function_removed() {
        let old = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let new: Vec<MinedSpec> = vec![];
        let cmp = compare_quality(&old, &new);
        assert_eq!(cmp.degraded.len(), 1);
        assert_eq!(cmp.degraded[0], "f");
    }

    // -----------------------------------------------------------------------
    // Quality trend
    // -----------------------------------------------------------------------

    #[test]
    fn test_quality_trend_empty_history() {
        let trend = quality_trend(&[], &HashMap::new());
        assert!(trend.is_empty());
    }

    #[test]
    fn test_quality_trend_single_iteration() {
        let history = vec![vec![make_spec(
            "f",
            "range",
            vec![],
            vec!["result >= 0"],
            true,
        )]];
        let trend = quality_trend(&history, &HashMap::new());
        assert_eq!(trend.len(), 1);
        assert_eq!(trend[0].iteration, 0);
        assert_eq!(trend[0].verified_count, 1);
        assert_eq!(trend[0].total_count, 1);
        assert!(trend[0].aggregate_quality > 0.0);
    }

    #[test]
    fn test_quality_trend_improving_iterations() {
        let iter0 = vec![make_spec(
            "f",
            "range",
            vec!["x > 0", "x < 100"],
            vec![],
            true,
        )];
        let iter1 = vec![make_spec("f", "range", vec![], vec!["result >= 0"], true)];
        let history = vec![iter0, iter1];
        let trend = quality_trend(&history, &HashMap::new());
        assert_eq!(trend.len(), 2);
        assert!(
            trend[1].aggregate_quality >= trend[0].aggregate_quality,
            "quality should improve: iter0={}, iter1={}",
            trend[0].aggregate_quality,
            trend[1].aggregate_quality,
        );
    }

    // -----------------------------------------------------------------------
    // Edge cases and integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_analyze_quality_all_dimensions_in_range() {
        let spec = make_spec(
            "f",
            "range",
            vec!["x > 0"],
            vec!["result >= 0", "result <= x"],
            true,
        );
        let q = analyze_quality(&spec, simple_source());
        assert!(q.completeness >= 0.0 && q.completeness <= 1.0);
        assert!(q.precision >= 0.0 && q.precision <= 1.0);
        assert!(q.robustness >= 0.0 && q.robustness <= 1.0);
        assert!(q.composability >= 0.0 && q.composability <= 1.0);
    }

    #[test]
    fn test_compare_quality_with_sources() {
        let old = vec![make_spec("abs", "range", vec![], vec!["result >= 0"], true)];
        let new = vec![make_spec(
            "abs",
            "range",
            vec![],
            vec!["result >= 0", "if x >= 0 then result == x"],
            true,
        )];
        let mut sources = HashMap::new();
        sources.insert("abs".to_string(), simple_source().to_string());

        let cmp = compare_quality_with_sources(&old, &new, &sources);
        assert!(
            cmp.overall_delta >= 0.0,
            "adding branch-aware ensures should improve or maintain quality"
        );
    }

    #[test]
    fn test_coverage_suggestions_error_paths() {
        let source = r#"fn safe_div(a: i32, b: i32) -> Option<i32> {
            if b == 0 { return None; }
            Some(a / b)
        }"#;
        let specs = vec![make_spec(
            "safe_div",
            "range",
            vec!["b != 0"],
            vec!["result >= 0"],
            true,
        )];
        let cov = analyze_coverage(&specs, "safe_div", source);
        let has_error_suggestion = cov
            .uncovered_suggestions
            .iter()
            .any(|s| s.contains("error") || s.contains("None"));
        assert!(
            has_error_suggestion,
            "should suggest covering None path, got: {:?}",
            cov.uncovered_suggestions
        );
    }

    #[test]
    fn test_coverage_suggestions_early_return() {
        let source = r#"fn bounded(x: u32) -> u32 {
            if x > 100 { return 100; }
            x
        }"#;
        let specs = vec![make_spec(
            "bounded",
            "range",
            vec![],
            vec!["result <= 100"],
            true,
        )];
        let cov = analyze_coverage(&specs, "bounded", source);
        let has_early_return_suggestion = cov
            .uncovered_suggestions
            .iter()
            .any(|s| s.contains("early-return"));
        assert!(
            has_early_return_suggestion,
            "should suggest covering early-return path, got: {:?}",
            cov.uncovered_suggestions
        );
    }

    #[test]
    fn test_quality_report_sorted_by_function_name() {
        let specs = vec![
            make_spec("zebra", "range", vec![], vec!["result >= 0"], true),
            make_spec("alpha", "range", vec![], vec!["result >= 0"], true),
            make_spec("middle", "range", vec![], vec!["result >= 0"], true),
        ];
        let report = build_quality_report(&specs, &HashMap::new());
        let names: Vec<&str> = report
            .entries
            .iter()
            .map(|e| e.function_name.as_str())
            .collect();
        assert_eq!(names, vec!["alpha", "middle", "zebra"]);
    }
}
