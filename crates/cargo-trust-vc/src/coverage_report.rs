// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verification coverage reports for the cargo-trust-vc CLI.
//!
//! Tracks which functions have specs, which are verified, and identifies
//! coverage gaps with prioritized recommendations for where to add
//! verification effort next.

use std::collections::BTreeMap;
use std::fmt::Write as _;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Controls what is included in a coverage report.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageConfig {
    /// Include private (non-`pub`) functions in the report.
    pub include_private: bool,
    /// Include `#[test]` functions in the report.
    pub include_tests: bool,
    /// Coverage percentage below which a warning is emitted.
    pub threshold_warning: f64,
    /// Coverage percentage below which an error is emitted.
    pub threshold_error: f64,
}

impl Default for CoverageConfig {
    fn default() -> Self {
        Self {
            include_private: false,
            include_tests: false,
            threshold_warning: 80.0,
            threshold_error: 50.0,
        }
    }
}

// ---------------------------------------------------------------------------
// Core data types
// ---------------------------------------------------------------------------

/// Visibility of a Rust item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Visibility {
    Public,
    PubCrate,
    Private,
}

impl std::fmt::Display for Visibility {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Public => f.write_str("pub"),
            Self::PubCrate => f.write_str("pub(crate)"),
            Self::Private => f.write_str("private"),
        }
    }
}

/// Metadata about a single function in the crate.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct FunctionInfo {
    pub name: String,
    pub file: String,
    pub line: usize,
    pub visibility: Visibility,
    pub has_spec: bool,
    pub is_verified: bool,
    pub complexity: usize,
    pub param_count: usize,
}

/// The verification coverage status of a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CoverageStatus {
    /// Function has a spec and verification passed.
    FullyVerified,
    /// Function has a spec but verification was inconclusive or partial.
    PartiallyVerified,
    /// Function has a spec but has not been verified yet.
    HasSpec,
    /// Function has no spec at all.
    NoSpec,
    /// Function was excluded from the report (e.g., private, test).
    Excluded,
}

impl std::fmt::Display for CoverageStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FullyVerified => f.write_str("fully-verified"),
            Self::PartiallyVerified => f.write_str("partially-verified"),
            Self::HasSpec => f.write_str("has-spec"),
            Self::NoSpec => f.write_str("no-spec"),
            Self::Excluded => f.write_str("excluded"),
        }
    }
}

/// A single row in the coverage report.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageEntry {
    pub function_info: FunctionInfo,
    pub coverage_status: CoverageStatus,
    pub recommendation: Option<Recommendation>,
}

// ---------------------------------------------------------------------------
// Summary and gaps
// ---------------------------------------------------------------------------

/// Aggregate coverage numbers.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct CoverageSummary {
    pub total: usize,
    pub verified: usize,
    pub partial: usize,
    pub with_spec: usize,
    pub without_spec: usize,
    pub excluded: usize,
    pub coverage_pct: f64,
}

/// A coverage gap: a function that should have verification but does not.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageGap {
    pub function_name: String,
    pub file: String,
    pub priority: GapPriority,
    pub reason: String,
    pub suggested_spec_template: String,
}

/// Priority level for a gap.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum GapPriority {
    Critical,
    High,
    Medium,
    Low,
}

impl std::fmt::Display for GapPriority {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Critical => f.write_str("critical"),
            Self::High => f.write_str("high"),
            Self::Medium => f.write_str("medium"),
            Self::Low => f.write_str("low"),
        }
    }
}

// ---------------------------------------------------------------------------
// Recommendations
// ---------------------------------------------------------------------------

/// A suggested action for improving coverage.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Recommendation {
    pub target_function: String,
    pub suggested_action: String,
    pub template: String,
    pub priority_score: u32,
}

/// Engine that prioritizes coverage gaps and suggests spec templates.
#[derive(Debug, Clone)]
pub struct RecommendationEngine {
    /// Weight multiplier for public functions.
    pub public_weight: u32,
    /// Weight multiplier for complexity.
    pub complexity_weight: u32,
    /// Weight multiplier for parameter count.
    pub param_weight: u32,
}

impl Default for RecommendationEngine {
    fn default() -> Self {
        Self {
            public_weight: 10,
            complexity_weight: 2,
            param_weight: 3,
        }
    }
}

impl RecommendationEngine {
    /// Compute a priority score for a function.
    #[must_use]
    pub fn score(&self, info: &FunctionInfo) -> u32 {
        let vis = match info.visibility {
            Visibility::Public => self.public_weight,
            Visibility::PubCrate => self.public_weight / 2,
            Visibility::Private => 1,
        };
        let complexity = u32::try_from(info.complexity).unwrap_or(u32::MAX);
        let param_count = u32::try_from(info.param_count).unwrap_or(u32::MAX);
        vis.saturating_add(complexity.saturating_mul(self.complexity_weight))
            .saturating_add(param_count.saturating_mul(self.param_weight))
    }

    /// Prioritize a list of gaps, returning recommendations sorted by score
    /// (highest first).
    #[must_use]
    pub fn prioritize(&self, gaps: &[CoverageGap], infos: &[FunctionInfo]) -> Vec<Recommendation> {
        let info_map: BTreeMap<&str, &FunctionInfo> =
            infos.iter().map(|i| (i.name.as_str(), i)).collect();

        let mut recs: Vec<Recommendation> = gaps
            .iter()
            .map(|gap| {
                let score = info_map
                    .get(gap.function_name.as_str())
                    .map(|i| self.score(i))
                    .unwrap_or(1);
                let template = info_map
                    .get(gap.function_name.as_str())
                    .map(|i| Self::suggest_template(i))
                    .unwrap_or_default();
                Recommendation {
                    target_function: gap.function_name.clone(),
                    suggested_action: format!(
                        "Add {} spec for `{}`",
                        if gap.priority <= GapPriority::High {
                            "requires+ensures"
                        } else {
                            "requires"
                        },
                        gap.function_name,
                    ),
                    template,
                    priority_score: score,
                }
            })
            .collect();

        recs.sort_by_key(|rec| std::cmp::Reverse(rec.priority_score));
        recs
    }

    /// Generate a spec template string for the given function.
    #[must_use]
    pub fn suggest_template(info: &FunctionInfo) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "#[requires(/* preconditions for {} */)]", info.name);
        let _ = writeln!(out, "#[ensures(|result| /* postcondition */)]");
        if info.complexity > 50 {
            let _ = writeln!(out, "#[decreases(/* termination measure */)]");
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Thresholds
// ---------------------------------------------------------------------------

/// Threshold enforcement result.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageThreshold {
    pub warn_level: f64,
    pub error_level: f64,
}

impl CoverageThreshold {
    #[must_use]
    pub fn new(warn: f64, error: f64) -> Self {
        Self {
            warn_level: warn,
            error_level: error,
        }
    }

    /// Check the coverage percentage against thresholds. Returns `Ok(())` if
    /// above the warning level, or `Err` with a list of violations.
    pub fn check(&self, coverage_pct: f64) -> Result<(), Vec<String>> {
        let mut violations = Vec::new();
        if coverage_pct < self.error_level {
            violations.push(format!(
                "ERROR: coverage {coverage_pct:.1}% is below error threshold {:.1}%",
                self.error_level,
            ));
        }
        if coverage_pct < self.warn_level {
            violations.push(format!(
                "WARNING: coverage {coverage_pct:.1}% is below warning threshold {:.1}%",
                self.warn_level,
            ));
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

// ---------------------------------------------------------------------------
// Trend and comparison
// ---------------------------------------------------------------------------

/// A single data point in historical coverage tracking.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageTrend {
    pub timestamp: String,
    pub coverage_pct: f64,
    pub total_functions: usize,
    pub verified_functions: usize,
}

/// Comparison between two coverage reports.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageComparison {
    pub old_pct: f64,
    pub new_pct: f64,
    pub delta_pct: f64,
    pub new_gaps: Vec<String>,
    pub closed_gaps: Vec<String>,
    pub regressions: Vec<String>,
}

impl CoverageComparison {
    /// Compute a diff between an old and a new report.
    #[must_use]
    pub fn diff(old: &CoverageReport, new: &CoverageReport) -> Self {
        let old_pct = old.summary.coverage_pct;
        let new_pct = new.summary.coverage_pct;

        let old_verified: std::collections::HashSet<&str> = old
            .entries
            .iter()
            .filter(|e| e.coverage_status == CoverageStatus::FullyVerified)
            .map(|e| e.function_info.name.as_str())
            .collect();

        let new_verified: std::collections::HashSet<&str> = new
            .entries
            .iter()
            .filter(|e| e.coverage_status == CoverageStatus::FullyVerified)
            .map(|e| e.function_info.name.as_str())
            .collect();

        let old_no_spec: std::collections::HashSet<&str> = old
            .entries
            .iter()
            .filter(|e| e.coverage_status == CoverageStatus::NoSpec)
            .map(|e| e.function_info.name.as_str())
            .collect();

        let new_no_spec: std::collections::HashSet<&str> = new
            .entries
            .iter()
            .filter(|e| e.coverage_status == CoverageStatus::NoSpec)
            .map(|e| e.function_info.name.as_str())
            .collect();

        // Regressions: was verified, now is not.
        let regressions: Vec<String> = old_verified
            .iter()
            .filter(|name| !new_verified.contains(**name))
            .map(|s| s.to_string())
            .collect();

        // New gaps: not in old no-spec set, but in new no-spec set.
        let new_gaps: Vec<String> = new_no_spec
            .iter()
            .filter(|name| !old_no_spec.contains(**name))
            .map(|s| s.to_string())
            .collect();

        // Closed gaps: was no-spec, now has spec or verified.
        let closed_gaps: Vec<String> = old_no_spec
            .iter()
            .filter(|name| !new_no_spec.contains(**name))
            .map(|s| s.to_string())
            .collect();

        Self {
            old_pct,
            new_pct,
            delta_pct: new_pct - old_pct,
            new_gaps,
            closed_gaps,
            regressions,
        }
    }

    /// Returns `true` if any regressions were detected.
    #[must_use]
    pub fn has_regressions(&self) -> bool {
        !self.regressions.is_empty()
    }

    /// Returns `true` if coverage improved.
    #[must_use]
    pub fn is_improvement(&self) -> bool {
        self.delta_pct > 0.0
    }
}

// ---------------------------------------------------------------------------
// The report itself
// ---------------------------------------------------------------------------

/// A complete verification coverage report.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CoverageReport {
    pub entries: Vec<CoverageEntry>,
    pub summary: CoverageSummary,
    pub timestamp: String,
    pub config: CoverageConfig,
}

impl CoverageReport {
    /// Compute coverage gaps: functions that are `NoSpec` or `HasSpec` (but not
    /// verified).
    #[must_use]
    pub fn gaps(&self) -> Vec<CoverageGap> {
        self.entries
            .iter()
            .filter(|e| {
                matches!(
                    e.coverage_status,
                    CoverageStatus::NoSpec | CoverageStatus::HasSpec
                )
            })
            .map(|e| {
                let priority = Self::gap_priority(&e.function_info, e.coverage_status);
                let reason = match e.coverage_status {
                    CoverageStatus::NoSpec => "Function has no specification".to_owned(),
                    CoverageStatus::HasSpec => {
                        "Function has a spec but is not yet verified".to_owned()
                    }
                    _ => String::new(),
                };
                CoverageGap {
                    function_name: e.function_info.name.clone(),
                    file: e.function_info.file.clone(),
                    priority,
                    reason,
                    suggested_spec_template: RecommendationEngine::suggest_template(
                        &e.function_info,
                    ),
                }
            })
            .collect()
    }

    /// Produce prioritized recommendations from this report.
    #[must_use]
    pub fn recommendations(&self) -> Vec<Recommendation> {
        let engine = RecommendationEngine::default();
        let gaps = self.gaps();
        let infos: Vec<FunctionInfo> = self
            .entries
            .iter()
            .map(|e| e.function_info.clone())
            .collect();
        engine.prioritize(&gaps, &infos)
    }

    /// Check whether the report meets the configured thresholds.
    pub fn check_thresholds(&self) -> Result<(), Vec<String>> {
        let threshold =
            CoverageThreshold::new(self.config.threshold_warning, self.config.threshold_error);
        threshold.check(self.summary.coverage_pct)
    }

    // -- Renderers ----------------------------------------------------------

    /// Render the report as human-readable text.
    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "Verification Coverage Report");
        let _ = writeln!(out, "============================");
        let _ = writeln!(out, "Generated: {}", self.timestamp);
        let _ = writeln!(out);
        let _ = writeln!(
            out,
            "Coverage: {:.1}% ({} / {} functions verified)",
            self.summary.coverage_pct, self.summary.verified, self.summary.total,
        );
        let _ = writeln!(out, "  Fully verified:      {}", self.summary.verified);
        let _ = writeln!(out, "  Partially verified:  {}", self.summary.partial);
        let _ = writeln!(out, "  With spec only:      {}", self.summary.with_spec);
        let _ = writeln!(out, "  Without spec:        {}", self.summary.without_spec);
        let _ = writeln!(out, "  Excluded:            {}", self.summary.excluded);
        let _ = writeln!(out);

        let gaps = self.gaps();
        if !gaps.is_empty() {
            let _ = writeln!(out, "Coverage Gaps ({}):", gaps.len());
            let _ = writeln!(out, "{:-<60}", "");
            for gap in &gaps {
                let _ = writeln!(
                    out,
                    "  [{priority}] {name} ({file})",
                    priority = gap.priority,
                    name = gap.function_name,
                    file = gap.file,
                );
                let _ = writeln!(out, "    {}", gap.reason);
            }
        }

        if let Err(violations) = self.check_thresholds() {
            let _ = writeln!(out);
            for v in &violations {
                let _ = writeln!(out, "{v}");
            }
        }

        out
    }

    /// Render the report as Markdown.
    #[must_use]
    pub fn render_markdown(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "# Verification Coverage Report");
        let _ = writeln!(out);
        let _ = writeln!(out, "**Generated:** {}", self.timestamp);
        let _ = writeln!(out);
        let _ = writeln!(out, "## Summary");
        let _ = writeln!(out);
        let _ = writeln!(out, "| Metric | Value |");
        let _ = writeln!(out, "|--------|-------|");
        let _ = writeln!(out, "| Coverage | {:.1}% |", self.summary.coverage_pct,);
        let _ = writeln!(out, "| Total functions | {} |", self.summary.total);
        let _ = writeln!(out, "| Fully verified | {} |", self.summary.verified);
        let _ = writeln!(out, "| Partially verified | {} |", self.summary.partial);
        let _ = writeln!(out, "| With spec only | {} |", self.summary.with_spec);
        let _ = writeln!(out, "| Without spec | {} |", self.summary.without_spec);
        let _ = writeln!(out, "| Excluded | {} |", self.summary.excluded);
        let _ = writeln!(out);

        let gaps = self.gaps();
        if !gaps.is_empty() {
            let _ = writeln!(out, "## Coverage Gaps");
            let _ = writeln!(out);
            let _ = writeln!(out, "| Priority | Function | File | Reason |");
            let _ = writeln!(out, "|----------|----------|------|--------|");
            for gap in &gaps {
                let _ = writeln!(
                    out,
                    "| {} | `{}` | {} | {} |",
                    gap.priority, gap.function_name, gap.file, gap.reason,
                );
            }
        }

        out
    }

    /// Render the report as JSON via serde.
    #[must_use]
    pub fn render_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_else(|e| format!("{{\"error\": \"{e}\"}}"))
    }

    /// Render the report as CSV.
    #[must_use]
    pub fn render_csv(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "function,file,line,visibility,has_spec,is_verified,complexity,param_count,status"
        );
        for entry in &self.entries {
            let fi = &entry.function_info;
            let _ = writeln!(
                out,
                "{},{},{},{},{},{},{},{},{}",
                fi.name,
                fi.file,
                fi.line,
                fi.visibility,
                fi.has_spec,
                fi.is_verified,
                fi.complexity,
                fi.param_count,
                entry.coverage_status,
            );
        }
        out
    }

    // -- Internal -----------------------------------------------------------

    fn gap_priority(info: &FunctionInfo, status: CoverageStatus) -> GapPriority {
        // Public + no spec + high complexity → critical.
        if info.visibility == Visibility::Public && status == CoverageStatus::NoSpec {
            if info.complexity > 50 {
                return GapPriority::Critical;
            }
            return GapPriority::High;
        }
        if info.visibility == Visibility::PubCrate && status == CoverageStatus::NoSpec {
            return GapPriority::Medium;
        }
        if status == CoverageStatus::HasSpec {
            return GapPriority::Medium;
        }
        GapPriority::Low
    }
}

// ---------------------------------------------------------------------------
// Builder
// ---------------------------------------------------------------------------

/// Fluent builder for assembling a [`CoverageReport`].
#[derive(Debug)]
pub struct CoverageBuilder {
    config: CoverageConfig,
    functions: Vec<FunctionInfo>,
    timestamp: String,
}

impl CoverageBuilder {
    /// Create a new builder with the given configuration.
    #[must_use]
    pub fn new(config: CoverageConfig) -> Self {
        Self {
            config,
            functions: Vec::new(),
            timestamp: String::new(),
        }
    }

    /// Add a function to be included in the report.
    #[must_use]
    pub fn add_function(mut self, info: FunctionInfo) -> Self {
        self.functions.push(info);
        self
    }

    /// Set the report timestamp.
    #[must_use]
    pub fn timestamp(mut self, ts: &str) -> Self {
        self.timestamp = ts.to_owned();
        self
    }

    /// Build the final [`CoverageReport`].
    #[must_use]
    pub fn build(self) -> CoverageReport {
        let mut entries = Vec::with_capacity(self.functions.len());
        let mut summary = CoverageSummary::default();

        for info in &self.functions {
            let status = self.classify(info);
            match status {
                CoverageStatus::FullyVerified => summary.verified += 1,
                CoverageStatus::PartiallyVerified => summary.partial += 1,
                CoverageStatus::HasSpec => summary.with_spec += 1,
                CoverageStatus::NoSpec => summary.without_spec += 1,
                CoverageStatus::Excluded => summary.excluded += 1,
            }
            if status != CoverageStatus::Excluded {
                summary.total += 1;
            }

            let recommendation =
                if matches!(status, CoverageStatus::NoSpec | CoverageStatus::HasSpec) {
                    let engine = RecommendationEngine::default();
                    let score = engine.score(info);
                    Some(Recommendation {
                        target_function: info.name.clone(),
                        suggested_action: format!("Add verification for `{}`", info.name),
                        template: RecommendationEngine::suggest_template(info),
                        priority_score: score,
                    })
                } else {
                    None
                };

            entries.push(CoverageEntry {
                function_info: info.clone(),
                coverage_status: status,
                recommendation,
            });
        }

        summary.coverage_pct = if summary.total == 0 {
            100.0
        } else {
            (summary.verified as f64 / summary.total as f64) * 100.0
        };

        CoverageReport {
            entries,
            summary,
            timestamp: if self.timestamp.is_empty() {
                "unknown".to_owned()
            } else {
                self.timestamp
            },
            config: self.config,
        }
    }

    fn classify(&self, info: &FunctionInfo) -> CoverageStatus {
        // Apply exclusion filters.
        if !self.config.include_private && info.visibility == Visibility::Private {
            return CoverageStatus::Excluded;
        }
        if !self.config.include_tests && info.name.starts_with("test_") {
            return CoverageStatus::Excluded;
        }

        if info.is_verified && info.has_spec {
            CoverageStatus::FullyVerified
        } else if info.has_spec && !info.is_verified {
            // Has spec but verification did not pass fully.
            CoverageStatus::HasSpec
        } else if info.is_verified && !info.has_spec {
            // Verified without explicit spec (e.g., default contracts).
            CoverageStatus::PartiallyVerified
        } else {
            CoverageStatus::NoSpec
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helpers ------------------------------------------------------------

    fn pub_verified(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/lib.rs".to_owned(),
            line: 10,
            visibility: Visibility::Public,
            has_spec: true,
            is_verified: true,
            complexity: 20,
            param_count: 2,
        }
    }

    fn pub_no_spec(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/lib.rs".to_owned(),
            line: 30,
            visibility: Visibility::Public,
            has_spec: false,
            is_verified: false,
            complexity: 15,
            param_count: 1,
        }
    }

    fn pub_has_spec_not_verified(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/lib.rs".to_owned(),
            line: 50,
            visibility: Visibility::Public,
            has_spec: true,
            is_verified: false,
            complexity: 30,
            param_count: 3,
        }
    }

    fn private_fn(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/internal.rs".to_owned(),
            line: 5,
            visibility: Visibility::Private,
            has_spec: false,
            is_verified: false,
            complexity: 5,
            param_count: 0,
        }
    }

    fn pub_crate_fn(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/util.rs".to_owned(),
            line: 20,
            visibility: Visibility::PubCrate,
            has_spec: false,
            is_verified: false,
            complexity: 10,
            param_count: 1,
        }
    }

    fn test_fn(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/tests.rs".to_owned(),
            line: 100,
            visibility: Visibility::Private,
            has_spec: false,
            is_verified: false,
            complexity: 3,
            param_count: 0,
        }
    }

    fn high_complexity_pub(name: &str) -> FunctionInfo {
        FunctionInfo {
            name: name.to_owned(),
            file: "src/core.rs".to_owned(),
            line: 200,
            visibility: Visibility::Public,
            has_spec: false,
            is_verified: false,
            complexity: 80,
            param_count: 5,
        }
    }

    fn default_config() -> CoverageConfig {
        CoverageConfig::default()
    }

    fn inclusive_config() -> CoverageConfig {
        CoverageConfig {
            include_private: true,
            include_tests: true,
            threshold_warning: 80.0,
            threshold_error: 50.0,
        }
    }

    fn build_report(config: CoverageConfig, fns: Vec<FunctionInfo>) -> CoverageReport {
        let mut builder = CoverageBuilder::new(config).timestamp("2026-03-28T00:00:00Z");
        for f in fns {
            builder = builder.add_function(f);
        }
        builder.build()
    }

    // -- CoverageConfig tests -----------------------------------------------

    #[test]
    fn test_config_default_excludes_private_and_tests() {
        let cfg = CoverageConfig::default();
        assert!(!cfg.include_private);
        assert!(!cfg.include_tests);
        assert!((cfg.threshold_warning - 80.0).abs() < f64::EPSILON);
        assert!((cfg.threshold_error - 50.0).abs() < f64::EPSILON);
    }

    // -- CoverageStatus tests -----------------------------------------------

    #[test]
    fn test_coverage_status_display() {
        assert_eq!(CoverageStatus::FullyVerified.to_string(), "fully-verified");
        assert_eq!(CoverageStatus::NoSpec.to_string(), "no-spec");
        assert_eq!(CoverageStatus::Excluded.to_string(), "excluded");
        assert_eq!(
            CoverageStatus::PartiallyVerified.to_string(),
            "partially-verified"
        );
        assert_eq!(CoverageStatus::HasSpec.to_string(), "has-spec");
    }

    // -- Visibility tests ---------------------------------------------------

    #[test]
    fn test_visibility_display() {
        assert_eq!(Visibility::Public.to_string(), "pub");
        assert_eq!(Visibility::PubCrate.to_string(), "pub(crate)");
        assert_eq!(Visibility::Private.to_string(), "private");
    }

    // -- Builder classification tests ---------------------------------------

    #[test]
    fn test_builder_classifies_verified_with_spec() {
        let report = build_report(default_config(), vec![pub_verified("foo")]);
        assert_eq!(report.entries.len(), 1);
        assert_eq!(
            report.entries[0].coverage_status,
            CoverageStatus::FullyVerified
        );
    }

    #[test]
    fn test_builder_classifies_no_spec() {
        let report = build_report(default_config(), vec![pub_no_spec("bar")]);
        assert_eq!(report.entries[0].coverage_status, CoverageStatus::NoSpec);
    }

    #[test]
    fn test_builder_classifies_has_spec_not_verified() {
        let report = build_report(default_config(), vec![pub_has_spec_not_verified("baz")]);
        assert_eq!(report.entries[0].coverage_status, CoverageStatus::HasSpec);
    }

    #[test]
    fn test_builder_classifies_partially_verified() {
        let mut info = pub_verified("partial");
        info.has_spec = false;
        let report = build_report(default_config(), vec![info]);
        assert_eq!(
            report.entries[0].coverage_status,
            CoverageStatus::PartiallyVerified
        );
    }

    #[test]
    fn test_builder_excludes_private_by_default() {
        let report = build_report(default_config(), vec![private_fn("helper")]);
        assert_eq!(report.entries[0].coverage_status, CoverageStatus::Excluded);
        assert_eq!(report.summary.total, 0);
        assert_eq!(report.summary.excluded, 1);
    }

    #[test]
    fn test_builder_includes_private_when_configured() {
        let report = build_report(inclusive_config(), vec![private_fn("helper")]);
        assert_eq!(report.entries[0].coverage_status, CoverageStatus::NoSpec);
        assert_eq!(report.summary.total, 1);
    }

    #[test]
    fn test_builder_excludes_test_functions_by_default() {
        let report = build_report(default_config(), vec![test_fn("test_something")]);
        assert_eq!(report.entries[0].coverage_status, CoverageStatus::Excluded);
    }

    #[test]
    fn test_builder_includes_test_functions_when_configured() {
        let report = build_report(inclusive_config(), vec![test_fn("test_something")]);
        // test_fn is also private, but inclusive_config includes private.
        assert_eq!(report.entries[0].coverage_status, CoverageStatus::NoSpec);
    }

    // -- Summary computation tests ------------------------------------------

    #[test]
    fn test_summary_counts_correct() {
        let report = build_report(
            default_config(),
            vec![
                pub_verified("a"),
                pub_verified("b"),
                pub_no_spec("c"),
                pub_has_spec_not_verified("d"),
            ],
        );
        assert_eq!(report.summary.total, 4);
        assert_eq!(report.summary.verified, 2);
        assert_eq!(report.summary.without_spec, 1);
        assert_eq!(report.summary.with_spec, 1);
        assert_eq!(report.summary.partial, 0);
    }

    #[test]
    fn test_summary_coverage_percentage() {
        let report = build_report(default_config(), vec![pub_verified("a"), pub_no_spec("b")]);
        assert!((report.summary.coverage_pct - 50.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_empty_report_100_percent() {
        let report = build_report(default_config(), vec![]);
        assert!((report.summary.coverage_pct - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_all_verified_100_percent() {
        let report = build_report(
            default_config(),
            vec![pub_verified("a"), pub_verified("b"), pub_verified("c")],
        );
        assert!((report.summary.coverage_pct - 100.0).abs() < f64::EPSILON);
    }

    // -- Gap detection tests ------------------------------------------------

    #[test]
    fn test_gaps_returns_no_spec_functions() {
        let report = build_report(
            default_config(),
            vec![pub_verified("ok"), pub_no_spec("gap")],
        );
        let gaps = report.gaps();
        assert_eq!(gaps.len(), 1);
        assert_eq!(gaps[0].function_name, "gap");
    }

    #[test]
    fn test_gaps_returns_has_spec_not_verified() {
        let report = build_report(default_config(), vec![pub_has_spec_not_verified("pending")]);
        let gaps = report.gaps();
        assert_eq!(gaps.len(), 1);
        assert_eq!(gaps[0].function_name, "pending");
    }

    #[test]
    fn test_gaps_empty_when_all_verified() {
        let report = build_report(default_config(), vec![pub_verified("a"), pub_verified("b")]);
        assert!(report.gaps().is_empty());
    }

    #[test]
    fn test_gap_priority_public_no_spec_high() {
        let report = build_report(default_config(), vec![pub_no_spec("f")]);
        let gaps = report.gaps();
        assert_eq!(gaps[0].priority, GapPriority::High);
    }

    #[test]
    fn test_gap_priority_public_high_complexity_critical() {
        let report = build_report(default_config(), vec![high_complexity_pub("complex_fn")]);
        let gaps = report.gaps();
        assert_eq!(gaps[0].priority, GapPriority::Critical);
    }

    #[test]
    fn test_gap_priority_pub_crate_medium() {
        let report = build_report(default_config(), vec![pub_crate_fn("helper")]);
        let gaps = report.gaps();
        assert_eq!(gaps[0].priority, GapPriority::Medium);
    }

    #[test]
    fn test_gap_has_suggested_template() {
        let report = build_report(default_config(), vec![pub_no_spec("f")]);
        let gaps = report.gaps();
        assert!(gaps[0].suggested_spec_template.contains("#[requires("));
        assert!(gaps[0].suggested_spec_template.contains("#[ensures("));
    }

    // -- Recommendation tests -----------------------------------------------

    #[test]
    fn test_recommendations_sorted_by_priority_score() {
        let report = build_report(
            default_config(),
            vec![pub_no_spec("low"), high_complexity_pub("high")],
        );
        let recs = report.recommendations();
        assert_eq!(recs.len(), 2);
        assert!(recs[0].priority_score >= recs[1].priority_score);
        assert_eq!(recs[0].target_function, "high");
    }

    #[test]
    fn test_recommendations_empty_when_fully_covered() {
        let report = build_report(default_config(), vec![pub_verified("a")]);
        assert!(report.recommendations().is_empty());
    }

    // -- RecommendationEngine tests -----------------------------------------

    #[test]
    fn test_engine_score_public_higher_than_private() {
        let engine = RecommendationEngine::default();
        let pub_fn = pub_no_spec("pub_fn");
        let priv_fn = private_fn("priv_fn");
        assert!(engine.score(&pub_fn) > engine.score(&priv_fn));
    }

    #[test]
    fn test_engine_score_increases_with_complexity() {
        let engine = RecommendationEngine::default();
        let low = pub_no_spec("low");
        let high = high_complexity_pub("high");
        assert!(engine.score(&high) > engine.score(&low));
    }

    #[test]
    fn test_engine_suggest_template_includes_decreases_for_complex() {
        let info = high_complexity_pub("complex");
        let template = RecommendationEngine::suggest_template(&info);
        assert!(template.contains("#[decreases("));
    }

    #[test]
    fn test_engine_suggest_template_no_decreases_for_simple() {
        let info = pub_no_spec("simple");
        let template = RecommendationEngine::suggest_template(&info);
        assert!(!template.contains("#[decreases("));
    }

    // -- Threshold tests ----------------------------------------------------

    #[test]
    fn test_threshold_passes_above_warning() {
        let t = CoverageThreshold::new(80.0, 50.0);
        assert!(t.check(90.0).is_ok());
    }

    #[test]
    fn test_threshold_warns_below_warning() {
        let t = CoverageThreshold::new(80.0, 50.0);
        let err = t.check(70.0).unwrap_err();
        assert_eq!(err.len(), 1);
        assert!(err[0].contains("WARNING"));
    }

    #[test]
    fn test_threshold_errors_below_error() {
        let t = CoverageThreshold::new(80.0, 50.0);
        let err = t.check(40.0).unwrap_err();
        assert_eq!(err.len(), 2);
        assert!(err[0].contains("ERROR"));
        assert!(err[1].contains("WARNING"));
    }

    #[test]
    fn test_check_thresholds_integration() {
        let report = build_report(
            CoverageConfig {
                threshold_warning: 80.0,
                threshold_error: 50.0,
                ..default_config()
            },
            vec![
                pub_verified("a"),
                pub_no_spec("b"),
                pub_no_spec("c"),
                pub_no_spec("d"),
            ],
        );
        // 25% coverage → below error threshold.
        let err = report.check_thresholds().unwrap_err();
        assert!(err.iter().any(|v| v.contains("ERROR")));
    }

    // -- Rendering tests ----------------------------------------------------

    #[test]
    fn test_render_text_contains_header() {
        let report = build_report(default_config(), vec![pub_verified("a")]);
        let text = report.render_text();
        assert!(text.contains("Verification Coverage Report"));
        assert!(text.contains("Coverage:"));
    }

    #[test]
    fn test_render_text_shows_gaps() {
        let report = build_report(default_config(), vec![pub_no_spec("missing")]);
        let text = report.render_text();
        assert!(text.contains("Coverage Gaps"));
        assert!(text.contains("missing"));
    }

    #[test]
    fn test_render_markdown_has_table() {
        let report = build_report(default_config(), vec![pub_verified("a"), pub_no_spec("b")]);
        let md = report.render_markdown();
        assert!(md.contains("| Metric | Value |"));
        assert!(md.contains("| Coverage |"));
        assert!(md.contains("## Coverage Gaps"));
    }

    #[test]
    fn test_render_json_parses() {
        let report = build_report(default_config(), vec![pub_verified("a")]);
        let json = report.render_json();
        let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
        assert!(parsed.get("summary").is_some());
        assert!(parsed.get("entries").is_some());
    }

    #[test]
    fn test_render_csv_has_header_and_rows() {
        let report = build_report(default_config(), vec![pub_verified("a"), pub_no_spec("b")]);
        let csv = report.render_csv();
        let lines: Vec<&str> = csv.lines().collect();
        assert_eq!(lines.len(), 3); // header + 2 rows
        assert!(lines[0].starts_with("function,file,"));
    }

    // -- CoverageComparison tests -------------------------------------------

    #[test]
    fn test_comparison_detects_improvement() {
        let old = build_report(default_config(), vec![pub_verified("a"), pub_no_spec("b")]);
        let new = build_report(default_config(), vec![pub_verified("a"), pub_verified("b")]);
        let cmp = CoverageComparison::diff(&old, &new);
        assert!(cmp.is_improvement());
        assert!((cmp.delta_pct - 50.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_comparison_detects_regression() {
        let old = build_report(default_config(), vec![pub_verified("a"), pub_verified("b")]);
        let new = build_report(default_config(), vec![pub_no_spec("a"), pub_verified("b")]);
        let cmp = CoverageComparison::diff(&old, &new);
        assert!(cmp.has_regressions());
        assert!(cmp.regressions.contains(&"a".to_string()));
    }

    #[test]
    fn test_comparison_detects_new_gaps() {
        let old = build_report(default_config(), vec![pub_verified("a")]);
        let new = build_report(default_config(), vec![pub_verified("a"), pub_no_spec("b")]);
        let cmp = CoverageComparison::diff(&old, &new);
        assert!(cmp.new_gaps.contains(&"b".to_string()));
    }

    #[test]
    fn test_comparison_detects_closed_gaps() {
        let old = build_report(default_config(), vec![pub_no_spec("a"), pub_verified("b")]);
        let new = build_report(default_config(), vec![pub_verified("a"), pub_verified("b")]);
        let cmp = CoverageComparison::diff(&old, &new);
        assert!(cmp.closed_gaps.contains(&"a".to_string()));
    }

    #[test]
    fn test_comparison_no_change() {
        let old = build_report(default_config(), vec![pub_verified("a")]);
        let new = build_report(default_config(), vec![pub_verified("a")]);
        let cmp = CoverageComparison::diff(&old, &new);
        assert!(!cmp.is_improvement());
        assert!(!cmp.has_regressions());
        assert!(cmp.new_gaps.is_empty());
        assert!(cmp.closed_gaps.is_empty());
    }

    // -- CoverageTrend tests ------------------------------------------------

    #[test]
    fn test_trend_serialization_roundtrip() {
        let trend = CoverageTrend {
            timestamp: "2026-03-28T00:00:00Z".to_owned(),
            coverage_pct: 75.5,
            total_functions: 100,
            verified_functions: 75,
        };
        let json = serde_json::to_string(&trend).expect("serialize");
        let deserialized: CoverageTrend = serde_json::from_str(&json).expect("deserialize");
        assert!((deserialized.coverage_pct - 75.5).abs() < f64::EPSILON);
        assert_eq!(deserialized.total_functions, 100);
    }

    // -- GapPriority ordering tests -----------------------------------------

    #[test]
    fn test_gap_priority_ordering() {
        assert!(GapPriority::Critical < GapPriority::High);
        assert!(GapPriority::High < GapPriority::Medium);
        assert!(GapPriority::Medium < GapPriority::Low);
    }

    // -- Builder timestamp test ---------------------------------------------

    #[test]
    fn test_builder_default_timestamp() {
        let report = CoverageBuilder::new(default_config())
            .add_function(pub_verified("a"))
            .build();
        assert_eq!(report.timestamp, "unknown");
    }

    #[test]
    fn test_builder_custom_timestamp() {
        let report = CoverageBuilder::new(default_config())
            .timestamp("2026-01-01")
            .add_function(pub_verified("a"))
            .build();
        assert_eq!(report.timestamp, "2026-01-01");
    }

    // -- Entry recommendation presence tests --------------------------------

    #[test]
    fn test_entry_has_recommendation_for_no_spec() {
        let report = build_report(default_config(), vec![pub_no_spec("gap_fn")]);
        assert!(report.entries[0].recommendation.is_some());
        let rec = report.entries[0].recommendation.as_ref().unwrap();
        assert_eq!(rec.target_function, "gap_fn");
        assert!(rec.template.contains("#[requires("));
    }

    #[test]
    fn test_entry_no_recommendation_for_verified() {
        let report = build_report(default_config(), vec![pub_verified("ok_fn")]);
        assert!(report.entries[0].recommendation.is_none());
    }

    // -- Mixed report test --------------------------------------------------

    #[test]
    fn test_mixed_report_comprehensive() {
        let report = build_report(
            default_config(),
            vec![
                pub_verified("verified_a"),
                pub_verified("verified_b"),
                pub_no_spec("no_spec_c"),
                pub_has_spec_not_verified("has_spec_d"),
                private_fn("private_e"),
                pub_crate_fn("pub_crate_f"),
                high_complexity_pub("complex_g"),
            ],
        );
        // private_e excluded, rest counted.
        assert_eq!(report.summary.total, 6);
        assert_eq!(report.summary.verified, 2);
        assert_eq!(report.summary.with_spec, 1);
        assert_eq!(report.summary.without_spec, 3);
        assert_eq!(report.summary.excluded, 1);

        let gaps = report.gaps();
        assert_eq!(gaps.len(), 4); // no_spec_c, has_spec_d, pub_crate_f, complex_g

        let recs = report.recommendations();
        assert_eq!(recs.len(), 4);
        // complex_g should be first (highest score).
        assert_eq!(recs[0].target_function, "complex_g");
    }

    // -- Render text threshold message test ---------------------------------

    #[test]
    fn test_render_text_shows_threshold_violations() {
        let report = build_report(
            CoverageConfig {
                threshold_warning: 90.0,
                threshold_error: 70.0,
                ..default_config()
            },
            vec![pub_verified("a"), pub_no_spec("b")],
        );
        let text = report.render_text();
        assert!(text.contains("ERROR"));
        assert!(text.contains("WARNING"));
    }

    // -- Render markdown no gaps section when all verified -------------------

    #[test]
    fn test_render_markdown_no_gaps_section_when_covered() {
        let report = build_report(default_config(), vec![pub_verified("a"), pub_verified("b")]);
        let md = report.render_markdown();
        assert!(!md.contains("## Coverage Gaps"));
    }

    // -- CSV field count test -----------------------------------------------

    #[test]
    fn test_render_csv_correct_field_count() {
        let report = build_report(default_config(), vec![pub_verified("a")]);
        let csv = report.render_csv();
        for line in csv.lines() {
            assert_eq!(line.split(',').count(), 9);
        }
    }
}
