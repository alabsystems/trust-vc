// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof status dashboard for the cargo-trust-vc CLI.
//!
//! Aggregates verification results across a project, tracks proof coverage,
//! identifies unverified functions, and generates summary reports in multiple
//! output formats (text, JSON, Markdown, CSV).

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::format_types::ReportFormat;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Function verification status.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum ProofStatus {
    Verified {
        elapsed: Duration,
        solver_mode: String,
    },
    Failed {
        obligation: String,
        counterexample: Option<String>,
    },
    Unknown {
        reason: String,
        is_retriable: bool,
    },
    Timeout {
        elapsed: Duration,
    },
    NotAttempted,
    Skipped {
        reason: String,
    },
}

impl ProofStatus {
    /// Returns the elapsed duration if available (Verified or Timeout).
    #[must_use]
    pub fn elapsed(&self) -> Option<Duration> {
        match self {
            Self::Verified { elapsed, .. } | Self::Timeout { elapsed } => Some(*elapsed),
            _ => None,
        }
    }

    /// Returns `true` when the function was successfully verified.
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified { .. })
    }

    /// Returns `true` when verification produced a definite failure.
    #[must_use]
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed { .. })
    }
}

/// A single function's proof record.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct FunctionProofRecord {
    pub name: String,
    pub file: PathBuf,
    pub line: usize,
    pub status: ProofStatus,
    pub has_requires: bool,
    pub has_ensures: bool,
    pub has_decreases: bool,
    pub assertion_count: usize,
    pub complexity_score: usize,
}

/// Module-level proof summary.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ModuleProofSummary {
    pub path: PathBuf,
    pub total_functions: usize,
    pub verified: usize,
    pub failed: usize,
    pub unknown: usize,
    pub not_attempted: usize,
    pub coverage_percent: f64,
    pub total_elapsed: Duration,
}

impl ModuleProofSummary {
    /// Compute a module summary from a slice of records that all belong to the
    /// same module path.
    #[must_use]
    pub fn from_records(path: &Path, records: &[FunctionProofRecord]) -> Self {
        let total_functions = records.len();
        let mut verified = 0usize;
        let mut failed = 0usize;
        let mut unknown = 0usize;
        let mut not_attempted = 0usize;
        let mut total_elapsed = Duration::ZERO;

        for r in records {
            match &r.status {
                ProofStatus::Verified { elapsed, .. } => {
                    verified += 1;
                    total_elapsed += *elapsed;
                }
                ProofStatus::Failed { .. } => failed += 1,
                ProofStatus::Unknown { .. } => unknown += 1,
                ProofStatus::Timeout { elapsed } => {
                    failed += 1;
                    total_elapsed += *elapsed;
                }
                ProofStatus::NotAttempted => not_attempted += 1,
                ProofStatus::Skipped { .. } => not_attempted += 1,
            }
        }

        let coverage_percent = if total_functions == 0 {
            0.0
        } else {
            (verified as f64 / total_functions as f64) * 100.0
        };

        Self {
            path: path.to_path_buf(),
            total_functions,
            verified,
            failed,
            unknown,
            not_attempted,
            coverage_percent,
            total_elapsed,
        }
    }
}

/// Project-wide dashboard.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ProofDashboard {
    pub project_name: String,
    pub modules: Vec<ModuleProofSummary>,
    pub functions: Vec<FunctionProofRecord>,
    pub overall_stats: DashboardStats,
    pub generated_at: String,
}

/// Aggregate statistics across all functions.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct DashboardStats {
    pub total_functions: usize,
    pub verified_count: usize,
    pub failed_count: usize,
    pub unknown_count: usize,
    pub timeout_count: usize,
    pub not_attempted_count: usize,
    pub skipped_count: usize,
    pub coverage_percent: f64,
    pub total_elapsed: Duration,
    pub average_verification_time: Duration,
    pub max_verification_time: Duration,
    pub total_assertions: usize,
    pub complexity_histogram: Vec<(String, usize)>,
}

impl DashboardStats {
    /// Compute aggregate statistics from a slice of function records.
    #[must_use]
    pub fn compute(records: &[FunctionProofRecord]) -> Self {
        let total_functions = records.len();
        let mut verified_count = 0usize;
        let mut failed_count = 0usize;
        let mut unknown_count = 0usize;
        let mut timeout_count = 0usize;
        let mut not_attempted_count = 0usize;
        let mut skipped_count = 0usize;
        let mut total_elapsed = Duration::ZERO;
        let mut max_verification_time = Duration::ZERO;
        let mut total_assertions = 0usize;
        let mut verified_durations_count = 0usize;

        let mut low = 0usize;
        let mut medium = 0usize;
        let mut high = 0usize;
        let mut critical = 0usize;

        for r in records {
            total_assertions += r.assertion_count;

            match Self::complexity_category(r.complexity_score) {
                "low" => low += 1,
                "medium" => medium += 1,
                "high" => high += 1,
                _ => critical += 1,
            }

            match &r.status {
                ProofStatus::Verified { elapsed, .. } => {
                    verified_count += 1;
                    total_elapsed += *elapsed;
                    verified_durations_count += 1;
                    if *elapsed > max_verification_time {
                        max_verification_time = *elapsed;
                    }
                }
                ProofStatus::Failed { .. } => failed_count += 1,
                ProofStatus::Unknown { .. } => unknown_count += 1,
                ProofStatus::Timeout { elapsed } => {
                    timeout_count += 1;
                    total_elapsed += *elapsed;
                    if *elapsed > max_verification_time {
                        max_verification_time = *elapsed;
                    }
                }
                ProofStatus::NotAttempted => not_attempted_count += 1,
                ProofStatus::Skipped { .. } => skipped_count += 1,
            }
        }

        let coverage_percent = if total_functions == 0 {
            0.0
        } else {
            (verified_count as f64 / total_functions as f64) * 100.0
        };

        let average_verification_time = if verified_durations_count == 0 {
            Duration::ZERO
        } else {
            total_elapsed / u32::try_from(verified_durations_count).unwrap_or(u32::MAX)
        };

        let complexity_histogram = vec![
            ("low".to_owned(), low),
            ("medium".to_owned(), medium),
            ("high".to_owned(), high),
            ("critical".to_owned(), critical),
        ];

        Self {
            total_functions,
            verified_count,
            failed_count,
            unknown_count,
            timeout_count,
            not_attempted_count,
            skipped_count,
            coverage_percent,
            total_elapsed,
            average_verification_time,
            max_verification_time,
            total_assertions,
            complexity_histogram,
        }
    }

    /// Classify a complexity score into a human-readable category.
    #[must_use]
    pub fn complexity_category(score: usize) -> &'static str {
        match score {
            0..=10 => "low",
            11..=50 => "medium",
            51..=100 => "high",
            _ => "critical",
        }
    }
}

// ---------------------------------------------------------------------------
// Trend tracking
// ---------------------------------------------------------------------------

/// A single historical snapshot for trend tracking.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ProofTrend {
    pub timestamp: String,
    pub verified: usize,
    pub failed: usize,
    pub total: usize,
    pub coverage: f64,
}

// ---------------------------------------------------------------------------
// Priority ranking
// ---------------------------------------------------------------------------

/// Priority ranking for an unverified function.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationPriority {
    pub function_name: String,
    pub file: PathBuf,
    pub priority_score: f64,
    pub reason: String,
}

// ---------------------------------------------------------------------------
// Dashboard builder
// ---------------------------------------------------------------------------

/// Incrementally constructs a [`ProofDashboard`].
#[must_use]
pub struct DashboardBuilder {
    project_name: String,
    records: Vec<FunctionProofRecord>,
    trends: Vec<ProofTrend>,
    generated_at: String,
}

impl DashboardBuilder {
    /// Create a new builder for the given project.
    pub fn new(project_name: &str) -> Self {
        Self {
            project_name: project_name.to_owned(),
            records: Vec::new(),
            trends: Vec::new(),
            generated_at: String::new(),
        }
    }

    /// Append a function proof record.
    pub fn add_record(&mut self, record: FunctionProofRecord) -> &mut Self {
        self.records.push(record);
        self
    }

    /// Append a historical trend data-point.
    pub fn add_trend(&mut self, trend: ProofTrend) -> &mut Self {
        self.trends.push(trend);
        self
    }

    /// Override the generated-at timestamp (useful for deterministic tests).
    pub fn set_generated_at(&mut self, ts: &str) -> &mut Self {
        self.generated_at = ts.to_owned();
        self
    }

    /// Consume the builder and produce a [`ProofDashboard`].
    pub fn build(self) -> ProofDashboard {
        // Group records by file to produce module summaries.
        let mut by_module: BTreeMap<PathBuf, Vec<FunctionProofRecord>> = BTreeMap::new();
        for r in &self.records {
            by_module.entry(r.file.clone()).or_default().push(r.clone());
        }

        let modules: Vec<ModuleProofSummary> = by_module
            .iter()
            .map(|(path, recs)| ModuleProofSummary::from_records(path, recs))
            .collect();

        let overall_stats = DashboardStats::compute(&self.records);

        let generated_at = if self.generated_at.is_empty() {
            "unknown".to_owned()
        } else {
            self.generated_at
        };

        ProofDashboard {
            project_name: self.project_name,
            modules,
            functions: self.records,
            overall_stats,
            generated_at,
        }
    }
}

// ---------------------------------------------------------------------------
// Dashboard methods
// ---------------------------------------------------------------------------

impl ProofDashboard {
    /// Render the dashboard in the given format.
    #[must_use]
    pub fn render(&self, format: ReportFormat) -> String {
        match format {
            ReportFormat::Text => self.render_text(),
            ReportFormat::Json => self.render_json(),
            ReportFormat::Markdown => self.render_markdown(),
            ReportFormat::Csv => self.render_csv(),
        }
    }

    /// Per-module coverage as `(path, coverage_percent)` pairs, sorted by path.
    #[must_use]
    pub fn coverage_by_module(&self) -> Vec<(PathBuf, f64)> {
        self.modules
            .iter()
            .map(|m| (m.path.clone(), m.coverage_percent))
            .collect()
    }

    /// All functions that are NOT verified (failed, unknown, timeout, not
    /// attempted, or skipped).
    #[must_use]
    pub fn unverified_functions(&self) -> Vec<&FunctionProofRecord> {
        self.functions
            .iter()
            .filter(|f| !f.status.is_verified())
            .collect()
    }

    /// Rank unverified functions by verification priority.
    ///
    /// Higher scores mean "verify this first." The heuristic weights:
    /// - complexity score (higher = more important to verify)
    /// - contract presence (has requires/ensures = more important)
    /// - assertion count (more assertions = more important)
    /// - failure status (failed > unknown > not attempted)
    #[must_use]
    pub fn prioritize_verification(&self) -> Vec<VerificationPriority> {
        let mut priorities: Vec<VerificationPriority> = self
            .functions
            .iter()
            .filter(|f| !f.status.is_verified())
            .map(|f| {
                let mut score = f.complexity_score as f64;

                // Contract presence multiplier.
                if f.has_requires {
                    score += 20.0;
                }
                if f.has_ensures {
                    score += 20.0;
                }
                if f.has_decreases {
                    score += 10.0;
                }

                // Assertions make a function more important to verify.
                score += f.assertion_count as f64 * 5.0;

                // Status-based boost: failures are more urgent than unknowns.
                let status_reason = match &f.status {
                    ProofStatus::Failed { obligation, .. } => {
                        score += 50.0;
                        format!("failed obligation: {obligation}")
                    }
                    ProofStatus::Unknown { reason, .. } => {
                        score += 30.0;
                        format!("unknown: {reason}")
                    }
                    ProofStatus::Timeout { elapsed } => {
                        score += 40.0;
                        format!("timeout after {:.1}s", elapsed.as_secs_f64())
                    }
                    ProofStatus::Skipped { reason } => {
                        score += 5.0;
                        format!("skipped: {reason}")
                    }
                    ProofStatus::NotAttempted => "not yet attempted".to_owned(),
                    ProofStatus::Verified { .. } => unreachable!(),
                };

                VerificationPriority {
                    function_name: f.name.clone(),
                    file: f.file.clone(),
                    priority_score: score,
                    reason: status_reason,
                }
            })
            .collect();

        priorities.sort_by(|a, b| {
            b.priority_score
                .partial_cmp(&a.priority_score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        priorities
    }

    /// Compare against a previous dashboard and return human-readable
    /// regression descriptions.
    ///
    /// A regression is any function that was `Verified` in `previous` but is
    /// no longer `Verified` in `self`.
    #[must_use]
    pub fn regression_check(&self, previous: &ProofDashboard) -> Vec<String> {
        let prev_verified: HashMap<&str, &FunctionProofRecord> = previous
            .functions
            .iter()
            .filter(|f| f.status.is_verified())
            .map(|f| (f.name.as_str(), f))
            .collect();

        let mut regressions = Vec::new();
        for name in prev_verified.keys() {
            match self.functions.iter().find(|f| f.name == *name) {
                Some(cur) if !cur.status.is_verified() => {
                    let desc = match &cur.status {
                        ProofStatus::Failed { obligation, .. } => {
                            format!("now fails: {obligation}")
                        }
                        ProofStatus::Unknown { reason, .. } => {
                            format!("now unknown: {reason}")
                        }
                        ProofStatus::Timeout { elapsed } => {
                            format!("now timeout after {:.1}s", elapsed.as_secs_f64())
                        }
                        ProofStatus::NotAttempted => "now not attempted".to_owned(),
                        ProofStatus::Skipped { reason } => {
                            format!("now skipped: {reason}")
                        }
                        ProofStatus::Verified { .. } => unreachable!(),
                    };
                    regressions.push(format!("REGRESSION: {name} — {desc}"));
                }
                None => {
                    regressions.push(format!("REGRESSION: {name} — removed from current run"));
                }
                _ => {} // still verified
            }
        }
        regressions.sort();
        regressions
    }

    // -- Renderers ----------------------------------------------------------

    /// Render as plain ASCII text.
    #[must_use]
    pub fn render_text(&self) -> String {
        let s = &self.overall_stats;
        let mut out = String::new();

        let _ = writeln!(out, "=== Proof Dashboard: {} ===", self.project_name);
        let _ = writeln!(out, "Generated: {}", self.generated_at);
        let _ = writeln!(out);

        let _ = writeln!(
            out,
            "Overall: {}/{} verified ({:.1}%)",
            s.verified_count, s.total_functions, s.coverage_percent
        );
        let _ = writeln!(
            out,
            "  Failed: {}  Unknown: {}  Timeout: {}  Skipped: {}  Not attempted: {}",
            s.failed_count,
            s.unknown_count,
            s.timeout_count,
            s.skipped_count,
            s.not_attempted_count
        );
        let _ = writeln!(
            out,
            "  Total time: {:.2}s  Avg: {:.2}s  Max: {:.2}s",
            s.total_elapsed.as_secs_f64(),
            s.average_verification_time.as_secs_f64(),
            s.max_verification_time.as_secs_f64(),
        );
        let _ = writeln!(out, "  Assertions: {}", s.total_assertions);
        let _ = writeln!(out);

        // Module table.
        let _ = writeln!(out, "--- Modules ---");
        let _ = writeln!(
            out,
            "{:<40} {:>5} {:>5} {:>5} {:>8}",
            "Module", "Total", "Pass", "Fail", "Cov%"
        );
        for m in &self.modules {
            let _ = writeln!(
                out,
                "{:<40} {:>5} {:>5} {:>5} {:>7.1}%",
                m.path.display(),
                m.total_functions,
                m.verified,
                m.failed,
                m.coverage_percent,
            );
        }
        let _ = writeln!(out);

        // Function detail for non-verified.
        let unverified = self.unverified_functions();
        if !unverified.is_empty() {
            let _ = writeln!(out, "--- Unverified Functions ---");
            for f in &unverified {
                let status_str = match &f.status {
                    ProofStatus::Failed { obligation, .. } => {
                        format!("FAILED ({obligation})")
                    }
                    ProofStatus::Unknown { reason, .. } => format!("UNKNOWN ({reason})"),
                    ProofStatus::Timeout { elapsed } => {
                        format!("TIMEOUT ({:.1}s)", elapsed.as_secs_f64())
                    }
                    ProofStatus::NotAttempted => "NOT ATTEMPTED".to_owned(),
                    ProofStatus::Skipped { reason } => format!("SKIPPED ({reason})"),
                    ProofStatus::Verified { .. } => unreachable!(),
                };
                let _ = writeln!(
                    out,
                    "  {}:{} {} — {}",
                    f.file.display(),
                    f.line,
                    f.name,
                    status_str,
                );
            }
        }

        out
    }

    /// Render as JSON via serde_json.
    #[must_use]
    pub fn render_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"))
    }

    /// Render as GitHub-Flavored Markdown tables.
    #[must_use]
    pub fn render_markdown(&self) -> String {
        let s = &self.overall_stats;
        let mut out = String::new();

        let _ = writeln!(out, "# Proof Dashboard: {}", self.project_name);
        let _ = writeln!(out);
        let _ = writeln!(out, "_Generated: {}_", self.generated_at);
        let _ = writeln!(out);

        let _ = writeln!(out, "## Summary");
        let _ = writeln!(out);
        let _ = writeln!(out, "| Metric | Value |");
        let _ = writeln!(out, "|--------|-------|");
        let _ = writeln!(out, "| Total functions | {} |", s.total_functions);
        let _ = writeln!(out, "| Verified | {} |", s.verified_count);
        let _ = writeln!(out, "| Failed | {} |", s.failed_count);
        let _ = writeln!(out, "| Unknown | {} |", s.unknown_count);
        let _ = writeln!(out, "| Timeout | {} |", s.timeout_count);
        let _ = writeln!(out, "| Skipped | {} |", s.skipped_count);
        let _ = writeln!(out, "| Not attempted | {} |", s.not_attempted_count);
        let _ = writeln!(out, "| Coverage | {:.1}% |", s.coverage_percent);
        let _ = writeln!(
            out,
            "| Total time | {:.2}s |",
            s.total_elapsed.as_secs_f64()
        );
        let _ = writeln!(out, "| Total assertions | {} |", s.total_assertions);
        let _ = writeln!(out);

        // Module table.
        let _ = writeln!(out, "## Modules");
        let _ = writeln!(out);
        let _ = writeln!(out, "| Module | Total | Verified | Failed | Coverage |");
        let _ = writeln!(out, "|--------|-------|----------|--------|----------|");
        for m in &self.modules {
            let _ = writeln!(
                out,
                "| {} | {} | {} | {} | {:.1}% |",
                m.path.display(),
                m.total_functions,
                m.verified,
                m.failed,
                m.coverage_percent,
            );
        }
        let _ = writeln!(out);

        // Unverified.
        let unverified = self.unverified_functions();
        if !unverified.is_empty() {
            let _ = writeln!(out, "## Unverified Functions");
            let _ = writeln!(out);
            let _ = writeln!(out, "| Function | File | Line | Status |");
            let _ = writeln!(out, "|----------|------|------|--------|");
            for f in &unverified {
                let status_str = status_short_description(&f.status);
                let _ = writeln!(
                    out,
                    "| {} | {} | {} | {} |",
                    f.name,
                    f.file.display(),
                    f.line,
                    status_str,
                );
            }
        }

        out
    }

    /// Render as CSV with a header row.
    #[must_use]
    pub fn render_csv(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "name,file,line,status,has_requires,has_ensures,has_decreases,assertion_count,complexity_score"
        );
        for f in &self.functions {
            let status_label = status_csv_label(&f.status);
            let _ = writeln!(
                out,
                "{},{},{},{},{},{},{},{},{}",
                csv_escape(&f.name),
                csv_escape(&f.file.display().to_string()),
                f.line,
                status_label,
                f.has_requires,
                f.has_ensures,
                f.has_decreases,
                f.assertion_count,
                f.complexity_score,
            );
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn status_short_description(status: &ProofStatus) -> String {
    match status {
        ProofStatus::Verified { solver_mode, .. } => format!("Verified ({solver_mode})"),
        ProofStatus::Failed { obligation, .. } => format!("Failed: {obligation}"),
        ProofStatus::Unknown { reason, .. } => format!("Unknown: {reason}"),
        ProofStatus::Timeout { elapsed } => {
            format!("Timeout ({:.1}s)", elapsed.as_secs_f64())
        }
        ProofStatus::NotAttempted => "Not attempted".to_owned(),
        ProofStatus::Skipped { reason } => format!("Skipped: {reason}"),
    }
}

fn status_csv_label(status: &ProofStatus) -> &'static str {
    match status {
        ProofStatus::Verified { .. } => "verified",
        ProofStatus::Failed { .. } => "failed",
        ProofStatus::Unknown { .. } => "unknown",
        ProofStatus::Timeout { .. } => "timeout",
        ProofStatus::NotAttempted => "not_attempted",
        ProofStatus::Skipped { .. } => "skipped",
    }
}

/// Minimal CSV escaping: wrap in quotes if the value contains commas, quotes,
/// or newlines.
fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_owned()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Test helpers -------------------------------------------------------

    fn verified_record(name: &str, file: &str, line: usize) -> FunctionProofRecord {
        FunctionProofRecord {
            name: name.to_owned(),
            file: PathBuf::from(file),
            line,
            status: ProofStatus::Verified {
                elapsed: Duration::from_millis(100),
                solver_mode: "Default".to_owned(),
            },
            has_requires: true,
            has_ensures: true,
            has_decreases: false,
            assertion_count: 2,
            complexity_score: 15,
        }
    }

    fn failed_record(name: &str, file: &str, line: usize) -> FunctionProofRecord {
        FunctionProofRecord {
            name: name.to_owned(),
            file: PathBuf::from(file),
            line,
            status: ProofStatus::Failed {
                obligation: "postcondition".to_owned(),
                counterexample: Some("x = 42".to_owned()),
            },
            has_requires: true,
            has_ensures: true,
            has_decreases: false,
            assertion_count: 3,
            complexity_score: 60,
        }
    }

    fn unknown_record(name: &str, file: &str, line: usize) -> FunctionProofRecord {
        FunctionProofRecord {
            name: name.to_owned(),
            file: PathBuf::from(file),
            line,
            status: ProofStatus::Unknown {
                reason: "quantifier instantiation".to_owned(),
                is_retriable: true,
            },
            has_requires: false,
            has_ensures: false,
            has_decreases: false,
            assertion_count: 1,
            complexity_score: 30,
        }
    }

    fn timeout_record(name: &str, file: &str, line: usize) -> FunctionProofRecord {
        FunctionProofRecord {
            name: name.to_owned(),
            file: PathBuf::from(file),
            line,
            status: ProofStatus::Timeout {
                elapsed: Duration::from_secs(60),
            },
            has_requires: true,
            has_ensures: true,
            has_decreases: true,
            assertion_count: 10,
            complexity_score: 120,
        }
    }

    fn not_attempted_record(name: &str, file: &str, line: usize) -> FunctionProofRecord {
        FunctionProofRecord {
            name: name.to_owned(),
            file: PathBuf::from(file),
            line,
            status: ProofStatus::NotAttempted,
            has_requires: false,
            has_ensures: false,
            has_decreases: false,
            assertion_count: 0,
            complexity_score: 5,
        }
    }

    fn skipped_record(name: &str, file: &str, line: usize) -> FunctionProofRecord {
        FunctionProofRecord {
            name: name.to_owned(),
            file: PathBuf::from(file),
            line,
            status: ProofStatus::Skipped {
                reason: "external_body".to_owned(),
            },
            has_requires: false,
            has_ensures: true,
            has_decreases: false,
            assertion_count: 0,
            complexity_score: 3,
        }
    }

    fn build_dashboard(records: Vec<FunctionProofRecord>) -> ProofDashboard {
        let mut builder = DashboardBuilder::new("test-project");
        builder.set_generated_at("2026-03-28T00:00:00Z");
        for r in records {
            builder.add_record(r);
        }
        builder.build()
    }

    // -- Tests --------------------------------------------------------------

    #[test]
    fn test_dashboard_builder_empty_dashboard() {
        let dash = build_dashboard(vec![]);
        assert_eq!(dash.project_name, "test-project");
        assert!(dash.functions.is_empty());
        assert!(dash.modules.is_empty());
        assert_eq!(dash.overall_stats.total_functions, 0);
        assert_eq!(dash.overall_stats.coverage_percent, 0.0);
    }

    #[test]
    fn test_dashboard_builder_single_verified() {
        let dash = build_dashboard(vec![verified_record("foo", "src/lib.rs", 10)]);
        assert_eq!(dash.overall_stats.total_functions, 1);
        assert_eq!(dash.overall_stats.verified_count, 1);
        assert_eq!(dash.overall_stats.coverage_percent, 100.0);
    }

    #[test]
    fn test_dashboard_builder_single_failed() {
        let dash = build_dashboard(vec![failed_record("bar", "src/lib.rs", 20)]);
        assert_eq!(dash.overall_stats.failed_count, 1);
        assert_eq!(dash.overall_stats.verified_count, 0);
        assert_eq!(dash.overall_stats.coverage_percent, 0.0);
    }

    #[test]
    fn test_dashboard_builder_single_unknown() {
        let dash = build_dashboard(vec![unknown_record("baz", "src/lib.rs", 30)]);
        assert_eq!(dash.overall_stats.unknown_count, 1);
        assert_eq!(dash.overall_stats.coverage_percent, 0.0);
    }

    #[test]
    fn test_module_summary_from_records_basic() {
        let records = vec![
            verified_record("a", "src/mod.rs", 1),
            failed_record("b", "src/mod.rs", 10),
        ];
        let summary = ModuleProofSummary::from_records(Path::new("src/mod.rs"), &records);
        assert_eq!(summary.total_functions, 2);
        assert_eq!(summary.verified, 1);
        assert_eq!(summary.failed, 1);
        assert_eq!(summary.coverage_percent, 50.0);
    }

    #[test]
    fn test_module_summary_empty_records() {
        let summary = ModuleProofSummary::from_records(Path::new("src/empty.rs"), &[]);
        assert_eq!(summary.total_functions, 0);
        assert_eq!(summary.coverage_percent, 0.0);
        assert_eq!(summary.total_elapsed, Duration::ZERO);
    }

    #[test]
    fn test_coverage_percent_accuracy() {
        let records = vec![
            verified_record("a", "src/lib.rs", 1),
            verified_record("b", "src/lib.rs", 10),
            failed_record("c", "src/lib.rs", 20),
        ];
        let dash = build_dashboard(records);
        // 2 out of 3 => 66.666...%
        let cov = dash.overall_stats.coverage_percent;
        assert!((cov - 66.666_666_666).abs() < 0.01);
    }

    #[test]
    fn test_coverage_by_module_multiple_modules() {
        let records = vec![
            verified_record("a", "src/alpha.rs", 1),
            verified_record("b", "src/alpha.rs", 10),
            failed_record("c", "src/beta.rs", 1),
        ];
        let dash = build_dashboard(records);
        let coverage = dash.coverage_by_module();
        assert_eq!(coverage.len(), 2);

        // BTreeMap ordering: alpha before beta.
        assert_eq!(coverage[0].0, PathBuf::from("src/alpha.rs"));
        assert_eq!(coverage[0].1, 100.0);

        assert_eq!(coverage[1].0, PathBuf::from("src/beta.rs"));
        assert_eq!(coverage[1].1, 0.0);
    }

    #[test]
    fn test_unverified_functions_returns_non_verified_only() {
        let records = vec![
            verified_record("ok", "src/lib.rs", 1),
            failed_record("bad", "src/lib.rs", 10),
            not_attempted_record("lazy", "src/lib.rs", 20),
        ];
        let dash = build_dashboard(records);
        let unverified = dash.unverified_functions();
        assert_eq!(unverified.len(), 2);
        let names: Vec<&str> = unverified.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"bad"));
        assert!(names.contains(&"lazy"));
    }

    #[test]
    fn test_prioritize_complex_unverified_over_simple() {
        let records = vec![
            // Complex failed function with contracts.
            failed_record("complex_fn", "src/lib.rs", 1),
            // Simple not-attempted function without contracts.
            not_attempted_record("simple_fn", "src/lib.rs", 50),
        ];
        let dash = build_dashboard(records);
        let priorities = dash.prioritize_verification();
        assert_eq!(priorities.len(), 2);
        // complex_fn should rank first (higher priority_score).
        assert_eq!(priorities[0].function_name, "complex_fn");
        assert!(priorities[0].priority_score > priorities[1].priority_score);
    }

    #[test]
    fn test_prioritize_timeout_higher_than_not_attempted() {
        let records = vec![
            timeout_record("slow", "src/lib.rs", 1),
            not_attempted_record("idle", "src/lib.rs", 2),
        ];
        let dash = build_dashboard(records);
        let priorities = dash.prioritize_verification();
        assert_eq!(priorities[0].function_name, "slow");
        assert!(priorities[0].priority_score > priorities[1].priority_score);
    }

    #[test]
    fn test_regression_check_detects_regression() {
        let previous = build_dashboard(vec![
            verified_record("foo", "src/lib.rs", 1),
            verified_record("bar", "src/lib.rs", 10),
        ]);
        let current = build_dashboard(vec![
            verified_record("foo", "src/lib.rs", 1),
            failed_record("bar", "src/lib.rs", 10),
        ]);
        let regressions = current.regression_check(&previous);
        assert_eq!(regressions.len(), 1);
        assert!(regressions[0].contains("bar"));
        assert!(regressions[0].contains("REGRESSION"));
    }

    #[test]
    fn test_regression_check_no_regression() {
        let previous = build_dashboard(vec![verified_record("foo", "src/lib.rs", 1)]);
        let current = build_dashboard(vec![verified_record("foo", "src/lib.rs", 1)]);
        let regressions = current.regression_check(&previous);
        assert!(regressions.is_empty());
    }

    #[test]
    fn test_regression_check_removed_function() {
        let previous = build_dashboard(vec![
            verified_record("foo", "src/lib.rs", 1),
            verified_record("removed", "src/lib.rs", 10),
        ]);
        let current = build_dashboard(vec![verified_record("foo", "src/lib.rs", 1)]);
        let regressions = current.regression_check(&previous);
        assert_eq!(regressions.len(), 1);
        assert!(regressions[0].contains("removed"));
    }

    #[test]
    fn test_render_text_contains_project_name() {
        let dash = build_dashboard(vec![verified_record("a", "src/lib.rs", 1)]);
        let text = dash.render(ReportFormat::Text);
        assert!(text.contains("test-project"));
        assert!(text.contains("1/1 verified"));
        assert!(text.contains("100.0%"));
    }

    #[test]
    fn test_render_text_shows_unverified_section() {
        let dash = build_dashboard(vec![failed_record("broken", "src/lib.rs", 42)]);
        let text = dash.render_text();
        assert!(text.contains("Unverified Functions"));
        assert!(text.contains("broken"));
        assert!(text.contains("FAILED"));
    }

    #[test]
    fn test_render_markdown_contains_tables() {
        let dash = build_dashboard(vec![
            verified_record("a", "src/lib.rs", 1),
            failed_record("b", "src/util.rs", 5),
        ]);
        let md = dash.render(ReportFormat::Markdown);
        assert!(md.contains("# Proof Dashboard: test-project"));
        assert!(md.contains("| Module | Total | Verified | Failed | Coverage |"));
        assert!(md.contains("## Unverified Functions"));
        assert!(md.contains("| b |"));
    }

    #[test]
    fn test_render_json_roundtrip() {
        let records = vec![
            verified_record("a", "src/lib.rs", 1),
            failed_record("b", "src/lib.rs", 10),
        ];
        let dash = build_dashboard(records);
        let json = dash.render(ReportFormat::Json);
        let deserialized: ProofDashboard = serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(deserialized.project_name, "test-project");
        assert_eq!(deserialized.functions.len(), 2);
        assert_eq!(
            deserialized.overall_stats.verified_count,
            dash.overall_stats.verified_count
        );
    }

    #[test]
    fn test_render_csv_header_and_rows() {
        let records = vec![
            verified_record("alpha", "src/lib.rs", 1),
            failed_record("beta", "src/lib.rs", 20),
        ];
        let dash = build_dashboard(records);
        let csv = dash.render(ReportFormat::Csv);
        let lines: Vec<&str> = csv.lines().collect();
        assert!(lines[0].starts_with("name,file,line,status"));
        assert_eq!(lines.len(), 3); // header + 2 rows
        assert!(lines[1].contains("alpha"));
        assert!(lines[1].contains("verified"));
        assert!(lines[2].contains("beta"));
        assert!(lines[2].contains("failed"));
    }

    #[test]
    fn test_complexity_category_boundaries() {
        assert_eq!(DashboardStats::complexity_category(0), "low");
        assert_eq!(DashboardStats::complexity_category(10), "low");
        assert_eq!(DashboardStats::complexity_category(11), "medium");
        assert_eq!(DashboardStats::complexity_category(50), "medium");
        assert_eq!(DashboardStats::complexity_category(51), "high");
        assert_eq!(DashboardStats::complexity_category(100), "high");
        assert_eq!(DashboardStats::complexity_category(101), "critical");
        assert_eq!(DashboardStats::complexity_category(1000), "critical");
    }

    #[test]
    fn test_complexity_histogram_distribution() {
        let records = vec![
            // low: score 5
            not_attempted_record("lo", "src/lib.rs", 1),
            // medium: score 15
            verified_record("med", "src/lib.rs", 10),
            // high: score 60
            failed_record("hi", "src/lib.rs", 20),
            // critical: score 120
            timeout_record("crit", "src/lib.rs", 30),
        ];
        let stats = DashboardStats::compute(&records);
        let hist: HashMap<String, usize> = stats.complexity_histogram.into_iter().collect();
        assert_eq!(hist["low"], 1);
        assert_eq!(hist["medium"], 1);
        assert_eq!(hist["high"], 1);
        assert_eq!(hist["critical"], 1);
    }

    #[test]
    fn test_trend_tracking_via_builder() {
        let mut builder = DashboardBuilder::new("proj");
        builder.add_trend(ProofTrend {
            timestamp: "2026-03-01".to_owned(),
            verified: 10,
            failed: 5,
            total: 15,
            coverage: 66.7,
        });
        builder.add_trend(ProofTrend {
            timestamp: "2026-03-15".to_owned(),
            verified: 13,
            failed: 2,
            total: 15,
            coverage: 86.7,
        });
        // Trends are stored in the builder but currently not serialized into
        // the dashboard (they are an input, not a computed output). Verify the
        // builder accepts them without error and builds successfully.
        let dash = builder.build();
        assert_eq!(dash.project_name, "proj");
    }

    #[test]
    fn test_all_verified_dashboard() {
        let records = vec![
            verified_record("a", "src/lib.rs", 1),
            verified_record("b", "src/lib.rs", 10),
            verified_record("c", "src/util.rs", 1),
        ];
        let dash = build_dashboard(records);
        assert_eq!(dash.overall_stats.coverage_percent, 100.0);
        assert_eq!(dash.overall_stats.failed_count, 0);
        assert_eq!(dash.overall_stats.unknown_count, 0);
        assert!(dash.unverified_functions().is_empty());
        assert!(dash.prioritize_verification().is_empty());
    }

    #[test]
    fn test_all_failed_dashboard() {
        let records = vec![
            failed_record("a", "src/lib.rs", 1),
            failed_record("b", "src/lib.rs", 10),
        ];
        let dash = build_dashboard(records);
        assert_eq!(dash.overall_stats.coverage_percent, 0.0);
        assert_eq!(dash.overall_stats.verified_count, 0);
        assert_eq!(dash.overall_stats.failed_count, 2);
        assert_eq!(dash.unverified_functions().len(), 2);
    }

    #[test]
    fn test_all_unknown_dashboard() {
        let records = vec![
            unknown_record("a", "src/lib.rs", 1),
            unknown_record("b", "src/lib.rs", 10),
            unknown_record("c", "src/lib.rs", 20),
        ];
        let dash = build_dashboard(records);
        assert_eq!(dash.overall_stats.unknown_count, 3);
        assert_eq!(dash.overall_stats.coverage_percent, 0.0);
    }

    #[test]
    fn test_mixed_status_multiple_modules() {
        let records = vec![
            verified_record("v1", "src/alpha.rs", 1),
            verified_record("v2", "src/alpha.rs", 10),
            failed_record("f1", "src/alpha.rs", 20),
            verified_record("v3", "src/beta.rs", 1),
            unknown_record("u1", "src/beta.rs", 10),
            not_attempted_record("n1", "src/gamma.rs", 1),
            skipped_record("s1", "src/gamma.rs", 10),
        ];
        let dash = build_dashboard(records);

        // Overall.
        assert_eq!(dash.overall_stats.total_functions, 7);
        assert_eq!(dash.overall_stats.verified_count, 3);
        assert_eq!(dash.overall_stats.failed_count, 1);
        assert_eq!(dash.overall_stats.unknown_count, 1);
        assert_eq!(dash.overall_stats.not_attempted_count, 1);
        assert_eq!(dash.overall_stats.skipped_count, 1);

        // 3 modules.
        assert_eq!(dash.modules.len(), 3);

        let alpha = dash
            .modules
            .iter()
            .find(|m| m.path == Path::new("src/alpha.rs"))
            .unwrap();
        assert_eq!(alpha.total_functions, 3);
        assert_eq!(alpha.verified, 2);
        assert!((alpha.coverage_percent - 66.666).abs() < 0.01);

        let beta = dash
            .modules
            .iter()
            .find(|m| m.path == Path::new("src/beta.rs"))
            .unwrap();
        assert_eq!(beta.total_functions, 2);
        assert_eq!(beta.verified, 1);
        assert_eq!(beta.coverage_percent, 50.0);

        let gamma = dash
            .modules
            .iter()
            .find(|m| m.path == Path::new("src/gamma.rs"))
            .unwrap();
        assert_eq!(gamma.total_functions, 2);
        assert_eq!(gamma.verified, 0);
        assert_eq!(gamma.coverage_percent, 0.0);
    }

    #[test]
    fn test_stats_timing_calculations() {
        let mut r1 = verified_record("fast", "src/lib.rs", 1);
        r1.status = ProofStatus::Verified {
            elapsed: Duration::from_millis(200),
            solver_mode: "Default".to_owned(),
        };
        let mut r2 = verified_record("slow", "src/lib.rs", 10);
        r2.status = ProofStatus::Verified {
            elapsed: Duration::from_millis(800),
            solver_mode: "BV".to_owned(),
        };
        let dash = build_dashboard(vec![r1, r2]);
        let s = &dash.overall_stats;

        assert_eq!(s.total_elapsed, Duration::from_millis(1000));
        assert_eq!(s.average_verification_time, Duration::from_millis(500));
        assert_eq!(s.max_verification_time, Duration::from_millis(800));
    }

    #[test]
    fn test_stats_total_assertions() {
        let records = vec![
            verified_record("a", "src/lib.rs", 1), // assertion_count: 2
            failed_record("b", "src/lib.rs", 10),  // assertion_count: 3
            unknown_record("c", "src/lib.rs", 20), // assertion_count: 1
        ];
        let stats = DashboardStats::compute(&records);
        assert_eq!(stats.total_assertions, 6);
    }

    #[test]
    fn test_proof_status_elapsed_helper() {
        let verified = ProofStatus::Verified {
            elapsed: Duration::from_secs(1),
            solver_mode: "Default".to_owned(),
        };
        assert_eq!(verified.elapsed(), Some(Duration::from_secs(1)));

        let timeout = ProofStatus::Timeout {
            elapsed: Duration::from_secs(30),
        };
        assert_eq!(timeout.elapsed(), Some(Duration::from_secs(30)));

        let failed = ProofStatus::Failed {
            obligation: "post".to_owned(),
            counterexample: None,
        };
        assert_eq!(failed.elapsed(), None);

        assert_eq!(ProofStatus::NotAttempted.elapsed(), None);
    }

    #[test]
    fn test_proof_status_is_verified() {
        assert!(ProofStatus::Verified {
            elapsed: Duration::ZERO,
            solver_mode: String::new(),
        }
        .is_verified());
        assert!(!ProofStatus::NotAttempted.is_verified());
    }

    #[test]
    fn test_proof_status_is_failed() {
        assert!(ProofStatus::Failed {
            obligation: "x".to_owned(),
            counterexample: None,
        }
        .is_failed());
        assert!(!ProofStatus::NotAttempted.is_failed());
    }

    #[test]
    fn test_csv_escape_commas() {
        assert_eq!(csv_escape("hello,world"), "\"hello,world\"");
        assert_eq!(csv_escape("plain"), "plain");
    }

    #[test]
    fn test_csv_escape_quotes() {
        assert_eq!(csv_escape("say \"hi\""), "\"say \"\"hi\"\"\"");
    }

    #[test]
    fn test_skipped_and_timeout_counts() {
        let records = vec![
            skipped_record("s1", "src/lib.rs", 1),
            skipped_record("s2", "src/lib.rs", 2),
            timeout_record("t1", "src/lib.rs", 3),
        ];
        let stats = DashboardStats::compute(&records);
        assert_eq!(stats.skipped_count, 2);
        assert_eq!(stats.timeout_count, 1);
        assert_eq!(stats.total_functions, 3);
    }

    #[test]
    fn test_module_summary_timeout_counted_as_failed() {
        let records = vec![timeout_record("slow", "src/lib.rs", 1)];
        let summary = ModuleProofSummary::from_records(Path::new("src/lib.rs"), &records);
        assert_eq!(summary.failed, 1);
        assert_eq!(summary.verified, 0);
    }

    #[test]
    fn test_render_text_empty_dashboard_no_unverified_section() {
        let dash = build_dashboard(vec![]);
        let text = dash.render_text();
        assert!(!text.contains("Unverified Functions"));
    }

    #[test]
    fn test_generated_at_propagated() {
        let mut builder = DashboardBuilder::new("proj");
        builder.set_generated_at("2026-01-01T12:00:00Z");
        let dash = builder.build();
        assert_eq!(dash.generated_at, "2026-01-01T12:00:00Z");
    }

    #[test]
    fn test_generated_at_default_unknown() {
        let builder = DashboardBuilder::new("proj");
        let dash = builder.build();
        assert_eq!(dash.generated_at, "unknown");
    }

    #[test]
    fn test_regression_previously_failed_now_verified_not_regression() {
        let previous = build_dashboard(vec![failed_record("foo", "src/lib.rs", 1)]);
        let current = build_dashboard(vec![verified_record("foo", "src/lib.rs", 1)]);
        let regressions = current.regression_check(&previous);
        assert!(regressions.is_empty());
    }

    #[test]
    fn test_prioritize_empty_when_all_verified() {
        let dash = build_dashboard(vec![
            verified_record("a", "src/lib.rs", 1),
            verified_record("b", "src/lib.rs", 10),
        ]);
        assert!(dash.prioritize_verification().is_empty());
    }

    #[test]
    fn test_prioritize_contracts_boost_score() {
        // Two not-attempted functions, same complexity, but one has contracts.
        let mut with_contracts = not_attempted_record("contracted", "src/lib.rs", 1);
        with_contracts.has_requires = true;
        with_contracts.has_ensures = true;

        let without_contracts = not_attempted_record("bare", "src/lib.rs", 10);

        let dash = build_dashboard(vec![with_contracts, without_contracts]);
        let priorities = dash.prioritize_verification();
        assert_eq!(priorities[0].function_name, "contracted");
        assert!(priorities[0].priority_score > priorities[1].priority_score);
    }
}
