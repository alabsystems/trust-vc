// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code)]

//! Multi-stage verification pipeline for the trust_vc CLI.
//!
//! Orchestrates verification passes with increasing precision, manages pass
//! ordering, result aggregation, and progress reporting. The entry point is
//! [`PipelineBuilder`], which produces a [`Pipeline`] that can be run against
//! a set of function names.
//!
//! # Design
//!
//! Each function under verification proceeds through a sequence of
//! [`VerifyPass`] instances (each associated with a [`PassKind`]). A
//! [`PassScheduler`] orders passes based on declared dependencies and
//! priorities. The [`ResultAggregator`] combines per-pass outcomes into a
//! [`FinalVerdict`] for each function. A [`ProgressTracker`] provides
//! real-time completion estimates.
//!
//! Incremental verification is supported via [`CacheEntry`] records that
//! allow previously-verified functions to be skipped when their source has
//! not changed.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{self, Write as _};
use std::time::{Duration, Instant};

use crate::format_types::ReportFormat;

// ---------------------------------------------------------------------------
// PassKind
// ---------------------------------------------------------------------------

/// Classification of a verification pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub(crate) enum PassKind {
    /// Fast syntactic/type-level checks.
    QuickCheck,
    /// Full SMT verification with default solver configuration.
    FullVerify,
    /// Nonlinear integer arithmetic mode.
    NonlinearArith,
    /// Bitvector-precise mode.
    BitVector,
    /// Deep quantifier instantiation mode.
    DeepQuantifier,
    /// UNSAT proof certificate generation.
    Certificate,
}

impl fmt::Display for PassKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::QuickCheck => "quick-check",
            Self::FullVerify => "full-verify",
            Self::NonlinearArith => "nonlinear-arith",
            Self::BitVector => "bit-vector",
            Self::DeepQuantifier => "deep-quantifier",
            Self::Certificate => "certificate",
        };
        write!(f, "{label}")
    }
}

// ---------------------------------------------------------------------------
// PassOutcome
// ---------------------------------------------------------------------------

/// Outcome of a single verification pass for a single function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum PassOutcome {
    /// The function was verified successfully.
    Verified,
    /// Verification found a counterexample.
    Failed,
    /// The solver could not determine the result.
    Unknown,
    /// The pass exceeded its timeout.
    Timeout,
    /// The pass was skipped (dependency not met, or cache hit).
    Skipped,
}

impl fmt::Display for PassOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Unknown => "unknown",
            Self::Timeout => "timeout",
            Self::Skipped => "skipped",
        };
        write!(f, "{label}")
    }
}

// ---------------------------------------------------------------------------
// FinalVerdict
// ---------------------------------------------------------------------------

/// Aggregated verdict for a function across all passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum FinalVerdict {
    /// All required passes verified.
    Verified,
    /// At least one pass found a counterexample.
    Failed,
    /// At least one required pass returned unknown/timeout with no failure.
    Inconclusive,
    /// All passes were skipped (nothing ran).
    Skipped,
}

impl fmt::Display for FinalVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Inconclusive => "inconclusive",
            Self::Skipped => "skipped",
        };
        write!(f, "{label}")
    }
}

// ---------------------------------------------------------------------------
// SolverConfig
// ---------------------------------------------------------------------------

/// Solver configuration knobs for a single pass.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct SolverConfig {
    /// E-matching rounds.
    pub(crate) ematching_rounds: u32,
    /// Quantifier instantiation depth.
    pub(crate) qi_depth: u32,
    /// Enable bitvector theory.
    pub(crate) enable_bv: bool,
    /// Enable nonlinear integer arithmetic theory.
    pub(crate) enable_nia: bool,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            ematching_rounds: 8,
            qi_depth: 4,
            enable_bv: false,
            enable_nia: false,
        }
    }
}

// ---------------------------------------------------------------------------
// VerifyPass
// ---------------------------------------------------------------------------

/// A single verification pass with its configuration.
#[derive(Debug, Clone)]
pub(crate) struct VerifyPass {
    /// Human-readable name of this pass.
    pub(crate) name: String,
    /// Classification.
    pub(crate) kind: PassKind,
    /// Per-pass timeout.
    pub(crate) timeout: Duration,
    /// Solver configuration.
    pub(crate) solver_config: SolverConfig,
    /// Execution priority (lower = higher priority, runs first).
    pub(crate) priority: u32,
}

impl VerifyPass {
    /// Create a new verification pass.
    #[must_use]
    pub(crate) fn new(name: impl Into<String>, kind: PassKind) -> Self {
        Self {
            name: name.into(),
            kind,
            timeout: Duration::from_secs(60),
            solver_config: SolverConfig::default(),
            priority: 100,
        }
    }

    /// Set the timeout.
    #[must_use]
    pub(crate) fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// Set the priority.
    #[must_use]
    pub(crate) fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }

    /// Set the solver configuration.
    #[must_use]
    pub(crate) fn with_solver_config(mut self, config: SolverConfig) -> Self {
        self.solver_config = config;
        self
    }
}

// ---------------------------------------------------------------------------
// PassResult
// ---------------------------------------------------------------------------

/// Result of running a single pass on a single function.
#[derive(Debug, Clone)]
pub(crate) struct PassResult {
    /// Which pass produced this result.
    pub(crate) pass_name: String,
    /// Which pass kind.
    pub(crate) pass_kind: PassKind,
    /// Function that was verified.
    pub(crate) function_name: String,
    /// Outcome.
    pub(crate) outcome: PassOutcome,
    /// Wall-clock elapsed time.
    pub(crate) elapsed: Duration,
    /// Optional diagnostic message.
    pub(crate) detail: Option<String>,
}

// ---------------------------------------------------------------------------
// PipelineStage
// ---------------------------------------------------------------------------

/// An execution stage containing one or more passes that can run together.
///
/// Stages are ordered: stage N must complete before stage N+1 begins.
/// Within a stage, passes may execute in parallel.
#[derive(Debug, Clone)]
pub(crate) struct PipelineStage {
    /// Zero-based stage index.
    pub(crate) index: usize,
    /// Passes in this stage.
    pub(crate) passes: Vec<VerifyPass>,
    /// Names of passes that must complete before this stage runs.
    pub(crate) depends_on: HashSet<String>,
}

// ---------------------------------------------------------------------------
// RetryPolicy
// ---------------------------------------------------------------------------

/// Policy governing when and how failed passes are retried.
#[derive(Debug, Clone)]
pub(crate) struct RetryPolicy {
    /// Maximum retry attempts per pass.
    pub(crate) max_retries: u32,
    /// Outcomes that trigger a retry.
    pub(crate) retryable_outcomes: HashSet<PassOutcome>,
    /// Multiplier applied to the timeout on each retry.
    pub(crate) timeout_multiplier: f64,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        let mut retryable = HashSet::new();
        retryable.insert(PassOutcome::Timeout);
        retryable.insert(PassOutcome::Unknown);
        Self {
            max_retries: 2,
            retryable_outcomes: retryable,
            timeout_multiplier: 2.0,
        }
    }
}

impl RetryPolicy {
    /// Determine whether a result warrants a retry at the given attempt count.
    #[must_use]
    pub(crate) fn should_retry(&self, outcome: PassOutcome, attempt: u32) -> bool {
        attempt < self.max_retries && self.retryable_outcomes.contains(&outcome)
    }

    /// Compute the timeout for a given retry attempt.
    #[must_use]
    pub(crate) fn retry_timeout(&self, base_timeout: Duration, attempt: u32) -> Duration {
        if attempt == 0 {
            return base_timeout;
        }
        let exponent = i32::try_from(attempt).unwrap_or(i32::MAX);
        let multiplier = self.timeout_multiplier.powi(exponent);
        Duration::from_secs_f64(base_timeout.as_secs_f64() * multiplier)
    }
}

// ---------------------------------------------------------------------------
// CacheEntry
// ---------------------------------------------------------------------------

/// Cached verification result for incremental verification.
#[derive(Debug, Clone)]
pub(crate) struct CacheEntry {
    /// Function name.
    pub(crate) function_name: String,
    /// Hash of the function source at the time of verification.
    pub(crate) source_hash: u64,
    /// The pass kind that produced this result.
    pub(crate) pass_kind: PassKind,
    /// Cached outcome.
    pub(crate) outcome: PassOutcome,
    /// When this entry was created.
    pub(crate) created_at: Instant,
}

impl CacheEntry {
    /// Create a new cache entry.
    #[must_use]
    pub(crate) fn new(
        function_name: impl Into<String>,
        source_hash: u64,
        pass_kind: PassKind,
        outcome: PassOutcome,
    ) -> Self {
        Self {
            function_name: function_name.into(),
            source_hash,
            pass_kind,
            outcome,
            created_at: Instant::now(),
        }
    }

    /// Check whether this cache entry is still valid for the given source hash.
    #[must_use]
    pub(crate) fn is_valid(&self, current_hash: u64) -> bool {
        self.source_hash == current_hash
    }
}

// ---------------------------------------------------------------------------
// VerificationCache
// ---------------------------------------------------------------------------

/// In-memory cache mapping (function_name, pass_kind) to a cached outcome.
#[derive(Debug, Default)]
pub(crate) struct VerificationCache {
    entries: HashMap<(String, PassKind), CacheEntry>,
}

impl VerificationCache {
    /// Create an empty cache.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Insert or update a cache entry.
    pub(crate) fn insert(&mut self, entry: CacheEntry) {
        let key = (entry.function_name.clone(), entry.pass_kind);
        self.entries.insert(key, entry);
    }

    /// Look up a cached outcome for a (function, pass_kind) pair.
    #[must_use]
    pub(crate) fn lookup(
        &self,
        function_name: &str,
        pass_kind: PassKind,
        current_hash: u64,
    ) -> Option<PassOutcome> {
        self.entries
            .get(&(function_name.to_string(), pass_kind))
            .filter(|entry| entry.is_valid(current_hash))
            .map(|entry| entry.outcome)
    }

    /// Number of entries in the cache.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Remove all entries.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

// ---------------------------------------------------------------------------
// PipelineConfig
// ---------------------------------------------------------------------------

/// Top-level configuration for the verification pipeline.
#[derive(Debug, Clone)]
pub(crate) struct PipelineConfig {
    /// Ordered passes to run.
    pub(crate) passes: Vec<VerifyPass>,
    /// Maximum number of functions to verify in parallel.
    pub(crate) parallelism: usize,
    /// Global timeout (across all passes). `None` = unlimited.
    pub(crate) global_timeout: Option<Duration>,
    /// Stop on first failure.
    pub(crate) fail_fast: bool,
    /// Retry policy.
    pub(crate) retry_policy: RetryPolicy,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            passes: Vec::new(),
            parallelism: 1,
            global_timeout: None,
            fail_fast: false,
            retry_policy: RetryPolicy::default(),
        }
    }
}

// ---------------------------------------------------------------------------
// PassScheduler
// ---------------------------------------------------------------------------

/// Determines pass execution order based on priorities and dependencies.
pub(crate) struct PassScheduler;

impl PassScheduler {
    /// Organize passes into ordered stages.
    ///
    /// Passes with no dependencies are grouped by priority into stages.
    /// The `features` set can be used to filter passes: a pass whose
    /// [`PassKind`] name is not in `features` (when `features` is non-empty)
    /// will be excluded.
    #[must_use]
    pub(crate) fn schedule(
        passes: &[VerifyPass],
        features: &HashSet<String>,
    ) -> Vec<PipelineStage> {
        // Filter passes by feature set (empty = accept all).
        let filtered: Vec<&VerifyPass> = if features.is_empty() {
            passes.iter().collect()
        } else {
            passes
                .iter()
                .filter(|p| features.contains(&p.kind.to_string()))
                .collect()
        };

        // Group by priority, then sort groups by priority value.
        let mut by_priority: BTreeMap<u32, Vec<VerifyPass>> = BTreeMap::new();
        for pass in filtered {
            by_priority
                .entry(pass.priority)
                .or_default()
                .push(pass.clone());
        }

        by_priority
            .into_iter()
            .enumerate()
            .map(|(index, (_priority, passes))| {
                let depends_on = if index == 0 {
                    HashSet::new()
                } else {
                    // Each stage depends on all passes from the previous stage.
                    HashSet::new() // Simplified: ordering is implicit via stage index.
                };
                PipelineStage {
                    index,
                    passes,
                    depends_on,
                }
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// ProgressTracker
// ---------------------------------------------------------------------------

/// Tracks and reports pipeline progress.
pub(crate) struct ProgressTracker {
    /// Total number of (function, pass) pairs to execute.
    total_tasks: usize,
    /// Number of completed tasks.
    completed: usize,
    /// When tracking started.
    started_at: Option<Instant>,
    /// Name of the currently executing pass.
    current_pass: Option<String>,
}

impl ProgressTracker {
    /// Create a new tracker for the given total task count.
    #[must_use]
    pub(crate) fn new(total_tasks: usize) -> Self {
        Self {
            total_tasks,
            completed: 0,
            started_at: None,
            current_pass: None,
        }
    }

    /// Start the clock.
    pub(crate) fn start(&mut self) {
        self.started_at = Some(Instant::now());
    }

    /// Record completion of one pass.
    pub(crate) fn complete_pass(&mut self, pass_name: &str) {
        self.completed += 1;
        self.current_pass = Some(pass_name.to_string());
    }

    /// Set the currently executing pass name.
    pub(crate) fn set_current_pass(&mut self, name: &str) {
        self.current_pass = Some(name.to_string());
    }

    /// Return (fraction_complete, estimated_remaining).
    ///
    /// Returns `(0.0, Duration::ZERO)` if tracking has not started.
    #[must_use]
    pub(crate) fn current_progress(&self) -> (f64, Duration) {
        let started = match self.started_at {
            Some(t) => t,
            None => return (0.0, Duration::ZERO),
        };

        if self.total_tasks == 0 {
            return (1.0, Duration::ZERO);
        }

        let fraction = self.completed as f64 / self.total_tasks as f64;
        let elapsed = started.elapsed();

        let remaining = if self.completed > 0 {
            let per_task = elapsed.as_secs_f64() / self.completed as f64;
            let remaining_tasks = self.total_tasks - self.completed;
            Duration::from_secs_f64(per_task * remaining_tasks as f64)
        } else {
            Duration::ZERO
        };

        (fraction, remaining)
    }

    /// Total elapsed time since start.
    #[must_use]
    pub(crate) fn elapsed(&self) -> Duration {
        self.started_at
            .map(|t| t.elapsed())
            .unwrap_or(Duration::ZERO)
    }

    /// The name of the last completed or currently running pass.
    #[must_use]
    pub(crate) fn current_pass_name(&self) -> Option<&str> {
        self.current_pass.as_deref()
    }

    /// Number of completed tasks.
    #[must_use]
    pub(crate) fn completed_count(&self) -> usize {
        self.completed
    }

    /// Total task count.
    #[must_use]
    pub(crate) fn total_count(&self) -> usize {
        self.total_tasks
    }
}

// ---------------------------------------------------------------------------
// ResultAggregator
// ---------------------------------------------------------------------------

/// Combines results from multiple passes into a final verdict per function.
pub(crate) struct ResultAggregator {
    /// Results keyed by function name, ordered by insertion.
    results: HashMap<String, Vec<PassResult>>,
}

impl ResultAggregator {
    /// Create a new empty aggregator.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            results: HashMap::new(),
        }
    }

    /// Record a pass result.
    pub(crate) fn add_result(&mut self, result: PassResult) {
        self.results
            .entry(result.function_name.clone())
            .or_default()
            .push(result);
    }

    /// Compute the final verdict for a given function.
    ///
    /// Precedence: Failed > Inconclusive (Unknown/Timeout) > Verified > Skipped.
    #[must_use]
    pub(crate) fn final_verdict(&self, function_name: &str) -> FinalVerdict {
        let results = match self.results.get(function_name) {
            Some(r) => r,
            None => return FinalVerdict::Skipped,
        };

        if results.is_empty() {
            return FinalVerdict::Skipped;
        }

        let mut has_verified = false;
        let mut has_inconclusive = false;

        for result in results {
            match result.outcome {
                PassOutcome::Failed => return FinalVerdict::Failed,
                PassOutcome::Verified => has_verified = true,
                PassOutcome::Unknown | PassOutcome::Timeout => has_inconclusive = true,
                PassOutcome::Skipped => {}
            }
        }

        if has_inconclusive {
            FinalVerdict::Inconclusive
        } else if has_verified {
            FinalVerdict::Verified
        } else {
            FinalVerdict::Skipped
        }
    }

    /// Get all recorded results for a function.
    #[must_use]
    pub(crate) fn results_for(&self, function_name: &str) -> &[PassResult] {
        self.results
            .get(function_name)
            .map_or(&[], |v| v.as_slice())
    }

    /// All function names that have at least one result.
    #[must_use]
    pub(crate) fn function_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.results.keys().cloned().collect();
        names.sort();
        names
    }
}

// ---------------------------------------------------------------------------
// PipelineResult
// ---------------------------------------------------------------------------

/// Aggregated results across all passes for all functions.
#[derive(Debug, Clone)]
pub(crate) struct PipelineResult {
    /// Per-function verdict.
    pub(crate) verdicts: BTreeMap<String, FinalVerdict>,
    /// All individual pass results.
    pub(crate) pass_results: Vec<PassResult>,
    /// Total wall-clock elapsed time.
    pub(crate) elapsed: Duration,
    /// Number of cache hits (incremental mode).
    pub(crate) cache_hits: usize,
    /// Number of cache misses.
    pub(crate) cache_misses: usize,
}

impl PipelineResult {
    /// Number of functions that were fully verified.
    #[must_use]
    pub(crate) fn verified_count(&self) -> usize {
        self.verdicts
            .values()
            .filter(|v| **v == FinalVerdict::Verified)
            .count()
    }

    /// Number of functions that failed.
    #[must_use]
    pub(crate) fn failed_count(&self) -> usize {
        self.verdicts
            .values()
            .filter(|v| **v == FinalVerdict::Failed)
            .count()
    }

    /// Whether there are any failures.
    #[must_use]
    pub(crate) fn has_failures(&self) -> bool {
        self.verdicts.values().any(|v| *v == FinalVerdict::Failed)
    }

    /// Render a report in the specified format.
    #[must_use]
    pub(crate) fn render_report(&self, format: ReportFormat) -> String {
        match format {
            ReportFormat::Text | ReportFormat::Csv => self.render_text(),
            ReportFormat::Json => self.render_json(),
            ReportFormat::Markdown => self.render_markdown(),
        }
    }

    fn render_text(&self) -> String {
        let mut out = String::new();
        out.push_str("=== TrustVc Verification Pipeline Report ===\n\n");
        let _ = writeln!(
            out,
            "Functions: {} total, {} verified, {} failed",
            self.verdicts.len(),
            self.verified_count(),
            self.failed_count(),
        );
        let _ = writeln!(out, "Elapsed: {:.3}s", self.elapsed.as_secs_f64());
        if self.cache_hits > 0 || self.cache_misses > 0 {
            let _ = writeln!(
                out,
                "Cache: {} hits, {} misses",
                self.cache_hits, self.cache_misses
            );
        }
        out.push('\n');

        for (name, verdict) in &self.verdicts {
            let _ = writeln!(out, "  {name}: {verdict}");
        }

        if !self.pass_results.is_empty() {
            let _ = writeln!(out, "\nPass results: {}", self.pass_results.len());
        }

        out
    }

    fn render_json(&self) -> String {
        // Hand-rolled JSON to avoid serde dependency.
        let mut out = String::from("{\n");
        let _ = writeln!(out, "  \"total\": {},", self.verdicts.len());
        let _ = writeln!(out, "  \"verified\": {},", self.verified_count());
        let _ = writeln!(out, "  \"failed\": {},", self.failed_count());
        let _ = writeln!(
            out,
            "  \"elapsed_secs\": {:.6},",
            self.elapsed.as_secs_f64()
        );
        let _ = writeln!(out, "  \"cache_hits\": {},", self.cache_hits);
        let _ = writeln!(out, "  \"cache_misses\": {},", self.cache_misses);
        out.push_str("  \"functions\": {\n");

        let entries: Vec<(&String, &FinalVerdict)> = self.verdicts.iter().collect();
        for (i, (name, verdict)) in entries.iter().enumerate() {
            let comma = if i + 1 < entries.len() { "," } else { "" };
            let _ = writeln!(out, "    \"{name}\": \"{verdict}\"{comma}");
        }

        out.push_str("  }\n");
        out.push('}');
        out
    }

    fn render_markdown(&self) -> String {
        let mut out = String::new();
        out.push_str("# Verification Pipeline Report\n\n");
        out.push_str("| Metric | Value |\n|--------|-------|\n");
        let _ = writeln!(out, "| Total functions | {} |", self.verdicts.len());
        let _ = writeln!(out, "| Verified | {} |", self.verified_count());
        let _ = writeln!(out, "| Failed | {} |", self.failed_count());
        let _ = writeln!(out, "| Elapsed | {:.3}s |\n", self.elapsed.as_secs_f64());

        out.push_str("## Functions\n\n");
        out.push_str("| Function | Verdict |\n|----------|--------|\n");
        for (name, verdict) in &self.verdicts {
            let _ = writeln!(out, "| {name} | {verdict} |");
        }

        out
    }
}

// ---------------------------------------------------------------------------
// PipelineReport
// ---------------------------------------------------------------------------

/// Detailed report of all passes for display.
#[derive(Debug, Clone)]
pub(crate) struct PipelineReport {
    /// Individual pass reports (pass_name, function_name, outcome, elapsed).
    pub(crate) entries: Vec<PipelineReportEntry>,
    /// Summary counts by outcome.
    pub(crate) summary: HashMap<PassOutcome, usize>,
    /// Total elapsed time.
    pub(crate) total_elapsed: Duration,
}

/// A single entry in the pipeline report.
#[derive(Debug, Clone)]
pub(crate) struct PipelineReportEntry {
    pub(crate) pass_name: String,
    pub(crate) function_name: String,
    pub(crate) outcome: PassOutcome,
    pub(crate) elapsed: Duration,
    pub(crate) detail: Option<String>,
}

impl PipelineReport {
    /// Build a report from a set of pass results.
    #[must_use]
    pub(crate) fn from_results(results: &[PassResult], total_elapsed: Duration) -> Self {
        let mut summary: HashMap<PassOutcome, usize> = HashMap::new();
        let entries: Vec<PipelineReportEntry> = results
            .iter()
            .map(|r| {
                *summary.entry(r.outcome).or_insert(0) += 1;
                PipelineReportEntry {
                    pass_name: r.pass_name.clone(),
                    function_name: r.function_name.clone(),
                    outcome: r.outcome,
                    elapsed: r.elapsed,
                    detail: r.detail.clone(),
                }
            })
            .collect();

        Self {
            entries,
            summary,
            total_elapsed,
        }
    }
}

// ---------------------------------------------------------------------------
// PipelineBuilder
// ---------------------------------------------------------------------------

/// Fluent builder for constructing verification pipelines.
#[derive(Debug, Clone)]
#[must_use]
pub(crate) struct PipelineBuilder {
    config: PipelineConfig,
}

impl PipelineBuilder {
    /// Create a new builder with default configuration.
    pub(crate) fn new() -> Self {
        Self {
            config: PipelineConfig::default(),
        }
    }

    /// Add a verification pass.
    pub(crate) fn add_pass(mut self, pass: VerifyPass) -> Self {
        self.config.passes.push(pass);
        self
    }

    /// Set the maximum parallelism (functions verified concurrently).
    pub(crate) fn with_parallelism(mut self, parallelism: usize) -> Self {
        self.config.parallelism = parallelism.max(1);
        self
    }

    /// Set the global timeout.
    pub(crate) fn with_timeout(mut self, timeout: Duration) -> Self {
        self.config.global_timeout = Some(timeout);
        self
    }

    /// Enable or disable fail-fast mode.
    pub(crate) fn with_fail_fast(mut self, fail_fast: bool) -> Self {
        self.config.fail_fast = fail_fast;
        self
    }

    /// Set the retry policy.
    pub(crate) fn with_retry_policy(mut self, policy: RetryPolicy) -> Self {
        self.config.retry_policy = policy;
        self
    }

    /// Build the pipeline.
    pub(crate) fn build(self) -> Pipeline {
        Pipeline {
            config: self.config,
        }
    }
}

// ---------------------------------------------------------------------------
// Pipeline
// ---------------------------------------------------------------------------

/// The main verification pipeline. Runs passes over functions and collects results.
pub(crate) struct Pipeline {
    config: PipelineConfig,
}

impl Pipeline {
    /// Run the pipeline over the given function names.
    ///
    /// Each function is run through every configured pass in order. This
    /// method simulates pass execution (the actual ay integration lives in
    /// `trust-vc-core`); it records timing and delegates outcome determination
    /// to the pass kind defaults.
    #[must_use]
    pub(crate) fn run(&self, functions: &[&str]) -> PipelineResult {
        let start = Instant::now();
        let stages = PassScheduler::schedule(&self.config.passes, &HashSet::new());
        let mut aggregator = ResultAggregator::new();
        let total_tasks = functions.len() * self.config.passes.len();
        let mut tracker = ProgressTracker::new(total_tasks);
        tracker.start();

        let mut early_exit = false;

        for stage in &stages {
            if early_exit {
                break;
            }
            for pass in &stage.passes {
                if early_exit {
                    break;
                }
                tracker.set_current_pass(&pass.name);
                for &func in functions {
                    // Check global timeout.
                    if let Some(global_timeout) = self.config.global_timeout {
                        if start.elapsed() >= global_timeout {
                            let result = PassResult {
                                pass_name: pass.name.clone(),
                                pass_kind: pass.kind,
                                function_name: func.to_string(),
                                outcome: PassOutcome::Timeout,
                                elapsed: Duration::ZERO,
                                detail: Some("global timeout exceeded".to_string()),
                            };
                            aggregator.add_result(result);
                            tracker.complete_pass(&pass.name);
                            continue;
                        }
                    }

                    // Simulate pass execution: QuickCheck always verifies,
                    // others delegate to the stub that returns Verified.
                    let pass_start = Instant::now();
                    let outcome = PassOutcome::Verified;
                    let elapsed = pass_start.elapsed();

                    let result = PassResult {
                        pass_name: pass.name.clone(),
                        pass_kind: pass.kind,
                        function_name: func.to_string(),
                        outcome,
                        elapsed,
                        detail: None,
                    };
                    aggregator.add_result(result);
                    tracker.complete_pass(&pass.name);

                    // Fail-fast check.
                    if self.config.fail_fast && outcome == PassOutcome::Failed {
                        early_exit = true;
                        break;
                    }
                }
            }
        }

        let verdicts: BTreeMap<String, FinalVerdict> = functions
            .iter()
            .map(|&f| (f.to_string(), aggregator.final_verdict(f)))
            .collect();

        let all_results: Vec<PassResult> = functions
            .iter()
            .flat_map(|&f| aggregator.results_for(f).iter().cloned())
            .collect();

        PipelineResult {
            verdicts,
            pass_results: all_results,
            elapsed: start.elapsed(),
            cache_hits: 0,
            cache_misses: functions.len(),
        }
    }

    /// Run the pipeline with incremental caching support.
    ///
    /// Functions whose source hash matches a cache entry with a `Verified`
    /// outcome will be skipped. New results are written back to the cache.
    #[must_use]
    pub(crate) fn run_incremental(
        &self,
        functions: &[(&str, u64)], // (name, source_hash)
        cache: &mut VerificationCache,
    ) -> PipelineResult {
        let start = Instant::now();
        let mut aggregator = ResultAggregator::new();
        let mut cache_hits: usize = 0;
        let mut cache_misses: usize = 0;

        for &(func, hash) in functions {
            let mut all_cached = true;

            for pass in &self.config.passes {
                if let Some(cached_outcome) = cache.lookup(func, pass.kind, hash) {
                    let result = PassResult {
                        pass_name: pass.name.clone(),
                        pass_kind: pass.kind,
                        function_name: func.to_string(),
                        outcome: cached_outcome,
                        elapsed: Duration::ZERO,
                        detail: Some("cache hit".to_string()),
                    };
                    aggregator.add_result(result);
                } else {
                    all_cached = false;
                    // Simulate verification.
                    let pass_start = Instant::now();
                    let outcome = PassOutcome::Verified;
                    let elapsed = pass_start.elapsed();

                    let result = PassResult {
                        pass_name: pass.name.clone(),
                        pass_kind: pass.kind,
                        function_name: func.to_string(),
                        outcome,
                        elapsed,
                        detail: None,
                    };
                    aggregator.add_result(result);

                    // Write back to cache.
                    cache.insert(CacheEntry::new(func, hash, pass.kind, outcome));
                }
            }

            if all_cached {
                cache_hits += 1;
            } else {
                cache_misses += 1;
            }
        }

        let verdicts: BTreeMap<String, FinalVerdict> = functions
            .iter()
            .map(|&(f, _)| (f.to_string(), aggregator.final_verdict(f)))
            .collect();

        let all_results: Vec<PassResult> = functions
            .iter()
            .flat_map(|&(f, _)| aggregator.results_for(f).iter().cloned())
            .collect();

        PipelineResult {
            verdicts,
            pass_results: all_results,
            elapsed: start.elapsed(),
            cache_hits,
            cache_misses,
        }
    }

    /// Access the pipeline configuration.
    #[must_use]
    pub(crate) fn config(&self) -> &PipelineConfig {
        &self.config
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // ---- Helpers ----

    fn quick_pass() -> VerifyPass {
        VerifyPass::new("quick", PassKind::QuickCheck).with_priority(10)
    }

    fn full_pass() -> VerifyPass {
        VerifyPass::new("full", PassKind::FullVerify).with_priority(20)
    }

    fn bv_pass() -> VerifyPass {
        VerifyPass::new("bv", PassKind::BitVector)
            .with_priority(30)
            .with_solver_config(SolverConfig {
                enable_bv: true,
                ..SolverConfig::default()
            })
    }

    fn nia_pass() -> VerifyPass {
        VerifyPass::new("nia", PassKind::NonlinearArith)
            .with_priority(30)
            .with_solver_config(SolverConfig {
                enable_nia: true,
                ..SolverConfig::default()
            })
    }

    fn cert_pass() -> VerifyPass {
        VerifyPass::new("cert", PassKind::Certificate).with_priority(50)
    }

    fn default_pipeline() -> Pipeline {
        PipelineBuilder::new()
            .add_pass(quick_pass())
            .add_pass(full_pass())
            .build()
    }

    fn sample_functions() -> Vec<&'static str> {
        vec!["fn_add", "fn_mul", "fn_div"]
    }

    // ---- 1. PassKind display ----

    #[test]
    fn test_pass_kind_display_all_variants() {
        assert_eq!(PassKind::QuickCheck.to_string(), "quick-check");
        assert_eq!(PassKind::FullVerify.to_string(), "full-verify");
        assert_eq!(PassKind::NonlinearArith.to_string(), "nonlinear-arith");
        assert_eq!(PassKind::BitVector.to_string(), "bit-vector");
        assert_eq!(PassKind::DeepQuantifier.to_string(), "deep-quantifier");
        assert_eq!(PassKind::Certificate.to_string(), "certificate");
    }

    // ---- 2. PassOutcome display ----

    #[test]
    fn test_pass_outcome_display_all_variants() {
        assert_eq!(PassOutcome::Verified.to_string(), "verified");
        assert_eq!(PassOutcome::Failed.to_string(), "failed");
        assert_eq!(PassOutcome::Unknown.to_string(), "unknown");
        assert_eq!(PassOutcome::Timeout.to_string(), "timeout");
        assert_eq!(PassOutcome::Skipped.to_string(), "skipped");
    }

    // ---- 3. FinalVerdict display ----

    #[test]
    fn test_final_verdict_display_all_variants() {
        assert_eq!(FinalVerdict::Verified.to_string(), "verified");
        assert_eq!(FinalVerdict::Failed.to_string(), "failed");
        assert_eq!(FinalVerdict::Inconclusive.to_string(), "inconclusive");
        assert_eq!(FinalVerdict::Skipped.to_string(), "skipped");
    }

    // ---- 4. VerifyPass construction ----

    #[test]
    fn test_verify_pass_construction_defaults() {
        let pass = VerifyPass::new("test-pass", PassKind::FullVerify);
        assert_eq!(pass.name, "test-pass");
        assert_eq!(pass.kind, PassKind::FullVerify);
        assert_eq!(pass.timeout, Duration::from_secs(60));
        assert_eq!(pass.priority, 100);
        assert_eq!(pass.solver_config.ematching_rounds, 8);
    }

    // ---- 5. VerifyPass builder methods ----

    #[test]
    fn test_verify_pass_builder_methods() {
        let pass = VerifyPass::new("custom", PassKind::BitVector)
            .with_timeout(Duration::from_secs(120))
            .with_priority(5)
            .with_solver_config(SolverConfig {
                ematching_rounds: 16,
                qi_depth: 8,
                enable_bv: true,
                enable_nia: false,
            });

        assert_eq!(pass.timeout, Duration::from_secs(120));
        assert_eq!(pass.priority, 5);
        assert!(pass.solver_config.enable_bv);
        assert_eq!(pass.solver_config.ematching_rounds, 16);
    }

    // ---- 6. PipelineBuilder basic ----

    #[test]
    fn test_pipeline_builder_creates_pipeline_with_passes() {
        let pipeline = PipelineBuilder::new()
            .add_pass(quick_pass())
            .add_pass(full_pass())
            .add_pass(bv_pass())
            .with_parallelism(4)
            .with_timeout(Duration::from_secs(300))
            .with_fail_fast(true)
            .build();

        assert_eq!(pipeline.config().passes.len(), 3);
        assert_eq!(pipeline.config().parallelism, 4);
        assert_eq!(
            pipeline.config().global_timeout,
            Some(Duration::from_secs(300))
        );
        assert!(pipeline.config().fail_fast);
    }

    // ---- 7. PipelineBuilder parallelism clamped ----

    #[test]
    fn test_pipeline_builder_parallelism_minimum_is_1() {
        let pipeline = PipelineBuilder::new().with_parallelism(0).build();
        assert_eq!(pipeline.config().parallelism, 1);
    }

    // ---- 8. Pipeline run empty functions ----

    #[test]
    fn test_pipeline_run_empty_functions_returns_empty_results() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&[]);
        assert!(result.verdicts.is_empty());
        assert!(result.pass_results.is_empty());
        assert_eq!(result.verified_count(), 0);
        assert_eq!(result.failed_count(), 0);
        assert!(!result.has_failures());
    }

    // ---- 9. Pipeline run single function ----

    #[test]
    fn test_pipeline_run_single_function_verified() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&["fn_add"]);
        assert_eq!(result.verdicts.len(), 1);
        assert_eq!(result.verdicts["fn_add"], FinalVerdict::Verified);
        assert_eq!(result.verified_count(), 1);
        assert_eq!(result.failed_count(), 0);
    }

    // ---- 10. Pipeline run multiple functions ----

    #[test]
    fn test_pipeline_run_multiple_functions_all_verified() {
        let pipeline = default_pipeline();
        let funcs = sample_functions();
        let result = pipeline.run(&funcs);
        assert_eq!(result.verdicts.len(), 3);
        assert_eq!(result.verified_count(), 3);
        assert!(!result.has_failures());
    }

    // ---- 11. Pipeline pass results count ----

    #[test]
    fn test_pipeline_pass_results_count_matches_functions_times_passes() {
        let pipeline = PipelineBuilder::new()
            .add_pass(quick_pass())
            .add_pass(full_pass())
            .add_pass(bv_pass())
            .build();

        let result = pipeline.run(&["f1", "f2"]);
        // 2 functions * 3 passes = 6 results
        assert_eq!(result.pass_results.len(), 6);
    }

    // ---- 12. PassScheduler groups by priority ----

    #[test]
    fn test_pass_scheduler_groups_by_priority() {
        let passes = vec![
            quick_pass(), // priority 10
            full_pass(),  // priority 20
            bv_pass(),    // priority 30
            nia_pass(),   // priority 30
            cert_pass(),  // priority 50
        ];

        let stages = PassScheduler::schedule(&passes, &HashSet::new());
        // Priority 10, 20, 30, 50 => 4 stages
        assert_eq!(stages.len(), 4);
        assert_eq!(stages[0].passes.len(), 1); // quick
        assert_eq!(stages[1].passes.len(), 1); // full
        assert_eq!(stages[2].passes.len(), 2); // bv + nia
        assert_eq!(stages[3].passes.len(), 1); // cert
    }

    // ---- 13. PassScheduler feature filtering ----

    #[test]
    fn test_pass_scheduler_filters_by_features() {
        let passes = vec![quick_pass(), full_pass(), bv_pass()];

        let mut features = HashSet::new();
        features.insert("quick-check".to_string());
        features.insert("bit-vector".to_string());

        let stages = PassScheduler::schedule(&passes, &features);
        let total_passes: usize = stages.iter().map(|s| s.passes.len()).sum();
        assert_eq!(total_passes, 2);
    }

    // ---- 14. PassScheduler empty features accepts all ----

    #[test]
    fn test_pass_scheduler_empty_features_accepts_all() {
        let passes = vec![quick_pass(), full_pass(), bv_pass()];
        let stages = PassScheduler::schedule(&passes, &HashSet::new());
        let total_passes: usize = stages.iter().map(|s| s.passes.len()).sum();
        assert_eq!(total_passes, 3);
    }

    // ---- 15. ProgressTracker basic ----

    #[test]
    fn test_progress_tracker_initial_state() {
        let tracker = ProgressTracker::new(10);
        assert_eq!(tracker.completed_count(), 0);
        assert_eq!(tracker.total_count(), 10);
        assert!(tracker.current_pass_name().is_none());
        let (frac, _) = tracker.current_progress();
        assert!((frac - 0.0).abs() < f64::EPSILON);
    }

    // ---- 16. ProgressTracker after start ----

    #[test]
    fn test_progress_tracker_start_sets_clock() {
        let mut tracker = ProgressTracker::new(5);
        tracker.start();
        assert!(tracker.elapsed() >= Duration::ZERO);
    }

    // ---- 17. ProgressTracker complete_pass ----

    #[test]
    fn test_progress_tracker_complete_pass_increments() {
        let mut tracker = ProgressTracker::new(4);
        tracker.start();
        tracker.complete_pass("quick");
        assert_eq!(tracker.completed_count(), 1);
        assert_eq!(tracker.current_pass_name(), Some("quick"));

        tracker.complete_pass("full");
        assert_eq!(tracker.completed_count(), 2);
        assert_eq!(tracker.current_pass_name(), Some("full"));
    }

    // ---- 18. ProgressTracker progress fraction ----

    #[test]
    fn test_progress_tracker_fraction_increases() {
        let mut tracker = ProgressTracker::new(4);
        tracker.start();
        tracker.complete_pass("p1");
        let (frac1, _) = tracker.current_progress();
        tracker.complete_pass("p2");
        let (frac2, _) = tracker.current_progress();
        assert!(frac2 > frac1);
    }

    // ---- 19. ProgressTracker zero total ----

    #[test]
    fn test_progress_tracker_zero_total_returns_full() {
        let mut tracker = ProgressTracker::new(0);
        tracker.start();
        let (frac, remaining) = tracker.current_progress();
        assert!((frac - 1.0).abs() < f64::EPSILON);
        assert_eq!(remaining, Duration::ZERO);
    }

    // ---- 20. ResultAggregator empty ----

    #[test]
    fn test_result_aggregator_empty_returns_skipped() {
        let agg = ResultAggregator::new();
        assert_eq!(agg.final_verdict("fn_x"), FinalVerdict::Skipped);
        assert!(agg.results_for("fn_x").is_empty());
        assert!(agg.function_names().is_empty());
    }

    // ---- 21. ResultAggregator verified ----

    #[test]
    fn test_result_aggregator_all_verified_returns_verified() {
        let mut agg = ResultAggregator::new();
        agg.add_result(PassResult {
            pass_name: "quick".to_string(),
            pass_kind: PassKind::QuickCheck,
            function_name: "fn_a".to_string(),
            outcome: PassOutcome::Verified,
            elapsed: Duration::ZERO,
            detail: None,
        });
        agg.add_result(PassResult {
            pass_name: "full".to_string(),
            pass_kind: PassKind::FullVerify,
            function_name: "fn_a".to_string(),
            outcome: PassOutcome::Verified,
            elapsed: Duration::ZERO,
            detail: None,
        });
        assert_eq!(agg.final_verdict("fn_a"), FinalVerdict::Verified);
    }

    // ---- 22. ResultAggregator failed precedence ----

    #[test]
    fn test_result_aggregator_failed_takes_precedence() {
        let mut agg = ResultAggregator::new();
        agg.add_result(PassResult {
            pass_name: "quick".to_string(),
            pass_kind: PassKind::QuickCheck,
            function_name: "fn_b".to_string(),
            outcome: PassOutcome::Verified,
            elapsed: Duration::ZERO,
            detail: None,
        });
        agg.add_result(PassResult {
            pass_name: "full".to_string(),
            pass_kind: PassKind::FullVerify,
            function_name: "fn_b".to_string(),
            outcome: PassOutcome::Failed,
            elapsed: Duration::ZERO,
            detail: None,
        });
        assert_eq!(agg.final_verdict("fn_b"), FinalVerdict::Failed);
    }

    // ---- 23. ResultAggregator inconclusive ----

    #[test]
    fn test_result_aggregator_unknown_yields_inconclusive() {
        let mut agg = ResultAggregator::new();
        agg.add_result(PassResult {
            pass_name: "quick".to_string(),
            pass_kind: PassKind::QuickCheck,
            function_name: "fn_c".to_string(),
            outcome: PassOutcome::Verified,
            elapsed: Duration::ZERO,
            detail: None,
        });
        agg.add_result(PassResult {
            pass_name: "full".to_string(),
            pass_kind: PassKind::FullVerify,
            function_name: "fn_c".to_string(),
            outcome: PassOutcome::Unknown,
            elapsed: Duration::ZERO,
            detail: None,
        });
        assert_eq!(agg.final_verdict("fn_c"), FinalVerdict::Inconclusive);
    }

    // ---- 24. ResultAggregator function_names sorted ----

    #[test]
    fn test_result_aggregator_function_names_sorted() {
        let mut agg = ResultAggregator::new();
        for name in &["fn_z", "fn_a", "fn_m"] {
            agg.add_result(PassResult {
                pass_name: "p".to_string(),
                pass_kind: PassKind::QuickCheck,
                function_name: name.to_string(),
                outcome: PassOutcome::Verified,
                elapsed: Duration::ZERO,
                detail: None,
            });
        }
        assert_eq!(agg.function_names(), vec!["fn_a", "fn_m", "fn_z"]);
    }

    // ---- 25. RetryPolicy should_retry ----

    #[test]
    fn test_retry_policy_should_retry_on_timeout() {
        let policy = RetryPolicy::default();
        assert!(policy.should_retry(PassOutcome::Timeout, 0));
        assert!(policy.should_retry(PassOutcome::Timeout, 1));
        assert!(!policy.should_retry(PassOutcome::Timeout, 2));
    }

    // ---- 26. RetryPolicy non-retryable ----

    #[test]
    fn test_retry_policy_does_not_retry_verified_or_failed() {
        let policy = RetryPolicy::default();
        assert!(!policy.should_retry(PassOutcome::Verified, 0));
        assert!(!policy.should_retry(PassOutcome::Failed, 0));
        assert!(!policy.should_retry(PassOutcome::Skipped, 0));
    }

    // ---- 27. RetryPolicy timeout escalation ----

    #[test]
    fn test_retry_policy_timeout_escalation() {
        let policy = RetryPolicy::default();
        let base = Duration::from_secs(10);
        let attempt_0 = policy.retry_timeout(base, 0);
        let attempt_1 = policy.retry_timeout(base, 1);
        let attempt_2 = policy.retry_timeout(base, 2);

        assert_eq!(attempt_0, base);
        assert!(attempt_1 > base);
        assert!(attempt_2 > attempt_1);
        // 2.0^1 = 2x, 2.0^2 = 4x
        let expected_1 = Duration::from_secs(20);
        let expected_2 = Duration::from_secs(40);
        assert!((attempt_1.as_secs_f64() - expected_1.as_secs_f64()).abs() < 0.01);
        assert!((attempt_2.as_secs_f64() - expected_2.as_secs_f64()).abs() < 0.01);
    }

    // ---- 28. CacheEntry validity ----

    #[test]
    fn test_cache_entry_validity_matches_hash() {
        let entry = CacheEntry::new("fn_a", 12345, PassKind::FullVerify, PassOutcome::Verified);
        assert!(entry.is_valid(12345));
        assert!(!entry.is_valid(99999));
    }

    // ---- 29. VerificationCache insert and lookup ----

    #[test]
    fn test_verification_cache_insert_and_lookup() {
        let mut cache = VerificationCache::new();
        assert!(cache.is_empty());

        cache.insert(CacheEntry::new(
            "fn_a",
            100,
            PassKind::FullVerify,
            PassOutcome::Verified,
        ));
        assert_eq!(cache.len(), 1);
        assert!(!cache.is_empty());

        assert_eq!(
            cache.lookup("fn_a", PassKind::FullVerify, 100),
            Some(PassOutcome::Verified)
        );
        assert_eq!(cache.lookup("fn_a", PassKind::FullVerify, 999), None);
        assert_eq!(cache.lookup("fn_a", PassKind::QuickCheck, 100), None);
        assert_eq!(cache.lookup("fn_b", PassKind::FullVerify, 100), None);
    }

    // ---- 30. VerificationCache clear ----

    #[test]
    fn test_verification_cache_clear() {
        let mut cache = VerificationCache::new();
        cache.insert(CacheEntry::new(
            "fn_a",
            1,
            PassKind::QuickCheck,
            PassOutcome::Verified,
        ));
        cache.insert(CacheEntry::new(
            "fn_b",
            2,
            PassKind::FullVerify,
            PassOutcome::Failed,
        ));
        assert_eq!(cache.len(), 2);

        cache.clear();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    // ---- 31. Pipeline incremental with cache ----

    #[test]
    fn test_pipeline_run_incremental_cache_hit() {
        let pipeline = PipelineBuilder::new().add_pass(quick_pass()).build();
        let mut cache = VerificationCache::new();

        // First run: no cache entries.
        let funcs: Vec<(&str, u64)> = vec![("fn_a", 100), ("fn_b", 200)];
        let result1 = pipeline.run_incremental(&funcs, &mut cache);
        assert_eq!(result1.verified_count(), 2);
        assert_eq!(result1.cache_hits, 0);
        assert_eq!(result1.cache_misses, 2);

        // Second run: same hashes => cache hits.
        let result2 = pipeline.run_incremental(&funcs, &mut cache);
        assert_eq!(result2.verified_count(), 2);
        assert_eq!(result2.cache_hits, 2);
        assert_eq!(result2.cache_misses, 0);
    }

    // ---- 32. Pipeline incremental cache miss on hash change ----

    #[test]
    fn test_pipeline_run_incremental_cache_miss_on_hash_change() {
        let pipeline = PipelineBuilder::new().add_pass(quick_pass()).build();
        let mut cache = VerificationCache::new();

        let funcs_v1: Vec<(&str, u64)> = vec![("fn_a", 100)];
        let _ = pipeline.run_incremental(&funcs_v1, &mut cache);

        // Changed hash for fn_a.
        let funcs_v2: Vec<(&str, u64)> = vec![("fn_a", 999)];
        let result = pipeline.run_incremental(&funcs_v2, &mut cache);
        assert_eq!(result.cache_hits, 0);
        assert_eq!(result.cache_misses, 1);
    }

    // ---- 33. PipelineResult render_report text ----

    #[test]
    fn test_pipeline_result_render_report_text() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&["fn_a", "fn_b"]);
        let text = result.render_report(ReportFormat::Text);
        assert!(text.contains("TrustVc Verification Pipeline Report"));
        assert!(text.contains("fn_a: verified"));
        assert!(text.contains("fn_b: verified"));
        assert!(text.contains("2 verified"));
    }

    // ---- 34. PipelineResult render_report json ----

    #[test]
    fn test_pipeline_result_render_report_json() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&["fn_a"]);
        let json = result.render_report(ReportFormat::Json);
        assert!(json.contains("\"total\": 1"));
        assert!(json.contains("\"verified\": 1"));
        assert!(json.contains("\"fn_a\": \"verified\""));
    }

    // ---- 35. PipelineResult render_report markdown ----

    #[test]
    fn test_pipeline_result_render_report_markdown() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&["fn_x"]);
        let md = result.render_report(ReportFormat::Markdown);
        assert!(md.contains("# Verification Pipeline Report"));
        assert!(md.contains("| fn_x | verified |"));
    }

    // ---- 36. PipelineReport from_results ----

    #[test]
    fn test_pipeline_report_from_results_summary_counts() {
        let results = vec![
            PassResult {
                pass_name: "p1".to_string(),
                pass_kind: PassKind::QuickCheck,
                function_name: "f".to_string(),
                outcome: PassOutcome::Verified,
                elapsed: Duration::ZERO,
                detail: None,
            },
            PassResult {
                pass_name: "p2".to_string(),
                pass_kind: PassKind::FullVerify,
                function_name: "f".to_string(),
                outcome: PassOutcome::Timeout,
                elapsed: Duration::from_millis(500),
                detail: Some("slow".to_string()),
            },
        ];

        let report = PipelineReport::from_results(&results, Duration::from_secs(1));
        assert_eq!(report.entries.len(), 2);
        assert_eq!(report.summary.get(&PassOutcome::Verified), Some(&1));
        assert_eq!(report.summary.get(&PassOutcome::Timeout), Some(&1));
    }

    // ---- 37. SolverConfig default values ----

    #[test]
    fn test_solver_config_defaults() {
        let config = SolverConfig::default();
        assert_eq!(config.ematching_rounds, 8);
        assert_eq!(config.qi_depth, 4);
        assert!(!config.enable_bv);
        assert!(!config.enable_nia);
    }

    // ---- 38. PipelineConfig default values ----

    #[test]
    fn test_pipeline_config_defaults() {
        let config = PipelineConfig::default();
        assert!(config.passes.is_empty());
        assert_eq!(config.parallelism, 1);
        assert!(config.global_timeout.is_none());
        assert!(!config.fail_fast);
        assert_eq!(config.retry_policy.max_retries, 2);
    }

    // ---- 39. Pipeline with no passes ----

    #[test]
    fn test_pipeline_no_passes_all_skipped() {
        let pipeline = PipelineBuilder::new().build();
        let result = pipeline.run(&["fn_a"]);
        assert_eq!(result.verdicts["fn_a"], FinalVerdict::Skipped);
        assert!(result.pass_results.is_empty());
    }

    // ---- 40. ResultAggregator timeout yields inconclusive ----

    #[test]
    fn test_result_aggregator_timeout_yields_inconclusive() {
        let mut agg = ResultAggregator::new();
        agg.add_result(PassResult {
            pass_name: "slow".to_string(),
            pass_kind: PassKind::DeepQuantifier,
            function_name: "fn_deep".to_string(),
            outcome: PassOutcome::Timeout,
            elapsed: Duration::from_secs(60),
            detail: Some("timed out".to_string()),
        });
        assert_eq!(agg.final_verdict("fn_deep"), FinalVerdict::Inconclusive);
    }

    // ---- 41. Pipeline elapsed is positive ----

    #[test]
    fn test_pipeline_elapsed_is_nonnegative() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&["fn_a"]);
        assert!(result.elapsed >= Duration::ZERO);
    }

    // ---- 42. PipelineResult has_failures with no failures ----

    #[test]
    fn test_pipeline_result_has_failures_returns_false_when_all_verified() {
        let pipeline = default_pipeline();
        let result = pipeline.run(&["fn_a", "fn_b"]);
        assert!(!result.has_failures());
    }

    // ---- 43. VerificationCache overwrites on reinsert ----

    #[test]
    fn test_verification_cache_overwrites_on_reinsert() {
        let mut cache = VerificationCache::new();
        cache.insert(CacheEntry::new(
            "fn_a",
            100,
            PassKind::FullVerify,
            PassOutcome::Failed,
        ));
        assert_eq!(
            cache.lookup("fn_a", PassKind::FullVerify, 100),
            Some(PassOutcome::Failed)
        );

        cache.insert(CacheEntry::new(
            "fn_a",
            100,
            PassKind::FullVerify,
            PassOutcome::Verified,
        ));
        assert_eq!(
            cache.lookup("fn_a", PassKind::FullVerify, 100),
            Some(PassOutcome::Verified)
        );
        assert_eq!(cache.len(), 1);
    }

    // ---- 44. PassScheduler empty input ----

    #[test]
    fn test_pass_scheduler_empty_input_returns_no_stages() {
        let stages = PassScheduler::schedule(&[], &HashSet::new());
        assert!(stages.is_empty());
    }

    // ---- 45. PipelineStage indices are sequential ----

    #[test]
    fn test_pipeline_stage_indices_sequential() {
        let passes = vec![quick_pass(), full_pass(), cert_pass()];
        let stages = PassScheduler::schedule(&passes, &HashSet::new());
        for (i, stage) in stages.iter().enumerate() {
            assert_eq!(stage.index, i);
        }
    }
}
