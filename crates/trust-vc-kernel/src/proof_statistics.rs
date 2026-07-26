// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof certificate statistics: complexity analysis, theory usage distribution,
//! resolution depth/width metrics, clause analysis, and quality scoring.
//!
//! This module is self-contained — only `std` types are used. Input data is
//! accepted as simple slices of lightweight descriptor structs so that callers
//! can feed data from any proof representation without coupling to wire formats.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

// ---------------------------------------------------------------------------
// Input descriptors — lightweight structs callers populate before computing
// ---------------------------------------------------------------------------

/// A clause descriptor for statistics computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputClause {
    pub id: u64,
    pub literals: Vec<i64>,
}

/// A resolution step descriptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputResolutionStep {
    pub id: u64,
    pub pivot: i64,
    pub parent1: u64,
    pub parent2: u64,
}

/// Theory kind tag for lemma classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Theory {
    Euf,
    Lra,
    Bv,
    Array,
    Nia,
    Seq,
    Unknown,
}

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Theory::Euf => write!(f, "EUF"),
            Theory::Lra => write!(f, "LRA"),
            Theory::Bv => write!(f, "BV"),
            Theory::Array => write!(f, "Array"),
            Theory::Nia => write!(f, "NIA"),
            Theory::Seq => write!(f, "Seq"),
            Theory::Unknown => write!(f, "Unknown"),
        }
    }
}

/// A theory lemma descriptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputTheoryLemma {
    pub id: u64,
    pub theory: Theory,
    pub literals: Vec<i64>,
    /// Whether this lemma was independently verified (`true`) or accepted
    /// on trust (`false`).
    pub verified: bool,
}

// ---------------------------------------------------------------------------
// Histogram
// ---------------------------------------------------------------------------

/// Bucket-based distribution tracker.
#[derive(Debug, Clone, PartialEq)]
pub struct Histogram {
    /// Upper bounds of each bucket (exclusive). The last bucket captures
    /// everything above the second-to-last bound.
    bucket_bounds: Vec<f64>,
    /// Count per bucket. Length is `bucket_bounds.len() + 1`.
    counts: Vec<u64>,
    /// All recorded values, kept for exact percentile computation.
    values: Vec<f64>,
}

impl Histogram {
    /// Create a histogram with the given bucket upper-bounds.
    ///
    /// Bounds are sorted internally. An implicit overflow bucket is appended.
    #[must_use]
    pub fn new(mut buckets: Vec<f64>) -> Self {
        buckets.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        let count_len = buckets.len() + 1;
        Self {
            bucket_bounds: buckets,
            counts: vec![0; count_len],
            values: Vec::new(),
        }
    }

    /// Record a single value.
    pub fn record(&mut self, value: f64) {
        self.values.push(value);
        let idx = self
            .bucket_bounds
            .iter()
            .position(|&b| value < b)
            .unwrap_or(self.bucket_bounds.len());
        self.counts[idx] += 1;
    }

    /// Number of recorded values.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.values.len() as u64
    }

    /// Arithmetic mean, or 0.0 for an empty histogram.
    #[must_use]
    pub fn mean(&self) -> f64 {
        if self.values.is_empty() {
            return 0.0;
        }
        self.values.iter().sum::<f64>() / self.values.len() as f64
    }

    /// Population standard deviation.
    #[must_use]
    pub fn std_dev(&self) -> f64 {
        if self.values.is_empty() {
            return 0.0;
        }
        let mean = self.mean();
        let variance =
            self.values.iter().map(|v| (v - mean).powi(2)).sum::<f64>() / self.values.len() as f64;
        variance.sqrt()
    }

    /// Percentile (0.0 ..= 100.0) via linear interpolation on sorted values.
    /// Returns 0.0 for empty histograms.
    #[must_use]
    pub fn percentile(&self, p: f64) -> f64 {
        if self.values.is_empty() {
            return 0.0;
        }
        let mut sorted = self.values.clone();
        sorted.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

        let clamped = p.clamp(0.0, 100.0);
        let rank = (clamped / 100.0) * (sorted.len() as f64 - 1.0);
        let lo = rank.floor() as usize;
        let hi = rank.ceil().min((sorted.len() - 1) as f64) as usize;
        let frac = rank - lo as f64;
        sorted[lo] * (1.0 - frac) + sorted[hi] * frac
    }

    /// Read-only access to bucket counts.
    #[must_use]
    pub fn bucket_counts(&self) -> &[u64] {
        &self.counts
    }
}

// ---------------------------------------------------------------------------
// TimeSeriesPoint
// ---------------------------------------------------------------------------

/// A single observation in a proof-evolution time series.
#[derive(Debug, Clone, PartialEq)]
pub struct TimeSeriesPoint {
    /// Monotonic index (e.g. iteration number or step ordinal).
    pub index: u64,
    /// Metric value at this index.
    pub value: f64,
    /// Optional label.
    pub label: String,
}

// ---------------------------------------------------------------------------
// ClauseStats
// ---------------------------------------------------------------------------

/// Statistics about a set of clauses.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ClauseStats {
    pub total_clauses: usize,
    pub total_literals: usize,
    pub min_length: usize,
    pub max_length: usize,
    pub avg_length: f64,
    pub median_length: f64,
    pub unit_clause_count: usize,
    pub empty_clause_count: usize,
    /// Distribution of clause lengths.
    pub length_histogram: Histogram,
    /// Number of distinct variables referenced.
    pub distinct_variables: usize,
}

impl ClauseStats {
    /// Compute clause statistics from a slice of input clauses.
    #[must_use]
    pub fn compute(clauses: &[InputClause]) -> Self {
        if clauses.is_empty() {
            return Self {
                total_clauses: 0,
                total_literals: 0,
                min_length: 0,
                max_length: 0,
                avg_length: 0.0,
                median_length: 0.0,
                unit_clause_count: 0,
                empty_clause_count: 0,
                length_histogram: Histogram::new(vec![1.0, 2.0, 4.0, 8.0, 16.0, 32.0]),
                distinct_variables: 0,
            };
        }

        let mut lengths: Vec<usize> = clauses.iter().map(|c| c.literals.len()).collect();
        lengths.sort_unstable();

        let total_literals: usize = lengths.iter().sum();
        let min_length = lengths[0];
        let max_length = lengths[lengths.len() - 1];
        let avg_length = total_literals as f64 / lengths.len() as f64;

        let median_length = if lengths.len().is_multiple_of(2) {
            (lengths[lengths.len() / 2 - 1] + lengths[lengths.len() / 2]) as f64 / 2.0
        } else {
            lengths[lengths.len() / 2] as f64
        };

        let unit_clause_count = lengths.iter().filter(|&&l| l == 1).count();
        let empty_clause_count = lengths.iter().filter(|&&l| l == 0).count();

        let mut histogram = Histogram::new(vec![1.0, 2.0, 4.0, 8.0, 16.0, 32.0]);
        for &len in &lengths {
            histogram.record(len as f64);
        }

        let mut vars = HashSet::new();
        for clause in clauses {
            for &lit in &clause.literals {
                vars.insert(lit.unsigned_abs());
            }
        }

        Self {
            total_clauses: clauses.len(),
            total_literals,
            min_length,
            max_length,
            avg_length,
            median_length,
            unit_clause_count,
            empty_clause_count,
            length_histogram: histogram,
            distinct_variables: vars.len(),
        }
    }
}

// ---------------------------------------------------------------------------
// ResolutionStats
// ---------------------------------------------------------------------------

/// Statistics about resolution steps in a proof.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ResolutionStats {
    pub total_steps: usize,
    /// Maximum depth from any input/lemma clause to the empty clause.
    pub max_depth: usize,
    /// Width: maximum number of steps at any single depth level.
    pub max_width: usize,
    /// Average branching factor (out-degree of each step used as parent).
    pub avg_branching_factor: f64,
    /// Fraction of steps that serve as parent to more than one other step.
    pub reuse_ratio: f64,
    /// Number of distinct pivot variables used.
    pub distinct_pivots: usize,
    /// Depth distribution histogram.
    pub depth_histogram: Histogram,
}

impl ResolutionStats {
    /// Compute resolution statistics.
    ///
    /// `input_ids` provides the set of clause IDs that are leaves
    /// (input clauses and theory lemmas).
    #[must_use]
    pub fn compute(steps: &[InputResolutionStep], input_ids: &HashSet<u64>) -> Self {
        if steps.is_empty() {
            return Self {
                total_steps: 0,
                max_depth: 0,
                max_width: 0,
                avg_branching_factor: 0.0,
                reuse_ratio: 0.0,
                distinct_pivots: 0,
                depth_histogram: Histogram::new(vec![5.0, 10.0, 20.0, 50.0, 100.0]),
            };
        }

        // Build parent-to-children adjacency for branching / reuse.
        let mut children_count: HashMap<u64, usize> = HashMap::new();

        // Compute depth of each step via topological order.
        let mut depth: HashMap<u64, usize> = HashMap::new();
        for &id in input_ids {
            depth.insert(id, 0);
        }

        // Iterative depth computation (BFS from leaves).
        let mut changed = true;
        while changed {
            changed = false;
            for step in steps {
                let d1 = depth.get(&step.parent1).copied();
                let d2 = depth.get(&step.parent2).copied();
                if let (Some(a), Some(b)) = (d1, d2) {
                    let new_depth = a.max(b) + 1;
                    let current = depth.get(&step.id).copied();
                    if current.is_none_or(|c| new_depth > c) {
                        depth.insert(step.id, new_depth);
                        changed = true;
                    }
                }
            }
        }

        // Branching: count how many times each clause is referenced as a parent.
        for step in steps {
            *children_count.entry(step.parent1).or_insert(0) += 1;
            *children_count.entry(step.parent2).or_insert(0) += 1;
        }

        let reused = children_count.values().filter(|&&c| c > 1).count();
        let total_parents = children_count.len();
        let reuse_ratio = if total_parents > 0 {
            reused as f64 / total_parents as f64
        } else {
            0.0
        };

        let total_children: usize = children_count.values().sum();
        let avg_branching = if total_parents > 0 {
            total_children as f64 / total_parents as f64
        } else {
            0.0
        };

        // Depth-level width.
        let mut level_counts: BTreeMap<usize, usize> = BTreeMap::new();
        let mut max_depth_val = 0usize;
        let mut depth_hist = Histogram::new(vec![5.0, 10.0, 20.0, 50.0, 100.0]);
        for step in steps {
            if let Some(&d) = depth.get(&step.id) {
                *level_counts.entry(d).or_insert(0) += 1;
                if d > max_depth_val {
                    max_depth_val = d;
                }
                depth_hist.record(d as f64);
            }
        }
        let max_width = level_counts.values().copied().max().unwrap_or(0);

        let distinct_pivots: HashSet<i64> = steps.iter().map(|s| s.pivot.abs()).collect();

        Self {
            total_steps: steps.len(),
            max_depth: max_depth_val,
            max_width,
            avg_branching_factor: avg_branching,
            reuse_ratio,
            distinct_pivots: distinct_pivots.len(),
            depth_histogram: depth_hist,
        }
    }
}

// ---------------------------------------------------------------------------
// TheoryUsageStats
// ---------------------------------------------------------------------------

/// Per-theory usage statistics.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct TheoryUsageStats {
    pub total_lemmas: usize,
    pub verified_count: usize,
    pub trusted_count: usize,
    /// Trust ratio: `trusted_count / total_lemmas`.
    pub trust_ratio: f64,
    /// Per-theory step counts.
    pub per_theory: BTreeMap<String, usize>,
    /// Per-theory trust ratios.
    pub per_theory_trust_ratio: BTreeMap<String, f64>,
    /// Average lemma width (number of literals).
    pub avg_lemma_width: f64,
}

impl TheoryUsageStats {
    /// Compute theory usage statistics from a slice of theory lemmas.
    #[must_use]
    pub fn compute(lemmas: &[InputTheoryLemma]) -> Self {
        if lemmas.is_empty() {
            return Self {
                total_lemmas: 0,
                verified_count: 0,
                trusted_count: 0,
                trust_ratio: 0.0,
                per_theory: BTreeMap::new(),
                per_theory_trust_ratio: BTreeMap::new(),
                avg_lemma_width: 0.0,
            };
        }

        let verified_count = lemmas.iter().filter(|l| l.verified).count();
        let trusted_count = lemmas.len() - verified_count;
        let trust_ratio = trusted_count as f64 / lemmas.len() as f64;

        let mut per_theory: BTreeMap<String, usize> = BTreeMap::new();
        let mut per_theory_trusted: BTreeMap<String, usize> = BTreeMap::new();

        for lemma in lemmas {
            let key = lemma.theory.to_string();
            *per_theory.entry(key.clone()).or_insert(0) += 1;
            if !lemma.verified {
                *per_theory_trusted.entry(key).or_insert(0) += 1;
            }
        }

        let mut per_theory_trust_ratio = BTreeMap::new();
        for (theory, &count) in &per_theory {
            let trusted = per_theory_trusted.get(theory).copied().unwrap_or(0);
            per_theory_trust_ratio.insert(theory.clone(), trusted as f64 / count as f64);
        }

        let total_lits: usize = lemmas.iter().map(|l| l.literals.len()).sum();
        let avg_lemma_width = total_lits as f64 / lemmas.len() as f64;

        Self {
            total_lemmas: lemmas.len(),
            verified_count,
            trusted_count,
            trust_ratio,
            per_theory,
            per_theory_trust_ratio,
            avg_lemma_width,
        }
    }
}

// ---------------------------------------------------------------------------
// ComplexityMetrics
// ---------------------------------------------------------------------------

/// Structural complexity measurements for a proof.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ComplexityMetrics {
    /// Total proof size (input clauses + resolution steps + theory lemmas).
    pub proof_size: usize,
    /// DAG compression ratio: `unique_subproofs / total_steps`.
    /// 1.0 means no sharing; lower means more subproof reuse.
    pub dag_compression_ratio: f64,
    /// Maximum tree height (longest path from root to any leaf).
    pub tree_height: usize,
    /// Maximum tree width (widest level).
    pub tree_width: usize,
    /// Ratio of resolution steps to input clauses.
    pub amplification_ratio: f64,
}

impl ComplexityMetrics {
    /// Compute complexity metrics.
    #[must_use]
    pub fn compute(
        steps: &[InputResolutionStep],
        input_count: usize,
        leaf_ids: &HashSet<u64>,
    ) -> Self {
        let proof_size = input_count + steps.len();

        // Compute tree height via depth propagation.
        let mut depth: HashMap<u64, usize> = HashMap::new();
        for &id in leaf_ids {
            depth.insert(id, 0);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for step in steps {
                let d1 = depth.get(&step.parent1).copied();
                let d2 = depth.get(&step.parent2).copied();
                if let (Some(a), Some(b)) = (d1, d2) {
                    let new_d = a.max(b) + 1;
                    if depth.get(&step.id).copied().is_none_or(|c| new_d > c) {
                        depth.insert(step.id, new_d);
                        changed = true;
                    }
                }
            }
        }

        let tree_height = depth.values().copied().max().unwrap_or(0);

        // Width per level.
        let mut level_counts: BTreeMap<usize, usize> = BTreeMap::new();
        for step in steps {
            if let Some(&d) = depth.get(&step.id) {
                *level_counts.entry(d).or_insert(0) += 1;
            }
        }
        let tree_width = level_counts.values().copied().max().unwrap_or(0);

        // DAG compression: count unique (parent1, parent2, pivot) triples.
        let unique: HashSet<(u64, u64, i64)> = steps
            .iter()
            .map(|s| {
                let (a, b) = if s.parent1 <= s.parent2 {
                    (s.parent1, s.parent2)
                } else {
                    (s.parent2, s.parent1)
                };
                (a, b, s.pivot.abs())
            })
            .collect();
        let dag_compression_ratio = if steps.is_empty() {
            1.0
        } else {
            unique.len() as f64 / steps.len() as f64
        };

        let amplification_ratio = if input_count == 0 {
            0.0
        } else {
            steps.len() as f64 / input_count as f64
        };

        Self {
            proof_size,
            dag_compression_ratio,
            tree_height,
            tree_width,
            amplification_ratio,
        }
    }
}

// ---------------------------------------------------------------------------
// QualityScore
// ---------------------------------------------------------------------------

/// A numeric quality rating for a proof certificate.
#[derive(Debug, Clone, PartialEq)]
pub struct QualityScore {
    /// Overall score 0–100.
    pub score: u32,
    /// Confidence in the score (0.0–1.0). Lower when the proof is very
    /// small and statistical measures are unreliable.
    pub confidence: f64,
    /// Breakdown of component scores.
    pub components: Vec<(String, u32)>,
}

impl QualityScore {
    /// Human-readable quality band.
    #[must_use]
    pub fn band(&self) -> &'static str {
        match self.score {
            90..=100 => "excellent",
            70..=89 => "good",
            50..=69 => "fair",
            25..=49 => "poor",
            _ => "critical",
        }
    }
}

// ---------------------------------------------------------------------------
// HealthWarning
// ---------------------------------------------------------------------------

/// Warning severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    Info,
    Warning,
    Error,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Severity::Info => write!(f, "info"),
            Severity::Warning => write!(f, "warning"),
            Severity::Error => write!(f, "error"),
        }
    }
}

/// Kind of health warning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum WarningKind {
    TooManyTrustSteps,
    DeepResolution,
    WideResolution,
    HighAmplification,
    LowDagCompression,
    NoTheoryLemmas,
    AllTrusted,
    LargeProof,
}

impl fmt::Display for WarningKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WarningKind::TooManyTrustSteps => write!(f, "too_many_trust_steps"),
            WarningKind::DeepResolution => write!(f, "deep_resolution"),
            WarningKind::WideResolution => write!(f, "wide_resolution"),
            WarningKind::HighAmplification => write!(f, "high_amplification"),
            WarningKind::LowDagCompression => write!(f, "low_dag_compression"),
            WarningKind::NoTheoryLemmas => write!(f, "no_theory_lemmas"),
            WarningKind::AllTrusted => write!(f, "all_trusted"),
            WarningKind::LargeProof => write!(f, "large_proof"),
        }
    }
}

/// A health warning emitted during proof quality analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HealthWarning {
    pub kind: WarningKind,
    pub severity: Severity,
    pub message: String,
}

// ---------------------------------------------------------------------------
// ProofHealthReport
// ---------------------------------------------------------------------------

/// A comprehensive health report for a proof certificate.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ProofHealthReport {
    pub quality: QualityScore,
    pub warnings: Vec<HealthWarning>,
    pub recommendations: Vec<String>,
}

// ---------------------------------------------------------------------------
// ProofStatistics (top-level)
// ---------------------------------------------------------------------------

/// Comprehensive statistics about a proof certificate.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ProofStatistics {
    pub clause_stats: ClauseStats,
    pub resolution_stats: ResolutionStats,
    pub theory_stats: TheoryUsageStats,
    pub complexity: ComplexityMetrics,
}

impl ProofStatistics {
    /// Compute a quality score from the gathered statistics.
    #[must_use]
    pub fn quality_score(&self) -> QualityScore {
        let mut components = Vec::new();
        let mut total: f64 = 0.0;
        let mut weight_sum: f64 = 0.0;

        // Trust score: lower trust ratio = higher score (weight 30).
        // Clamp to [0, 100] to guard against NaN inputs (NaN as u32 silently yields 0).
        let trust_score = ((1.0 - self.theory_stats.trust_ratio) * 100.0).clamp(0.0, 100.0) as u32;
        components.push(("trust".to_string(), trust_score));
        total += trust_score as f64 * 30.0;
        weight_sum += 30.0;

        // Depth score: shallower proofs score higher (weight 25).
        let depth_score = if self.resolution_stats.max_depth == 0 {
            100u32
        } else if self.resolution_stats.max_depth <= 10 {
            90
        } else if self.resolution_stats.max_depth <= 50 {
            70
        } else if self.resolution_stats.max_depth <= 200 {
            50
        } else {
            25
        };
        components.push(("depth".to_string(), depth_score));
        total += depth_score as f64 * 25.0;
        weight_sum += 25.0;

        // Compression score: higher DAG sharing = better (weight 20).
        // Clamp to guard against NaN from dag_compression_ratio.
        let compression_score = ((1.0 - self.complexity.dag_compression_ratio.min(1.0)) * 80.0
            + 20.0)
            .clamp(0.0, 100.0) as u32;
        components.push(("compression".to_string(), compression_score.min(100)));
        total += compression_score.min(100) as f64 * 20.0;
        weight_sum += 20.0;

        // Amplification score (weight 15).
        let amp_score = if self.complexity.amplification_ratio <= 2.0 {
            95u32
        } else if self.complexity.amplification_ratio <= 5.0 {
            80
        } else if self.complexity.amplification_ratio <= 20.0 {
            60
        } else {
            30
        };
        components.push(("amplification".to_string(), amp_score));
        total += amp_score as f64 * 15.0;
        weight_sum += 15.0;

        // Reuse score (weight 10).
        // Clamp to guard against NaN from reuse_ratio.
        let reuse_score = (self.resolution_stats.reuse_ratio * 100.0).clamp(0.0, 100.0) as u32;
        components.push(("reuse".to_string(), reuse_score));
        total += reuse_score as f64 * 10.0;
        weight_sum += 10.0;

        let score = if weight_sum > 0.0 {
            (total / weight_sum).round().clamp(0.0, 100.0) as u32
        } else {
            0
        };

        // Confidence: low for very small proofs.
        let n = self.complexity.proof_size;
        let confidence = if n == 0 {
            0.0
        } else if n < 5 {
            0.3
        } else if n < 20 {
            0.6
        } else if n < 100 {
            0.85
        } else {
            1.0
        };

        QualityScore {
            score: score.min(100),
            confidence,
            components,
        }
    }

    /// Generate a health report with warnings and recommendations.
    #[must_use]
    pub fn health_report(&self) -> ProofHealthReport {
        let quality = self.quality_score();
        let mut warnings = Vec::new();
        let mut recommendations = Vec::new();

        // Trust ratio check.
        if self.theory_stats.trust_ratio > 0.5 && self.theory_stats.total_lemmas > 0 {
            warnings.push(HealthWarning {
                kind: WarningKind::TooManyTrustSteps,
                severity: Severity::Warning,
                message: format!(
                    "{:.0}% of theory lemmas are accepted on trust ({}/{})",
                    self.theory_stats.trust_ratio * 100.0,
                    self.theory_stats.trusted_count,
                    self.theory_stats.total_lemmas,
                ),
            });
            recommendations
                .push("Enable theory checkers for BV/Array/NIA to reduce trust ratio.".to_string());
        }

        if self.theory_stats.total_lemmas > 0
            && self.theory_stats.trusted_count == self.theory_stats.total_lemmas
        {
            warnings.push(HealthWarning {
                kind: WarningKind::AllTrusted,
                severity: Severity::Error,
                message: "All theory lemmas are accepted on trust — no independent verification."
                    .to_string(),
            });
        }

        // Depth check.
        if self.resolution_stats.max_depth > 200 {
            warnings.push(HealthWarning {
                kind: WarningKind::DeepResolution,
                severity: Severity::Warning,
                message: format!(
                    "Resolution depth {} exceeds recommended maximum of 200.",
                    self.resolution_stats.max_depth,
                ),
            });
            recommendations
                .push("Consider proof compaction to reduce resolution depth.".to_string());
        }

        // Width check.
        if self.resolution_stats.max_width > 500 {
            warnings.push(HealthWarning {
                kind: WarningKind::WideResolution,
                severity: Severity::Warning,
                message: format!(
                    "Resolution width {} exceeds recommended maximum of 500.",
                    self.resolution_stats.max_width,
                ),
            });
        }

        // Amplification check.
        if self.complexity.amplification_ratio > 20.0 {
            warnings.push(HealthWarning {
                kind: WarningKind::HighAmplification,
                severity: Severity::Warning,
                message: format!(
                    "Amplification ratio {:.1}x exceeds recommended maximum of 20x.",
                    self.complexity.amplification_ratio,
                ),
            });
        }

        // DAG compression.
        if self.complexity.dag_compression_ratio > 0.98 && self.resolution_stats.total_steps > 10 {
            warnings.push(HealthWarning {
                kind: WarningKind::LowDagCompression,
                severity: Severity::Info,
                message: "Very little subproof sharing detected.".to_string(),
            });
            recommendations.push("Run proof compression to identify shared subproofs.".to_string());
        }

        // Large proof.
        if self.complexity.proof_size > 10_000 {
            warnings.push(HealthWarning {
                kind: WarningKind::LargeProof,
                severity: Severity::Info,
                message: format!(
                    "Proof size {} is large; consider compaction.",
                    self.complexity.proof_size,
                ),
            });
        }

        ProofHealthReport {
            quality,
            warnings,
            recommendations,
        }
    }

    /// Produce a human-readable summary.
    #[must_use]
    pub fn summary_text(&self) -> String {
        let quality = self.quality_score();
        let report = self.health_report();

        let mut out = String::new();
        out.push_str("=== Proof Statistics Summary ===\n\n");

        out.push_str(&format!(
            "Quality: {}/100 ({}) [confidence: {:.0}%]\n\n",
            quality.score,
            quality.band(),
            quality.confidence * 100.0,
        ));

        out.push_str("-- Clauses --\n");
        out.push_str(&format!("  Total: {}\n", self.clause_stats.total_clauses));
        out.push_str(&format!(
            "  Length: min={}, max={}, avg={:.1}, median={:.1}\n",
            self.clause_stats.min_length,
            self.clause_stats.max_length,
            self.clause_stats.avg_length,
            self.clause_stats.median_length,
        ));
        out.push_str(&format!(
            "  Unit clauses: {}, Empty clauses: {}\n",
            self.clause_stats.unit_clause_count, self.clause_stats.empty_clause_count,
        ));
        out.push_str(&format!(
            "  Distinct variables: {}\n\n",
            self.clause_stats.distinct_variables,
        ));

        out.push_str("-- Resolution --\n");
        out.push_str(&format!("  Steps: {}\n", self.resolution_stats.total_steps,));
        out.push_str(&format!(
            "  Depth: max={}, Width: max={}\n",
            self.resolution_stats.max_depth, self.resolution_stats.max_width,
        ));
        out.push_str(&format!(
            "  Branching factor: {:.2}, Reuse ratio: {:.2}\n",
            self.resolution_stats.avg_branching_factor, self.resolution_stats.reuse_ratio,
        ));
        out.push_str(&format!(
            "  Distinct pivots: {}\n\n",
            self.resolution_stats.distinct_pivots,
        ));

        out.push_str("-- Theory Usage --\n");
        out.push_str(&format!(
            "  Total lemmas: {} (verified: {}, trusted: {})\n",
            self.theory_stats.total_lemmas,
            self.theory_stats.verified_count,
            self.theory_stats.trusted_count,
        ));
        out.push_str(&format!(
            "  Trust ratio: {:.1}%\n",
            self.theory_stats.trust_ratio * 100.0,
        ));
        for (theory, count) in &self.theory_stats.per_theory {
            let tr = self
                .theory_stats
                .per_theory_trust_ratio
                .get(theory)
                .copied()
                .unwrap_or(0.0);
            out.push_str(&format!(
                "  {}: {} lemmas (trust: {:.0}%)\n",
                theory,
                count,
                tr * 100.0,
            ));
        }
        out.push('\n');

        out.push_str("-- Complexity --\n");
        out.push_str(&format!("  Proof size: {}\n", self.complexity.proof_size));
        out.push_str(&format!(
            "  DAG compression: {:.2}\n",
            self.complexity.dag_compression_ratio,
        ));
        out.push_str(&format!(
            "  Tree: height={}, width={}\n",
            self.complexity.tree_height, self.complexity.tree_width,
        ));
        out.push_str(&format!(
            "  Amplification: {:.1}x\n\n",
            self.complexity.amplification_ratio,
        ));

        if !report.warnings.is_empty() {
            out.push_str("-- Warnings --\n");
            for w in &report.warnings {
                out.push_str(&format!("  [{}] {}: {}\n", w.severity, w.kind, w.message));
            }
            out.push('\n');
        }

        if !report.recommendations.is_empty() {
            out.push_str("-- Recommendations --\n");
            for r in &report.recommendations {
                out.push_str(&format!("  - {}\n", r));
            }
        }

        out
    }
}

// ---------------------------------------------------------------------------
// ProofComparison
// ---------------------------------------------------------------------------

/// Statistical comparison of two proof certificates.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ProofComparison {
    pub size_delta: i64,
    pub depth_delta: i64,
    pub width_delta: i64,
    pub trust_ratio_delta: f64,
    pub quality_delta: i32,
    pub amplification_delta: f64,
    pub improved: bool,
    pub summary: String,
}

impl ProofComparison {
    /// Compare two proof statistics, treating `old` as the baseline.
    #[must_use]
    pub fn compare(old: &ProofStatistics, new: &ProofStatistics) -> Self {
        let size_delta = i64::try_from(new.complexity.proof_size).unwrap_or(i64::MAX)
            - i64::try_from(old.complexity.proof_size).unwrap_or(i64::MAX);
        let depth_delta = i64::try_from(new.resolution_stats.max_depth).unwrap_or(i64::MAX)
            - i64::try_from(old.resolution_stats.max_depth).unwrap_or(i64::MAX);
        let width_delta = i64::try_from(new.resolution_stats.max_width).unwrap_or(i64::MAX)
            - i64::try_from(old.resolution_stats.max_width).unwrap_or(i64::MAX);
        let trust_ratio_delta = new.theory_stats.trust_ratio - old.theory_stats.trust_ratio;
        let old_q = old.quality_score().score as i32;
        let new_q = new.quality_score().score as i32;
        let quality_delta = new_q - old_q;
        let amplification_delta =
            new.complexity.amplification_ratio - old.complexity.amplification_ratio;

        // Improved if quality went up, or stayed the same but size went down.
        let improved = quality_delta > 0 || (quality_delta == 0 && size_delta < 0);

        let direction = if improved {
            "improved"
        } else {
            "regressed or unchanged"
        };
        let summary = format!(
            "Proof {}: quality {} -> {} (delta {:+}), size {} -> {} (delta {:+}), depth {} -> {} (delta {:+})",
            direction,
            old_q, new_q, quality_delta,
            old.complexity.proof_size, new.complexity.proof_size, size_delta,
            old.resolution_stats.max_depth, new.resolution_stats.max_depth, depth_delta,
        );

        Self {
            size_delta,
            depth_delta,
            width_delta,
            trust_ratio_delta,
            quality_delta,
            amplification_delta,
            improved,
            summary,
        }
    }
}

// ---------------------------------------------------------------------------
// StatisticsComputer — main computation engine
// ---------------------------------------------------------------------------

/// Main engine for computing proof statistics from raw proof data.
pub struct StatisticsComputer;

impl StatisticsComputer {
    /// Compute comprehensive statistics from proof components.
    #[must_use]
    pub fn compute(
        input_clauses: &[InputClause],
        resolution_steps: &[InputResolutionStep],
        theory_lemmas: &[InputTheoryLemma],
    ) -> ProofStatistics {
        // Build the set of leaf IDs (input clauses + theory lemmas).
        let mut leaf_ids: HashSet<u64> = input_clauses.iter().map(|c| c.id).collect();
        for lemma in theory_lemmas {
            leaf_ids.insert(lemma.id);
        }

        // Clause stats cover both input clauses and theory lemma clauses.
        let mut all_clauses: Vec<InputClause> = input_clauses.to_vec();
        for lemma in theory_lemmas {
            all_clauses.push(InputClause {
                id: lemma.id,
                literals: lemma.literals.clone(),
            });
        }

        let clause_stats = ClauseStats::compute(&all_clauses);
        let resolution_stats = ResolutionStats::compute(resolution_steps, &leaf_ids);
        let theory_stats = TheoryUsageStats::compute(theory_lemmas);
        let input_count = input_clauses.len() + theory_lemmas.len();
        let complexity = ComplexityMetrics::compute(resolution_steps, input_count, &leaf_ids);

        ProofStatistics {
            clause_stats,
            resolution_stats,
            theory_stats,
            complexity,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helpers --

    fn make_clause(id: u64, lits: &[i64]) -> InputClause {
        InputClause {
            id,
            literals: lits.to_vec(),
        }
    }

    fn make_step(id: u64, pivot: i64, p1: u64, p2: u64) -> InputResolutionStep {
        InputResolutionStep {
            id,
            pivot,
            parent1: p1,
            parent2: p2,
        }
    }

    fn make_lemma(id: u64, theory: Theory, lits: &[i64], verified: bool) -> InputTheoryLemma {
        InputTheoryLemma {
            id,
            theory,
            literals: lits.to_vec(),
            verified,
        }
    }

    // -- Histogram tests --

    #[test]
    fn test_histogram_empty_returns_zero_mean() {
        let h = Histogram::new(vec![1.0, 5.0, 10.0]);
        assert_eq!(h.mean(), 0.0);
        assert_eq!(h.std_dev(), 0.0);
        assert_eq!(h.count(), 0);
    }

    #[test]
    fn test_histogram_single_value() {
        let mut h = Histogram::new(vec![5.0, 10.0]);
        h.record(3.0);
        assert_eq!(h.count(), 1);
        assert!((h.mean() - 3.0).abs() < f64::EPSILON);
        assert!((h.std_dev()).abs() < f64::EPSILON);
    }

    #[test]
    fn test_histogram_mean_multiple() {
        let mut h = Histogram::new(vec![5.0]);
        h.record(2.0);
        h.record(4.0);
        h.record(6.0);
        assert!((h.mean() - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_histogram_std_dev() {
        let mut h = Histogram::new(vec![10.0]);
        for v in [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0] {
            h.record(v);
        }
        // Population std dev of [2,4,4,4,5,5,7,9] = sqrt(4) = 2.0
        assert!((h.std_dev() - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_histogram_percentile_median() {
        let mut h = Histogram::new(vec![50.0, 100.0]);
        for v in 1..=100 {
            h.record(v as f64);
        }
        let p50 = h.percentile(50.0);
        assert!((p50 - 50.5).abs() < 1e-10);
    }

    #[test]
    fn test_histogram_percentile_bounds() {
        let mut h = Histogram::new(vec![10.0]);
        h.record(1.0);
        h.record(2.0);
        h.record(3.0);
        assert!((h.percentile(0.0) - 1.0).abs() < f64::EPSILON);
        assert!((h.percentile(100.0) - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_histogram_empty_percentile() {
        let h = Histogram::new(vec![1.0]);
        assert_eq!(h.percentile(50.0), 0.0);
    }

    #[test]
    fn test_histogram_bucket_counts() {
        let mut h = Histogram::new(vec![5.0, 10.0]);
        h.record(1.0); // bucket 0 (<5)
        h.record(3.0); // bucket 0
        h.record(7.0); // bucket 1 (5..10)
        h.record(15.0); // bucket 2 (>=10)
        assert_eq!(h.bucket_counts(), &[2, 1, 1]);
    }

    // -- ClauseStats tests --

    #[test]
    fn test_clause_stats_empty() {
        let stats = ClauseStats::compute(&[]);
        assert_eq!(stats.total_clauses, 0);
        assert_eq!(stats.total_literals, 0);
        assert_eq!(stats.min_length, 0);
        assert_eq!(stats.max_length, 0);
    }

    #[test]
    fn test_clause_stats_single_unit_clause() {
        let clauses = [make_clause(1, &[42])];
        let stats = ClauseStats::compute(&clauses);
        assert_eq!(stats.total_clauses, 1);
        assert_eq!(stats.unit_clause_count, 1);
        assert_eq!(stats.min_length, 1);
        assert_eq!(stats.max_length, 1);
        assert!((stats.avg_length - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_clause_stats_mixed_lengths() {
        let clauses = [
            make_clause(1, &[1]),
            make_clause(2, &[1, 2, 3]),
            make_clause(3, &[1, 2, 3, 4, 5]),
        ];
        let stats = ClauseStats::compute(&clauses);
        assert_eq!(stats.total_clauses, 3);
        assert_eq!(stats.min_length, 1);
        assert_eq!(stats.max_length, 5);
        assert!((stats.avg_length - 3.0).abs() < f64::EPSILON);
        assert!((stats.median_length - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_clause_stats_empty_clause() {
        let clauses = [make_clause(1, &[])];
        let stats = ClauseStats::compute(&clauses);
        assert_eq!(stats.empty_clause_count, 1);
        assert_eq!(stats.unit_clause_count, 0);
    }

    #[test]
    fn test_clause_stats_distinct_variables() {
        let clauses = [make_clause(1, &[1, -2, 3]), make_clause(2, &[2, -3, 4])];
        let stats = ClauseStats::compute(&clauses);
        // Variables: 1, 2, 3, 4
        assert_eq!(stats.distinct_variables, 4);
    }

    #[test]
    fn test_clause_stats_median_even_count() {
        let clauses = [
            make_clause(1, &[1]),
            make_clause(2, &[1, 2]),
            make_clause(3, &[1, 2, 3]),
            make_clause(4, &[1, 2, 3, 4]),
        ];
        let stats = ClauseStats::compute(&clauses);
        // Lengths: 1, 2, 3, 4 -> median = (2+3)/2 = 2.5
        assert!((stats.median_length - 2.5).abs() < f64::EPSILON);
    }

    // -- ResolutionStats tests --

    #[test]
    fn test_resolution_stats_empty() {
        let stats = ResolutionStats::compute(&[], &HashSet::new());
        assert_eq!(stats.total_steps, 0);
        assert_eq!(stats.max_depth, 0);
        assert_eq!(stats.max_width, 0);
    }

    #[test]
    fn test_resolution_stats_single_step() {
        let input_ids: HashSet<u64> = [1, 2].into_iter().collect();
        let steps = [make_step(3, 1, 1, 2)];
        let stats = ResolutionStats::compute(&steps, &input_ids);
        assert_eq!(stats.total_steps, 1);
        assert_eq!(stats.max_depth, 1);
        assert_eq!(stats.distinct_pivots, 1);
    }

    #[test]
    fn test_resolution_stats_chain_depth() {
        // Linear chain: 1,2 -> 3, 3,4 -> 5, 5,6 -> 7
        let input_ids: HashSet<u64> = [1, 2, 4, 6].into_iter().collect();
        let steps = [
            make_step(3, 1, 1, 2),
            make_step(5, 2, 3, 4),
            make_step(7, 3, 5, 6),
        ];
        let stats = ResolutionStats::compute(&steps, &input_ids);
        assert_eq!(stats.max_depth, 3);
    }

    #[test]
    fn test_resolution_stats_reuse() {
        // Step 3 resolves 1,2. Step 4 resolves 1,3. Clause 1 reused.
        let input_ids: HashSet<u64> = [1, 2].into_iter().collect();
        let steps = [make_step(3, 1, 1, 2), make_step(4, 2, 1, 3)];
        let stats = ResolutionStats::compute(&steps, &input_ids);
        assert!(stats.reuse_ratio > 0.0);
    }

    #[test]
    fn test_resolution_stats_distinct_pivots() {
        let input_ids: HashSet<u64> = [1, 2, 3].into_iter().collect();
        let steps = [
            make_step(10, 5, 1, 2),
            make_step(11, -5, 2, 3), // same variable, different sign
            make_step(12, 7, 10, 11),
        ];
        let stats = ResolutionStats::compute(&steps, &input_ids);
        assert_eq!(stats.distinct_pivots, 2); // |5| and |7|
    }

    // -- TheoryUsageStats tests --

    #[test]
    fn test_theory_stats_empty() {
        let stats = TheoryUsageStats::compute(&[]);
        assert_eq!(stats.total_lemmas, 0);
        assert_eq!(stats.trust_ratio, 0.0);
    }

    #[test]
    fn test_theory_stats_all_verified() {
        let lemmas = [
            make_lemma(1, Theory::Euf, &[1, -2], true),
            make_lemma(2, Theory::Lra, &[3, -4], true),
        ];
        let stats = TheoryUsageStats::compute(&lemmas);
        assert_eq!(stats.verified_count, 2);
        assert_eq!(stats.trusted_count, 0);
        assert!((stats.trust_ratio).abs() < f64::EPSILON);
    }

    #[test]
    fn test_theory_stats_mixed_trust() {
        let lemmas = [
            make_lemma(1, Theory::Euf, &[1, -2], true),
            make_lemma(2, Theory::Bv, &[3], false),
            make_lemma(3, Theory::Array, &[4, 5], false),
        ];
        let stats = TheoryUsageStats::compute(&lemmas);
        assert_eq!(stats.verified_count, 1);
        assert_eq!(stats.trusted_count, 2);
        assert!((stats.trust_ratio - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_theory_stats_per_theory_counts() {
        let lemmas = [
            make_lemma(1, Theory::Euf, &[1], true),
            make_lemma(2, Theory::Euf, &[2], true),
            make_lemma(3, Theory::Lra, &[3], false),
        ];
        let stats = TheoryUsageStats::compute(&lemmas);
        assert_eq!(stats.per_theory.get("EUF"), Some(&2));
        assert_eq!(stats.per_theory.get("LRA"), Some(&1));
    }

    #[test]
    fn test_theory_stats_per_theory_trust_ratio() {
        let lemmas = [
            make_lemma(1, Theory::Euf, &[1], true),
            make_lemma(2, Theory::Euf, &[2], false),
        ];
        let stats = TheoryUsageStats::compute(&lemmas);
        let euf_tr = stats
            .per_theory_trust_ratio
            .get("EUF")
            .copied()
            .expect("per_theory_trust_ratio should contain EUF entry");
        assert!((euf_tr - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_theory_stats_avg_lemma_width() {
        let lemmas = [
            make_lemma(1, Theory::Euf, &[1, 2, 3], true),
            make_lemma(2, Theory::Lra, &[4], true),
        ];
        let stats = TheoryUsageStats::compute(&lemmas);
        assert!((stats.avg_lemma_width - 2.0).abs() < f64::EPSILON);
    }

    // -- ComplexityMetrics tests --

    #[test]
    fn test_complexity_empty() {
        let metrics = ComplexityMetrics::compute(&[], 0, &HashSet::new());
        assert_eq!(metrics.proof_size, 0);
        assert_eq!(metrics.tree_height, 0);
        assert!((metrics.dag_compression_ratio - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_complexity_simple_proof() {
        let leaf_ids: HashSet<u64> = [1, 2].into_iter().collect();
        let steps = [make_step(3, 1, 1, 2)];
        let metrics = ComplexityMetrics::compute(&steps, 2, &leaf_ids);
        assert_eq!(metrics.proof_size, 3);
        assert_eq!(metrics.tree_height, 1);
        assert!((metrics.amplification_ratio - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_complexity_dag_compression() {
        // Two identical steps (same parents+pivot) should compress.
        let leaf_ids: HashSet<u64> = [1, 2].into_iter().collect();
        let steps = [
            make_step(3, 1, 1, 2),
            make_step(4, 1, 1, 2), // duplicate structure
        ];
        let metrics = ComplexityMetrics::compute(&steps, 2, &leaf_ids);
        assert!((metrics.dag_compression_ratio - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_complexity_amplification_ratio() {
        let leaf_ids: HashSet<u64> = [1, 2].into_iter().collect();
        let steps = [
            make_step(3, 1, 1, 2),
            make_step(4, 2, 1, 3),
            make_step(5, 3, 3, 4),
            make_step(6, 4, 4, 2),
        ];
        let metrics = ComplexityMetrics::compute(&steps, 2, &leaf_ids);
        assert!((metrics.amplification_ratio - 2.0).abs() < f64::EPSILON);
    }

    // -- QualityScore tests --

    #[test]
    fn test_quality_score_band_excellent() {
        let qs = QualityScore {
            score: 95,
            confidence: 1.0,
            components: vec![],
        };
        assert_eq!(qs.band(), "excellent");
    }

    #[test]
    fn test_quality_score_band_good() {
        let qs = QualityScore {
            score: 75,
            confidence: 0.9,
            components: vec![],
        };
        assert_eq!(qs.band(), "good");
    }

    #[test]
    fn test_quality_score_band_critical() {
        let qs = QualityScore {
            score: 10,
            confidence: 0.5,
            components: vec![],
        };
        assert_eq!(qs.band(), "critical");
    }

    // -- StatisticsComputer integration tests --

    #[test]
    fn test_compute_trivial_proof() {
        let clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let steps = [make_step(3, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &[]);
        assert_eq!(stats.clause_stats.total_clauses, 2);
        assert_eq!(stats.resolution_stats.total_steps, 1);
        assert_eq!(stats.theory_stats.total_lemmas, 0);
        assert_eq!(stats.complexity.proof_size, 3);
    }

    #[test]
    fn test_compute_with_theory_lemmas() {
        let clauses = [make_clause(1, &[1, 2])];
        let lemmas = [make_lemma(2, Theory::Euf, &[-1], true)];
        let steps = [make_step(3, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &lemmas);
        assert_eq!(stats.clause_stats.total_clauses, 2); // 1 input + 1 theory
        assert_eq!(stats.theory_stats.total_lemmas, 1);
        assert_eq!(stats.theory_stats.verified_count, 1);
    }

    #[test]
    fn test_compute_empty_proof() {
        let stats = StatisticsComputer::compute(&[], &[], &[]);
        assert_eq!(stats.complexity.proof_size, 0);
        assert_eq!(stats.clause_stats.total_clauses, 0);
    }

    // -- ProofStatistics quality and health --

    #[test]
    fn test_quality_score_all_verified_shallow() {
        let clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let lemmas = [make_lemma(3, Theory::Euf, &[2], true)];
        let steps = [make_step(4, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &lemmas);
        let qs = stats.quality_score();
        // All verified + shallow depth => high quality
        assert!(qs.score >= 70);
    }

    #[test]
    fn test_health_report_high_trust() {
        let clauses = [make_clause(1, &[1])];
        let lemmas = [
            make_lemma(2, Theory::Bv, &[-1], false),
            make_lemma(3, Theory::Array, &[2], false),
            make_lemma(4, Theory::Nia, &[-2], false),
        ];
        let steps = [make_step(5, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &lemmas);
        let report = stats.health_report();
        let trust_warnings: Vec<_> = report
            .warnings
            .iter()
            .filter(|w| w.kind == WarningKind::TooManyTrustSteps)
            .collect();
        assert!(!trust_warnings.is_empty());
    }

    #[test]
    fn test_health_report_all_trusted_emits_error() {
        let clauses = [make_clause(1, &[1])];
        let lemmas = [make_lemma(2, Theory::Bv, &[-1], false)];
        let steps = [make_step(3, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &lemmas);
        let report = stats.health_report();
        let all_trusted: Vec<_> = report
            .warnings
            .iter()
            .filter(|w| w.kind == WarningKind::AllTrusted)
            .collect();
        assert!(!all_trusted.is_empty());
        assert_eq!(all_trusted[0].severity, Severity::Error);
    }

    #[test]
    fn test_health_report_no_warnings_clean_proof() {
        let clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let steps = [make_step(3, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &[]);
        let report = stats.health_report();
        // Simple proof with no theory should have no warnings.
        assert!(report.warnings.is_empty());
    }

    #[test]
    fn test_summary_text_contains_sections() {
        let clauses = [make_clause(1, &[1, 2]), make_clause(2, &[-1])];
        let steps = [make_step(3, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &[]);
        let text = stats.summary_text();
        assert!(text.contains("Proof Statistics Summary"));
        assert!(text.contains("Clauses"));
        assert!(text.contains("Resolution"));
        assert!(text.contains("Complexity"));
    }

    // -- ProofComparison tests --

    #[test]
    fn test_comparison_improved() {
        let clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let old = StatisticsComputer::compute(
            &clauses,
            &[make_step(3, 1, 1, 2), make_step(4, 1, 1, 2)],
            &[make_lemma(5, Theory::Bv, &[3], false)],
        );
        let new = StatisticsComputer::compute(&clauses, &[make_step(3, 1, 1, 2)], &[]);
        let cmp = ProofComparison::compare(&old, &new);
        assert!(cmp.size_delta < 0); // smaller proof
        assert!(cmp.improved);
        assert!(cmp.summary.contains("improved"));
    }

    #[test]
    fn test_comparison_regressed() {
        let clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let old = StatisticsComputer::compute(&clauses, &[make_step(3, 1, 1, 2)], &[]);
        let new = StatisticsComputer::compute(
            &clauses,
            &[make_step(3, 1, 1, 2), make_step(4, 1, 1, 2)],
            &[make_lemma(5, Theory::Bv, &[3], false)],
        );
        let cmp = ProofComparison::compare(&old, &new);
        assert!(cmp.size_delta > 0);
    }

    // -- Severity ordering --

    #[test]
    fn test_severity_ordering() {
        assert!(Severity::Info < Severity::Warning);
        assert!(Severity::Warning < Severity::Error);
    }

    // -- Theory Display --

    #[test]
    fn test_theory_display() {
        assert_eq!(Theory::Euf.to_string(), "EUF");
        assert_eq!(Theory::Lra.to_string(), "LRA");
        assert_eq!(Theory::Bv.to_string(), "BV");
        assert_eq!(Theory::Array.to_string(), "Array");
        assert_eq!(Theory::Nia.to_string(), "NIA");
        assert_eq!(Theory::Seq.to_string(), "Seq");
        assert_eq!(Theory::Unknown.to_string(), "Unknown");
    }

    // -- TimeSeriesPoint --

    #[test]
    fn test_time_series_point_construction() {
        let pt = TimeSeriesPoint {
            index: 42,
            value: 3.25,
            label: "step_count".to_string(),
        };
        assert_eq!(pt.index, 42);
        assert!((pt.value - 3.25).abs() < f64::EPSILON);
    }

    // -- WarningKind Display --

    #[test]
    fn test_warning_kind_display() {
        assert_eq!(
            WarningKind::TooManyTrustSteps.to_string(),
            "too_many_trust_steps"
        );
        assert_eq!(WarningKind::DeepResolution.to_string(), "deep_resolution");
        assert_eq!(WarningKind::LargeProof.to_string(), "large_proof");
    }

    // -- Confidence scaling --

    #[test]
    fn test_quality_confidence_scales_with_size() {
        let small = StatisticsComputer::compute(&[make_clause(1, &[1])], &[], &[]);
        let large_clauses: Vec<InputClause> =
            (1..=50).map(|i| make_clause(i, &[i as i64])).collect();
        let large_steps: Vec<InputResolutionStep> =
            (51..=100).map(|i| make_step(i, 1, 1, 2)).collect();
        let large = StatisticsComputer::compute(&large_clauses, &large_steps, &[]);

        assert!(small.quality_score().confidence < large.quality_score().confidence);
    }

    // ---------------------------------------------------------------
    // Additional coverage tests
    // ---------------------------------------------------------------

    /// Mixed theory lemmas: 4 theories, varied verification states.
    /// Verifies per-theory counts and per-theory trust ratios are correct.
    #[test]
    fn test_theory_stats_mixed_theories_per_theory_trust_ratios() {
        let lemmas = [
            // EUF: 2 verified, 1 trusted  -> trust ratio 1/3
            make_lemma(1, Theory::Euf, &[1, -2], true),
            make_lemma(2, Theory::Euf, &[3], true),
            make_lemma(3, Theory::Euf, &[-4, 5], false),
            // BV: 0 verified, 2 trusted   -> trust ratio 1.0
            make_lemma(4, Theory::Bv, &[6], false),
            make_lemma(5, Theory::Bv, &[-7, 8], false),
            // LRA: 1 verified, 0 trusted  -> trust ratio 0.0
            make_lemma(6, Theory::Lra, &[9, -10, 11], true),
            // Array: 1 verified, 1 trusted -> trust ratio 0.5
            make_lemma(7, Theory::Array, &[-12], true),
            make_lemma(8, Theory::Array, &[13, 14], false),
        ];
        let stats = TheoryUsageStats::compute(&lemmas);

        assert_eq!(stats.total_lemmas, 8);
        assert_eq!(stats.verified_count, 4);
        assert_eq!(stats.trusted_count, 4);
        assert!((stats.trust_ratio - 0.5).abs() < f64::EPSILON);

        // Per-theory counts
        assert_eq!(stats.per_theory.get("EUF"), Some(&3));
        assert_eq!(stats.per_theory.get("BV"), Some(&2));
        assert_eq!(stats.per_theory.get("LRA"), Some(&1));
        assert_eq!(stats.per_theory.get("Array"), Some(&2));

        // Per-theory trust ratios
        let euf_tr = stats.per_theory_trust_ratio["EUF"];
        assert!(
            (euf_tr - 1.0 / 3.0).abs() < 1e-10,
            "EUF trust ratio: {euf_tr}"
        );

        let bv_tr = stats.per_theory_trust_ratio["BV"];
        assert!(
            (bv_tr - 1.0).abs() < f64::EPSILON,
            "BV trust ratio: {bv_tr}"
        );

        let lra_tr = stats.per_theory_trust_ratio["LRA"];
        assert!(
            (lra_tr - 0.0).abs() < f64::EPSILON,
            "LRA trust ratio: {lra_tr}"
        );

        let arr_tr = stats.per_theory_trust_ratio["Array"];
        assert!(
            (arr_tr - 0.5).abs() < f64::EPSILON,
            "Array trust ratio: {arr_tr}"
        );

        // Average lemma width: (2+1+2+1+2+3+1+2)/8 = 14/8 = 1.75
        assert!((stats.avg_lemma_width - 1.75).abs() < f64::EPSILON);
    }

    /// Resolution chain with a diamond (fork+join): tests depth through
    /// the longest path and width at the widest level.
    ///
    /// Shape:
    ///   leaves: 1, 2, 3, 4
    ///   step 10: resolve(1, 2) => depth 1
    ///   step 11: resolve(3, 4) => depth 1
    ///   step 12: resolve(10, 11) => depth 2
    ///
    /// Depth = 2, width at depth 1 = 2 steps.
    #[test]
    fn test_resolution_stats_diamond_depth_and_width() {
        let input_ids: HashSet<u64> = [1, 2, 3, 4].into_iter().collect();
        let steps = [
            make_step(10, 1, 1, 2),
            make_step(11, 2, 3, 4),
            make_step(12, 3, 10, 11),
        ];
        let stats = ResolutionStats::compute(&steps, &input_ids);

        assert_eq!(stats.total_steps, 3);
        assert_eq!(stats.max_depth, 2);
        // Width: depth 1 has 2 steps (10, 11), depth 2 has 1 step (12)
        assert_eq!(stats.max_width, 2);
        assert_eq!(stats.distinct_pivots, 3); // |1|, |2|, |3|
    }

    /// Variable usage frequency: many clauses share the same variables.
    /// distinct_variables should count each variable exactly once.
    #[test]
    fn test_clause_stats_variable_frequency_heavy_overlap() {
        // 5 clauses all using variables 1, 2, 3 in different polarities
        let clauses = [
            make_clause(1, &[1, 2, 3]),
            make_clause(2, &[-1, 2, -3]),
            make_clause(3, &[1, -2, 3]),
            make_clause(4, &[-1, -2, -3]),
            make_clause(5, &[1, 2, 3]),
        ];
        let stats = ClauseStats::compute(&clauses);

        assert_eq!(stats.total_clauses, 5);
        assert_eq!(stats.total_literals, 15);
        // Only 3 distinct variables: |1|, |2|, |3|
        assert_eq!(stats.distinct_variables, 3);
        // All clauses have length 3
        assert_eq!(stats.min_length, 3);
        assert_eq!(stats.max_length, 3);
        assert!((stats.avg_length - 3.0).abs() < f64::EPSILON);
        assert!((stats.median_length - 3.0).abs() < f64::EPSILON);
        assert_eq!(stats.unit_clause_count, 0);
    }

    /// Single resolution step: verify max_width is 1, branching factor,
    /// and reuse_ratio when parents are not shared.
    #[test]
    fn test_resolution_stats_single_step_exact_values() {
        let input_ids: HashSet<u64> = [1, 2].into_iter().collect();
        let steps = [make_step(3, 7, 1, 2)];
        let stats = ResolutionStats::compute(&steps, &input_ids);

        assert_eq!(stats.total_steps, 1);
        assert_eq!(stats.max_depth, 1);
        assert_eq!(stats.max_width, 1);
        assert_eq!(stats.distinct_pivots, 1);
        // Two parents (1 and 2) each referenced once => no reuse
        assert!((stats.reuse_ratio - 0.0).abs() < f64::EPSILON);
        // avg branching = 2 children-refs / 2 unique parents = 1.0
        assert!((stats.avg_branching_factor - 1.0).abs() < f64::EPSILON);
    }

    /// Empty theory stats aggregated through StatisticsComputer: nontrivial
    /// clauses and steps, but zero theory lemmas. Verify theory_stats fields
    /// are all default zeros and clause_stats is computed only from inputs.
    #[test]
    fn test_statistics_computer_no_theory_lemmas_clause_accuracy() {
        let clauses = [
            make_clause(1, &[1, -2]),
            make_clause(2, &[-1, 3]),
            make_clause(3, &[2, -3]),
        ];
        let steps = [make_step(4, 1, 1, 2), make_step(5, 3, 4, 3)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &[]);

        // Theory stats all zeroed
        assert_eq!(stats.theory_stats.total_lemmas, 0);
        assert_eq!(stats.theory_stats.verified_count, 0);
        assert_eq!(stats.theory_stats.trusted_count, 0);
        assert!((stats.theory_stats.trust_ratio).abs() < f64::EPSILON);
        assert!(stats.theory_stats.per_theory.is_empty());

        // Clause stats from the 3 input clauses only
        assert_eq!(stats.clause_stats.total_clauses, 3);
        assert_eq!(stats.clause_stats.total_literals, 6);
        assert_eq!(stats.clause_stats.distinct_variables, 3);

        // Complexity: proof_size = 3 inputs + 2 steps = 5
        assert_eq!(stats.complexity.proof_size, 5);
        // Amplification: 2 steps / 3 inputs
        assert!((stats.complexity.amplification_ratio - 2.0 / 3.0).abs() < 1e-10);
    }

    /// Quality score component values for a fully-verified shallow proof.
    /// Checks that each named component exists and has the expected value.
    #[test]
    fn test_quality_score_component_breakdown_values() {
        // Craft a simple, fully verified, shallow proof:
        //   2 input clauses, 1 verified EUF lemma, 1 resolution step
        let clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let lemmas = [make_lemma(3, Theory::Euf, &[2], true)];
        let steps = [make_step(4, 1, 1, 2)];
        let stats = StatisticsComputer::compute(&clauses, &steps, &lemmas);
        let qs = stats.quality_score();

        // Verify all 5 components are present
        let names: Vec<&str> = qs.components.iter().map(|(n, _)| n.as_str()).collect();
        assert!(names.contains(&"trust"), "missing trust component");
        assert!(names.contains(&"depth"), "missing depth component");
        assert!(
            names.contains(&"compression"),
            "missing compression component"
        );
        assert!(
            names.contains(&"amplification"),
            "missing amplification component"
        );
        assert!(names.contains(&"reuse"), "missing reuse component");

        // trust: all verified => trust_ratio = 0.0 => score = (1.0 - 0.0)*100 = 100
        let trust_val = qs.components.iter().find(|(n, _)| n == "trust").unwrap().1;
        assert_eq!(trust_val, 100);

        // depth: max_depth = 1 (<=10) => score = 90
        let depth_val = qs.components.iter().find(|(n, _)| n == "depth").unwrap().1;
        assert_eq!(depth_val, 90);

        // amplification: ratio = 1 step / 3 inputs = 0.33 (<=2.0) => score = 95
        let amp_val = qs
            .components
            .iter()
            .find(|(n, _)| n == "amplification")
            .unwrap()
            .1;
        assert_eq!(amp_val, 95);

        // Confidence: proof_size = 3 inputs + 1 step = 4 => <5 => 0.3
        assert!((qs.confidence - 0.3).abs() < f64::EPSILON);
    }

    /// Health report emits DeepResolution warning when depth > 200.
    #[test]
    fn test_health_report_deep_resolution_warning() {
        // Build a linear chain of 201 resolution steps.
        let mut input_ids: HashSet<u64> = HashSet::new();
        input_ids.insert(0);
        input_ids.insert(1);
        let mut steps = Vec::new();
        // Each step i resolves (i-1) and leaf clause 1.
        // Depths: step 2 = 1, step 3 = 2, ... step 202 = 201
        for i in 2..=202u64 {
            steps.push(make_step(i, 1, i - 1, 1));
            // To keep things simple, add each intermediate as an input so
            // depth propagation stays sequential.
        }
        // Only 0 and 1 are true leaves. Depth propagation through the BFS
        // will chain up to depth 201.
        let stats = ResolutionStats::compute(&steps, &input_ids);
        assert!(
            stats.max_depth > 200,
            "expected depth > 200, got {}",
            stats.max_depth
        );

        // Now build full ProofStatistics to exercise health_report.
        let clauses = [make_clause(0, &[1]), make_clause(1, &[-1])];
        let full_stats = StatisticsComputer::compute(&clauses, &steps, &[]);
        let report = full_stats.health_report();

        let deep_warnings: Vec<_> = report
            .warnings
            .iter()
            .filter(|w| w.kind == WarningKind::DeepResolution)
            .collect();
        assert!(!deep_warnings.is_empty(), "expected DeepResolution warning");
        assert_eq!(deep_warnings[0].severity, Severity::Warning);
        assert!(
            report
                .recommendations
                .iter()
                .any(|r| r.contains("compaction")),
            "expected compaction recommendation"
        );
    }

    /// ProofComparison tie-breaker: equal quality but smaller size counts
    /// as improved.
    #[test]
    fn test_comparison_equal_quality_smaller_size_is_improved() {
        // "old" has an extra input clause that inflates proof_size but does
        // not participate in resolution, so all quality-relevant metrics
        // (depth, compression, trust, amplification, reuse) remain identical.
        let base_clauses = [make_clause(1, &[1]), make_clause(2, &[-1])];
        let steps = [make_step(3, 1, 1, 2)];
        let new = StatisticsComputer::compute(&base_clauses, &steps, &[]);

        let old_clauses = [
            make_clause(1, &[1]),
            make_clause(2, &[-1]),
            make_clause(10, &[99, -99]), // extra unused clause
        ];
        let old = StatisticsComputer::compute(&old_clauses, &steps, &[]);

        let old_q = old.quality_score().score;
        let new_q = new.quality_score().score;
        // Pre-condition: quality scores are equal
        assert_eq!(
            old_q, new_q,
            "expected equal quality scores for tie-break test"
        );
        // Old has larger proof_size (3 inputs + 1 step = 4) vs new (2 + 1 = 3)
        assert!(old.complexity.proof_size > new.complexity.proof_size);

        let cmp = ProofComparison::compare(&old, &new);
        assert!(cmp.size_delta < 0, "new should be smaller");
        assert_eq!(cmp.quality_delta, 0, "quality should be equal");
        assert!(
            cmp.improved,
            "equal quality + smaller size should count as improved"
        );
    }
}
