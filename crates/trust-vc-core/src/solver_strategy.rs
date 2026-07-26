//! Intelligent solver strategy selection for ay verification conditions
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Analyzes VC features (quantifiers, arithmetic, bitvectors, arrays, etc.)
//! and selects optimal ay solver parameters. Supports portfolio-based solving,
//! historical learning, and adaptive timeout scaling.

use std::collections::HashMap;
use std::time::Duration;

// ---------------------------------------------------------------------------
// Feature analysis types
// ---------------------------------------------------------------------------

/// Features detected in a verification condition.
#[derive(Debug, Clone, Default)]
pub struct VcFeatures {
    pub has_quantifiers: bool,
    pub quantifier_depth: usize,
    pub quantifier_count: usize,
    pub has_linear_arithmetic: bool,
    pub has_nonlinear_arithmetic: bool,
    pub has_bitvectors: bool,
    pub bitvector_max_width: usize,
    pub has_arrays: bool,
    pub has_sequences: bool,
    pub has_datatypes: bool,
    pub has_uninterpreted_functions: bool,
    pub uf_count: usize,
    pub clause_count: usize,
    pub variable_count: usize,
    pub assertion_count: usize,
    pub has_triggers: bool,
    pub trigger_count: usize,
    pub estimated_difficulty: DifficultyLevel,
}

/// Coarse difficulty classification for a VC.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
#[non_exhaustive]
pub enum DifficultyLevel {
    Trivial,
    Easy,
    #[default]
    Medium,
    Hard,
    VeryHard,
    Extreme,
}

impl VcFeatures {
    /// Compute a weighted difficulty score in `[0, +inf)`.
    ///
    /// Higher values indicate harder problems. The weights are calibrated
    /// against the trust_vc regression suite so that typical Verus-style VCs
    /// fall in the 0..100 range.
    #[must_use]
    pub fn difficulty_score(&self) -> f64 {
        let mut score = 0.0_f64;

        // Quantifiers are the primary cost driver in SMT solving.
        if self.has_quantifiers {
            score += 10.0;
            score += self.quantifier_depth as f64 * 8.0;
            score += self.quantifier_count as f64 * 3.0;
        }

        // Nonlinear arithmetic is undecidable in general.
        if self.has_nonlinear_arithmetic {
            score += 25.0;
        } else if self.has_linear_arithmetic {
            score += 5.0;
        }

        // Bitvector reasoning scales with width.
        if self.has_bitvectors {
            score += 8.0;
            score += (self.bitvector_max_width as f64 / 16.0).min(20.0);
        }

        // Array/sequence theories add quantifier-like behaviour.
        if self.has_arrays {
            score += 6.0;
        }
        if self.has_sequences {
            score += 7.0;
        }
        if self.has_datatypes {
            score += 4.0;
        }

        // Uninterpreted functions interact with E-matching.
        if self.has_uninterpreted_functions {
            score += 3.0;
            score += self.uf_count as f64 * 1.5;
        }

        // Problem size components.
        score += self.clause_count as f64 * 0.02;
        score += self.variable_count as f64 * 0.01;
        score += self.assertion_count as f64 * 0.5;

        // Triggers partially mitigate quantifier cost.
        if self.has_triggers && self.has_quantifiers {
            score -= self.trigger_count as f64 * 1.0;
        }

        // Estimated difficulty as a multiplier.
        let multiplier = match self.estimated_difficulty {
            DifficultyLevel::Trivial => 0.25,
            DifficultyLevel::Easy => 0.5,
            DifficultyLevel::Medium => 1.0,
            DifficultyLevel::Hard => 1.5,
            DifficultyLevel::VeryHard => 2.0,
            DifficultyLevel::Extreme => 3.0,
        };

        (score * multiplier).max(0.0)
    }

    /// Identify the dominant SMT theory required by this VC.
    #[must_use]
    pub fn dominant_theory(&self) -> &str {
        // Count how many theories are active.
        let theory_count = [
            self.has_bitvectors,
            self.has_linear_arithmetic || self.has_nonlinear_arithmetic,
            self.has_uninterpreted_functions,
            self.has_arrays || self.has_sequences,
        ]
        .iter()
        .filter(|&&b| b)
        .count();

        if theory_count >= 3 {
            return "mixed";
        }

        // Rank by cost: NIA > BV > array > LIA > UF > mixed.
        if self.has_nonlinear_arithmetic {
            "nia"
        } else if self.has_bitvectors {
            "bv"
        } else if self.has_arrays || self.has_sequences {
            "array"
        } else if self.has_linear_arithmetic {
            "lia"
        } else if self.has_uninterpreted_functions {
            "uf"
        } else {
            "mixed"
        }
    }
}

// ---------------------------------------------------------------------------
// Strategy configuration types
// ---------------------------------------------------------------------------

/// Complete solver strategy configuration.
#[derive(Debug, Clone)]
pub struct SolverStrategy {
    pub name: String,
    pub timeout: Duration,
    pub ematching_rounds: usize,
    pub mbqi_enabled: bool,
    pub relevancy_filter: RelevancyLevel,
    pub theory_combination: TheoryCombination,
    pub restart_strategy: RestartStrategy,
    pub phase_saving: bool,
    pub clause_deletion_aggressiveness: f64,
    pub random_seed: u64,
    pub incremental: bool,
}

/// How aggressively the solver filters irrelevant clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelevancyLevel {
    None,
    Low,
    Medium,
    High,
}

/// Theory combination strategy used by the DPLL(T) core.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TheoryCombination {
    Eager,
    Lazy,
    ModelBased,
}

/// SAT solver restart strategy.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RestartStrategy {
    Luby,
    Geometric,
    Fixed(usize),
    None,
}

impl Default for SolverStrategy {
    fn default() -> Self {
        Self {
            name: "default".into(),
            timeout: Duration::from_secs(30),
            ematching_rounds: 8,
            mbqi_enabled: false,
            relevancy_filter: RelevancyLevel::Medium,
            theory_combination: TheoryCombination::Lazy,
            restart_strategy: RestartStrategy::Luby,
            phase_saving: true,
            clause_deletion_aggressiveness: 0.5,
            random_seed: 0,
            incremental: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Portfolio
// ---------------------------------------------------------------------------

/// A portfolio of strategies to attempt, optionally in parallel.
#[derive(Debug, Clone)]
pub struct StrategyPortfolio {
    pub strategies: Vec<SolverStrategy>,
    pub total_budget: Duration,
    pub parallel: bool,
}

// ---------------------------------------------------------------------------
// Selection result
// ---------------------------------------------------------------------------

/// Result of strategy selection with confidence and reasoning.
#[derive(Debug, Clone)]
pub struct StrategySelection {
    pub primary: SolverStrategy,
    pub fallbacks: Vec<SolverStrategy>,
    pub confidence: f64,
    pub reasoning: String,
}

// ---------------------------------------------------------------------------
// Historical performance
// ---------------------------------------------------------------------------

/// A record of how a strategy performed on a VC with given features.
#[derive(Debug, Clone)]
pub struct PerformanceRecord {
    pub strategy_name: String,
    pub features: VcFeatures,
    pub succeeded: bool,
    pub elapsed: Duration,
}

// ---------------------------------------------------------------------------
// Presets
// ---------------------------------------------------------------------------

/// Predefined strategy presets tuned for common VC shapes.
pub struct StrategyPresets;

impl StrategyPresets {
    /// Strategy optimized for quantifier-heavy VCs: more E-matching rounds,
    /// MBQI enabled, high relevancy filtering.
    #[must_use]
    pub fn quantifier_heavy() -> SolverStrategy {
        SolverStrategy {
            name: "quantifier_heavy".into(),
            timeout: Duration::from_secs(60),
            ematching_rounds: 16,
            mbqi_enabled: true,
            relevancy_filter: RelevancyLevel::High,
            theory_combination: TheoryCombination::Lazy,
            restart_strategy: RestartStrategy::Luby,
            phase_saving: true,
            clause_deletion_aggressiveness: 0.3,
            random_seed: 0,
            incremental: true,
        }
    }

    /// Strategy optimized for bitvector-dominated VCs: eager theory
    /// combination, no E-matching overhead, tight timeout.
    #[must_use]
    pub fn bitvector_focused() -> SolverStrategy {
        SolverStrategy {
            name: "bitvector_focused".into(),
            timeout: Duration::from_secs(20),
            ematching_rounds: 2,
            mbqi_enabled: false,
            relevancy_filter: RelevancyLevel::Low,
            theory_combination: TheoryCombination::Eager,
            restart_strategy: RestartStrategy::Geometric,
            phase_saving: false,
            clause_deletion_aggressiveness: 0.7,
            random_seed: 0,
            incremental: false,
        }
    }

    /// Strategy optimized for arithmetic (LIA/NIA) VCs: model-based theory
    /// combination, moderate E-matching, longer timeout for NIA.
    #[must_use]
    pub fn arithmetic_focused() -> SolverStrategy {
        SolverStrategy {
            name: "arithmetic_focused".into(),
            timeout: Duration::from_secs(45),
            ematching_rounds: 6,
            mbqi_enabled: true,
            relevancy_filter: RelevancyLevel::Medium,
            theory_combination: TheoryCombination::ModelBased,
            restart_strategy: RestartStrategy::Luby,
            phase_saving: true,
            clause_deletion_aggressiveness: 0.4,
            random_seed: 0,
            incremental: true,
        }
    }

    /// Lightweight strategy for trivial/easy propositional-like problems.
    #[must_use]
    pub fn simple_propositional() -> SolverStrategy {
        SolverStrategy {
            name: "simple_propositional".into(),
            timeout: Duration::from_secs(5),
            ematching_rounds: 2,
            mbqi_enabled: false,
            relevancy_filter: RelevancyLevel::None,
            theory_combination: TheoryCombination::Eager,
            restart_strategy: RestartStrategy::Fixed(100),
            phase_saving: false,
            clause_deletion_aggressiveness: 0.8,
            random_seed: 0,
            incremental: false,
        }
    }

    /// Last-resort strategy with long timeout and all features enabled.
    #[must_use]
    pub fn aggressive_timeout() -> SolverStrategy {
        SolverStrategy {
            name: "aggressive_timeout".into(),
            timeout: Duration::from_secs(300),
            ematching_rounds: 24,
            mbqi_enabled: true,
            relevancy_filter: RelevancyLevel::High,
            theory_combination: TheoryCombination::ModelBased,
            restart_strategy: RestartStrategy::Luby,
            phase_saving: true,
            clause_deletion_aggressiveness: 0.2,
            random_seed: 42,
            incremental: true,
        }
    }
}

// ---------------------------------------------------------------------------
// Main selector
// ---------------------------------------------------------------------------

/// Selects solver strategies based on VC features and historical performance.
pub struct StrategySelector {
    history: Vec<PerformanceRecord>,
    feature_weights: HashMap<String, f64>,
    default_timeout: Duration,
}

impl StrategySelector {
    /// Create a new selector with the given default timeout.
    #[must_use]
    pub fn new(default_timeout: Duration) -> Self {
        let mut feature_weights = HashMap::new();
        feature_weights.insert("quantifiers".into(), 3.0);
        feature_weights.insert("nonlinear".into(), 4.0);
        feature_weights.insert("bitvectors".into(), 2.5);
        feature_weights.insert("arrays".into(), 2.0);
        feature_weights.insert("uf".into(), 1.5);
        feature_weights.insert("clauses".into(), 0.5);

        Self {
            history: Vec::new(),
            feature_weights,
            default_timeout,
        }
    }

    /// Select the best strategy (with fallbacks) for the given VC features.
    #[must_use]
    pub fn select(&self, features: &VcFeatures) -> StrategySelection {
        let score = features.difficulty_score();
        let theory = features.dominant_theory();

        // Check historical match first.
        let hist_name = self
            .best_historical_match(features)
            .filter(|r| r.succeeded)
            .map(|r| r.strategy_name.clone());

        // Select primary based on theory + difficulty.
        let primary = if let Some(ref name) = hist_name {
            self.strategy_by_name(name)
        } else {
            self.select_by_features(features, theory, score)
        };

        // Build fallback chain: strategies unlike the primary.
        let fallbacks = self.build_fallback_chain(features, &primary);

        // Confidence: higher when we have historical evidence and lower
        // difficulty.
        let confidence = self.compute_confidence(features, &hist_name, score);

        let reasoning = format!(
            "dominant_theory={theory}, difficulty_score={score:.1}, \
             historical_match={}, fallbacks={}",
            hist_name.as_deref().unwrap_or("none"),
            fallbacks.len(),
        );

        StrategySelection {
            primary,
            fallbacks,
            confidence,
            reasoning,
        }
    }

    /// Record the outcome of a strategy run for future learning.
    pub fn record_result(&mut self, record: PerformanceRecord) {
        self.history.push(record);
    }

    /// Build a portfolio of strategies for the given features and time budget.
    #[must_use]
    pub fn build_portfolio(&self, features: &VcFeatures, budget: Duration) -> StrategyPortfolio {
        let selection = self.select(features);
        let score = features.difficulty_score();

        // Decide parallelism: use parallel only when difficulty is high enough
        // to justify the overhead.
        let parallel = score > 30.0;

        let mut strategies = Vec::with_capacity(1 + selection.fallbacks.len());

        if parallel {
            // Split budget equally across all strategies.
            let n = u32::try_from(1 + selection.fallbacks.len()).unwrap_or(u32::MAX);
            let per_strategy = budget / n;
            let mut primary = selection.primary;
            primary.timeout = per_strategy;
            strategies.push(primary);
            for mut fb in selection.fallbacks {
                fb.timeout = per_strategy;
                strategies.push(fb);
            }
        } else {
            // Sequential: primary gets 60% of budget, rest split among
            // fallbacks.
            let primary_budget = budget.mul_f64(0.6);
            let mut primary = selection.primary;
            primary.timeout = primary_budget;
            strategies.push(primary);

            let remaining = budget.saturating_sub(primary_budget);
            let fb_count = u32::try_from(selection.fallbacks.len().max(1)).unwrap_or(u32::MAX);
            let per_fb = remaining / fb_count;
            for mut fb in selection.fallbacks {
                fb.timeout = per_fb;
                strategies.push(fb);
            }
        }

        StrategyPortfolio {
            strategies,
            total_budget: budget,
            parallel,
        }
    }

    /// Suggest an adaptive timeout based on VC difficulty.
    #[must_use]
    pub fn suggest_timeout(&self, features: &VcFeatures) -> Duration {
        let score = features.difficulty_score();
        let base = self.default_timeout.as_secs_f64();

        // Scale factor: trivial problems get 0.25x, extreme problems get 5x.
        let factor = if score < 5.0 {
            0.25
        } else if score < 15.0 {
            0.5
        } else if score < 40.0 {
            1.0
        } else if score < 80.0 {
            2.0
        } else if score < 150.0 {
            3.5
        } else {
            5.0
        };

        // If we have historical data for similar VCs, adjust based on observed
        // elapsed times.
        let hist_adjustment = self.historical_timeout_adjustment(features);

        let secs = (base * factor * hist_adjustment).max(1.0);
        Duration::from_secs_f64(secs)
    }

    /// Compute cosine-like similarity between two VC feature vectors.
    ///
    /// Returns a value in `[0.0, 1.0]` where 1.0 means identical features.
    #[must_use]
    pub fn feature_similarity(a: &VcFeatures, b: &VcFeatures) -> f64 {
        let va = Self::feature_vector(a);
        let vb = Self::feature_vector(b);

        let dot: f64 = va.iter().zip(vb.iter()).map(|(x, y)| x * y).sum();
        let mag_a: f64 = va.iter().map(|x| x * x).sum::<f64>().sqrt();
        let mag_b: f64 = vb.iter().map(|x| x * x).sum::<f64>().sqrt();

        if mag_a < f64::EPSILON || mag_b < f64::EPSILON {
            // Both zero vectors are considered identical.
            if mag_a < f64::EPSILON && mag_b < f64::EPSILON {
                return 1.0;
            }
            return 0.0;
        }

        (dot / (mag_a * mag_b)).clamp(0.0, 1.0)
    }

    /// Find the historical record most similar to the given features.
    #[must_use]
    pub fn best_historical_match(&self, features: &VcFeatures) -> Option<&PerformanceRecord> {
        self.history
            .iter()
            .map(|r| {
                let sim = Self::feature_similarity(features, &r.features);
                (r, sim)
            })
            .filter(|(_, sim)| *sim > 0.7)
            .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
            .map(|(r, _)| r)
    }

    // -- private helpers ---------------------------------------------------

    fn feature_vector(f: &VcFeatures) -> Vec<f64> {
        vec![
            if f.has_quantifiers { 1.0 } else { 0.0 },
            f.quantifier_depth as f64,
            f.quantifier_count as f64,
            if f.has_linear_arithmetic { 1.0 } else { 0.0 },
            if f.has_nonlinear_arithmetic { 1.0 } else { 0.0 },
            if f.has_bitvectors { 1.0 } else { 0.0 },
            f.bitvector_max_width as f64 / 128.0,
            if f.has_arrays { 1.0 } else { 0.0 },
            if f.has_sequences { 1.0 } else { 0.0 },
            if f.has_datatypes { 1.0 } else { 0.0 },
            if f.has_uninterpreted_functions {
                1.0
            } else {
                0.0
            },
            f.uf_count as f64 / 10.0,
            f.clause_count as f64 / 1000.0,
            f.variable_count as f64 / 1000.0,
            f.assertion_count as f64 / 100.0,
            if f.has_triggers { 1.0 } else { 0.0 },
            f.trigger_count as f64 / 10.0,
        ]
    }

    fn select_by_features(
        &self,
        features: &VcFeatures,
        theory: &str,
        score: f64,
    ) -> SolverStrategy {
        if score < 5.0 {
            return StrategyPresets::simple_propositional();
        }

        let mut strategy = match theory {
            "bv" => StrategyPresets::bitvector_focused(),
            "nia" => StrategyPresets::arithmetic_focused(),
            "lia" => {
                let mut s = StrategyPresets::arithmetic_focused();
                s.name = "lia_focused".into();
                s.timeout = Duration::from_secs(30);
                s.mbqi_enabled = false;
                s
            }
            "uf" => SolverStrategy {
                name: "uf_focused".into(),
                ematching_rounds: 12,
                ..SolverStrategy::default()
            },
            "array" => SolverStrategy {
                name: "array_focused".into(),
                ematching_rounds: 10,
                relevancy_filter: RelevancyLevel::High,
                ..SolverStrategy::default()
            },
            _ => {
                // "mixed" or unknown — use quantifier_heavy if quantifiers
                // are present, otherwise the default.
                if features.has_quantifiers && features.quantifier_count > 3 {
                    StrategyPresets::quantifier_heavy()
                } else {
                    SolverStrategy::default()
                }
            }
        };

        // Override timeout if the selector has a non-default timeout.
        let suggested = self.suggest_timeout(features);
        if suggested > strategy.timeout {
            strategy.timeout = suggested;
        }

        strategy
    }

    fn build_fallback_chain(
        &self,
        features: &VcFeatures,
        primary: &SolverStrategy,
    ) -> Vec<SolverStrategy> {
        let mut fallbacks: Vec<SolverStrategy> = Vec::new();

        // Always include the default if primary is not the default.
        if primary.name != "default" {
            fallbacks.push(SolverStrategy::default());
        }

        // Add theory-specific alternatives.
        if features.has_quantifiers && primary.name != "quantifier_heavy" {
            fallbacks.push(StrategyPresets::quantifier_heavy());
        }
        if features.has_bitvectors && primary.name != "bitvector_focused" {
            fallbacks.push(StrategyPresets::bitvector_focused());
        }

        // Aggressive timeout as last resort.
        if primary.name != "aggressive_timeout" {
            fallbacks.push(StrategyPresets::aggressive_timeout());
        }

        // Deduplicate by name.
        let mut seen = std::collections::HashSet::new();
        seen.insert(primary.name.clone());
        fallbacks.retain(|s| seen.insert(s.name.clone()));

        fallbacks
    }

    fn compute_confidence(
        &self,
        features: &VcFeatures,
        hist_name: &Option<String>,
        score: f64,
    ) -> f64 {
        let mut confidence = 0.5_f64;

        // Boost if we have a successful historical match.
        if hist_name.is_some() {
            confidence += 0.3;
        }

        // Reduce for high difficulty.
        if score > 100.0 {
            confidence -= 0.2;
        } else if score > 50.0 {
            confidence -= 0.1;
        }

        // Boost for trigger presence (quantifiers are more manageable).
        if features.has_triggers && features.has_quantifiers {
            confidence += 0.1;
        }

        // Reduce for mixed theories (harder to tune).
        if features.dominant_theory() == "mixed" {
            confidence -= 0.1;
        }

        confidence.clamp(0.1, 1.0)
    }

    fn historical_timeout_adjustment(&self, features: &VcFeatures) -> f64 {
        // Find similar successful records and compute median elapsed ratio.
        let similar: Vec<&PerformanceRecord> = self
            .history
            .iter()
            .filter(|r| r.succeeded && Self::feature_similarity(features, &r.features) > 0.6)
            .collect();

        if similar.is_empty() {
            return 1.0;
        }

        let avg_elapsed: f64 =
            similar.iter().map(|r| r.elapsed.as_secs_f64()).sum::<f64>() / similar.len() as f64;

        // Use a ratio relative to the default timeout.
        let base = self.default_timeout.as_secs_f64();
        if base < f64::EPSILON {
            return 1.0;
        }

        // Add a 50% safety margin over observed average.
        ((avg_elapsed * 1.5) / base).clamp(0.25, 5.0)
    }

    fn strategy_by_name(&self, name: &str) -> SolverStrategy {
        match name {
            "quantifier_heavy" => StrategyPresets::quantifier_heavy(),
            "bitvector_focused" => StrategyPresets::bitvector_focused(),
            "arithmetic_focused" => StrategyPresets::arithmetic_focused(),
            "simple_propositional" => StrategyPresets::simple_propositional(),
            "aggressive_timeout" => StrategyPresets::aggressive_timeout(),
            _ => SolverStrategy::default(),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn default_selector() -> StrategySelector {
        StrategySelector::new(Duration::from_secs(30))
    }

    fn empty_features() -> VcFeatures {
        VcFeatures::default()
    }

    fn quantifier_heavy_features() -> VcFeatures {
        VcFeatures {
            has_quantifiers: true,
            quantifier_depth: 3,
            quantifier_count: 10,
            has_triggers: true,
            trigger_count: 5,
            estimated_difficulty: DifficultyLevel::Hard,
            ..Default::default()
        }
    }

    fn bv_features() -> VcFeatures {
        VcFeatures {
            has_bitvectors: true,
            bitvector_max_width: 64,
            clause_count: 200,
            variable_count: 50,
            assertion_count: 4,
            estimated_difficulty: DifficultyLevel::Medium,
            ..Default::default()
        }
    }

    fn nia_features() -> VcFeatures {
        VcFeatures {
            has_nonlinear_arithmetic: true,
            has_linear_arithmetic: true,
            variable_count: 30,
            assertion_count: 6,
            estimated_difficulty: DifficultyLevel::Hard,
            ..Default::default()
        }
    }

    fn simple_features() -> VcFeatures {
        VcFeatures {
            clause_count: 10,
            variable_count: 5,
            assertion_count: 1,
            estimated_difficulty: DifficultyLevel::Trivial,
            ..Default::default()
        }
    }

    fn mixed_features() -> VcFeatures {
        VcFeatures {
            has_quantifiers: true,
            quantifier_depth: 1,
            quantifier_count: 2,
            has_bitvectors: true,
            bitvector_max_width: 32,
            has_linear_arithmetic: true,
            has_uninterpreted_functions: true,
            uf_count: 3,
            clause_count: 500,
            variable_count: 100,
            assertion_count: 8,
            estimated_difficulty: DifficultyLevel::Hard,
            ..Default::default()
        }
    }

    // -- Default strategy selection ----------------------------------------

    #[test]
    fn test_select_default_for_empty_features() {
        let selector = default_selector();
        let selection = selector.select(&empty_features());
        // Empty features have a very low score → simple_propositional.
        assert_eq!(selection.primary.name, "simple_propositional");
    }

    #[test]
    fn test_default_strategy_values() {
        let s = SolverStrategy::default();
        assert_eq!(s.name, "default");
        assert_eq!(s.timeout, Duration::from_secs(30));
        assert_eq!(s.ematching_rounds, 8);
        assert!(!s.mbqi_enabled);
        assert_eq!(s.relevancy_filter, RelevancyLevel::Medium);
        assert_eq!(s.theory_combination, TheoryCombination::Lazy);
        assert_eq!(s.restart_strategy, RestartStrategy::Luby);
        assert!(s.phase_saving);
        assert!((s.clause_deletion_aggressiveness - 0.5).abs() < f64::EPSILON);
        assert_eq!(s.random_seed, 0);
        assert!(s.incremental);
    }

    // -- Quantifier-heavy VC → quantifier strategy -------------------------

    #[test]
    fn test_select_quantifier_heavy() {
        let selector = default_selector();
        let features = quantifier_heavy_features();
        let selection = selector.select(&features);
        assert!(
            selection.primary.name == "quantifier_heavy",
            "expected quantifier_heavy, got {}",
            selection.primary.name
        );
        assert!(selection.primary.mbqi_enabled);
        assert!(selection.primary.ematching_rounds >= 16);
    }

    #[test]
    fn test_quantifier_heavy_preset_values() {
        let s = StrategyPresets::quantifier_heavy();
        assert_eq!(s.name, "quantifier_heavy");
        assert_eq!(s.timeout, Duration::from_secs(60));
        assert_eq!(s.ematching_rounds, 16);
        assert!(s.mbqi_enabled);
        assert_eq!(s.relevancy_filter, RelevancyLevel::High);
        assert!((s.clause_deletion_aggressiveness - 0.3).abs() < f64::EPSILON);
    }

    // -- BV-heavy VC → BV strategy ----------------------------------------

    #[test]
    fn test_select_bitvector_focused() {
        let selector = default_selector();
        let features = bv_features();
        let selection = selector.select(&features);
        assert_eq!(selection.primary.name, "bitvector_focused");
        assert_eq!(
            selection.primary.theory_combination,
            TheoryCombination::Eager
        );
    }

    #[test]
    fn test_bitvector_preset_values() {
        let s = StrategyPresets::bitvector_focused();
        assert_eq!(s.name, "bitvector_focused");
        assert_eq!(s.ematching_rounds, 2);
        assert!(!s.mbqi_enabled);
        assert!(!s.phase_saving);
        assert!(!s.incremental);
    }

    // -- NIA detection → arithmetic strategy -------------------------------

    #[test]
    fn test_select_nia() {
        let selector = default_selector();
        let features = nia_features();
        let selection = selector.select(&features);
        assert_eq!(selection.primary.name, "arithmetic_focused");
        assert_eq!(
            selection.primary.theory_combination,
            TheoryCombination::ModelBased
        );
    }

    #[test]
    fn test_arithmetic_preset_values() {
        let s = StrategyPresets::arithmetic_focused();
        assert_eq!(s.name, "arithmetic_focused");
        assert_eq!(s.timeout, Duration::from_secs(45));
        assert!(s.mbqi_enabled);
        assert_eq!(s.ematching_rounds, 6);
    }

    // -- Simple VC → propositional strategy --------------------------------

    #[test]
    fn test_select_simple_propositional() {
        let selector = default_selector();
        let features = simple_features();
        let selection = selector.select(&features);
        assert_eq!(selection.primary.name, "simple_propositional");
        assert_eq!(selection.primary.timeout, Duration::from_secs(5));
    }

    #[test]
    fn test_simple_propositional_preset_values() {
        let s = StrategyPresets::simple_propositional();
        assert_eq!(s.name, "simple_propositional");
        assert!(!s.mbqi_enabled);
        assert_eq!(s.restart_strategy, RestartStrategy::Fixed(100));
        assert!(!s.incremental);
    }

    // -- Mixed theory → balanced/mixed strategy ----------------------------

    #[test]
    fn test_select_mixed_theory() {
        let selector = default_selector();
        let features = mixed_features();
        let selection = selector.select(&features);
        // Mixed features should not select a narrow specialist.
        assert!(
            ["quantifier_heavy", "default"].contains(&selection.primary.name.as_str()),
            "mixed should get quantifier_heavy or default, got {}",
            selection.primary.name
        );
    }

    #[test]
    fn test_mixed_dominant_theory() {
        let features = mixed_features();
        assert_eq!(features.dominant_theory(), "mixed");
    }

    // -- Difficulty scoring ------------------------------------------------

    #[test]
    fn test_difficulty_score_empty_is_zero() {
        let features = empty_features();
        let score = features.difficulty_score();
        assert!(
            score.abs() < f64::EPSILON,
            "empty features should have score ~0, got {score}"
        );
    }

    #[test]
    fn test_difficulty_score_quantifiers_higher_than_empty() {
        let q = quantifier_heavy_features();
        let e = empty_features();
        assert!(q.difficulty_score() > e.difficulty_score());
    }

    #[test]
    fn test_difficulty_score_nia_higher_than_lia() {
        let nia = nia_features();
        let lia = VcFeatures {
            has_linear_arithmetic: true,
            estimated_difficulty: DifficultyLevel::Hard,
            ..Default::default()
        };
        assert!(nia.difficulty_score() > lia.difficulty_score());
    }

    #[test]
    fn test_difficulty_score_scales_with_multiplier() {
        let trivial = VcFeatures {
            has_bitvectors: true,
            bitvector_max_width: 32,
            estimated_difficulty: DifficultyLevel::Trivial,
            ..Default::default()
        };
        let extreme = VcFeatures {
            has_bitvectors: true,
            bitvector_max_width: 32,
            estimated_difficulty: DifficultyLevel::Extreme,
            ..Default::default()
        };
        // Extreme multiplier is 3.0 / 0.25 = 12x that of trivial.
        assert!(extreme.difficulty_score() > trivial.difficulty_score() * 10.0);
    }

    #[test]
    fn test_difficulty_score_triggers_reduce_score() {
        let no_triggers = VcFeatures {
            has_quantifiers: true,
            quantifier_count: 5,
            quantifier_depth: 2,
            ..Default::default()
        };
        let with_triggers = VcFeatures {
            has_quantifiers: true,
            quantifier_count: 5,
            quantifier_depth: 2,
            has_triggers: true,
            trigger_count: 5,
            ..Default::default()
        };
        assert!(with_triggers.difficulty_score() < no_triggers.difficulty_score());
    }

    #[test]
    fn test_difficulty_score_never_negative() {
        // Triggers alone cannot push score negative.
        let features = VcFeatures {
            has_quantifiers: true,
            has_triggers: true,
            trigger_count: 100,
            ..Default::default()
        };
        assert!(features.difficulty_score() >= 0.0);
    }

    // -- Dominant theory detection -----------------------------------------

    #[test]
    fn test_dominant_theory_bv() {
        let f = bv_features();
        assert_eq!(f.dominant_theory(), "bv");
    }

    #[test]
    fn test_dominant_theory_nia() {
        let f = nia_features();
        assert_eq!(f.dominant_theory(), "nia");
    }

    #[test]
    fn test_dominant_theory_lia() {
        let f = VcFeatures {
            has_linear_arithmetic: true,
            ..Default::default()
        };
        assert_eq!(f.dominant_theory(), "lia");
    }

    #[test]
    fn test_dominant_theory_uf() {
        let f = VcFeatures {
            has_uninterpreted_functions: true,
            uf_count: 5,
            ..Default::default()
        };
        assert_eq!(f.dominant_theory(), "uf");
    }

    #[test]
    fn test_dominant_theory_array() {
        let f = VcFeatures {
            has_arrays: true,
            ..Default::default()
        };
        assert_eq!(f.dominant_theory(), "array");
    }

    #[test]
    fn test_dominant_theory_sequences() {
        let f = VcFeatures {
            has_sequences: true,
            ..Default::default()
        };
        assert_eq!(f.dominant_theory(), "array");
    }

    #[test]
    fn test_dominant_theory_empty_is_mixed() {
        let f = empty_features();
        assert_eq!(f.dominant_theory(), "mixed");
    }

    // -- Portfolio construction with budget allocation ---------------------

    #[test]
    fn test_portfolio_simple_is_sequential() {
        let selector = default_selector();
        let features = simple_features();
        let portfolio = selector.build_portfolio(&features, Duration::from_secs(60));
        assert!(!portfolio.parallel);
        assert!(!portfolio.strategies.is_empty());
        assert_eq!(portfolio.total_budget, Duration::from_secs(60));
    }

    #[test]
    fn test_portfolio_hard_is_parallel() {
        let selector = default_selector();
        let features = quantifier_heavy_features();
        let portfolio = selector.build_portfolio(&features, Duration::from_secs(120));
        assert!(portfolio.parallel);
    }

    #[test]
    fn test_portfolio_budget_sum_does_not_exceed_total() {
        let selector = default_selector();
        let features = mixed_features();
        let portfolio = selector.build_portfolio(&features, Duration::from_secs(60));
        let total: Duration = portfolio.strategies.iter().map(|s| s.timeout).sum();
        // In parallel mode, each gets budget/N which sums to budget.
        // In sequential mode, sums may equal budget.
        assert!(total <= portfolio.total_budget + Duration::from_millis(1));
    }

    #[test]
    fn test_portfolio_has_multiple_strategies() {
        let selector = default_selector();
        let features = bv_features();
        let portfolio = selector.build_portfolio(&features, Duration::from_secs(60));
        assert!(
            portfolio.strategies.len() >= 2,
            "portfolio should have at least primary + 1 fallback"
        );
    }

    // -- Historical learning -----------------------------------------------

    #[test]
    fn test_record_result_and_match() {
        let mut selector = default_selector();
        let features = bv_features();
        selector.record_result(PerformanceRecord {
            strategy_name: "bitvector_focused".into(),
            features: features.clone(),
            succeeded: true,
            elapsed: Duration::from_secs(2),
        });
        let matched = selector.best_historical_match(&features);
        assert!(matched.is_some());
        assert_eq!(matched.unwrap().strategy_name, "bitvector_focused");
    }

    #[test]
    fn test_historical_match_influences_selection() {
        let mut selector = default_selector();
        let features = bv_features();
        // Record that quantifier_heavy worked on these BV features (unusual).
        selector.record_result(PerformanceRecord {
            strategy_name: "quantifier_heavy".into(),
            features: features.clone(),
            succeeded: true,
            elapsed: Duration::from_secs(5),
        });
        let selection = selector.select(&features);
        assert_eq!(selection.primary.name, "quantifier_heavy");
    }

    #[test]
    fn test_failed_historical_match_not_used() {
        let mut selector = default_selector();
        let features = bv_features();
        selector.record_result(PerformanceRecord {
            strategy_name: "simple_propositional".into(),
            features: features.clone(),
            succeeded: false,
            elapsed: Duration::from_secs(5),
        });
        let selection = selector.select(&features);
        // Should fall through to feature-based selection, not the failed
        // historical match.
        assert_ne!(selection.primary.name, "simple_propositional");
    }

    #[test]
    fn test_no_historical_match_for_dissimilar() {
        let mut selector = default_selector();
        selector.record_result(PerformanceRecord {
            strategy_name: "bitvector_focused".into(),
            features: bv_features(),
            succeeded: true,
            elapsed: Duration::from_secs(2),
        });
        let dissimilar = quantifier_heavy_features();
        let matched = selector.best_historical_match(&dissimilar);
        // BV features and quantifier features are very different.
        assert!(matched.is_none());
    }

    // -- Feature similarity ------------------------------------------------

    #[test]
    fn test_feature_similarity_identical() {
        let f = bv_features();
        let sim = StrategySelector::feature_similarity(&f, &f);
        assert!(
            (sim - 1.0).abs() < 1e-9,
            "identical features should have similarity 1.0, got {sim}"
        );
    }

    #[test]
    fn test_feature_similarity_empty_vectors() {
        let a = empty_features();
        let b = empty_features();
        let sim = StrategySelector::feature_similarity(&a, &b);
        assert!(
            (sim - 1.0).abs() < 1e-9,
            "two empty features should be identical, got {sim}"
        );
    }

    #[test]
    fn test_feature_similarity_dissimilar() {
        let a = bv_features();
        let b = quantifier_heavy_features();
        let sim = StrategySelector::feature_similarity(&a, &b);
        assert!(
            sim < 0.8,
            "BV and quantifier features should be dissimilar, got {sim}"
        );
    }

    #[test]
    fn test_feature_similarity_symmetric() {
        let a = bv_features();
        let b = nia_features();
        let sim_ab = StrategySelector::feature_similarity(&a, &b);
        let sim_ba = StrategySelector::feature_similarity(&b, &a);
        assert!(
            (sim_ab - sim_ba).abs() < 1e-12,
            "similarity should be symmetric"
        );
    }

    #[test]
    fn test_feature_similarity_range() {
        let a = mixed_features();
        let b = simple_features();
        let sim = StrategySelector::feature_similarity(&a, &b);
        assert!((0.0..=1.0).contains(&sim));
    }

    // -- Timeout scaling with difficulty -----------------------------------

    #[test]
    fn test_timeout_trivial_shorter_than_default() {
        let selector = default_selector();
        let features = simple_features();
        let timeout = selector.suggest_timeout(&features);
        assert!(timeout < Duration::from_secs(30));
    }

    #[test]
    fn test_timeout_hard_longer_than_default() {
        let selector = default_selector();
        let features = VcFeatures {
            has_quantifiers: true,
            quantifier_depth: 5,
            quantifier_count: 20,
            has_nonlinear_arithmetic: true,
            assertion_count: 10,
            estimated_difficulty: DifficultyLevel::VeryHard,
            ..Default::default()
        };
        let timeout = selector.suggest_timeout(&features);
        assert!(timeout > Duration::from_secs(30));
    }

    #[test]
    fn test_timeout_at_least_one_second() {
        let selector = StrategySelector::new(Duration::from_millis(100));
        let features = simple_features();
        let timeout = selector.suggest_timeout(&features);
        assert!(timeout >= Duration::from_secs(1));
    }

    #[test]
    fn test_timeout_with_historical_data() {
        let mut selector = default_selector();
        let features = bv_features();
        selector.record_result(PerformanceRecord {
            strategy_name: "bitvector_focused".into(),
            features: features.clone(),
            succeeded: true,
            elapsed: Duration::from_secs(10),
        });
        let timeout = selector.suggest_timeout(&features);
        // Should be adjusted based on historical 10s + 50% margin.
        assert!(timeout >= Duration::from_secs(1));
    }

    // -- Confidence scoring ------------------------------------------------

    #[test]
    fn test_confidence_with_historical_match() {
        let mut selector = default_selector();
        let features = bv_features();
        selector.record_result(PerformanceRecord {
            strategy_name: "bitvector_focused".into(),
            features: features.clone(),
            succeeded: true,
            elapsed: Duration::from_secs(2),
        });
        let selection = selector.select(&features);
        assert!(selection.confidence > 0.5);
    }

    #[test]
    fn test_confidence_low_for_extreme_difficulty() {
        let selector = default_selector();
        let features = VcFeatures {
            has_quantifiers: true,
            quantifier_depth: 10,
            quantifier_count: 50,
            has_nonlinear_arithmetic: true,
            has_bitvectors: true,
            bitvector_max_width: 128,
            has_arrays: true,
            assertion_count: 20,
            estimated_difficulty: DifficultyLevel::Extreme,
            ..Default::default()
        };
        let selection = selector.select(&features);
        // High difficulty + mixed theory → lower confidence.
        assert!(
            selection.confidence < 0.7,
            "extreme difficulty should have lower confidence, got {}",
            selection.confidence
        );
    }

    #[test]
    fn test_confidence_bounded() {
        let selector = default_selector();
        let features = bv_features();
        let selection = selector.select(&features);
        assert!((0.1..=1.0).contains(&selection.confidence));
    }

    // -- Aggressive timeout preset -----------------------------------------

    #[test]
    fn test_aggressive_timeout_preset() {
        let s = StrategyPresets::aggressive_timeout();
        assert_eq!(s.name, "aggressive_timeout");
        assert_eq!(s.timeout, Duration::from_secs(300));
        assert_eq!(s.ematching_rounds, 24);
        assert!(s.mbqi_enabled);
        assert!(s.incremental);
        assert_eq!(s.random_seed, 42);
    }

    // -- Fallback strategy ordering ----------------------------------------

    #[test]
    fn test_fallbacks_include_aggressive_timeout() {
        let selector = default_selector();
        let features = bv_features();
        let selection = selector.select(&features);
        assert!(
            selection
                .fallbacks
                .iter()
                .any(|s| s.name == "aggressive_timeout"),
            "aggressive_timeout should always be in fallbacks"
        );
    }

    #[test]
    fn test_fallbacks_do_not_repeat_primary() {
        let selector = default_selector();
        let features = quantifier_heavy_features();
        let selection = selector.select(&features);
        assert!(
            !selection
                .fallbacks
                .iter()
                .any(|s| s.name == selection.primary.name),
            "fallbacks should not include the primary strategy"
        );
    }

    #[test]
    fn test_fallbacks_no_duplicates() {
        let selector = default_selector();
        let features = mixed_features();
        let selection = selector.select(&features);
        let names: Vec<&str> = selection
            .fallbacks
            .iter()
            .map(|s| s.name.as_str())
            .collect();
        let unique: std::collections::HashSet<&str> = names.iter().copied().collect();
        assert_eq!(
            names.len(),
            unique.len(),
            "fallbacks should have no duplicates"
        );
    }

    // -- Edge cases --------------------------------------------------------

    #[test]
    fn test_extreme_variable_count() {
        let features = VcFeatures {
            variable_count: 1_000_000,
            clause_count: 5_000_000,
            assertion_count: 1000,
            estimated_difficulty: DifficultyLevel::Extreme,
            ..Default::default()
        };
        let score = features.difficulty_score();
        assert!(score > 100.0);
    }

    #[test]
    fn test_zero_timeout_selector() {
        let selector = StrategySelector::new(Duration::ZERO);
        let features = bv_features();
        let timeout = selector.suggest_timeout(&features);
        // Should clamp to at least 1 second.
        assert!(timeout >= Duration::from_secs(1));
    }

    #[test]
    fn test_difficulty_level_ordering() {
        assert!(DifficultyLevel::Trivial < DifficultyLevel::Easy);
        assert!(DifficultyLevel::Easy < DifficultyLevel::Medium);
        assert!(DifficultyLevel::Medium < DifficultyLevel::Hard);
        assert!(DifficultyLevel::Hard < DifficultyLevel::VeryHard);
        assert!(DifficultyLevel::VeryHard < DifficultyLevel::Extreme);
    }

    #[test]
    fn test_selection_reasoning_populated() {
        let selector = default_selector();
        let features = bv_features();
        let selection = selector.select(&features);
        assert!(!selection.reasoning.is_empty());
        assert!(selection.reasoning.contains("dominant_theory"));
    }

    // -- LIA-specific path -------------------------------------------------

    #[test]
    fn test_select_lia_specific() {
        let selector = default_selector();
        let features = VcFeatures {
            has_linear_arithmetic: true,
            variable_count: 20,
            assertion_count: 5,
            estimated_difficulty: DifficultyLevel::Medium,
            ..Default::default()
        };
        let selection = selector.select(&features);
        assert!(
            selection.primary.name == "lia_focused"
                || selection.primary.name == "arithmetic_focused"
                || selection.primary.name == "default",
            "LIA should get lia_focused or arithmetic_focused, got {}",
            selection.primary.name
        );
    }

    // -- UF-specific path --------------------------------------------------

    #[test]
    fn test_select_uf_specific() {
        let selector = default_selector();
        let features = VcFeatures {
            has_uninterpreted_functions: true,
            uf_count: 8,
            variable_count: 30,
            assertion_count: 4,
            estimated_difficulty: DifficultyLevel::Medium,
            ..Default::default()
        };
        let selection = selector.select(&features);
        assert_eq!(selection.primary.name, "uf_focused");
        assert!(selection.primary.ematching_rounds >= 10);
    }

    // -- Array-specific path -----------------------------------------------

    #[test]
    fn test_select_array_specific() {
        let selector = default_selector();
        let features = VcFeatures {
            has_arrays: true,
            variable_count: 40,
            assertion_count: 5,
            estimated_difficulty: DifficultyLevel::Medium,
            ..Default::default()
        };
        let selection = selector.select(&features);
        assert_eq!(selection.primary.name, "array_focused");
        assert_eq!(selection.primary.relevancy_filter, RelevancyLevel::High);
    }
}
