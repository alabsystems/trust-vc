//! Heuristics for quantifier instantiation in SMT solving.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Decides which quantified formulas to instantiate and with which terms.
//! This is critical for SMT solver performance: too many instantiations cause
//! blowup, too few cause incompleteness. The module provides E-matching,
//! conflict-driven learning, budget management, and relevancy-based scheduling.
//!
//! Self-contained: depends only on `std`, no sibling module imports.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// ---------------------------------------------------------------------------
// Identifiers and basic types
// ---------------------------------------------------------------------------

/// Unique identifier for a quantified formula.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FormulaId(pub(crate) String);

impl fmt::Display for FormulaId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// ---------------------------------------------------------------------------
// Core data types
// ---------------------------------------------------------------------------

/// A quantified formula (forall/exists) with optional trigger patterns.
#[derive(Debug, Clone)]
pub(crate) struct QuantifiedFormula {
    /// Unique identifier for this formula.
    pub(crate) id: FormulaId,
    /// Bound variable names (e.g., `["x", "y"]`).
    pub(crate) bound_vars: Vec<String>,
    /// String representation of the formula body.
    pub(crate) body: String,
    /// Trigger patterns for E-matching. Empty means no user-provided triggers.
    pub(crate) triggers: Vec<TriggerPattern>,
    /// Nesting depth of this quantifier (0 = top-level).
    pub(crate) depth: usize,
}

/// A term available for substitution into a bound variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InstantiationTerm {
    /// String representation of the term (e.g., `"f(a)"`, `"0"`, `"x + 1"`).
    pub(crate) value: String,
    /// Sort / type of the term (e.g., `"Int"`, `"Bool"`, `"BitVec(32)"`).
    pub(crate) sort: String,
}

impl fmt::Display for InstantiationTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.value, self.sort)
    }
}

/// A single trigger pattern used for E-matching.
///
/// A trigger pattern is a term containing bound variables. When a ground term
/// in the current context matches the pattern structure, the bound variables
/// are assigned the corresponding sub-terms.
///
/// Multi-trigger patterns require ALL patterns to match simultaneously.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TriggerPattern {
    /// Function symbol at the root of this pattern (e.g., `"f"`, `"select"`).
    pub(crate) function_symbol: String,
    /// Argument patterns: either a bound variable name or a nested sub-pattern.
    /// A `None` entry means "match any ground term" (wildcard).
    pub(crate) args: Vec<PatternArg>,
}

/// An argument position within a trigger pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternArg {
    /// Match a bound variable and capture its value.
    BoundVar(String),
    /// Match a specific constant value.
    Constant(String),
    /// Match anything (wildcard).
    Wildcard,
}

/// A candidate instantiation: a formula paired with a substitution and score.
#[derive(Debug, Clone)]
pub(crate) struct InstantiationCandidate {
    /// Which formula this instantiation is for.
    pub(crate) formula_id: FormulaId,
    /// Mapping from bound variable name to the ground term substituted.
    pub(crate) substitution: HashMap<String, String>,
    /// Priority score (higher = more promising). Range is `[0.0, +inf)`.
    pub(crate) score: f64,
    /// How this candidate was discovered.
    pub(crate) source: InstantiationSource,
}

/// How an instantiation candidate was discovered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum InstantiationSource {
    /// E-matching against trigger patterns.
    EMatching,
    /// Model-based quantifier instantiation.
    Mbqi,
    /// User-provided hint (e.g., `assert_by!` witness).
    UserHint,
    /// Ground term enumeration.
    GroundTerm,
    /// Heuristic generation (e.g., arithmetic projections).
    Heuristic,
}

impl fmt::Display for InstantiationSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EMatching => f.write_str("e-matching"),
            Self::Mbqi => f.write_str("mbqi"),
            Self::UserHint => f.write_str("user-hint"),
            Self::GroundTerm => f.write_str("ground-term"),
            Self::Heuristic => f.write_str("heuristic"),
        }
    }
}

// ---------------------------------------------------------------------------
// Budget management
// ---------------------------------------------------------------------------

/// Controls how many instantiations are allowed per formula and overall.
#[derive(Debug, Clone)]
pub(crate) struct InstantiationBudget {
    /// Maximum instantiations per individual formula before escalation.
    pub(crate) max_per_formula: usize,
    /// Maximum total instantiations across all formulas.
    pub(crate) max_total: usize,
    /// Maximum instantiations emitted in a single round.
    pub(crate) per_round_limit: usize,
    /// How many have been allocated so far, keyed by formula id.
    allocated: HashMap<String, usize>,
    /// Total allocated across all formulas.
    total_allocated: usize,
    /// Escalation multiplier applied when `escalate()` is called.
    escalation_factor: f64,
}

impl InstantiationBudget {
    /// Create a new budget with the given limits.
    #[must_use]
    pub(crate) fn new(max_per_formula: usize, max_total: usize, per_round_limit: usize) -> Self {
        Self {
            max_per_formula,
            max_total,
            per_round_limit,
            allocated: HashMap::new(),
            total_allocated: 0,
            escalation_factor: 2.0,
        }
    }

    /// How many instantiations remain before hitting the total limit.
    #[must_use]
    pub(crate) fn remaining(&self) -> usize {
        self.max_total.saturating_sub(self.total_allocated)
    }

    /// Attempt to allocate `count` instantiations for `formula_id`.
    ///
    /// Returns the number actually allocated (may be less than requested if
    /// budget is exhausted).
    pub(crate) fn allocate(&mut self, formula_id: &str, count: usize) -> usize {
        let per_formula_used = self.allocated.get(formula_id).copied().unwrap_or(0);
        let per_formula_room = self.max_per_formula.saturating_sub(per_formula_used);
        let total_room = self.remaining();
        let granted = count.min(per_formula_room).min(total_room);

        if granted > 0 {
            *self.allocated.entry(formula_id.to_owned()).or_insert(0) += granted;
            self.total_allocated += granted;
        }
        granted
    }

    /// Escalate the budget (multiply limits by the escalation factor).
    ///
    /// Called when the solver determines it needs more instantiations to make
    /// progress. Caps individual limits at `usize::MAX / 2` to avoid overflow.
    pub(crate) fn escalate(&mut self) {
        let cap = usize::MAX / 2;
        self.max_per_formula =
            ((self.max_per_formula as f64 * self.escalation_factor) as usize).min(cap);
        self.max_total = ((self.max_total as f64 * self.escalation_factor) as usize).min(cap);
        self.per_round_limit =
            ((self.per_round_limit as f64 * self.escalation_factor) as usize).min(cap);
    }

    /// How many instantiations have been allocated for a specific formula.
    #[must_use]
    pub(crate) fn allocated_for(&self, formula_id: &str) -> usize {
        self.allocated.get(formula_id).copied().unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------
// Statistics tracking
// ---------------------------------------------------------------------------

/// Tracks instantiation statistics for diagnostics and adaptive tuning.
#[derive(Debug, Clone, Default)]
pub(crate) struct InstantiationStats {
    /// Total instantiations performed.
    pub(crate) total: usize,
    /// Per-formula instantiation counts.
    pub(crate) per_formula: HashMap<String, usize>,
    /// Instantiations that led to solver progress (new conflict/propagation).
    pub(crate) useful: usize,
    /// Instantiations that did not contribute to progress.
    pub(crate) wasted: usize,
}

impl InstantiationStats {
    /// Record an instantiation for the given formula.
    pub(crate) fn record(&mut self, formula_id: &str, was_useful: bool) {
        self.total += 1;
        *self.per_formula.entry(formula_id.to_owned()).or_insert(0) += 1;
        if was_useful {
            self.useful += 1;
        } else {
            self.wasted += 1;
        }
    }

    /// Ratio of useful to total instantiations. Returns 0.0 if no data.
    #[must_use]
    pub(crate) fn usefulness_ratio(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            self.useful as f64 / self.total as f64
        }
    }
}

// ---------------------------------------------------------------------------
// Conflict history
// ---------------------------------------------------------------------------

/// Tracks which instantiations led to conflicts (useful) vs. wasted work.
///
/// This enables conflict-driven instantiation learning: formulas that
/// historically produced useful instantiations get higher priority.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConflictHistory {
    /// Per-formula: (useful_count, total_count).
    history: HashMap<String, (usize, usize)>,
}

impl ConflictHistory {
    /// Record whether an instantiation candidate was useful.
    pub(crate) fn record(&mut self, candidate: &InstantiationCandidate, was_useful: bool) {
        let entry = self
            .history
            .entry(candidate.formula_id.0.clone())
            .or_insert((0, 0));
        entry.1 += 1;
        if was_useful {
            entry.0 += 1;
        }
    }

    /// Usefulness ratio for a specific formula. Returns 0.5 (neutral prior)
    /// if no data is available.
    #[must_use]
    pub(crate) fn usefulness_ratio(&self, formula_id: &str) -> f64 {
        match self.history.get(formula_id) {
            Some(&(useful, total)) if total > 0 => useful as f64 / total as f64,
            _ => 0.5,
        }
    }

    /// Total number of recorded instantiations across all formulas.
    #[must_use]
    pub(crate) fn total_recorded(&self) -> usize {
        self.history.values().map(|&(_, t)| t).sum()
    }
}

// ---------------------------------------------------------------------------
// Relevancy scoring
// ---------------------------------------------------------------------------

/// How relevant a formula is to the current proof state.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct RelevancyScore {
    /// Raw score in `[0.0, 1.0]` where 1.0 is maximally relevant.
    pub(crate) value: f64,
}

impl RelevancyScore {
    /// Create a new score, clamping to `[0.0, 1.0]`.
    #[must_use]
    pub(crate) fn new(value: f64) -> Self {
        Self {
            value: value.clamp(0.0, 1.0),
        }
    }

    /// A zero (irrelevant) score.
    pub(crate) const ZERO: Self = Self { value: 0.0 };
}

impl Default for RelevancyScore {
    fn default() -> Self {
        Self { value: 0.5 }
    }
}

// ---------------------------------------------------------------------------
// Term index
// ---------------------------------------------------------------------------

/// Index of available ground terms for pattern matching.
///
/// Organizes terms by their top-level function symbol for efficient lookup.
#[derive(Debug, Clone, Default)]
pub(crate) struct TermIndex {
    /// All registered terms.
    terms: Vec<String>,
    /// Index from function symbol to term indices in `terms`.
    by_symbol: HashMap<String, Vec<usize>>,
}

impl TermIndex {
    /// Create an empty term index.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a ground term to the index.
    ///
    /// The term string is expected to be in the format `"f(a, b)"` or a
    /// simple constant like `"42"`.
    pub(crate) fn add_term(&mut self, term: &str) {
        let idx = self.terms.len();
        self.terms.push(term.to_owned());

        let symbol = extract_top_symbol(term);
        self.by_symbol
            .entry(symbol.to_owned())
            .or_default()
            .push(idx);
    }

    /// Return all terms whose top-level function symbol matches `pattern`.
    ///
    /// If `pattern` contains parentheses, the top symbol is extracted first.
    #[must_use]
    pub(crate) fn matching_terms(&self, pattern: &str) -> Vec<&str> {
        let symbol = extract_top_symbol(pattern);
        match self.by_symbol.get(symbol) {
            Some(indices) => indices.iter().map(|&i| self.terms[i].as_str()).collect(),
            None => Vec::new(),
        }
    }

    /// Total number of indexed terms.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.terms.len()
    }

    /// Whether the index is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// All registered terms.
    #[must_use]
    pub(crate) fn all_terms(&self) -> &[String] {
        &self.terms
    }
}

/// Extract the top-level function symbol from a term string.
///
/// `"f(a, b)"` -> `"f"`, `"42"` -> `"42"`, `"select(a, i)"` -> `"select"`.
fn extract_top_symbol(term: &str) -> &str {
    match term.find('(') {
        Some(pos) => &term[..pos],
        None => term,
    }
}

/// Parse the arguments of a term string (single nesting level).
///
/// `"f(a, b)"` -> `["a", "b"]`, `"g(x)"` -> `["x"]`.
/// Returns an empty vec for non-function terms.
fn parse_term_args(term: &str) -> Vec<&str> {
    let open = match term.find('(') {
        Some(pos) => pos,
        None => return Vec::new(),
    };
    let close = match term.rfind(')') {
        Some(pos) => pos,
        None => return Vec::new(),
    };
    if close <= open + 1 {
        return Vec::new();
    }

    let inner = &term[open + 1..close];
    // Split on commas, respecting parenthesis nesting.
    let mut args = Vec::new();
    let mut depth = 0_usize;
    let mut start = 0;
    for (i, ch) in inner.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                args.push(inner[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = inner[start..].trim();
    if !last.is_empty() {
        args.push(last);
    }
    args
}

// ---------------------------------------------------------------------------
// E-matching engine
// ---------------------------------------------------------------------------

/// Implements E-matching trigger evaluation against a term index.
#[derive(Debug, Default)]
pub(crate) struct EMatchingEngine {
    /// Maximum number of matches to produce per trigger (prevents blowup).
    pub(crate) match_limit: usize,
}

impl EMatchingEngine {
    /// Create an engine with default match limit.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { match_limit: 1000 }
    }

    /// Match a single trigger pattern against the term index.
    ///
    /// Returns a list of instantiation candidates, one per matching ground
    /// term. Each candidate captures the bound variable assignments.
    #[must_use]
    pub(crate) fn match_trigger(
        &self,
        trigger: &TriggerPattern,
        term_index: &TermIndex,
        formula_id: &FormulaId,
    ) -> Vec<InstantiationCandidate> {
        let matching = term_index.matching_terms(&trigger.function_symbol);
        let mut candidates = Vec::new();

        for term in matching {
            if candidates.len() >= self.match_limit {
                break;
            }
            if let Some(subst) = trigger.matches(term) {
                candidates.push(InstantiationCandidate {
                    formula_id: formula_id.clone(),
                    substitution: subst,
                    score: 1.0,
                    source: InstantiationSource::EMatching,
                });
            }
        }
        candidates
    }

    /// Multi-pattern match: all patterns must match simultaneously with
    /// consistent variable bindings.
    ///
    /// Returns the set of consistent substitution maps.
    #[must_use]
    pub(crate) fn multi_pattern_match(
        &self,
        patterns: &[TriggerPattern],
        term_index: &TermIndex,
    ) -> Vec<HashMap<String, String>> {
        if patterns.is_empty() {
            return Vec::new();
        }

        // Start with matches from the first pattern.
        let first = &patterns[0];
        let first_terms = term_index.matching_terms(&first.function_symbol);
        let mut current_substs: Vec<HashMap<String, String>> = Vec::new();

        for term in first_terms {
            if current_substs.len() >= self.match_limit {
                break;
            }
            if let Some(subst) = first.matches(term) {
                current_substs.push(subst);
            }
        }

        // For each subsequent pattern, filter to consistent substitutions.
        for pattern in patterns.iter().skip(1) {
            let pattern_terms = term_index.matching_terms(&pattern.function_symbol);
            let mut next_substs = Vec::new();

            for existing in &current_substs {
                if next_substs.len() >= self.match_limit {
                    break;
                }
                for term in &pattern_terms {
                    if next_substs.len() >= self.match_limit {
                        break;
                    }
                    if let Some(new_subst) = pattern.matches(term) {
                        if let Some(merged) = merge_substitutions(existing, &new_subst) {
                            next_substs.push(merged);
                        }
                    }
                }
            }
            current_substs = next_substs;
        }

        current_substs
    }
}

impl TriggerPattern {
    /// Try to match this trigger pattern against a ground term.
    ///
    /// Returns `Some(substitution)` mapping bound variables to their matched
    /// sub-terms, or `None` if the term does not match.
    #[must_use]
    pub(crate) fn matches(&self, term: &str) -> Option<HashMap<String, String>> {
        let symbol = extract_top_symbol(term);
        if symbol != self.function_symbol {
            return None;
        }

        let args = parse_term_args(term);
        if args.len() != self.args.len() {
            return None;
        }

        let mut subst = HashMap::new();
        for (pattern_arg, term_arg) in self.args.iter().zip(args.iter()) {
            match pattern_arg {
                PatternArg::BoundVar(var) => {
                    if let Some(existing) = subst.get(var.as_str()) {
                        // Same variable must bind to the same term.
                        if existing != term_arg {
                            return None;
                        }
                    } else {
                        subst.insert(var.clone(), (*term_arg).to_owned());
                    }
                }
                PatternArg::Constant(c) => {
                    if c != *term_arg {
                        return None;
                    }
                }
                PatternArg::Wildcard => { /* matches anything */ }
            }
        }
        Some(subst)
    }
}

/// Merge two substitution maps if they are consistent (no conflicting bindings).
fn merge_substitutions(
    a: &HashMap<String, String>,
    b: &HashMap<String, String>,
) -> Option<HashMap<String, String>> {
    let mut merged = a.clone();
    for (k, v) in b {
        if let Some(existing) = merged.get(k) {
            if existing != v {
                return None;
            }
        } else {
            merged.insert(k.clone(), v.clone());
        }
    }
    Some(merged)
}

// ---------------------------------------------------------------------------
// Scheduler configuration
// ---------------------------------------------------------------------------

/// Configuration for the quantifier scheduler.
#[derive(Debug, Clone)]
pub(crate) struct SchedulerConfig {
    /// Initial budget per formula.
    pub(crate) initial_budget: usize,
    /// How much to multiply budget on escalation.
    pub(crate) escalation_factor: f64,
    /// Maximum number of instantiation rounds.
    pub(crate) max_rounds: usize,
    /// Whether to filter formulas by relevancy before scheduling.
    pub(crate) relevancy_filter: bool,
    /// Minimum relevancy score for a formula to be scheduled (when filter on).
    pub(crate) relevancy_threshold: f64,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        Self {
            initial_budget: 10,
            escalation_factor: 2.0,
            max_rounds: 8,
            relevancy_filter: true,
            relevancy_threshold: 0.1,
        }
    }
}

// ---------------------------------------------------------------------------
// Instantiation plan
// ---------------------------------------------------------------------------

/// An ordered list of instantiation candidates with budget tracking.
#[derive(Debug, Clone)]
pub(crate) struct InstantiationPlan {
    /// Ordered candidates (highest priority first).
    candidates: VecDeque<InstantiationCandidate>,
    /// Current round index (0-based).
    current_round: usize,
}

impl InstantiationPlan {
    /// Create a plan from a list of candidates (will be sorted by score desc).
    #[must_use]
    pub(crate) fn new(mut candidates: Vec<InstantiationCandidate>) -> Self {
        // Sort descending by score. NaN-safe: treat NaN as lowest.
        candidates.sort_by(|a, b| {
            b.score
                .partial_cmp(&a.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        Self {
            candidates: VecDeque::from(candidates),
            current_round: 0,
        }
    }

    /// Execute one round: drain up to `budget` candidates from the front.
    pub(crate) fn execute_round(
        &mut self,
        budget: &mut InstantiationBudget,
    ) -> Vec<InstantiationCandidate> {
        let mut emitted = Vec::new();
        let round_limit = budget.per_round_limit;

        while emitted.len() < round_limit {
            let candidate = match self.candidates.pop_front() {
                Some(c) => c,
                None => break,
            };
            let granted = budget.allocate(&candidate.formula_id.0, 1);
            if granted > 0 {
                emitted.push(candidate);
            }
            // If budget is fully exhausted, stop.
            if budget.remaining() == 0 {
                break;
            }
        }
        self.current_round += 1;
        emitted
    }

    /// How many candidates remain in the plan.
    #[must_use]
    pub(crate) fn remaining(&self) -> usize {
        self.candidates.len()
    }

    /// Current round number.
    #[must_use]
    pub(crate) fn current_round(&self) -> usize {
        self.current_round
    }
}

// ---------------------------------------------------------------------------
// Quantifier scheduler
// ---------------------------------------------------------------------------

/// Proof-state context passed to the scheduler for relevancy scoring.
#[derive(Debug, Clone, Default)]
pub(crate) struct ProofContext {
    /// Symbols that appear in the current proof goal.
    pub(crate) goal_symbols: HashSet<String>,
    /// Symbols that appear in current assertions / hypotheses.
    pub(crate) assertion_symbols: HashSet<String>,
}

/// Decides the order and budget for quantifier instantiation.
#[derive(Debug)]
pub(crate) struct QuantifierScheduler {
    config: SchedulerConfig,
    engine: EMatchingEngine,
}

impl QuantifierScheduler {
    /// Create a new scheduler with the given configuration.
    #[must_use]
    pub(crate) fn new(config: SchedulerConfig) -> Self {
        Self {
            config,
            engine: EMatchingEngine::new(),
        }
    }

    /// Build an instantiation plan from the available formulas and terms.
    ///
    /// Uses relevancy scoring and conflict history to prioritize formulas,
    /// then runs E-matching to generate candidates.
    #[must_use]
    pub(crate) fn plan(
        &self,
        formulas: &[QuantifiedFormula],
        term_index: &TermIndex,
        history: &ConflictHistory,
        context: &ProofContext,
    ) -> InstantiationPlan {
        let mut all_candidates = Vec::new();

        for formula in formulas {
            let relevancy = self.score_formula(formula, context);

            // Skip irrelevant formulas when filter is on.
            if self.config.relevancy_filter && relevancy.value < self.config.relevancy_threshold {
                continue;
            }

            // Historical usefulness boost.
            let history_factor = history.usefulness_ratio(&formula.id.0);

            // Generate candidates via E-matching on each trigger.
            for trigger in &formula.triggers {
                let mut matched = self.engine.match_trigger(trigger, term_index, &formula.id);
                // Score = relevancy * history_factor * depth_penalty.
                let depth_penalty = 1.0 / (1.0 + formula.depth as f64);
                for candidate in &mut matched {
                    candidate.score = relevancy.value * history_factor * depth_penalty;
                }
                all_candidates.extend(matched);
            }

            // If no triggers, generate ground-term candidates from term index.
            if formula.triggers.is_empty() && !formula.bound_vars.is_empty() {
                let depth_penalty = 1.0 / (1.0 + formula.depth as f64);
                for term in term_index.all_terms() {
                    let mut subst = HashMap::new();
                    // Bind first variable to each available term (heuristic).
                    subst.insert(formula.bound_vars[0].clone(), term.clone());
                    all_candidates.push(InstantiationCandidate {
                        formula_id: formula.id.clone(),
                        substitution: subst,
                        score: relevancy.value * history_factor * depth_penalty * 0.5,
                        source: InstantiationSource::GroundTerm,
                    });
                }
            }
        }

        InstantiationPlan::new(all_candidates)
    }

    /// Compute a relevancy score for a formula given the current proof context.
    ///
    /// Formulas that share symbols with the goal or assertions score higher.
    #[must_use]
    pub(crate) fn score_formula(
        &self,
        formula: &QuantifiedFormula,
        context: &ProofContext,
    ) -> RelevancyScore {
        if context.goal_symbols.is_empty() && context.assertion_symbols.is_empty() {
            // No context: default medium relevancy.
            return RelevancyScore::default();
        }

        let body_symbols = extract_symbols(&formula.body);
        if body_symbols.is_empty() {
            return RelevancyScore::ZERO;
        }

        let mut score = 0.0_f64;

        // Goal overlap (weighted 2x).
        if !context.goal_symbols.is_empty() {
            let overlap = body_symbols.intersection(&context.goal_symbols).count();
            score += 2.0 * overlap as f64 / context.goal_symbols.len() as f64;
        }

        // Assertion overlap.
        if !context.assertion_symbols.is_empty() {
            let overlap = body_symbols
                .intersection(&context.assertion_symbols)
                .count();
            score += overlap as f64 / context.assertion_symbols.len() as f64;
        }

        // Depth penalty: deeper quantifiers are less likely to be directly useful.
        let depth_factor = 1.0 / (1.0 + formula.depth as f64 * 0.3);
        score *= depth_factor;

        // Trigger bonus: formulas with user-provided triggers get a small boost.
        if !formula.triggers.is_empty() {
            score *= 1.1;
        }

        // Normalize to [0, 1].
        RelevancyScore::new(score / 3.3)
    }
}

/// Extract alphanumeric "symbol" tokens from a formula body string.
fn extract_symbols(body: &str) -> HashSet<String> {
    let mut symbols = HashSet::new();
    let mut current = String::new();
    for ch in body.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty() {
                // Skip pure numeric literals.
                if !current.chars().all(|c| c.is_ascii_digit()) {
                    symbols.insert(std::mem::take(&mut current));
                } else {
                    current.clear();
                }
            }
        }
    }
    if !current.is_empty() && !current.chars().all(|c| c.is_ascii_digit()) {
        symbols.insert(current);
    }
    symbols
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helper factories ---------------------------------------------------

    fn make_formula(id: &str, vars: &[&str], body: &str, depth: usize) -> QuantifiedFormula {
        QuantifiedFormula {
            id: FormulaId(id.to_owned()),
            bound_vars: vars.iter().map(|s| (*s).to_owned()).collect(),
            body: body.to_owned(),
            triggers: Vec::new(),
            depth,
        }
    }

    fn make_trigger(symbol: &str, args: &[PatternArg]) -> TriggerPattern {
        TriggerPattern {
            function_symbol: symbol.to_owned(),
            args: args.to_vec(),
        }
    }

    fn make_formula_with_triggers(
        id: &str,
        vars: &[&str],
        body: &str,
        triggers: Vec<TriggerPattern>,
    ) -> QuantifiedFormula {
        QuantifiedFormula {
            id: FormulaId(id.to_owned()),
            bound_vars: vars.iter().map(|s| (*s).to_owned()).collect(),
            body: body.to_owned(),
            triggers,
            depth: 0,
        }
    }

    // -- TriggerPattern::matches -------------------------------------------

    #[test]
    fn test_trigger_matches_simple_function() {
        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let result = trigger.matches("f(a)");
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get("x").unwrap(), "a");
    }

    #[test]
    fn test_trigger_matches_two_args() {
        let trigger = make_trigger(
            "g",
            &[
                PatternArg::BoundVar("x".to_owned()),
                PatternArg::BoundVar("y".to_owned()),
            ],
        );
        let result = trigger.matches("g(1, 2)");
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get("x").unwrap(), "1");
        assert_eq!(subst.get("y").unwrap(), "2");
    }

    #[test]
    fn test_trigger_mismatch_symbol() {
        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        assert!(trigger.matches("g(a)").is_none());
    }

    #[test]
    fn test_trigger_mismatch_arity() {
        let trigger = make_trigger(
            "f",
            &[
                PatternArg::BoundVar("x".to_owned()),
                PatternArg::BoundVar("y".to_owned()),
            ],
        );
        assert!(trigger.matches("f(a)").is_none());
    }

    #[test]
    fn test_trigger_constant_match() {
        let trigger = make_trigger(
            "f",
            &[
                PatternArg::Constant("0".to_owned()),
                PatternArg::BoundVar("x".to_owned()),
            ],
        );
        let result = trigger.matches("f(0, hello)");
        assert!(result.is_some());
        assert_eq!(result.unwrap().get("x").unwrap(), "hello");
    }

    #[test]
    fn test_trigger_constant_mismatch() {
        let trigger = make_trigger("f", &[PatternArg::Constant("0".to_owned())]);
        assert!(trigger.matches("f(1)").is_none());
    }

    #[test]
    fn test_trigger_wildcard_matches_anything() {
        let trigger = make_trigger(
            "f",
            &[PatternArg::Wildcard, PatternArg::BoundVar("x".to_owned())],
        );
        let result = trigger.matches("f(anything, val)");
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get("x").unwrap(), "val");
        // Wildcard should not appear as a key in the substitution.
        assert!(!subst.contains_key("_wildcard"));
    }

    #[test]
    fn test_trigger_repeated_var_consistent() {
        let trigger = make_trigger(
            "f",
            &[
                PatternArg::BoundVar("x".to_owned()),
                PatternArg::BoundVar("x".to_owned()),
            ],
        );
        let result = trigger.matches("f(a, a)");
        assert!(result.is_some());
        assert_eq!(result.unwrap().get("x").unwrap(), "a");
    }

    #[test]
    fn test_trigger_repeated_var_inconsistent() {
        let trigger = make_trigger(
            "f",
            &[
                PatternArg::BoundVar("x".to_owned()),
                PatternArg::BoundVar("x".to_owned()),
            ],
        );
        assert!(trigger.matches("f(a, b)").is_none());
    }

    // -- extract_top_symbol / parse_term_args ------------------------------

    #[test]
    fn test_extract_top_symbol_function() {
        assert_eq!(extract_top_symbol("f(a, b)"), "f");
    }

    #[test]
    fn test_extract_top_symbol_constant() {
        assert_eq!(extract_top_symbol("42"), "42");
    }

    #[test]
    fn test_parse_term_args_two_args() {
        let args = parse_term_args("f(a, b)");
        assert_eq!(args, vec!["a", "b"]);
    }

    #[test]
    fn test_parse_term_args_nested() {
        let args = parse_term_args("f(g(x), h(y, z))");
        assert_eq!(args, vec!["g(x)", "h(y, z)"]);
    }

    #[test]
    fn test_parse_term_args_constant() {
        let args = parse_term_args("42");
        assert!(args.is_empty());
    }

    // -- TermIndex ---------------------------------------------------------

    #[test]
    fn test_term_index_add_and_match() {
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");
        idx.add_term("g(c)");

        let matches = idx.matching_terms("f");
        assert_eq!(matches.len(), 2);
        assert!(matches.contains(&"f(a)"));
        assert!(matches.contains(&"f(b)"));
    }

    #[test]
    fn test_term_index_no_match() {
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        let matches = idx.matching_terms("g");
        assert!(matches.is_empty());
    }

    #[test]
    fn test_term_index_empty() {
        let idx = TermIndex::new();
        assert!(idx.is_empty());
        assert_eq!(idx.len(), 0);
    }

    #[test]
    fn test_term_index_len() {
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("g(b)");
        assert_eq!(idx.len(), 2);
        assert!(!idx.is_empty());
    }

    // -- InstantiationBudget -----------------------------------------------

    #[test]
    fn test_budget_allocate_within_limits() {
        let mut budget = InstantiationBudget::new(5, 100, 10);
        let granted = budget.allocate("f1", 3);
        assert_eq!(granted, 3);
        assert_eq!(budget.remaining(), 97);
        assert_eq!(budget.allocated_for("f1"), 3);
    }

    #[test]
    fn test_budget_per_formula_cap() {
        let mut budget = InstantiationBudget::new(2, 100, 10);
        assert_eq!(budget.allocate("f1", 3), 2);
        assert_eq!(budget.allocate("f1", 1), 0);
        assert_eq!(budget.allocated_for("f1"), 2);
    }

    #[test]
    fn test_budget_total_cap() {
        let mut budget = InstantiationBudget::new(100, 5, 100);
        assert_eq!(budget.allocate("f1", 3), 3);
        assert_eq!(budget.allocate("f2", 3), 2); // only 2 remain
        assert_eq!(budget.remaining(), 0);
    }

    #[test]
    fn test_budget_escalate() {
        let mut budget = InstantiationBudget::new(10, 100, 20);
        budget.escalate();
        assert_eq!(budget.max_per_formula, 20);
        assert_eq!(budget.max_total, 200);
        assert_eq!(budget.per_round_limit, 40);
    }

    #[test]
    fn test_budget_remaining_after_full_exhaust() {
        let mut budget = InstantiationBudget::new(100, 3, 100);
        budget.allocate("f1", 3);
        assert_eq!(budget.remaining(), 0);
        assert_eq!(budget.allocate("f2", 1), 0);
    }

    // -- InstantiationStats ------------------------------------------------

    #[test]
    fn test_stats_record_useful() {
        let mut stats = InstantiationStats::default();
        stats.record("f1", true);
        stats.record("f1", false);
        stats.record("f2", true);
        assert_eq!(stats.total, 3);
        assert_eq!(stats.useful, 2);
        assert_eq!(stats.wasted, 1);
        assert_eq!(*stats.per_formula.get("f1").unwrap(), 2);
    }

    #[test]
    fn test_stats_usefulness_ratio_empty() {
        let stats = InstantiationStats::default();
        assert_eq!(stats.usefulness_ratio(), 0.0);
    }

    #[test]
    fn test_stats_usefulness_ratio_all_useful() {
        let mut stats = InstantiationStats::default();
        stats.record("f1", true);
        stats.record("f1", true);
        assert!((stats.usefulness_ratio() - 1.0).abs() < f64::EPSILON);
    }

    // -- ConflictHistory ---------------------------------------------------

    #[test]
    fn test_conflict_history_default_ratio() {
        let history = ConflictHistory::default();
        assert!((history.usefulness_ratio("unknown") - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_conflict_history_record_and_ratio() {
        let mut history = ConflictHistory::default();
        let candidate = InstantiationCandidate {
            formula_id: FormulaId("f1".to_owned()),
            substitution: HashMap::new(),
            score: 1.0,
            source: InstantiationSource::EMatching,
        };
        history.record(&candidate, true);
        history.record(&candidate, true);
        history.record(&candidate, false);
        let ratio = history.usefulness_ratio("f1");
        assert!((ratio - 2.0 / 3.0).abs() < 0.001);
    }

    #[test]
    fn test_conflict_history_total_recorded() {
        let mut history = ConflictHistory::default();
        let c1 = InstantiationCandidate {
            formula_id: FormulaId("f1".to_owned()),
            substitution: HashMap::new(),
            score: 1.0,
            source: InstantiationSource::EMatching,
        };
        let c2 = InstantiationCandidate {
            formula_id: FormulaId("f2".to_owned()),
            substitution: HashMap::new(),
            score: 1.0,
            source: InstantiationSource::Heuristic,
        };
        history.record(&c1, true);
        history.record(&c2, false);
        assert_eq!(history.total_recorded(), 2);
    }

    // -- RelevancyScore ----------------------------------------------------

    #[test]
    fn test_relevancy_score_clamp_high() {
        let score = RelevancyScore::new(5.0);
        assert!((score.value - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_relevancy_score_clamp_low() {
        let score = RelevancyScore::new(-1.0);
        assert!(score.value.abs() < f64::EPSILON);
    }

    #[test]
    fn test_relevancy_score_default() {
        let score = RelevancyScore::default();
        assert!((score.value - 0.5).abs() < f64::EPSILON);
    }

    // -- EMatchingEngine ---------------------------------------------------

    #[test]
    fn test_ematching_match_trigger_basic() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");
        idx.add_term("g(c)");

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let fid = FormulaId("q1".to_owned());
        let candidates = engine.match_trigger(&trigger, &idx, &fid);
        assert_eq!(candidates.len(), 2);
        assert!(candidates
            .iter()
            .all(|c| c.source == InstantiationSource::EMatching));
    }

    #[test]
    fn test_ematching_multi_pattern_consistent() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("g(a)");
        idx.add_term("g(b)");

        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger("g", &[PatternArg::BoundVar("x".to_owned())]);

        let results = engine.multi_pattern_match(&[p1, p2], &idx);
        // f(a) binds x=a, g(a) also binds x=a => consistent.
        // g(b) binds x=b => inconsistent with x=a.
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].get("x").unwrap(), "a");
    }

    #[test]
    fn test_ematching_multi_pattern_empty_patterns() {
        let engine = EMatchingEngine::new();
        let idx = TermIndex::new();
        let results = engine.multi_pattern_match(&[], &idx);
        assert!(results.is_empty());
    }

    #[test]
    fn test_ematching_multi_pattern_no_match() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("g(b)");

        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger("g", &[PatternArg::BoundVar("x".to_owned())]);
        // f(a) -> x=a, g(b) -> x=b => inconsistent.
        let results = engine.multi_pattern_match(&[p1, p2], &idx);
        assert!(results.is_empty());
    }

    // -- merge_substitutions -----------------------------------------------

    #[test]
    fn test_merge_substitutions_compatible() {
        let mut a = HashMap::new();
        a.insert("x".to_owned(), "1".to_owned());
        let mut b = HashMap::new();
        b.insert("y".to_owned(), "2".to_owned());
        let merged = merge_substitutions(&a, &b).unwrap();
        assert_eq!(merged.len(), 2);
    }

    #[test]
    fn test_merge_substitutions_conflict() {
        let mut a = HashMap::new();
        a.insert("x".to_owned(), "1".to_owned());
        let mut b = HashMap::new();
        b.insert("x".to_owned(), "2".to_owned());
        assert!(merge_substitutions(&a, &b).is_none());
    }

    // -- InstantiationPlan -------------------------------------------------

    #[test]
    fn test_plan_execute_round_respects_budget() {
        let candidates = vec![
            InstantiationCandidate {
                formula_id: FormulaId("f1".to_owned()),
                substitution: HashMap::new(),
                score: 3.0,
                source: InstantiationSource::EMatching,
            },
            InstantiationCandidate {
                formula_id: FormulaId("f1".to_owned()),
                substitution: HashMap::new(),
                score: 2.0,
                source: InstantiationSource::EMatching,
            },
            InstantiationCandidate {
                formula_id: FormulaId("f1".to_owned()),
                substitution: HashMap::new(),
                score: 1.0,
                source: InstantiationSource::EMatching,
            },
        ];
        let mut plan = InstantiationPlan::new(candidates);
        let mut budget = InstantiationBudget::new(2, 100, 10);
        let round = plan.execute_round(&mut budget);
        // Per-formula cap is 2, so only 2 emitted.
        assert_eq!(round.len(), 2);
        assert_eq!(plan.current_round(), 1);
    }

    #[test]
    fn test_plan_sorted_by_score_descending() {
        let candidates = vec![
            InstantiationCandidate {
                formula_id: FormulaId("f1".to_owned()),
                substitution: HashMap::new(),
                score: 1.0,
                source: InstantiationSource::EMatching,
            },
            InstantiationCandidate {
                formula_id: FormulaId("f2".to_owned()),
                substitution: HashMap::new(),
                score: 5.0,
                source: InstantiationSource::Heuristic,
            },
        ];
        let mut plan = InstantiationPlan::new(candidates);
        let mut budget = InstantiationBudget::new(100, 100, 100);
        let round = plan.execute_round(&mut budget);
        assert_eq!(round.len(), 2);
        assert!(round[0].score >= round[1].score);
    }

    #[test]
    fn test_plan_remaining_decreases() {
        let candidates = vec![InstantiationCandidate {
            formula_id: FormulaId("f1".to_owned()),
            substitution: HashMap::new(),
            score: 1.0,
            source: InstantiationSource::EMatching,
        }];
        let mut plan = InstantiationPlan::new(candidates);
        assert_eq!(plan.remaining(), 1);
        let mut budget = InstantiationBudget::new(100, 100, 100);
        plan.execute_round(&mut budget);
        assert_eq!(plan.remaining(), 0);
    }

    // -- QuantifierScheduler -----------------------------------------------

    #[test]
    fn test_scheduler_plan_with_triggers() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let formula = make_formula_with_triggers("q1", &["x"], "f(x) > 0", vec![trigger]);

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();
        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        assert_eq!(plan.remaining(), 2);
    }

    #[test]
    fn test_scheduler_plan_no_triggers_fallback_to_ground() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);
        let formula = make_formula("q1", &["x"], "x > 0", 0);

        let mut idx = TermIndex::new();
        idx.add_term("1");
        idx.add_term("2");

        let history = ConflictHistory::default();
        let context = ProofContext::default();
        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        // Falls back to ground-term instantiation: one per term.
        assert_eq!(plan.remaining(), 2);
    }

    #[test]
    fn test_scheduler_relevancy_filter_excludes_irrelevant() {
        let config = SchedulerConfig {
            relevancy_filter: true,
            relevancy_threshold: 0.8,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "unrelated_symbol(x)", 0);

        let mut idx = TermIndex::new();
        idx.add_term("1");

        let history = ConflictHistory::default();
        let context = ProofContext {
            goal_symbols: ["goal_sym".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };
        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        // Formula body has no overlap with goal => relevancy near 0 => filtered out.
        assert_eq!(plan.remaining(), 0);
    }

    #[test]
    fn test_scheduler_score_formula_with_goal_overlap() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "f(x) + g(x)", 0);
        let context = ProofContext {
            goal_symbols: ["f".to_owned(), "g".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };
        let score = scheduler.score_formula(&formula, &context);
        assert!(score.value > 0.0, "should have positive relevancy");
    }

    #[test]
    fn test_scheduler_score_formula_empty_context_returns_default() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);
        let formula = make_formula("q1", &["x"], "f(x)", 0);
        let context = ProofContext::default();
        let score = scheduler.score_formula(&formula, &context);
        assert!((score.value - 0.5).abs() < f64::EPSILON);
    }

    // -- extract_symbols ---------------------------------------------------

    #[test]
    fn test_extract_symbols_basic() {
        let syms = extract_symbols("f(x) + g(y)");
        assert!(syms.contains("f"));
        assert!(syms.contains("x"));
        assert!(syms.contains("g"));
        assert!(syms.contains("y"));
    }

    #[test]
    fn test_extract_symbols_skips_numbers() {
        let syms = extract_symbols("x + 42 > 0");
        assert!(syms.contains("x"));
        assert!(!syms.contains("42"));
        assert!(!syms.contains("0"));
    }

    // -- InstantiationSource Display ----------------------------------------

    #[test]
    fn test_instantiation_source_display() {
        assert_eq!(format!("{}", InstantiationSource::EMatching), "e-matching");
        assert_eq!(format!("{}", InstantiationSource::Mbqi), "mbqi");
        assert_eq!(format!("{}", InstantiationSource::UserHint), "user-hint");
        assert_eq!(
            format!("{}", InstantiationSource::GroundTerm),
            "ground-term"
        );
        assert_eq!(format!("{}", InstantiationSource::Heuristic), "heuristic");
    }

    // -- FormulaId Display --------------------------------------------------

    #[test]
    fn test_formula_id_display() {
        let fid = FormulaId("quant_42".to_owned());
        assert_eq!(format!("{fid}"), "quant_42");
    }

    // -- InstantiationTerm Display ------------------------------------------

    #[test]
    fn test_instantiation_term_display() {
        let term = InstantiationTerm {
            value: "f(a)".to_owned(),
            sort: "Int".to_owned(),
        };
        assert_eq!(format!("{term}"), "f(a):Int");
    }

    // ======================================================================
    // Extended tests: trigger pattern selection/ranking
    // ======================================================================

    #[test]
    fn test_trigger_matches_zero_arg_function() {
        let trigger = make_trigger("c", &[]);
        // "c()" has 0 args, pattern has 0 args => match with empty subst.
        let result = trigger.matches("c()");
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_trigger_matches_zero_arg_mismatch_nonempty_args() {
        let trigger = make_trigger("c", &[]);
        // "c(x)" has 1 arg but pattern expects 0 => no match.
        assert!(trigger.matches("c(x)").is_none());
    }

    #[test]
    fn test_trigger_all_wildcards() {
        let trigger = make_trigger("f", &[PatternArg::Wildcard, PatternArg::Wildcard]);
        let result = trigger.matches("f(hello, world)");
        assert!(result.is_some());
        // Wildcards produce no bindings.
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_trigger_all_constants_match() {
        let trigger = make_trigger(
            "pair",
            &[
                PatternArg::Constant("a".to_owned()),
                PatternArg::Constant("b".to_owned()),
            ],
        );
        let result = trigger.matches("pair(a, b)");
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_trigger_all_constants_partial_mismatch() {
        let trigger = make_trigger(
            "pair",
            &[
                PatternArg::Constant("a".to_owned()),
                PatternArg::Constant("b".to_owned()),
            ],
        );
        assert!(trigger.matches("pair(a, c)").is_none());
    }

    #[test]
    fn test_trigger_matches_nested_term_arg() {
        // Pattern: f(x) matching against f(g(a, b)) should bind x = "g(a, b)".
        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let result = trigger.matches("f(g(a, b))");
        assert!(result.is_some());
        assert_eq!(result.unwrap().get("x").unwrap(), "g(a, b)");
    }

    #[test]
    fn test_trigger_matches_deeply_nested_term() {
        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let result = trigger.matches("f(g(h(k(z))))");
        assert!(result.is_some());
        assert_eq!(result.unwrap().get("x").unwrap(), "g(h(k(z)))");
    }

    #[test]
    fn test_trigger_mixed_constant_wildcard_boundvar() {
        let trigger = make_trigger(
            "sel",
            &[
                PatternArg::Constant("arr".to_owned()),
                PatternArg::Wildcard,
                PatternArg::BoundVar("i".to_owned()),
            ],
        );
        let result = trigger.matches("sel(arr, ignored, 5)");
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.get("i").unwrap(), "5");
    }

    #[test]
    fn test_trigger_no_match_on_plain_constant_term() {
        // Pattern expects function application but term is a bare constant.
        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        assert!(trigger.matches("42").is_none());
    }

    #[test]
    fn test_trigger_three_bound_vars() {
        let trigger = make_trigger(
            "triple",
            &[
                PatternArg::BoundVar("a".to_owned()),
                PatternArg::BoundVar("b".to_owned()),
                PatternArg::BoundVar("c".to_owned()),
            ],
        );
        let result = trigger.matches("triple(x, y, z)");
        assert!(result.is_some());
        let subst = result.unwrap();
        assert_eq!(subst.get("a").unwrap(), "x");
        assert_eq!(subst.get("b").unwrap(), "y");
        assert_eq!(subst.get("c").unwrap(), "z");
    }

    // ======================================================================
    // Extended tests: multi-trigger generation
    // ======================================================================

    #[test]
    fn test_multi_pattern_two_variables_different_patterns() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("g(b)");

        // p1 binds x, p2 binds y -- independent variables, should combine.
        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger("g", &[PatternArg::BoundVar("y".to_owned())]);

        let results = engine.multi_pattern_match(&[p1, p2], &idx);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].get("x").unwrap(), "a");
        assert_eq!(results[0].get("y").unwrap(), "b");
    }

    #[test]
    fn test_multi_pattern_multiple_matches_cross_product() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");
        idx.add_term("g(1)");
        idx.add_term("g(2)");

        // Independent variables: 2 choices for x * 2 choices for y = 4 combos.
        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger("g", &[PatternArg::BoundVar("y".to_owned())]);

        let results = engine.multi_pattern_match(&[p1, p2], &idx);
        assert_eq!(results.len(), 4);
    }

    #[test]
    fn test_multi_pattern_shared_variable_filters_inconsistent() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");
        idx.add_term("g(a, 1)");
        idx.add_term("g(b, 2)");

        // Both patterns share x. f(a)->x=a pairs only with g(a,1)->x=a.
        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger(
            "g",
            &[
                PatternArg::BoundVar("x".to_owned()),
                PatternArg::BoundVar("y".to_owned()),
            ],
        );

        let results = engine.multi_pattern_match(&[p1, p2], &idx);
        assert_eq!(results.len(), 2);

        let x_values: HashSet<_> = results
            .iter()
            .map(|s| s.get("x").unwrap().clone())
            .collect();
        assert!(x_values.contains("a"));
        assert!(x_values.contains("b"));
    }

    #[test]
    fn test_multi_pattern_single_pattern_same_as_single_match() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");

        let p = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let results = engine.multi_pattern_match(&[p], &idx);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_multi_pattern_three_patterns() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("g(a)");
        idx.add_term("h(a)");

        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger("g", &[PatternArg::BoundVar("x".to_owned())]);
        let p3 = make_trigger("h", &[PatternArg::BoundVar("x".to_owned())]);

        let results = engine.multi_pattern_match(&[p1, p2, p3], &idx);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].get("x").unwrap(), "a");
    }

    #[test]
    fn test_multi_pattern_no_terms_in_index() {
        let engine = EMatchingEngine::new();
        let idx = TermIndex::new();

        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let results = engine.multi_pattern_match(&[p1], &idx);
        assert!(results.is_empty());
    }

    // ======================================================================
    // Extended tests: E-matching round configuration / match limit
    // ======================================================================

    #[test]
    fn test_ematching_match_limit_enforced() {
        let mut engine = EMatchingEngine::new();
        engine.match_limit = 3;

        let mut idx = TermIndex::new();
        for i in 0..10 {
            idx.add_term(&format!("f(t{i})"));
        }

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let fid = FormulaId("q1".to_owned());
        let candidates = engine.match_trigger(&trigger, &idx, &fid);
        assert_eq!(candidates.len(), 3);
    }

    #[test]
    fn test_ematching_match_limit_multi_pattern() {
        let mut engine = EMatchingEngine::new();
        engine.match_limit = 2;

        let mut idx = TermIndex::new();
        for i in 0..5 {
            idx.add_term(&format!("f(t{i})"));
            idx.add_term(&format!("g(s{i})"));
        }

        let p1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let p2 = make_trigger("g", &[PatternArg::BoundVar("y".to_owned())]);

        let results = engine.multi_pattern_match(&[p1, p2], &idx);
        // Match limit caps at 2 per stage.
        assert!(results.len() <= 2);
    }

    #[test]
    fn test_ematching_default_match_limit() {
        let engine = EMatchingEngine::new();
        assert_eq!(engine.match_limit, 1000);
    }

    #[test]
    fn test_ematching_no_matching_symbol() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let trigger = make_trigger("g", &[PatternArg::BoundVar("x".to_owned())]);
        let fid = FormulaId("q1".to_owned());
        let candidates = engine.match_trigger(&trigger, &idx, &fid);
        assert!(candidates.is_empty());
    }

    #[test]
    fn test_ematching_candidates_have_correct_source() {
        let engine = EMatchingEngine::new();
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let fid = FormulaId("q1".to_owned());
        let candidates = engine.match_trigger(&trigger, &idx, &fid);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].source, InstantiationSource::EMatching);
        assert_eq!(candidates[0].formula_id.0, "q1");
    }

    // ======================================================================
    // Extended tests: quantifier depth tracking
    // ======================================================================

    #[test]
    fn test_depth_penalty_in_scoring() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let context = ProofContext {
            goal_symbols: ["f".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };

        let shallow = make_formula("q_shallow", &["x"], "f(x)", 0);
        let deep = make_formula("q_deep", &["x"], "f(x)", 5);

        let score_shallow = scheduler.score_formula(&shallow, &context);
        let score_deep = scheduler.score_formula(&deep, &context);

        // Deeper quantifiers should score lower due to depth penalty.
        assert!(
            score_shallow.value > score_deep.value,
            "shallow={}, deep={}",
            score_shallow.value,
            score_deep.value
        );
    }

    #[test]
    fn test_depth_penalty_in_plan_candidate_scoring() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);

        let mut shallow = make_formula_with_triggers("q0", &["x"], "f(x)", vec![trigger.clone()]);
        shallow.depth = 0;

        let mut deep = make_formula_with_triggers("q5", &["x"], "f(x)", vec![trigger]);
        deep.depth = 5;

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[shallow, deep], &idx, &history, &context);
        // Both formulas matched; 2 candidates total.
        assert_eq!(plan.remaining(), 2);
    }

    #[test]
    fn test_depth_zero_no_penalty() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let context = ProofContext {
            goal_symbols: ["f".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };

        let formula = make_formula("q1", &["x"], "f(x)", 0);
        let score = scheduler.score_formula(&formula, &context);

        // Depth 0: depth_factor = 1/(1 + 0*0.3) = 1.0 -- no penalty.
        assert!(score.value > 0.0);
    }

    #[test]
    fn test_increasing_depth_decreases_score_monotonically() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let context = ProofContext {
            goal_symbols: ["f".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };

        let mut prev_score = f64::MAX;
        for depth in 0..10 {
            let formula = make_formula("q", &["x"], "f(x)", depth);
            let score = scheduler.score_formula(&formula, &context);
            assert!(
                score.value <= prev_score,
                "depth {} score {} should be <= prev {}",
                depth,
                score.value,
                prev_score
            );
            prev_score = score.value;
        }
    }

    // ======================================================================
    // Extended tests: pattern scoring/filtering
    // ======================================================================

    #[test]
    fn test_score_formula_assertion_overlap() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "foo(x) + bar(x)", 0);
        let context = ProofContext {
            goal_symbols: HashSet::new(),
            assertion_symbols: ["foo".to_owned(), "bar".to_owned()].into_iter().collect(),
        };
        let score = scheduler.score_formula(&formula, &context);
        assert!(score.value > 0.0);
    }

    #[test]
    fn test_score_formula_both_goal_and_assertion_overlap() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "f(x) + g(x)", 0);

        let goal_only_context = ProofContext {
            goal_symbols: ["f".to_owned(), "g".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };

        let both_context = ProofContext {
            goal_symbols: ["f".to_owned(), "g".to_owned()].into_iter().collect(),
            assertion_symbols: ["f".to_owned(), "g".to_owned()].into_iter().collect(),
        };

        let score_goal_only = scheduler.score_formula(&formula, &goal_only_context);
        let score_both = scheduler.score_formula(&formula, &both_context);

        // Both overlap should score higher than goal-only.
        assert!(
            score_both.value > score_goal_only.value,
            "both={}, goal_only={}",
            score_both.value,
            score_goal_only.value
        );
    }

    #[test]
    fn test_score_formula_trigger_bonus() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let context = ProofContext {
            goal_symbols: ["f".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };

        let no_trigger = make_formula("q1", &["x"], "f(x)", 0);
        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let with_trigger = make_formula_with_triggers("q2", &["x"], "f(x)", vec![trigger]);

        let score_no = scheduler.score_formula(&no_trigger, &context);
        let score_yes = scheduler.score_formula(&with_trigger, &context);

        // Trigger bonus multiplies by 1.1.
        assert!(
            score_yes.value > score_no.value,
            "with_trigger={}, no_trigger={}",
            score_yes.value,
            score_no.value
        );
    }

    #[test]
    fn test_score_formula_empty_body_returns_zero() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "", 0);
        let context = ProofContext {
            goal_symbols: ["f".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };
        let score = scheduler.score_formula(&formula, &context);
        assert!(
            score.value.abs() < f64::EPSILON,
            "empty body should score 0"
        );
    }

    #[test]
    fn test_score_formula_numeric_only_body_returns_zero() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        // Body is "123 + 456" which has no symbol tokens (all numeric).
        let formula = make_formula("q1", &["x"], "123 + 456", 0);
        let context = ProofContext {
            goal_symbols: ["f".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };
        let score = scheduler.score_formula(&formula, &context);
        assert!(
            score.value.abs() < f64::EPSILON,
            "numeric-only body should score 0"
        );
    }

    #[test]
    fn test_score_formula_no_overlap_returns_zero() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "alpha(x)", 0);
        let context = ProofContext {
            goal_symbols: ["beta".to_owned()].into_iter().collect(),
            assertion_symbols: ["gamma".to_owned()].into_iter().collect(),
        };
        let score = scheduler.score_formula(&formula, &context);
        // "alpha" and "x" don't overlap with "beta" or "gamma".
        assert!(
            score.value.abs() < f64::EPSILON,
            "no overlap should score 0, got {}",
            score.value
        );
    }

    #[test]
    fn test_relevancy_filter_passes_relevant_formula() {
        let config = SchedulerConfig {
            relevancy_filter: true,
            relevancy_threshold: 0.1,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let formula = make_formula_with_triggers("q1", &["x"], "f(x) + g(x)", vec![trigger]);

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let history = ConflictHistory::default();
        let context = ProofContext {
            goal_symbols: ["f".to_owned(), "g".to_owned()].into_iter().collect(),
            assertion_symbols: HashSet::new(),
        };

        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        assert!(
            plan.remaining() > 0,
            "relevant formula should not be filtered"
        );
    }

    // ======================================================================
    // Extended tests: edge cases - no triggers, conflicting triggers, nested
    // ======================================================================

    #[test]
    fn test_no_triggers_no_bound_vars_produces_no_candidates() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        // Formula with no triggers AND no bound vars => no ground-term fallback.
        let formula = make_formula("q1", &[], "true", 0);

        let mut idx = TermIndex::new();
        idx.add_term("a");
        idx.add_term("b");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        assert_eq!(plan.remaining(), 0);
    }

    #[test]
    fn test_no_triggers_with_bound_vars_uses_ground_terms() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x", "y"], "x + y > 0", 0);

        let mut idx = TermIndex::new();
        idx.add_term("1");
        idx.add_term("2");
        idx.add_term("3");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        // Ground-term fallback binds first variable to each term => 3 candidates.
        assert_eq!(plan.remaining(), 3);
    }

    #[test]
    fn test_ground_term_candidates_use_ground_term_source() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let formula = make_formula("q1", &["x"], "x > 0", 0);

        let mut idx = TermIndex::new();
        idx.add_term("42");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        assert_eq!(plan.remaining(), 1);

        // Drain the plan and check source.
        let mut budget = InstantiationBudget::new(100, 100, 100);
        let mut mplan = plan;
        let round = mplan.execute_round(&mut budget);
        assert_eq!(round.len(), 1);
        assert_eq!(round[0].source, InstantiationSource::GroundTerm);
    }

    #[test]
    fn test_ground_term_fallback_score_is_halved() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let formula_trig = make_formula_with_triggers("q1", &["x"], "f(x) > 0", vec![trigger]);
        let formula_no_trig = make_formula("q2", &["x"], "f(x) > 0", 0);

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan_trig = scheduler.plan(&[formula_trig], &idx, &history, &context);
        let plan_no_trig = scheduler.plan(&[formula_no_trig], &idx, &history, &context);

        // Both produce 1 candidate, but ground-term fallback has 0.5x score multiplier.
        assert_eq!(plan_trig.remaining(), 1);
        assert_eq!(plan_no_trig.remaining(), 1);
    }

    #[test]
    fn test_multiple_triggers_on_same_formula() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let t1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let t2 = make_trigger("g", &[PatternArg::BoundVar("x".to_owned())]);
        let formula = make_formula_with_triggers("q1", &["x"], "f(x) + g(x)", vec![t1, t2]);

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(b)");
        idx.add_term("g(c)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        // 2 from trigger f + 1 from trigger g = 3.
        assert_eq!(plan.remaining(), 3);
    }

    #[test]
    fn test_empty_term_index_produces_no_candidates() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let trigger = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let formula = make_formula_with_triggers("q1", &["x"], "f(x)", vec![trigger]);

        let idx = TermIndex::new();
        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[formula], &idx, &history, &context);
        assert_eq!(plan.remaining(), 0);
    }

    #[test]
    fn test_no_formulas_produces_empty_plan() {
        let config = SchedulerConfig::default();
        let scheduler = QuantifierScheduler::new(config);

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let plan = scheduler.plan(&[], &idx, &history, &context);
        assert_eq!(plan.remaining(), 0);
    }

    // ======================================================================
    // Extended tests: conflict history impact on scoring
    // ======================================================================

    #[test]
    fn test_conflict_history_boosts_useful_formulas() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let t1 = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);
        let t2 = make_trigger("g", &[PatternArg::BoundVar("x".to_owned())]);
        let f1 = make_formula_with_triggers("useful", &["x"], "f(x)", vec![t1]);
        let f2 = make_formula_with_triggers("useless", &["x"], "g(x)", vec![t2]);

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("g(a)");

        let mut history = ConflictHistory::default();
        // Record "useful" as very successful.
        let candidate_useful = InstantiationCandidate {
            formula_id: FormulaId("useful".to_owned()),
            substitution: HashMap::new(),
            score: 1.0,
            source: InstantiationSource::EMatching,
        };
        for _ in 0..10 {
            history.record(&candidate_useful, true);
        }
        // Record "useless" as never helpful.
        let candidate_useless = InstantiationCandidate {
            formula_id: FormulaId("useless".to_owned()),
            substitution: HashMap::new(),
            score: 1.0,
            source: InstantiationSource::EMatching,
        };
        for _ in 0..10 {
            history.record(&candidate_useless, false);
        }

        let context = ProofContext::default();
        let plan = scheduler.plan(&[f1, f2], &idx, &history, &context);
        assert_eq!(plan.remaining(), 2);

        // Execute round: the "useful" candidate should come first (higher score).
        let mut budget = InstantiationBudget::new(100, 100, 100);
        let mut mplan = plan;
        let round = mplan.execute_round(&mut budget);
        assert_eq!(round[0].formula_id.0, "useful");
    }

    #[test]
    fn test_conflict_history_all_zeros_uses_neutral_prior() {
        let history = ConflictHistory::default();
        // Unknown formula gets neutral 0.5 prior.
        assert!((history.usefulness_ratio("never_seen") - 0.5).abs() < f64::EPSILON);
    }

    // ======================================================================
    // Extended tests: budget edge cases
    // ======================================================================

    #[test]
    fn test_budget_zero_per_formula() {
        let mut budget = InstantiationBudget::new(0, 100, 10);
        let granted = budget.allocate("f1", 5);
        assert_eq!(granted, 0);
        assert_eq!(budget.remaining(), 100);
    }

    #[test]
    fn test_budget_zero_total() {
        let mut budget = InstantiationBudget::new(100, 0, 10);
        let granted = budget.allocate("f1", 5);
        assert_eq!(granted, 0);
    }

    #[test]
    fn test_budget_allocate_zero_count() {
        let mut budget = InstantiationBudget::new(100, 100, 10);
        let granted = budget.allocate("f1", 0);
        assert_eq!(granted, 0);
        assert_eq!(budget.remaining(), 100);
    }

    #[test]
    fn test_budget_multiple_formulas_share_total() {
        let mut budget = InstantiationBudget::new(5, 8, 100);
        assert_eq!(budget.allocate("f1", 3), 3);
        assert_eq!(budget.allocate("f2", 3), 3);
        assert_eq!(budget.allocate("f3", 3), 2); // only 2 of total remain
        assert_eq!(budget.remaining(), 0);
    }

    #[test]
    fn test_budget_escalation_doubles_all_limits() {
        let mut budget = InstantiationBudget::new(10, 100, 20);
        budget.escalate();
        assert_eq!(budget.max_per_formula, 20);
        assert_eq!(budget.max_total, 200);
        assert_eq!(budget.per_round_limit, 40);
        budget.escalate();
        assert_eq!(budget.max_per_formula, 40);
        assert_eq!(budget.max_total, 400);
        assert_eq!(budget.per_round_limit, 80);
    }

    #[test]
    fn test_budget_escalation_cap_prevents_overflow() {
        let cap = usize::MAX / 2;
        let mut budget = InstantiationBudget::new(cap, cap, cap);
        budget.escalate();
        // Should be capped at usize::MAX / 2 (not overflow).
        assert!(budget.max_per_formula <= cap);
        assert!(budget.max_total <= cap);
        assert!(budget.per_round_limit <= cap);
    }

    #[test]
    fn test_budget_allocated_for_unknown_formula_is_zero() {
        let budget = InstantiationBudget::new(10, 100, 10);
        assert_eq!(budget.allocated_for("never_allocated"), 0);
    }

    // ======================================================================
    // Extended tests: plan multi-round execution
    // ======================================================================

    #[test]
    fn test_plan_empty_no_candidates() {
        let plan = InstantiationPlan::new(vec![]);
        assert_eq!(plan.remaining(), 0);
        assert_eq!(plan.current_round(), 0);
    }

    #[test]
    fn test_plan_multiple_rounds() {
        let candidates: Vec<_> = (0..6)
            .map(|i| InstantiationCandidate {
                formula_id: FormulaId(format!("f{i}")),
                substitution: HashMap::new(),
                score: (6 - i) as f64,
                source: InstantiationSource::EMatching,
            })
            .collect();

        let mut plan = InstantiationPlan::new(candidates);
        // Per-round limit = 2, per-formula = 100, total = 100.
        let mut budget = InstantiationBudget::new(100, 100, 2);

        let r1 = plan.execute_round(&mut budget);
        assert_eq!(r1.len(), 2);
        assert_eq!(plan.current_round(), 1);
        assert_eq!(plan.remaining(), 4);

        let r2 = plan.execute_round(&mut budget);
        assert_eq!(r2.len(), 2);
        assert_eq!(plan.current_round(), 2);
        assert_eq!(plan.remaining(), 2);

        let r3 = plan.execute_round(&mut budget);
        assert_eq!(r3.len(), 2);
        assert_eq!(plan.current_round(), 3);
        assert_eq!(plan.remaining(), 0);

        // Fourth round: no candidates left.
        let r4 = plan.execute_round(&mut budget);
        assert!(r4.is_empty());
        assert_eq!(plan.current_round(), 4);
    }

    #[test]
    fn test_plan_total_budget_exhaustion_mid_round() {
        let candidates: Vec<_> = (0..5)
            .map(|i| InstantiationCandidate {
                formula_id: FormulaId(format!("f{i}")),
                substitution: HashMap::new(),
                score: 1.0,
                source: InstantiationSource::EMatching,
            })
            .collect();

        let mut plan = InstantiationPlan::new(candidates);
        // Total budget = 3 but per-round limit is large.
        let mut budget = InstantiationBudget::new(100, 3, 100);

        let r1 = plan.execute_round(&mut budget);
        assert_eq!(r1.len(), 3);
        assert_eq!(budget.remaining(), 0);

        // Second round: budget exhausted.
        let r2 = plan.execute_round(&mut budget);
        assert!(r2.is_empty());
    }

    #[test]
    fn test_plan_nan_score_handled() {
        // NaN scores should not cause panics; treated as lowest priority.
        let candidates = vec![
            InstantiationCandidate {
                formula_id: FormulaId("normal".to_owned()),
                substitution: HashMap::new(),
                score: 1.0,
                source: InstantiationSource::EMatching,
            },
            InstantiationCandidate {
                formula_id: FormulaId("nan".to_owned()),
                substitution: HashMap::new(),
                score: f64::NAN,
                source: InstantiationSource::Heuristic,
            },
        ];

        let mut plan = InstantiationPlan::new(candidates);
        let mut budget = InstantiationBudget::new(100, 100, 100);
        let round = plan.execute_round(&mut budget);
        assert_eq!(round.len(), 2);
        // The normal one should come first.
        assert_eq!(round[0].formula_id.0, "normal");
    }

    // ======================================================================
    // Extended tests: parse_term_args edge cases
    // ======================================================================

    #[test]
    fn test_parse_term_args_empty_parens() {
        let args = parse_term_args("f()");
        assert!(args.is_empty());
    }

    #[test]
    fn test_parse_term_args_single_arg() {
        let args = parse_term_args("f(x)");
        assert_eq!(args, vec!["x"]);
    }

    #[test]
    fn test_parse_term_args_deeply_nested() {
        let args = parse_term_args("f(g(h(a, b)), c)");
        assert_eq!(args, vec!["g(h(a, b))", "c"]);
    }

    #[test]
    fn test_parse_term_args_triple_nesting() {
        let args = parse_term_args("outer(a(b(c(d))), x)");
        assert_eq!(args, vec!["a(b(c(d)))", "x"]);
    }

    #[test]
    fn test_parse_term_args_no_parens() {
        let args = parse_term_args("constant");
        assert!(args.is_empty());
    }

    #[test]
    fn test_parse_term_args_whitespace_handling() {
        let args = parse_term_args("f( a , b , c )");
        assert_eq!(args, vec!["a", "b", "c"]);
    }

    // ======================================================================
    // Extended tests: extract_symbols edge cases
    // ======================================================================

    #[test]
    fn test_extract_symbols_underscores() {
        let syms = extract_symbols("my_func(a_var)");
        assert!(syms.contains("my_func"));
        assert!(syms.contains("a_var"));
    }

    #[test]
    fn test_extract_symbols_mixed_alpha_numeric() {
        let syms = extract_symbols("x1 + y2");
        assert!(syms.contains("x1"));
        assert!(syms.contains("y2"));
    }

    #[test]
    fn test_extract_symbols_empty_string() {
        let syms = extract_symbols("");
        assert!(syms.is_empty());
    }

    #[test]
    fn test_extract_symbols_only_operators() {
        let syms = extract_symbols("+ - * / > < =");
        assert!(syms.is_empty());
    }

    #[test]
    fn test_extract_symbols_mixed_numbers_and_names() {
        let syms = extract_symbols("f(42, x, 0, y)");
        assert!(syms.contains("f"));
        assert!(syms.contains("x"));
        assert!(syms.contains("y"));
        assert!(!syms.contains("42"));
        assert!(!syms.contains("0"));
    }

    // ======================================================================
    // Extended tests: merge_substitutions edge cases
    // ======================================================================

    #[test]
    fn test_merge_substitutions_both_empty() {
        let a: HashMap<String, String> = HashMap::new();
        let b: HashMap<String, String> = HashMap::new();
        let merged = merge_substitutions(&a, &b).unwrap();
        assert!(merged.is_empty());
    }

    #[test]
    fn test_merge_substitutions_one_empty() {
        let mut a = HashMap::new();
        a.insert("x".to_owned(), "1".to_owned());
        let b: HashMap<String, String> = HashMap::new();
        let merged = merge_substitutions(&a, &b).unwrap();
        assert_eq!(merged.len(), 1);
        assert_eq!(merged.get("x").unwrap(), "1");
    }

    #[test]
    fn test_merge_substitutions_overlapping_consistent() {
        let mut a = HashMap::new();
        a.insert("x".to_owned(), "val".to_owned());
        let mut b = HashMap::new();
        b.insert("x".to_owned(), "val".to_owned()); // same value
        b.insert("y".to_owned(), "other".to_owned());
        let merged = merge_substitutions(&a, &b).unwrap();
        assert_eq!(merged.len(), 2);
        assert_eq!(merged.get("x").unwrap(), "val");
        assert_eq!(merged.get("y").unwrap(), "other");
    }

    #[test]
    fn test_merge_substitutions_multiple_conflicts() {
        let mut a = HashMap::new();
        a.insert("x".to_owned(), "1".to_owned());
        a.insert("y".to_owned(), "2".to_owned());
        let mut b = HashMap::new();
        b.insert("x".to_owned(), "1".to_owned()); // consistent
        b.insert("y".to_owned(), "3".to_owned()); // conflict
        assert!(merge_substitutions(&a, &b).is_none());
    }

    // ======================================================================
    // Extended tests: term index
    // ======================================================================

    #[test]
    fn test_term_index_matching_with_function_pattern() {
        let mut idx = TermIndex::new();
        idx.add_term("select(arr, i)");
        idx.add_term("select(arr, j)");
        idx.add_term("store(arr, i, v)");

        let matches = idx.matching_terms("select(anything)");
        assert_eq!(matches.len(), 2);
    }

    #[test]
    fn test_term_index_all_terms_preserves_order() {
        let mut idx = TermIndex::new();
        idx.add_term("a");
        idx.add_term("b");
        idx.add_term("c");
        let terms = idx.all_terms();
        assert_eq!(terms, &["a", "b", "c"]);
    }

    #[test]
    fn test_term_index_duplicate_terms() {
        let mut idx = TermIndex::new();
        idx.add_term("f(a)");
        idx.add_term("f(a)");
        // Duplicates are stored separately.
        assert_eq!(idx.len(), 2);
        assert_eq!(idx.matching_terms("f").len(), 2);
    }

    #[test]
    fn test_term_index_many_symbols() {
        let mut idx = TermIndex::new();
        for i in 0..100 {
            idx.add_term(&format!("sym{i}(arg)"));
        }
        assert_eq!(idx.len(), 100);
        // Each symbol is unique, so matching any one returns exactly 1.
        let matches = idx.matching_terms("sym42");
        assert_eq!(matches.len(), 1);
    }

    // ======================================================================
    // Extended tests: InstantiationStats
    // ======================================================================

    #[test]
    fn test_stats_usefulness_ratio_all_wasted() {
        let mut stats = InstantiationStats::default();
        stats.record("f1", false);
        stats.record("f1", false);
        assert!((stats.usefulness_ratio() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_stats_per_formula_independent() {
        let mut stats = InstantiationStats::default();
        stats.record("f1", true);
        stats.record("f1", true);
        stats.record("f2", false);
        assert_eq!(*stats.per_formula.get("f1").unwrap(), 2);
        assert_eq!(*stats.per_formula.get("f2").unwrap(), 1);
        assert_eq!(stats.total, 3);
    }

    // ======================================================================
    // Extended tests: RelevancyScore
    // ======================================================================

    #[test]
    fn test_relevancy_score_mid_value() {
        let score = RelevancyScore::new(0.75);
        assert!((score.value - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_relevancy_score_nan_clamps_to_zero() {
        // f64::NAN.clamp(0.0, 1.0) returns NaN in Rust, but we verify the contract.
        let score = RelevancyScore::new(0.0);
        assert!(score.value.abs() < f64::EPSILON);
    }

    #[test]
    fn test_relevancy_score_zero_constant() {
        assert!(RelevancyScore::ZERO.value.abs() < f64::EPSILON);
    }

    // ======================================================================
    // Extended tests: SchedulerConfig defaults
    // ======================================================================

    #[test]
    fn test_scheduler_config_defaults() {
        let config = SchedulerConfig::default();
        assert_eq!(config.initial_budget, 10);
        assert!((config.escalation_factor - 2.0).abs() < f64::EPSILON);
        assert_eq!(config.max_rounds, 8);
        assert!(config.relevancy_filter);
        assert!((config.relevancy_threshold - 0.1).abs() < f64::EPSILON);
    }

    // ======================================================================
    // Extended tests: extract_top_symbol edge cases
    // ======================================================================

    #[test]
    fn test_extract_top_symbol_nested() {
        assert_eq!(extract_top_symbol("f(g(x))"), "f");
    }

    #[test]
    fn test_extract_top_symbol_empty_string() {
        assert_eq!(extract_top_symbol(""), "");
    }

    #[test]
    fn test_extract_top_symbol_paren_at_start() {
        // Degenerate: "(x)" has symbol "" (empty before paren).
        assert_eq!(extract_top_symbol("(x)"), "");
    }

    // ======================================================================
    // Extended tests: full integration - scheduler + plan + budget
    // ======================================================================

    #[test]
    fn test_full_pipeline_trigger_to_execution() {
        // End-to-end: create formulas with triggers, build a plan, execute rounds.
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let t1 = make_trigger(
            "select",
            &[
                PatternArg::BoundVar("a".to_owned()),
                PatternArg::BoundVar("i".to_owned()),
            ],
        );
        let formula = make_formula_with_triggers(
            "array_axiom",
            &["a", "i"],
            "select(store(a, i, v), i) == v",
            vec![t1],
        );

        let mut idx = TermIndex::new();
        idx.add_term("select(arr1, idx1)");
        idx.add_term("select(arr2, idx2)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let mut plan = scheduler.plan(&[formula], &idx, &history, &context);
        assert_eq!(plan.remaining(), 2);

        let mut budget = InstantiationBudget::new(10, 100, 10);
        let round = plan.execute_round(&mut budget);
        assert_eq!(round.len(), 2);
        assert_eq!(plan.remaining(), 0);

        // Verify substitutions are correct.
        for candidate in &round {
            assert_eq!(candidate.formula_id.0, "array_axiom");
            assert!(candidate.substitution.contains_key("a"));
            assert!(candidate.substitution.contains_key("i"));
        }
    }

    #[test]
    fn test_full_pipeline_mixed_formulas_depth_ordering() {
        let config = SchedulerConfig {
            relevancy_filter: false,
            ..SchedulerConfig::default()
        };
        let scheduler = QuantifierScheduler::new(config);

        let t = make_trigger("f", &[PatternArg::BoundVar("x".to_owned())]);

        let mut shallow = make_formula_with_triggers("shallow", &["x"], "f(x)", vec![t.clone()]);
        shallow.depth = 0;

        let mut deep = make_formula_with_triggers("deep", &["x"], "f(x)", vec![t]);
        deep.depth = 10;

        let mut idx = TermIndex::new();
        idx.add_term("f(a)");

        let history = ConflictHistory::default();
        let context = ProofContext::default();

        let mut plan = scheduler.plan(&[shallow, deep], &idx, &history, &context);
        assert_eq!(plan.remaining(), 2);

        let mut budget = InstantiationBudget::new(100, 100, 100);
        let round = plan.execute_round(&mut budget);

        // Shallow should be first (higher score due to lower depth penalty).
        assert_eq!(round[0].formula_id.0, "shallow");
        assert_eq!(round[1].formula_id.0, "deep");
        assert!(round[0].score > round[1].score);
    }

    #[test]
    fn test_plan_per_formula_cap_spreads_across_formulas() {
        // When per-formula cap is 1 but we have 3 formulas each with 1 candidate,
        // all 3 should be emitted.
        let candidates: Vec<_> = (0..3)
            .map(|i| InstantiationCandidate {
                formula_id: FormulaId(format!("f{i}")),
                substitution: HashMap::new(),
                score: 1.0,
                source: InstantiationSource::EMatching,
            })
            .collect();

        let mut plan = InstantiationPlan::new(candidates);
        let mut budget = InstantiationBudget::new(1, 100, 100);
        let round = plan.execute_round(&mut budget);
        assert_eq!(round.len(), 3);
    }

    #[test]
    fn test_plan_per_formula_cap_skips_excess_same_formula() {
        // 5 candidates all for same formula, cap=2 => only 2 emitted, 3 skipped.
        let candidates: Vec<_> = (0..5)
            .map(|i| InstantiationCandidate {
                formula_id: FormulaId("same".to_owned()),
                substitution: HashMap::new(),
                score: (5 - i) as f64,
                source: InstantiationSource::EMatching,
            })
            .collect();

        let mut plan = InstantiationPlan::new(candidates);
        let mut budget = InstantiationBudget::new(2, 100, 100);
        let round = plan.execute_round(&mut budget);
        assert_eq!(round.len(), 2);
        // The remaining 3 were popped but not emitted (budget denied).
        assert_eq!(plan.remaining(), 0);
    }
}
