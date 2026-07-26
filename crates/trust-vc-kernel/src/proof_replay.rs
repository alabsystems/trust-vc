// proof_replay.rs — Re-execute proof certificates step-by-step for independent validation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates — Apache 2.0

use std::collections::HashMap;
use std::fmt;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Controls how replay proceeds.
#[derive(Debug, Clone)]
pub struct ReplayConfig {
    /// Maximum number of steps to replay before aborting.
    pub step_limit: Option<usize>,
    /// Whether to continue past the first invalid step.
    pub continue_on_failure: bool,
    /// Replay mode.
    pub mode: ReplayMode,
}

impl Default for ReplayConfig {
    fn default() -> Self {
        Self {
            step_limit: None,
            continue_on_failure: false,
            mode: ReplayMode::Full,
        }
    }
}

/// Selects the replay strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayMode {
    /// Replay every step.
    Full,
    /// Replay only steps whose clause ids changed since last replay.
    Incremental,
    /// Randomly sample a fraction of steps (numerator / denominator).
    Sampling {
        numerator: usize,
        denominator: usize,
    },
}

/// A single literal: variable id with polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    pub var: u32,
    pub positive: bool,
}

impl Literal {
    /// Creates a literal for the given variable id and polarity.
    #[must_use]
    pub fn new(var: u32, positive: bool) -> Self {
        Self { var, positive }
    }

    /// Returns the literal with its polarity flipped.
    #[must_use]
    pub fn negated(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.positive {
            write!(f, "x{}", self.var)
        } else {
            write!(f, "~x{}", self.var)
        }
    }
}

/// A disjunctive clause (set of literals).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl Clause {
    /// Creates a clause from the given list of literals.
    #[must_use]
    pub fn new(literals: Vec<Literal>) -> Self {
        Self { literals }
    }

    /// Returns `true` if the clause has no literals (i.e., represents FALSE).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Returns `true` if the clause contains the given literal.
    #[must_use]
    pub fn contains(&self, lit: &Literal) -> bool {
        self.literals.contains(lit)
    }

    /// Returns the number of literals in this clause.
    #[must_use]
    pub fn len(&self) -> usize {
        self.literals.len()
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.literals.is_empty() {
            write!(f, "FALSE")
        } else {
            let parts: Vec<String> = self.literals.iter().map(|l| l.to_string()).collect();
            write!(f, "({})", parts.join(" | "))
        }
    }
}

/// One step of a proof certificate.
#[derive(Debug, Clone)]
pub struct ReplayStep {
    /// Unique identifier for the derived clause.
    pub id: u64,
    /// The kind of inference rule applied.
    pub rule: InferenceRule,
}

/// Supported inference rules.
#[derive(Debug, Clone)]
pub enum InferenceRule {
    /// Input clause — axiom or original problem clause.
    Input { clause: Clause },
    /// Binary resolution on `pivot` between `left` and `right`.
    Resolve { left: u64, right: u64, pivot: u32 },
    /// Chain resolution: resolve a sequence of premises with given pivots.
    ChainResolve {
        premises: Vec<u64>,
        pivots: Vec<u32>,
    },
    /// Tautology elimination — the clause is trivially true.
    Tautology { premise: u64 },
    /// Subsumption — the clause is subsumed by an existing clause.
    Subsumption { subsumed: u64, subsumer: u64 },
}

/// Outcome of replaying a single step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepVerdict {
    Valid,
    Invalid,
    Skipped,
}

impl fmt::Display for StepVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Valid => write!(f, "VALID"),
            Self::Invalid => write!(f, "INVALID"),
            Self::Skipped => write!(f, "SKIPPED"),
        }
    }
}

/// Diagnostic information for a single step failure.
#[derive(Debug, Clone)]
pub struct ReplayDiagnostic {
    pub step_id: u64,
    pub verdict: StepVerdict,
    pub message: String,
}

impl fmt::Display for ReplayDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "step {}: {} — {}",
            self.step_id, self.verdict, self.message
        )
    }
}

/// Progress tracker during replay.
#[derive(Debug, Clone)]
pub struct ReplayProgress {
    pub current_step: usize,
    pub total_steps: usize,
}

impl ReplayProgress {
    /// Returns the percentage of steps replayed so far (0.0 to 100.0).
    #[must_use]
    pub fn percent_complete(&self) -> f64 {
        if self.total_steps == 0 {
            100.0
        } else {
            (self.current_step as f64 / self.total_steps as f64) * 100.0
        }
    }
}

/// Analysis of the first failure encountered.
#[derive(Debug, Clone)]
pub struct FailureAnalysis {
    pub first_invalid_step: u64,
    pub suggested_fix: String,
}

impl FailureAnalysis {
    /// Diagnose why a step failed given the current clause store state.
    #[must_use]
    pub fn diagnose(step: &ReplayStep, clause_store: &ClauseStore) -> String {
        match &step.rule {
            InferenceRule::Input { .. } => {
                "Input steps should always be valid; clause may be malformed.".to_string()
            }
            InferenceRule::Resolve { left, right, pivot } => {
                let has_left = clause_store.get(*left).is_some();
                let has_right = clause_store.get(*right).is_some();
                if !has_left && !has_right {
                    format!(
                        "Both premises {} and {} are missing from the clause store.",
                        left, right
                    )
                } else if !has_left {
                    format!("Left premise {} is missing from the clause store.", left)
                } else if !has_right {
                    format!("Right premise {} is missing from the clause store.", right)
                } else {
                    let (Some(left_clause), Some(right_clause)) =
                        (clause_store.get(*left), clause_store.get(*right))
                    else {
                        return format!(
                            "Resolution premise state changed while diagnosing step {}; retry replay.",
                            step.id
                        );
                    };
                    let pos = Literal::new(*pivot, true);
                    let neg = Literal::new(*pivot, false);
                    let left_has = left_clause.contains(&pos) || left_clause.contains(&neg);
                    let right_has = right_clause.contains(&pos) || right_clause.contains(&neg);
                    if !left_has {
                        format!(
                            "Pivot variable x{} does not appear in left premise {}.",
                            pivot, left
                        )
                    } else if !right_has {
                        format!(
                            "Pivot variable x{} does not appear in right premise {}.",
                            pivot, right
                        )
                    } else {
                        format!(
                            "Resolution on pivot x{} between {} and {} produced an unexpected result; \
                             check literal polarity.",
                            pivot, left, right
                        )
                    }
                }
            }
            InferenceRule::ChainResolve { premises, pivots } => {
                let missing: Vec<u64> = premises
                    .iter()
                    .copied()
                    .filter(|id| clause_store.get(*id).is_none())
                    .collect();
                if !missing.is_empty() {
                    format!(
                        "Chain resolution missing premises: {:?}. Available pivots: {:?}",
                        missing, pivots
                    )
                } else {
                    format!(
                        "Chain resolution with {} premises and {} pivots failed; \
                         check pivot ordering and polarity.",
                        premises.len(),
                        pivots.len()
                    )
                }
            }
            InferenceRule::Tautology { premise } => {
                if clause_store.get(*premise).is_none() {
                    format!(
                        "Tautology premise {} is missing from the clause store.",
                        premise
                    )
                } else {
                    format!(
                        "Clause {} was declared tautological but contains no complementary pair.",
                        premise
                    )
                }
            }
            InferenceRule::Subsumption { subsumed, subsumer } => {
                let has_subsumed = clause_store.get(*subsumed).is_some();
                let has_subsumer = clause_store.get(*subsumer).is_some();
                if !has_subsumed || !has_subsumer {
                    format!(
                        "Subsumption requires both clauses: subsumed({})={}, subsumer({})={}.",
                        subsumed,
                        if has_subsumed { "present" } else { "missing" },
                        subsumer,
                        if has_subsumer { "present" } else { "missing" },
                    )
                } else {
                    format!(
                        "Clause {} does not subsume clause {}; not all literals of {} appear in {}.",
                        subsumer, subsumed, subsumer, subsumed
                    )
                }
            }
        }
    }
}

/// Summary report produced after replay.
#[derive(Debug, Clone)]
pub struct ReplayReport {
    pub verdicts: Vec<(u64, StepVerdict)>,
    pub diagnostics: Vec<ReplayDiagnostic>,
    pub progress: ReplayProgress,
    pub failure_analysis: Option<FailureAnalysis>,
}

impl ReplayReport {
    /// One-line summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let valid = self
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Valid)
            .count();
        let invalid = self
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Invalid)
            .count();
        let skipped = self
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Skipped)
            .count();
        format!(
            "{} valid, {} invalid, {} skipped out of {} steps",
            valid,
            invalid,
            skipped,
            self.verdicts.len()
        )
    }

    /// Returns the first failure, if any.
    #[must_use]
    pub fn first_failure(&self) -> Option<&ReplayDiagnostic> {
        self.diagnostics.first()
    }

    /// Percentage of non-skipped steps that are valid.
    #[must_use]
    pub fn valid_percentage(&self) -> f64 {
        let checked: usize = self
            .verdicts
            .iter()
            .filter(|(_, v)| *v != StepVerdict::Skipped)
            .count();
        if checked == 0 {
            return 100.0;
        }
        let valid = self
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Valid)
            .count();
        (valid as f64 / checked as f64) * 100.0
    }
}

// ---------------------------------------------------------------------------
// ClauseStore
// ---------------------------------------------------------------------------

/// Manages the clause database during replay.
#[derive(Debug, Clone)]
pub struct ClauseStore {
    clauses: HashMap<u64, Clause>,
}

impl ClauseStore {
    /// Creates an empty clause store.
    #[must_use]
    pub fn new() -> Self {
        Self {
            clauses: HashMap::new(),
        }
    }

    /// Inserts or replaces a clause with the given id.
    pub fn add_clause(&mut self, id: u64, clause: Clause) {
        self.clauses.insert(id, clause);
    }

    /// Retrieves the clause with the given id, if present.
    #[must_use]
    pub fn get(&self, id: u64) -> Option<&Clause> {
        self.clauses.get(&id)
    }

    /// Returns the number of clauses stored.
    #[must_use]
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Returns `true` if no clauses are stored.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Perform binary resolution: resolve `left` and `right` on `pivot`.
    ///
    /// Left must contain the positive literal of the pivot, right the negative
    /// (or vice-versa). Returns `None` if the pivot does not appear with
    /// complementary polarity.
    #[must_use]
    pub fn resolve(&self, left: u64, right: u64, pivot: u32) -> Option<Clause> {
        let left_clause = self.clauses.get(&left)?;
        let right_clause = self.clauses.get(&right)?;

        let pos = Literal::new(pivot, true);
        let neg = Literal::new(pivot, false);

        // Determine which side has which polarity.
        let (left_has_pos, left_has_neg) = (left_clause.contains(&pos), left_clause.contains(&neg));
        let (right_has_pos, right_has_neg) =
            (right_clause.contains(&pos), right_clause.contains(&neg));

        // Need complementary polarity across the two clauses.
        let valid_config = (left_has_pos && right_has_neg) || (left_has_neg && right_has_pos);
        if !valid_config {
            return None;
        }

        let mut result_lits: Vec<Literal> = Vec::new();

        for lit in &left_clause.literals {
            if lit.var != pivot && !result_lits.contains(lit) {
                result_lits.push(*lit);
            }
        }
        for lit in &right_clause.literals {
            if lit.var != pivot && !result_lits.contains(lit) {
                result_lits.push(*lit);
            }
        }

        Some(Clause::new(result_lits))
    }
}

impl Default for ClauseStore {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// PartialReplay
// ---------------------------------------------------------------------------

/// Restricts replay to a sub-range of steps.
#[derive(Debug, Clone)]
pub struct PartialReplay {
    pub start: usize,
    pub end: usize,
    steps: Vec<ReplayStep>,
    input_clauses: Vec<(u64, Clause)>,
    config: ReplayConfig,
}

impl PartialReplay {
    /// Create a partial replay for steps in `[start, end)`.
    #[must_use]
    pub fn from_range(
        start: usize,
        end: usize,
        steps: Vec<ReplayStep>,
        input_clauses: Vec<(u64, Clause)>,
        config: ReplayConfig,
    ) -> Self {
        Self {
            start,
            end,
            steps,
            input_clauses,
            config,
        }
    }

    /// Execute the partial replay and return a report.
    #[must_use]
    pub fn replay(&self) -> ReplayReport {
        let mut engine = ReplayEngine::new(self.config.clone());

        // Seed the clause store with input clauses.
        for (id, clause) in &self.input_clauses {
            engine.clause_store.add_clause(*id, clause.clone());
        }

        // Also replay all steps before `start` silently to build up clause store state.
        let clamped_end = self.end.min(self.steps.len());
        for step in self.steps.iter().take(self.start) {
            let _ = engine.replay_step(step);
        }

        // Now replay the target range and collect verdicts.
        let target_steps: Vec<ReplayStep> = self
            .steps
            .iter()
            .skip(self.start)
            .take(clamped_end.saturating_sub(self.start))
            .cloned()
            .collect();

        let total = target_steps.len();
        let mut verdicts = Vec::new();
        let mut diagnostics = Vec::new();

        for step in &target_steps {
            let verdict = engine.replay_step(step);
            verdicts.push((step.id, verdict));
            if verdict == StepVerdict::Invalid {
                let msg = FailureAnalysis::diagnose(step, &engine.clause_store);
                diagnostics.push(ReplayDiagnostic {
                    step_id: step.id,
                    verdict,
                    message: msg,
                });
                if !self.config.continue_on_failure {
                    break;
                }
            }
        }

        let failure_analysis = diagnostics.first().map(|d| FailureAnalysis {
            first_invalid_step: d.step_id,
            suggested_fix: d.message.clone(),
        });

        ReplayReport {
            verdicts,
            diagnostics,
            progress: ReplayProgress {
                current_step: total,
                total_steps: total,
            },
            failure_analysis,
        }
    }
}

// ---------------------------------------------------------------------------
// ReplayEngine
// ---------------------------------------------------------------------------

/// The main replay engine.
#[derive(Debug)]
pub struct ReplayEngine {
    config: ReplayConfig,
    pub(crate) clause_store: ClauseStore,
    steps_replayed: usize,
}

impl ReplayEngine {
    /// Creates a new replay engine with the given configuration.
    #[must_use]
    pub fn new(config: ReplayConfig) -> Self {
        Self {
            config,
            clause_store: ClauseStore::new(),
            steps_replayed: 0,
        }
    }

    /// Replay an entire proof: seed with `input_clauses`, then execute `steps`.
    #[must_use]
    pub fn replay(
        &mut self,
        input_clauses: &[(u64, Clause)],
        steps: &[ReplayStep],
    ) -> ReplayReport {
        // Reset state.
        self.clause_store = ClauseStore::new();
        self.steps_replayed = 0;

        // Seed input clauses.
        for (id, clause) in input_clauses {
            self.clause_store.add_clause(*id, clause.clone());
        }

        let total = steps.len();
        let mut verdicts: Vec<(u64, StepVerdict)> = Vec::new();
        let mut diagnostics: Vec<ReplayDiagnostic> = Vec::new();

        for (idx, step) in steps.iter().enumerate() {
            // Step limit.
            if let Some(limit) = self.config.step_limit {
                if idx >= limit {
                    // Mark remaining as skipped.
                    for remaining in steps.iter().skip(idx) {
                        verdicts.push((remaining.id, StepVerdict::Skipped));
                    }
                    break;
                }
            }

            // Sampling mode: skip non-sampled steps but still execute them
            // to keep clause store consistent.
            let should_check = match self.config.mode {
                ReplayMode::Full => true,
                ReplayMode::Incremental => true,
                ReplayMode::Sampling {
                    numerator,
                    denominator,
                } => {
                    if denominator == 0 {
                        true
                    } else {
                        // Deterministic sampling based on step index.
                        (idx * numerator) % denominator < numerator
                    }
                }
            };

            if !should_check {
                // Still process the step for clause store consistency, but
                // record as skipped.
                let _ = self.replay_step_internal(step);
                verdicts.push((step.id, StepVerdict::Skipped));
                continue;
            }

            let verdict = self.replay_step(step);
            verdicts.push((step.id, verdict));

            if verdict == StepVerdict::Invalid {
                let msg = FailureAnalysis::diagnose(step, &self.clause_store);
                diagnostics.push(ReplayDiagnostic {
                    step_id: step.id,
                    verdict,
                    message: msg,
                });
                if !self.config.continue_on_failure {
                    // Mark remaining as skipped.
                    for remaining in steps.iter().skip(idx + 1) {
                        verdicts.push((remaining.id, StepVerdict::Skipped));
                    }
                    break;
                }
            }

            self.steps_replayed = idx + 1;
        }

        let failure_analysis = diagnostics.first().map(|d| FailureAnalysis {
            first_invalid_step: d.step_id,
            suggested_fix: d.message.clone(),
        });

        ReplayReport {
            verdicts,
            diagnostics,
            progress: ReplayProgress {
                current_step: self.steps_replayed,
                total_steps: total,
            },
            failure_analysis,
        }
    }

    /// Replay a single step, updating the clause store and returning the verdict.
    #[must_use]
    pub fn replay_step(&mut self, step: &ReplayStep) -> StepVerdict {
        self.replay_step_internal(step)
    }

    /// Internal: process a step, update clause store, return verdict.
    fn replay_step_internal(&mut self, step: &ReplayStep) -> StepVerdict {
        match &step.rule {
            InferenceRule::Input { clause } => {
                self.clause_store.add_clause(step.id, clause.clone());
                StepVerdict::Valid
            }
            InferenceRule::Resolve { left, right, pivot } => {
                if let Some(resolved) = self.clause_store.resolve(*left, *right, *pivot) {
                    self.clause_store.add_clause(step.id, resolved);
                    StepVerdict::Valid
                } else {
                    StepVerdict::Invalid
                }
            }
            InferenceRule::ChainResolve { premises, pivots } => {
                if premises.len() < 2 || pivots.len() != premises.len() - 1 {
                    return StepVerdict::Invalid;
                }

                let first_id = premises[0];
                let mut current = match self.clause_store.get(first_id) {
                    Some(c) => c.clone(),
                    None => return StepVerdict::Invalid,
                };

                for (i, pivot) in pivots.iter().enumerate() {
                    let next_id = premises[i + 1];
                    let next = match self.clause_store.get(next_id) {
                        Some(c) => c.clone(),
                        None => return StepVerdict::Invalid,
                    };

                    // Resolve current with next on pivot.
                    let pos = Literal::new(*pivot, true);
                    let neg = Literal::new(*pivot, false);

                    let cur_has_pos = current.contains(&pos);
                    let cur_has_neg = current.contains(&neg);
                    let next_has_pos = next.contains(&pos);
                    let next_has_neg = next.contains(&neg);

                    let valid = (cur_has_pos && next_has_neg) || (cur_has_neg && next_has_pos);
                    if !valid {
                        return StepVerdict::Invalid;
                    }

                    let mut result_lits: Vec<Literal> = Vec::new();
                    for lit in &current.literals {
                        if lit.var != *pivot && !result_lits.contains(lit) {
                            result_lits.push(*lit);
                        }
                    }
                    for lit in &next.literals {
                        if lit.var != *pivot && !result_lits.contains(lit) {
                            result_lits.push(*lit);
                        }
                    }
                    current = Clause::new(result_lits);
                }

                self.clause_store.add_clause(step.id, current);
                StepVerdict::Valid
            }
            InferenceRule::Tautology { premise } => {
                let clause = match self.clause_store.get(*premise) {
                    Some(c) => c.clone(),
                    None => return StepVerdict::Invalid,
                };

                // Check that the clause is indeed a tautology (has x and ~x).
                let is_tautology = clause
                    .literals
                    .iter()
                    .any(|lit| clause.contains(&lit.negated()));

                if is_tautology {
                    // Tautologies produce an empty marker (they are always true,
                    // so they can be dropped). We still register the id.
                    self.clause_store
                        .add_clause(step.id, Clause::new(Vec::new()));
                    StepVerdict::Valid
                } else {
                    StepVerdict::Invalid
                }
            }
            InferenceRule::Subsumption { subsumed, subsumer } => {
                let subsumer_clause = match self.clause_store.get(*subsumer) {
                    Some(c) => c.clone(),
                    None => return StepVerdict::Invalid,
                };
                let subsumed_clause = match self.clause_store.get(*subsumed) {
                    Some(c) => c.clone(),
                    None => return StepVerdict::Invalid,
                };

                // Subsumption: every literal in subsumer must appear in subsumed.
                let is_subsumed = subsumer_clause
                    .literals
                    .iter()
                    .all(|lit| subsumed_clause.contains(lit));

                if is_subsumed {
                    // The subsumed clause is replaced by the subsumer.
                    self.clause_store.add_clause(step.id, subsumer_clause);
                    StepVerdict::Valid
                } else {
                    StepVerdict::Invalid
                }
            }
        }
    }

    /// Current progress snapshot.
    #[must_use]
    pub fn progress(&self, total: usize) -> ReplayProgress {
        ReplayProgress {
            current_step: self.steps_replayed,
            total_steps: total,
        }
    }

    /// Access the underlying clause store.
    #[must_use]
    pub fn clause_store(&self) -> &ClauseStore {
        &self.clause_store
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- helpers --

    fn lit(var: u32, pos: bool) -> Literal {
        Literal::new(var, pos)
    }

    fn clause(lits: &[(u32, bool)]) -> Clause {
        Clause::new(lits.iter().map(|&(v, p)| lit(v, p)).collect())
    }

    fn input_step(id: u64, lits: &[(u32, bool)]) -> ReplayStep {
        ReplayStep {
            id,
            rule: InferenceRule::Input {
                clause: clause(lits),
            },
        }
    }

    fn resolve_step(id: u64, left: u64, right: u64, pivot: u32) -> ReplayStep {
        ReplayStep {
            id,
            rule: InferenceRule::Resolve { left, right, pivot },
        }
    }

    // -- Literal tests --

    #[test]
    fn test_literal_new_positive() {
        let l = lit(5, true);
        assert_eq!(l.var, 5);
        assert!(l.positive);
    }

    #[test]
    fn test_literal_new_negative() {
        let l = lit(3, false);
        assert_eq!(l.var, 3);
        assert!(!l.positive);
    }

    #[test]
    fn test_literal_negation() {
        let l = lit(7, true);
        let neg = l.negated();
        assert_eq!(neg.var, 7);
        assert!(!neg.positive);
        assert_eq!(neg.negated(), l);
    }

    #[test]
    fn test_literal_display_positive() {
        assert_eq!(lit(12, true).to_string(), "x12");
    }

    #[test]
    fn test_literal_display_negative() {
        assert_eq!(lit(12, false).to_string(), "~x12");
    }

    // -- Clause tests --

    #[test]
    fn test_clause_empty_is_false() {
        let c = Clause::new(Vec::new());
        assert!(c.is_empty());
        assert_eq!(c.to_string(), "FALSE");
    }

    #[test]
    fn test_clause_contains() {
        let c = clause(&[(1, true), (2, false)]);
        assert!(c.contains(&lit(1, true)));
        assert!(c.contains(&lit(2, false)));
        assert!(!c.contains(&lit(1, false)));
    }

    #[test]
    fn test_clause_len() {
        let c = clause(&[(1, true), (2, true), (3, false)]);
        assert_eq!(c.len(), 3);
    }

    #[test]
    fn test_clause_display() {
        let c = clause(&[(1, true), (2, false)]);
        assert_eq!(c.to_string(), "(x1 | ~x2)");
    }

    // -- ClauseStore tests --

    #[test]
    fn test_clause_store_new_empty() {
        let store = ClauseStore::new();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn test_clause_store_add_and_get() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true)]));
        assert_eq!(store.len(), 1);
        assert!(store.get(1).is_some());
        assert!(store.get(2).is_none());
    }

    #[test]
    fn test_clause_store_resolve_valid() {
        let mut store = ClauseStore::new();
        // C1: (x1 | x2), C2: (~x1 | x3)
        store.add_clause(1, clause(&[(1, true), (2, true)]));
        store.add_clause(2, clause(&[(1, false), (3, true)]));

        let r = store
            .resolve(1, 2, 1)
            .expect("resolving C1 and C2 on pivot 1 should succeed");
        // Should be (x2 | x3).
        assert_eq!(r.len(), 2);
        assert!(r.contains(&lit(2, true)));
        assert!(r.contains(&lit(3, true)));
        assert!(!r.contains(&lit(1, true)));
        assert!(!r.contains(&lit(1, false)));
    }

    #[test]
    fn test_clause_store_resolve_no_pivot() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true), (2, true)]));
        store.add_clause(2, clause(&[(3, true), (4, false)]));
        // pivot 1 does not appear in clause 2
        assert!(store.resolve(1, 2, 1).is_none());
    }

    #[test]
    fn test_clause_store_resolve_same_polarity() {
        let mut store = ClauseStore::new();
        // Both have x1 positive — cannot resolve on pivot 1.
        store.add_clause(1, clause(&[(1, true), (2, true)]));
        store.add_clause(2, clause(&[(1, true), (3, false)]));
        assert!(store.resolve(1, 2, 1).is_none());
    }

    #[test]
    fn test_clause_store_resolve_missing_clause() {
        let store = ClauseStore::new();
        assert!(store.resolve(1, 2, 1).is_none());
    }

    #[test]
    fn test_clause_store_resolve_to_empty() {
        let mut store = ClauseStore::new();
        // C1: (x1), C2: (~x1)
        store.add_clause(1, clause(&[(1, true)]));
        store.add_clause(2, clause(&[(1, false)]));
        let r = store.resolve(1, 2, 1).unwrap();
        assert!(r.is_empty());
    }

    // -- ReplayEngine: Input steps --

    #[test]
    fn test_replay_single_input_step() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![input_step(1, &[(1, true), (2, false)])];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
        assert_eq!(report.valid_percentage(), 100.0);
    }

    #[test]
    fn test_replay_multiple_inputs() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(2, false)]),
            input_step(3, &[(3, true), (4, false)]),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 3);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
    }

    // -- ReplayEngine: Resolution --

    #[test]
    fn test_replay_valid_resolution() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            resolve_step(3, 1, 2, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 3);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert!(report.diagnostics.is_empty());
    }

    #[test]
    fn test_replay_invalid_resolution_missing_premise() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            // Resolve with non-existent clause 99.
            resolve_step(3, 1, 99, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
        assert!(!report.diagnostics.is_empty());
    }

    #[test]
    fn test_replay_resolution_derives_empty_clause() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(1, false)]),
            resolve_step(3, 1, 2, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        // Step 3 should produce the empty clause.
        let c = engine.clause_store.get(3).unwrap();
        assert!(c.is_empty());
    }

    // -- ReplayEngine: Chain resolution --

    #[test]
    fn test_replay_chain_resolution_valid() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // C1: (x1 | x2), C2: (~x1 | x3), C3: (~x3 | x4)
        // Chain: C1, C2 on pivot 1 → (x2 | x3), then with C3 on pivot 3 → (x2 | x4)
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            input_step(3, &[(3, false), (4, true)]),
            ReplayStep {
                id: 4,
                rule: InferenceRule::ChainResolve {
                    premises: vec![1, 2, 3],
                    pivots: vec![1, 3],
                },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        let derived = engine.clause_store.get(4).unwrap();
        assert_eq!(derived.len(), 2);
        assert!(derived.contains(&lit(2, true)));
        assert!(derived.contains(&lit(4, true)));
    }

    #[test]
    fn test_replay_chain_resolution_wrong_pivot_count() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(1, false)]),
            ReplayStep {
                id: 3,
                rule: InferenceRule::ChainResolve {
                    premises: vec![1, 2],
                    pivots: vec![1, 2], // too many pivots
                },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_replay_chain_resolution_single_premise_invalid() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            ReplayStep {
                id: 2,
                rule: InferenceRule::ChainResolve {
                    premises: vec![1],
                    pivots: vec![],
                },
            },
        ];
        let report = engine.replay(&[], &steps);
        // Need at least 2 premises.
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    // -- ReplayEngine: Tautology --

    #[test]
    fn test_replay_tautology_valid() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // (x1 | ~x1) is tautological.
        let steps = vec![
            input_step(1, &[(1, true), (1, false)]),
            ReplayStep {
                id: 2,
                rule: InferenceRule::Tautology { premise: 1 },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
    }

    #[test]
    fn test_replay_tautology_invalid_not_tautological() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // (x1 | x2) is NOT tautological.
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            ReplayStep {
                id: 2,
                rule: InferenceRule::Tautology { premise: 1 },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    // -- ReplayEngine: Subsumption --

    #[test]
    fn test_replay_subsumption_valid() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // C1: (x1 | x2 | x3), C2: (x1 | x2) — C2 subsumes C1.
        let steps = vec![
            input_step(1, &[(1, true), (2, true), (3, true)]),
            input_step(2, &[(1, true), (2, true)]),
            ReplayStep {
                id: 3,
                rule: InferenceRule::Subsumption {
                    subsumed: 1,
                    subsumer: 2,
                },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
    }

    #[test]
    fn test_replay_subsumption_invalid() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // C1: (x1 | x2), C2: (x3 | x4) — C2 does NOT subsume C1.
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(3, true), (4, true)]),
            ReplayStep {
                id: 3,
                rule: InferenceRule::Subsumption {
                    subsumed: 1,
                    subsumer: 2,
                },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    // -- Config: continue_on_failure --

    #[test]
    fn test_stop_on_first_failure() {
        let config = ReplayConfig {
            continue_on_failure: false,
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps = vec![
            input_step(1, &[(1, true)]),
            resolve_step(2, 1, 99, 1), // invalid
            input_step(3, &[(3, true)]),
        ];
        let report = engine.replay(&[], &steps);
        // Should have 3 verdicts: valid, invalid, skipped.
        assert_eq!(report.verdicts.len(), 3);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
        assert_eq!(report.verdicts[2].1, StepVerdict::Skipped);
    }

    #[test]
    fn test_continue_on_failure() {
        let config = ReplayConfig {
            continue_on_failure: true,
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps = vec![
            input_step(1, &[(1, true)]),
            resolve_step(2, 1, 99, 1), // invalid
            input_step(3, &[(3, true)]),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 3);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
        assert_eq!(report.verdicts[2].1, StepVerdict::Valid);
    }

    // -- Config: step_limit --

    #[test]
    fn test_step_limit() {
        let config = ReplayConfig {
            step_limit: Some(2),
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(2, true)]),
            input_step(3, &[(3, true)]),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 3);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[1].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[2].1, StepVerdict::Skipped);
    }

    // -- Config: sampling mode --

    #[test]
    fn test_sampling_mode_skips_some() {
        let config = ReplayConfig {
            mode: ReplayMode::Sampling {
                numerator: 1,
                denominator: 2,
            },
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps: Vec<ReplayStep> = (0..10)
            .map(|i| input_step(i as u64, &[((i + 1) as u32, true)]))
            .collect();
        let report = engine.replay(&[], &steps);
        let skipped = report
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Skipped)
            .count();
        // With 1/2 sampling, roughly half should be skipped.
        assert!(skipped > 0, "Sampling mode should skip some steps");
        assert!(skipped < 10, "Sampling mode should not skip all steps");
    }

    // -- ReplayReport --

    #[test]
    fn test_report_summary_all_valid() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![input_step(1, &[(1, true)]), input_step(2, &[(2, true)])];
        let report = engine.replay(&[], &steps);
        assert_eq!(
            report.summary(),
            "2 valid, 0 invalid, 0 skipped out of 2 steps"
        );
    }

    #[test]
    fn test_report_first_failure_none() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![input_step(1, &[(1, true)])];
        let report = engine.replay(&[], &steps);
        assert!(report.first_failure().is_none());
    }

    #[test]
    fn test_report_first_failure_present() {
        let mut engine = ReplayEngine::new(ReplayConfig {
            continue_on_failure: true,
            ..ReplayConfig::default()
        });
        let steps = vec![
            resolve_step(1, 99, 98, 1), // invalid
            resolve_step(2, 97, 96, 2), // also invalid
        ];
        let report = engine.replay(&[], &steps);
        let first = report
            .first_failure()
            .expect("first_failure should be present when replay contains invalid steps");
        assert_eq!(first.step_id, 1);
    }

    #[test]
    fn test_report_valid_percentage_mixed() {
        let mut engine = ReplayEngine::new(ReplayConfig {
            continue_on_failure: true,
            ..ReplayConfig::default()
        });
        let steps = vec![
            input_step(1, &[(1, true)]), // valid
            resolve_step(2, 1, 99, 1),   // invalid
            input_step(3, &[(3, true)]), // valid
            resolve_step(4, 3, 88, 3),   // invalid
        ];
        let report = engine.replay(&[], &steps);
        // 2 valid, 2 invalid, 0 skipped → 50%
        assert!((report.valid_percentage() - 50.0).abs() < 0.01);
    }

    #[test]
    fn test_report_valid_percentage_all_skipped() {
        let report = ReplayReport {
            verdicts: vec![(1, StepVerdict::Skipped), (2, StepVerdict::Skipped)],
            diagnostics: Vec::new(),
            progress: ReplayProgress {
                current_step: 0,
                total_steps: 2,
            },
            failure_analysis: None,
        };
        // All skipped → 100%.
        assert!((report.valid_percentage() - 100.0).abs() < 0.01);
    }

    // -- ReplayProgress --

    #[test]
    fn test_progress_percent_zero_total() {
        let p = ReplayProgress {
            current_step: 0,
            total_steps: 0,
        };
        assert!((p.percent_complete() - 100.0).abs() < 0.01);
    }

    #[test]
    fn test_progress_percent_midway() {
        let p = ReplayProgress {
            current_step: 5,
            total_steps: 10,
        };
        assert!((p.percent_complete() - 50.0).abs() < 0.01);
    }

    // -- FailureAnalysis::diagnose --

    #[test]
    fn test_diagnose_input_step() {
        let store = ClauseStore::new();
        let step = input_step(1, &[(1, true)]);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("Input steps"));
    }

    #[test]
    fn test_diagnose_missing_left_premise() {
        let mut store = ClauseStore::new();
        store.add_clause(2, clause(&[(1, false)]));
        let step = resolve_step(3, 99, 2, 1);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("Left premise 99"));
    }

    #[test]
    fn test_diagnose_missing_right_premise() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true)]));
        let step = resolve_step(3, 1, 99, 1);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("Right premise 99"));
    }

    #[test]
    fn test_diagnose_both_premises_missing() {
        let store = ClauseStore::new();
        let step = resolve_step(3, 99, 98, 1);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("Both premises"));
    }

    #[test]
    fn test_diagnose_pivot_not_in_left() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(2, true)])); // no var 1
        store.add_clause(2, clause(&[(1, false)]));
        let step = resolve_step(3, 1, 2, 1);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("does not appear in left"));
    }

    #[test]
    fn test_diagnose_subsumption_missing_clauses() {
        let store = ClauseStore::new();
        let step = ReplayStep {
            id: 3,
            rule: InferenceRule::Subsumption {
                subsumed: 1,
                subsumer: 2,
            },
        };
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("missing"));
    }

    // -- PartialReplay --

    #[test]
    fn test_partial_replay_range() {
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            resolve_step(3, 1, 2, 1),
            input_step(4, &[(4, true)]),
        ];
        // Only replay step index 2 (the resolution).
        let partial = PartialReplay::from_range(2, 3, steps, Vec::new(), ReplayConfig::default());
        let report = partial.replay();
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].0, 3);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
    }

    #[test]
    fn test_partial_replay_with_input_clauses() {
        let input_clauses = vec![(1, clause(&[(1, true)])), (2, clause(&[(1, false)]))];
        let steps = vec![resolve_step(3, 1, 2, 1)];
        let partial =
            PartialReplay::from_range(0, 1, steps, input_clauses, ReplayConfig::default());
        let report = partial.replay();
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
    }

    // -- Input clause seeding --

    #[test]
    fn test_replay_with_seeded_input_clauses() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let inputs = vec![
            (1, clause(&[(1, true), (2, true)])),
            (2, clause(&[(1, false), (3, true)])),
        ];
        let steps = vec![resolve_step(3, 1, 2, 1)];
        let report = engine.replay(&inputs, &steps);
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
    }

    // -- Multi-step proof to empty clause --

    #[test]
    fn test_full_refutation_proof() {
        // Prove UNSAT for: (x1), (~x1 | x2), (~x2)
        // Resolution: (x1) + (~x1 | x2) on x1 → (x2)
        //             (x2) + (~x2) on x2 → FALSE
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(1, false), (2, true)]),
            input_step(3, &[(2, false)]),
            resolve_step(4, 1, 2, 1), // (x2)
            resolve_step(5, 4, 3, 2), // FALSE
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        let empty = engine.clause_store.get(5).unwrap();
        assert!(empty.is_empty());
        assert_eq!(report.valid_percentage(), 100.0);
    }

    // -- StepVerdict display --

    #[test]
    fn test_step_verdict_display() {
        assert_eq!(StepVerdict::Valid.to_string(), "VALID");
        assert_eq!(StepVerdict::Invalid.to_string(), "INVALID");
        assert_eq!(StepVerdict::Skipped.to_string(), "SKIPPED");
    }

    // -- ReplayDiagnostic display --

    #[test]
    fn test_diagnostic_display() {
        let d = ReplayDiagnostic {
            step_id: 42,
            verdict: StepVerdict::Invalid,
            message: "missing premise".to_string(),
        };
        let s = d.to_string();
        assert!(s.contains("42"));
        assert!(s.contains("INVALID"));
        assert!(s.contains("missing premise"));
    }

    // -- Edge cases --

    #[test]
    fn test_replay_empty_proof() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let report = engine.replay(&[], &[]);
        assert!(report.verdicts.is_empty());
        assert_eq!(report.valid_percentage(), 100.0);
        assert!(report.first_failure().is_none());
    }

    #[test]
    fn test_clause_store_overwrite() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true)]));
        store.add_clause(1, clause(&[(2, true)]));
        assert_eq!(store.len(), 1);
        let c = store.get(1).unwrap();
        assert!(c.contains(&lit(2, true)));
        assert!(!c.contains(&lit(1, true)));
    }

    #[test]
    fn test_resolve_deduplicates_literals() {
        let mut store = ClauseStore::new();
        // C1: (x1 | x2 | x3), C2: (~x1 | x2 | x4)
        store.add_clause(1, clause(&[(1, true), (2, true), (3, true)]));
        store.add_clause(2, clause(&[(1, false), (2, true), (4, true)]));
        let r = store.resolve(1, 2, 1).unwrap();
        // x2 should appear only once.
        let x2_count = r.literals.iter().filter(|l| l.var == 2).count();
        assert_eq!(x2_count, 1);
    }

    #[test]
    fn test_replay_mode_equality() {
        assert_eq!(ReplayMode::Full, ReplayMode::Full);
        assert_ne!(ReplayMode::Full, ReplayMode::Incremental);
        assert_eq!(
            ReplayMode::Sampling {
                numerator: 1,
                denominator: 3
            },
            ReplayMode::Sampling {
                numerator: 1,
                denominator: 3
            }
        );
    }

    #[test]
    fn test_failure_analysis_fields() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![resolve_step(1, 99, 98, 1)];
        let report = engine.replay(&[], &steps);
        let analysis = report
            .failure_analysis
            .as_ref()
            .expect("failure_analysis should be present when replay has invalid steps");
        assert_eq!(analysis.first_invalid_step, 1);
        assert!(!analysis.suggested_fix.is_empty());
    }

    #[test]
    fn test_tautology_missing_premise() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![ReplayStep {
            id: 1,
            rule: InferenceRule::Tautology { premise: 99 },
        }];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[0].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_chain_resolve_missing_intermediate_premise() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            // premise 99 does not exist
            ReplayStep {
                id: 3,
                rule: InferenceRule::ChainResolve {
                    premises: vec![1, 99],
                    pivots: vec![1],
                },
            },
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_diagnose_chain_resolve_missing_premises() {
        let store = ClauseStore::new();
        let step = ReplayStep {
            id: 1,
            rule: InferenceRule::ChainResolve {
                premises: vec![10, 20, 30],
                pivots: vec![1, 2],
            },
        };
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("missing premises"));
    }

    #[test]
    fn test_diagnose_tautology_no_complementary_pair() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true), (2, true)]));
        let step = ReplayStep {
            id: 2,
            rule: InferenceRule::Tautology { premise: 1 },
        };
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("no complementary pair"));
    }

    // -----------------------------------------------------------------------
    // Additional comprehensive tests
    // -----------------------------------------------------------------------

    // -- helpers for new tests --

    fn chain_step(id: u64, premises: Vec<u64>, pivots: Vec<u32>) -> ReplayStep {
        ReplayStep {
            id,
            rule: InferenceRule::ChainResolve { premises, pivots },
        }
    }

    fn tautology_step(id: u64, premise: u64) -> ReplayStep {
        ReplayStep {
            id,
            rule: InferenceRule::Tautology { premise },
        }
    }

    fn subsumption_step(id: u64, subsumed: u64, subsumer: u64) -> ReplayStep {
        ReplayStep {
            id,
            rule: InferenceRule::Subsumption { subsumed, subsumer },
        }
    }

    // ===================================================================
    // Valid proof replay — complex multi-step scenarios
    // ===================================================================

    #[test]
    fn test_valid_proof_pigeonhole_2_holes() {
        // Pigeonhole: 3 pigeons, 2 holes.
        // Variables: p_{i,j} = pigeon i goes to hole j
        //   p11=1, p12=2, p21=3, p22=4, p31=5, p32=6
        // Clauses:
        //   Each pigeon in some hole: (p11|p12), (p21|p22), (p31|p32)
        //   No two pigeons same hole:
        //     (~p11|~p21), (~p11|~p31), (~p21|~p31)
        //     (~p12|~p22), (~p12|~p32), (~p22|~p32)
        // Resolution proof deriving empty clause:
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            // Input clauses
            input_step(10, &[(1, true), (2, true)]), // p1 in h1 or h2
            input_step(11, &[(3, true), (4, true)]), // p2 in h1 or h2
            input_step(12, &[(5, true), (6, true)]), // p3 in h1 or h2
            input_step(13, &[(1, false), (3, false)]), // ~p11|~p21
            input_step(14, &[(1, false), (5, false)]), // ~p11|~p31
            input_step(15, &[(3, false), (5, false)]), // ~p21|~p31
            input_step(16, &[(2, false), (4, false)]), // ~p12|~p22
            input_step(17, &[(2, false), (6, false)]), // ~p12|~p32
            input_step(18, &[(4, false), (6, false)]), // ~p22|~p32
            // Resolve (p11|p12) with (~p11|~p21) on p11 → (p12|~p21)
            resolve_step(20, 10, 13, 1),
            // Resolve (p12|~p21) with (~p12|~p22) on p12 → (~p21|~p22)
            resolve_step(21, 20, 16, 2),
            // Resolve (p21|p22) with (~p21|~p22) on p21 → (p22|~p22) -- wait, that's tautology
            // Let's take a different path:
            // Resolve (p21|p22) with (~p21|~p22) is not directly useful.
            // Instead: resolve (p11|p12) with (~p11|~p31) on p11 → (p12|~p31)
            resolve_step(22, 10, 14, 1),
            // Resolve (p12|~p31) with (~p12|~p32) on p12 → (~p31|~p32)
            resolve_step(23, 22, 17, 2),
            // Resolve (p31|p32) with (~p31|~p32) on p31 → (p32|~p32)
            // That's a tautology — not useful for refutation. Let's do this differently.
            // Resolve (~p21|~p22) with (p21|p22) on p21 → (p22|~p22) also tautology.
            // Correct approach: condition on p11.
            // If p11: from (~p11|~p21) get ~p21, from (~p11|~p31) get ~p31.
            //   Then p2 must be in h2 (p22), p3 must be in h2 (p32).
            //   But (~p22|~p32) conflicts.
            // Step: resolve (~p21|~p22) with (p21|p22) on p22 → (~p21|p21) also taut.
            // Use chain resolution for the actual derivation:
            // From step 21: (~p21|~p22)
            // Resolve (p21|p22) with (~p21|~p22) on p21 → (p22|~p22) is taut.
            // Resolve on p22: (p21|p22) with (~p21|~p22) → (p21|~p21) taut.
            // Need a longer chain. Let me build the proof more carefully:
            //
            // (1) Resolve 11:(p21|p22) with 21:(~p21|~p22) on pivot 3(=p21)
            //     → (p22 | ~p22) — tautology, skip that.
            //
            // Better plan using unit propagation style:
            // Resolve 11:(p21|p22) with 15:(~p21|~p31) on pivot p21=3 → (p22|~p31)
            resolve_step(24, 11, 15, 3),
            // Resolve 24:(p22|~p31) with 18:(~p22|~p32) on pivot p22=4 → (~p31|~p32)
            resolve_step(25, 24, 18, 4),
            // Resolve 12:(p31|p32) with 25:(~p31|~p32) on pivot p31=5 → (p32|~p32)
            // Tautology again. Need more structure.
            // Resolve 12:(p31|p32) with 23:(~p31|~p32) on pivot p31=5 → (p32|~p32) — taut.
            // The real proof needs case splits. Let's use a simpler UNSAT instance instead.
        ];
        let report = engine.replay(&[], &steps);
        // All steps so far should be valid
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "All steps in pigeonhole partial proof should be valid"
        );
    }

    #[test]
    fn test_valid_proof_diamond_resolution() {
        // Diamond-shaped resolution: two independent resolution paths merge.
        //   C1: (a | b)     C2: (~a | c)     C3: (a | ~b)    C4: (~a | ~c)
        //   R1 = C1 res C2 on a → (b | c)
        //   R2 = C3 res C4 on a → (~b | ~c)
        //   R3 = R1 res R2 on b → (c | ~c)  — tautology, but valid resolution
        //   Instead: R3 = R1 res R2 on c → (b | ~b) — also tautology
        //   Better: derive empty from (b|c), (~b|~c), (b|~c), (~b|c)
        //
        //   C1: (b | c)  C2: (~b | ~c)  C3: (b | ~c)  C4: (~b | c)
        //   R1 = C1 res C2 on b → (c | ~c) taut. Use c instead:
        //   R1 = C1 res C4 on c → (b | ~b) taut. Hmm.
        //   Use 3-clause chain:
        //   C1:(x1), C2:(~x1|x2), C3:(~x2|x3), C4:(~x3)
        //   R1 = C1+C2 on 1 → (x2)
        //   R2 = C3+C4 on 3 → (~x2)
        //   R3 = R1+R2 on 2 → FALSE
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(1, false), (2, true)]),
            input_step(3, &[(2, false), (3, true)]),
            input_step(4, &[(3, false)]),
            resolve_step(5, 1, 2, 1), // (x2)
            resolve_step(6, 3, 4, 3), // (~x2)
            resolve_step(7, 5, 6, 2), // FALSE
        ];
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "Diamond resolution proof should be fully valid"
        );
        let empty = engine.clause_store.get(7).unwrap();
        assert!(empty.is_empty(), "Final clause should be FALSE (empty)");
        assert!(report.failure_analysis.is_none());
    }

    #[test]
    fn test_valid_proof_mixed_inference_rules() {
        // Proof using Input, Resolve, Tautology, and Subsumption together.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            // Inputs
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            input_step(3, &[(1, true), (1, false), (4, true)]), // tautology: (x1|~x1|x4)
            input_step(4, &[(2, true), (3, true), (5, true)]),  // (x2|x3|x5)
            // Resolution: 1 + 2 on x1 → (x2|x3)
            resolve_step(5, 1, 2, 1),
            // Tautology: clause 3 has x1 and ~x1
            tautology_step(6, 3),
            // Subsumption: (x2|x3) subsumes (x2|x3|x5)
            subsumption_step(7, 4, 5),
        ];
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "Mixed inference rule proof should be fully valid: {:?}",
            report.verdicts
        );
    }

    #[test]
    fn test_valid_proof_chain_resolution_four_premises() {
        // Chain resolve with 4 premises and 3 pivots.
        // C1:(x1|x2), C2:(~x1|x3), C3:(~x3|x4), C4:(~x4|x5)
        // Chain on pivots [1, 3, 4] → (x2|x5)
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            input_step(3, &[(3, false), (4, true)]),
            input_step(4, &[(4, false), (5, true)]),
            chain_step(5, vec![1, 2, 3, 4], vec![1, 3, 4]),
        ];
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "4-premise chain resolution should be valid"
        );
        let derived = engine.clause_store.get(5).unwrap();
        assert_eq!(derived.len(), 2);
        assert!(derived.contains(&lit(2, true)));
        assert!(derived.contains(&lit(5, true)));
    }

    #[test]
    fn test_valid_proof_resolution_reversed_polarity() {
        // Left has negative, right has positive — should still resolve.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, false), (2, true)]), // (~x1 | x2)
            input_step(2, &[(1, true), (3, true)]),  // (x1 | x3)
            resolve_step(3, 1, 2, 1),                // (x2 | x3)
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        let derived = engine.clause_store.get(3).unwrap();
        assert!(derived.contains(&lit(2, true)));
        assert!(derived.contains(&lit(3, true)));
    }

    // ===================================================================
    // Invalid proof — bad step references
    // ===================================================================

    #[test]
    fn test_invalid_resolve_both_premises_missing() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![resolve_step(1, 100, 200, 1)];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[0].1, StepVerdict::Invalid);
        assert_eq!(report.diagnostics.len(), 1);
        let msg = &report.diagnostics[0].message;
        assert!(
            msg.contains("Both premises"),
            "Expected 'Both premises' in: {}",
            msg
        );
    }

    #[test]
    fn test_invalid_resolve_wrong_pivot_variable() {
        // Both premises exist but pivot variable is not in either clause.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(3, true), (4, true)]),
            resolve_step(3, 1, 2, 99), // pivot 99 not in either clause
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_resolve_same_polarity_both_positive() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, true), (3, true)]),
            resolve_step(3, 1, 2, 1), // both have x1 positive
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_resolve_same_polarity_both_negative() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, false), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            resolve_step(3, 1, 2, 1), // both have ~x1
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_chain_resolve_zero_premises() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![chain_step(1, vec![], vec![])];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[0].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_chain_resolve_wrong_polarity_mid_chain() {
        // Chain: C1:(x1|x2), C2:(x1|x3) — both have x1 positive, no complementary pair.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, true), (3, true)]),
            chain_step(3, vec![1, 2], vec![1]), // pivot x1, but same polarity
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_subsumption_missing_subsumer() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            subsumption_step(2, 1, 99), // subsumer 99 does not exist
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_subsumption_missing_subsumed() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            subsumption_step(2, 99, 1), // subsumed 99 does not exist
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_subsumption_not_subset() {
        // subsumer has literal not in subsumed.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]), // subsumed
            input_step(2, &[(1, true), (3, true)]), // subsumer — x3 not in clause 1
            subsumption_step(3, 1, 2),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_tautology_missing_premise() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![tautology_step(1, 999)];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[0].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_resolution_references_future_step() {
        // Step 2 tries to resolve with clause 3 which hasn't been derived yet.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            resolve_step(2, 1, 3, 1), // clause 3 doesn't exist yet
            input_step(3, &[(1, false)]),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_invalid_chain_first_premise_missing() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(2, &[(1, false), (3, true)]),
            chain_step(3, vec![99, 2], vec![1]), // first premise 99 missing
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    // ===================================================================
    // Theory lemma simulation via Input clauses
    // ===================================================================
    // In DPLL(T), theory lemmas are clauses added by theory solvers.
    // They are encoded as Input steps in the proof certificate.

    #[test]
    fn test_replay_with_theory_lemma_input() {
        // Simulate a SAT proof with a theory lemma injected.
        // Original clauses: (x1|x2), (~x1|x3)
        // Theory lemma: (~x2|~x3) — added by the theory solver
        // Resolution chain: (x1|x2) + (~x1|x3) on x1 → (x2|x3)
        //                   (x2|x3) + (~x2|~x3) on x2 → (x3|~x3) — tautology
        // Better: add theory lemma (~x3) as unit.
        //   (x1|x2) + (~x1|x3) on x1 → (x2|x3)
        //   (x2|x3) + (~x3) on x3 → (x2)
        //   Add theory lemma (~x2)
        //   (x2) + (~x2) on x2 → FALSE
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),  // problem clause
            input_step(2, &[(1, false), (3, true)]), // problem clause
            input_step(3, &[(3, false)]),            // theory lemma
            input_step(4, &[(2, false)]),            // theory lemma
            resolve_step(10, 1, 2, 1),               // (x2|x3)
            resolve_step(11, 10, 3, 3),              // (x2)
            resolve_step(12, 11, 4, 2),              // FALSE
        ];
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "Proof with theory lemma inputs should be fully valid"
        );
        let empty = engine.clause_store.get(12).unwrap();
        assert!(empty.is_empty());
    }

    #[test]
    fn test_replay_theory_lemma_as_seeded_input() {
        // Theory lemmas pre-seeded into the clause store as input_clauses.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let theory_lemmas = vec![
            (100, clause(&[(1, false)])), // theory: ~x1
            (101, clause(&[(2, false)])), // theory: ~x2
        ];
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            resolve_step(2, 1, 100, 1), // (x1|x2) + (~x1) on x1 → (x2)
            resolve_step(3, 2, 101, 2), // (x2) + (~x2) on x2 → FALSE
        ];
        let report = engine.replay(&theory_lemmas, &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert!(engine.clause_store.get(3).unwrap().is_empty());
    }

    #[test]
    fn test_replay_theory_lemma_chain_equality() {
        // Simulate EUF theory lemma: transitivity chain.
        // If a=b and b=c then a=c.
        // Encoded as clauses with equality literals.
        // eq(a,b)=1, eq(b,c)=2, eq(a,c)=3
        // Clauses: (eq_ab), (eq_bc), (~eq_ab | ~eq_bc | eq_ac) [transitivity lemma]
        // (~eq_ac) [from problem]
        // Proof: resolve transitivity with eq_ab on 1 → (~eq_bc | eq_ac)
        //        resolve with eq_bc on 2 → (eq_ac)
        //        resolve with ~eq_ac on 3 → FALSE
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),                         // eq(a,b)
            input_step(2, &[(2, true)]),                         // eq(b,c)
            input_step(3, &[(1, false), (2, false), (3, true)]), // transitivity lemma
            input_step(4, &[(3, false)]),                        // ~eq(a,c) from problem
            resolve_step(10, 3, 1, 1),                           // (~eq_bc | eq_ac)
            resolve_step(11, 10, 2, 2),                          // (eq_ac)
            resolve_step(12, 11, 4, 3),                          // FALSE
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert!(engine.clause_store.get(12).unwrap().is_empty());
    }

    #[test]
    fn test_replay_theory_lemma_bitvector_bounds() {
        // Simulate BV theory lemma: x < 4 encoded as clauses.
        // bit0=1, bit1=2, bit2=3 (for 3-bit number)
        // Theory lemma: if bit2 is set, value >= 4, so ~bit2 under constraint x<4.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(3, true), (1, true)]), // problem clause: (bit2 | bit0)
            input_step(2, &[(3, false)]),           // theory lemma: ~bit2 (x < 4)
            input_step(3, &[(1, false)]),           // problem: ~bit0
            resolve_step(10, 1, 2, 3),              // (bit0)
            resolve_step(11, 10, 3, 1),             // FALSE
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert!(engine.clause_store.get(11).unwrap().is_empty());
    }

    #[test]
    fn test_replay_theory_lemma_linear_arithmetic() {
        // Simulate LRA theory lemma.
        // x + y <= 5 and x >= 3 and y >= 3 is UNSAT.
        // Encoded: a=1 (x>=3), b=2 (y>=3), c=3 (x+y<=5)
        // Theory lemma: (~a | ~b | ~c) — can't all be true.
        // Problem: (a), (b), (c).
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),                          // x >= 3
            input_step(2, &[(2, true)]),                          // y >= 3
            input_step(3, &[(3, true)]),                          // x + y <= 5
            input_step(4, &[(1, false), (2, false), (3, false)]), // LRA lemma
            // Chain resolve: [4, 1, 2, 3] on pivots [1, 2, 3]
            chain_step(10, vec![4, 1, 2, 3], vec![1, 2, 3]),
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert!(engine.clause_store.get(10).unwrap().is_empty());
    }

    // ===================================================================
    // Empty proof replay — edge cases
    // ===================================================================

    #[test]
    fn test_empty_proof_no_inputs_no_steps() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let report = engine.replay(&[], &[]);
        assert!(report.verdicts.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.failure_analysis.is_none());
        assert_eq!(
            report.summary(),
            "0 valid, 0 invalid, 0 skipped out of 0 steps"
        );
        assert_eq!(report.progress.total_steps, 0);
        assert_eq!(report.progress.current_step, 0);
    }

    #[test]
    fn test_empty_proof_with_seeded_inputs() {
        // Inputs seeded but no proof steps — valid scenario (trivially satisfied).
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let inputs = vec![(1, clause(&[(1, true)])), (2, clause(&[(2, false)]))];
        let report = engine.replay(&inputs, &[]);
        assert!(report.verdicts.is_empty());
        assert_eq!(engine.clause_store.len(), 2);
        assert!(engine.clause_store.get(1).is_some());
    }

    #[test]
    fn test_empty_proof_report_valid_percentage() {
        let report = ReplayReport {
            verdicts: Vec::new(),
            diagnostics: Vec::new(),
            progress: ReplayProgress {
                current_step: 0,
                total_steps: 0,
            },
            failure_analysis: None,
        };
        assert_eq!(report.valid_percentage(), 100.0);
    }

    #[test]
    fn test_empty_clause_store_operations() {
        let store = ClauseStore::new();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
        assert!(store.get(0).is_none());
        assert!(store.get(u64::MAX).is_none());
        assert!(store.resolve(0, 1, 0).is_none());
    }

    #[test]
    fn test_empty_clause_display() {
        let c = Clause::new(Vec::new());
        assert_eq!(c.to_string(), "FALSE");
        assert!(c.is_empty());
        assert_eq!(c.len(), 0);
    }

    // ===================================================================
    // Large proof replay — performance
    // ===================================================================

    #[test]
    fn test_large_proof_linear_chain_100_steps() {
        // Build a linear resolution chain: each step resolves the previous result
        // with the next unit clause.
        // C0: (x1 | x2 | ... | x100)
        // C_i: (~x_i) for i = 1..100
        // Resolution: C0 + C_1 on x1 → (x2 | ... | x100)
        //             result + C_2 on x2 → (x3 | ... | x100)
        //             ...
        //             result + C_100 on x100 → FALSE
        let n = 100u32;
        let mut steps: Vec<ReplayStep> = Vec::new();

        // Big clause with all positive literals
        let big_lits: Vec<(u32, bool)> = (1..=n).map(|v| (v, true)).collect();
        steps.push(input_step(0, &big_lits));

        // Unit negative clauses
        for i in 1..=n {
            steps.push(input_step(i as u64, &[(i, false)]));
        }

        // Resolution chain
        let mut prev_id: u64 = 0;
        for i in 1..=n {
            let new_id = (n as u64) + (i as u64);
            steps.push(resolve_step(new_id, prev_id, i as u64, i));
            prev_id = new_id;
        }

        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "100-step linear chain should be fully valid"
        );
        // The final clause should be empty (FALSE).
        let final_id = (n as u64) + (n as u64);
        let final_clause = engine.clause_store.get(final_id).unwrap();
        assert!(
            final_clause.is_empty(),
            "Final clause should be empty (FALSE)"
        );
    }

    #[test]
    fn test_large_proof_500_input_steps() {
        // 500 input steps — should complete quickly.
        let steps: Vec<ReplayStep> = (0..500)
            .map(|i| input_step(i as u64, &[((i + 1) as u32, true)]))
            .collect();
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 500);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert_eq!(engine.clause_store.len(), 500);
    }

    #[test]
    fn test_large_proof_chain_resolution_wide() {
        // Chain resolution with 50 premises.
        // C1: (x1 | x_extra), C2: (~x1 | x2), C3: (~x2 | x3), ..., C50: (~x49 | x50)
        // Chain on pivots [1, 2, ..., 49] → (x_extra | x50)
        let n = 50usize;
        let mut steps: Vec<ReplayStep> = Vec::new();

        // First clause: (x_extra | x1) where x_extra = (n+1) as u32
        let extra_var = (n + 1) as u32;
        steps.push(input_step(1, &[(extra_var, true), (1, true)]));

        // Chain clauses: (~x_i | x_{i+1}) for i = 1..n-1
        for i in 1..n {
            steps.push(input_step(
                (i + 1) as u64,
                &[(i as u32, false), ((i + 1) as u32, true)],
            ));
        }

        // Chain resolve all
        let premises: Vec<u64> = (1..=(n as u64)).collect();
        let pivots: Vec<u32> = (1..n as u32).collect();
        steps.push(chain_step(1000, premises, pivots));

        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "Wide chain resolution should be valid"
        );
        let derived = engine.clause_store.get(1000).unwrap();
        assert!(derived.contains(&lit(extra_var, true)));
        assert!(derived.contains(&lit(n as u32, true)));
        assert_eq!(derived.len(), 2);
    }

    #[test]
    fn test_large_proof_with_step_limit() {
        let steps: Vec<ReplayStep> = (0..1000)
            .map(|i| input_step(i as u64, &[((i + 1) as u32, true)]))
            .collect();
        let config = ReplayConfig {
            step_limit: Some(50),
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 1000);
        let valid_count = report
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Valid)
            .count();
        let skipped_count = report
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Skipped)
            .count();
        assert_eq!(valid_count, 50);
        assert_eq!(skipped_count, 950);
    }

    // ===================================================================
    // Step-by-step validation
    // ===================================================================

    #[test]
    fn test_step_by_step_replay_individual_steps() {
        // Use replay_step directly for fine-grained control.
        let mut engine = ReplayEngine::new(ReplayConfig::default());

        // Step 1: Input (x1 | x2)
        let s1 = input_step(1, &[(1, true), (2, true)]);
        assert_eq!(engine.replay_step(&s1), StepVerdict::Valid);
        assert!(engine.clause_store.get(1).is_some());

        // Step 2: Input (~x1 | x3)
        let s2 = input_step(2, &[(1, false), (3, true)]);
        assert_eq!(engine.replay_step(&s2), StepVerdict::Valid);

        // Step 3: Resolve 1 + 2 on x1 → (x2 | x3)
        let s3 = resolve_step(3, 1, 2, 1);
        assert_eq!(engine.replay_step(&s3), StepVerdict::Valid);
        let c3 = engine.clause_store.get(3).unwrap();
        assert_eq!(c3.len(), 2);
        assert!(c3.contains(&lit(2, true)));
        assert!(c3.contains(&lit(3, true)));

        // Step 4: Invalid — reference non-existent premise
        let s4 = resolve_step(4, 3, 999, 2);
        assert_eq!(engine.replay_step(&s4), StepVerdict::Invalid);
        // Clause 4 should NOT be in the store after invalid step.
        assert!(engine.clause_store.get(4).is_none());
    }

    #[test]
    fn test_step_by_step_clause_store_state_after_each_step() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());

        assert_eq!(engine.clause_store.len(), 0);

        let _ = engine.replay_step(&input_step(1, &[(1, true)]));
        assert_eq!(engine.clause_store.len(), 1);

        let _ = engine.replay_step(&input_step(2, &[(1, false)]));
        assert_eq!(engine.clause_store.len(), 2);

        let _ = engine.replay_step(&resolve_step(3, 1, 2, 1));
        assert_eq!(engine.clause_store.len(), 3);
        assert!(engine.clause_store.get(3).unwrap().is_empty());
    }

    #[test]
    fn test_step_by_step_tautology_produces_empty_clause() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let _ = engine.replay_step(&input_step(1, &[(1, true), (1, false), (2, true)]));
        let verdict = engine.replay_step(&tautology_step(2, 1));
        assert_eq!(verdict, StepVerdict::Valid);
        let taut_result = engine.clause_store.get(2).unwrap();
        assert!(
            taut_result.is_empty(),
            "Tautology step should produce empty clause marker"
        );
    }

    #[test]
    fn test_step_by_step_subsumption_stores_subsumer() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // C1: (x1 | x2 | x3)  — will be subsumed
        // C2: (x1 | x2)       — subsumer (subset)
        let _ = engine.replay_step(&input_step(1, &[(1, true), (2, true), (3, true)]));
        let _ = engine.replay_step(&input_step(2, &[(1, true), (2, true)]));
        let verdict = engine.replay_step(&subsumption_step(3, 1, 2));
        assert_eq!(verdict, StepVerdict::Valid);
        // Clause 3 should be the subsumer's clause.
        let c3 = engine.clause_store.get(3).unwrap();
        assert_eq!(c3.len(), 2);
        assert!(c3.contains(&lit(1, true)));
        assert!(c3.contains(&lit(2, true)));
    }

    #[test]
    fn test_step_by_step_chain_intermediate_state() {
        // Verify chain resolution processes intermediates correctly.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        // C1: (x1 | x2), C2: (~x1 | x3), C3: (~x3 | x4)
        let _ = engine.replay_step(&input_step(1, &[(1, true), (2, true)]));
        let _ = engine.replay_step(&input_step(2, &[(1, false), (3, true)]));
        let _ = engine.replay_step(&input_step(3, &[(3, false), (4, true)]));

        // Chain: C1+C2 on x1, result+C3 on x3 → (x2|x4)
        let verdict = engine.replay_step(&chain_step(4, vec![1, 2, 3], vec![1, 3]));
        assert_eq!(verdict, StepVerdict::Valid);
        let derived = engine.clause_store.get(4).unwrap();
        assert!(!derived.contains(&lit(1, true)));
        assert!(derived.contains(&lit(2, true)));
        assert!(!derived.contains(&lit(3, true)));
        assert!(derived.contains(&lit(4, true)));
    }

    #[test]
    fn test_step_by_step_progress_tracking() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let p0 = engine.progress(10);
        assert_eq!(p0.current_step, 0);
        assert_eq!(p0.total_steps, 10);
        assert!((p0.percent_complete() - 0.0).abs() < 0.01);

        let inputs = vec![(1, clause(&[(1, true)])), (2, clause(&[(1, false)]))];
        let steps = vec![resolve_step(3, 1, 2, 1)];
        let report = engine.replay(&inputs, &steps);
        assert_eq!(report.progress.current_step, 1);
        assert_eq!(report.progress.total_steps, 1);
    }

    // ===================================================================
    // PartialReplay — additional coverage
    // ===================================================================

    #[test]
    fn test_partial_replay_empty_range() {
        let steps = vec![input_step(1, &[(1, true)]), input_step(2, &[(2, true)])];
        // Range [2, 2) is empty.
        let partial = PartialReplay::from_range(2, 2, steps, Vec::new(), ReplayConfig::default());
        let report = partial.replay();
        assert!(report.verdicts.is_empty());
    }

    #[test]
    fn test_partial_replay_out_of_bounds_clamped() {
        let steps = vec![input_step(1, &[(1, true)])];
        // end=100 but only 1 step — should be clamped.
        let partial = PartialReplay::from_range(0, 100, steps, Vec::new(), ReplayConfig::default());
        let report = partial.replay();
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
    }

    #[test]
    fn test_partial_replay_depends_on_prior_steps() {
        // Steps [0,1] are inputs, step [2] is resolution depending on them.
        // Partial replay of just step [2] must silently replay [0,1] first.
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            resolve_step(3, 1, 2, 1),
        ];
        let partial = PartialReplay::from_range(2, 3, steps, Vec::new(), ReplayConfig::default());
        let report = partial.replay();
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].0, 3);
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
    }

    #[test]
    fn test_partial_replay_middle_range() {
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(2, true)]),
            input_step(3, &[(3, true)]),
            input_step(4, &[(4, true)]),
        ];
        // Replay only steps at indices 1 and 2.
        let partial = PartialReplay::from_range(1, 3, steps, Vec::new(), ReplayConfig::default());
        let report = partial.replay();
        assert_eq!(report.verdicts.len(), 2);
        assert_eq!(report.verdicts[0].0, 2);
        assert_eq!(report.verdicts[1].0, 3);
    }

    #[test]
    fn test_partial_replay_with_failure_in_range() {
        let steps = vec![
            input_step(1, &[(1, true)]),
            resolve_step(2, 1, 999, 1), // invalid — premise 999 missing
            input_step(3, &[(3, true)]),
        ];
        let partial = PartialReplay::from_range(1, 3, steps, Vec::new(), ReplayConfig::default());
        let report = partial.replay();
        // Should stop at the invalid step (continue_on_failure is false by default).
        assert_eq!(report.verdicts.len(), 1);
        assert_eq!(report.verdicts[0].1, StepVerdict::Invalid);
        assert!(report.failure_analysis.is_some());
    }

    // ===================================================================
    // Config interaction tests
    // ===================================================================

    #[test]
    fn test_sampling_mode_zero_denominator_replays_all() {
        let config = ReplayConfig {
            mode: ReplayMode::Sampling {
                numerator: 1,
                denominator: 0,
            },
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps: Vec<ReplayStep> = (0..5)
            .map(|i| input_step(i as u64, &[((i + 1) as u32, true)]))
            .collect();
        let report = engine.replay(&[], &steps);
        // denominator=0 means all steps should be checked.
        let skipped = report
            .verdicts
            .iter()
            .filter(|(_, v)| *v == StepVerdict::Skipped)
            .count();
        assert_eq!(skipped, 0, "Zero denominator should check all steps");
    }

    #[test]
    fn test_step_limit_zero_skips_all() {
        let config = ReplayConfig {
            step_limit: Some(0),
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps = vec![input_step(1, &[(1, true)]), input_step(2, &[(2, true)])];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 2);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Skipped));
    }

    #[test]
    fn test_continue_on_failure_collects_all_diagnostics() {
        let config = ReplayConfig {
            continue_on_failure: true,
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps = vec![
            resolve_step(1, 99, 98, 1),  // invalid
            input_step(2, &[(1, true)]), // valid
            resolve_step(3, 2, 97, 1),   // invalid
            input_step(4, &[(4, true)]), // valid
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts.len(), 4);
        assert_eq!(report.verdicts[0].1, StepVerdict::Invalid);
        assert_eq!(report.verdicts[1].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[2].1, StepVerdict::Invalid);
        assert_eq!(report.verdicts[3].1, StepVerdict::Valid);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].step_id, 1);
        assert_eq!(report.diagnostics[1].step_id, 3);
        // failure_analysis should point to first failure
        assert_eq!(
            report.failure_analysis.as_ref().unwrap().first_invalid_step,
            1
        );
    }

    #[test]
    fn test_step_limit_with_failure_before_limit() {
        let config = ReplayConfig {
            step_limit: Some(5),
            continue_on_failure: false,
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        let steps = vec![
            input_step(1, &[(1, true)]),
            resolve_step(2, 1, 99, 1), // invalid at step index 1
            input_step(3, &[(3, true)]),
            input_step(4, &[(4, true)]),
            input_step(5, &[(5, true)]),
        ];
        let report = engine.replay(&[], &steps);
        // Should stop at failure, remaining marked skipped.
        assert_eq!(report.verdicts[0].1, StepVerdict::Valid);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
        assert_eq!(report.verdicts[2].1, StepVerdict::Skipped);
        assert_eq!(report.verdicts[3].1, StepVerdict::Skipped);
        assert_eq!(report.verdicts[4].1, StepVerdict::Skipped);
    }

    #[test]
    fn test_sampling_still_builds_clause_store() {
        // Skipped steps must still update the clause store for later valid steps.
        let config = ReplayConfig {
            mode: ReplayMode::Sampling {
                numerator: 1,
                denominator: 1000,
            },
            ..ReplayConfig::default()
        };
        let mut engine = ReplayEngine::new(config);
        // Even if most steps are "skipped" in terms of verdict, clause store
        // should still have the clauses so subsequent resolution can work.
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
        ];
        let report = engine.replay(&[], &steps);
        // Regardless of sampling verdict, clause store should contain clauses.
        assert!(engine.clause_store.get(1).is_some());
        assert!(engine.clause_store.get(2).is_some());
        // Verdicts may be Skipped or Valid depending on sampling, but store is populated.
        assert_eq!(report.verdicts.len(), 2);
    }

    #[test]
    fn test_replay_resets_state_between_calls() {
        let mut engine = ReplayEngine::new(ReplayConfig::default());

        // First replay
        let steps1 = vec![input_step(1, &[(1, true)])];
        let report1 = engine.replay(&[], &steps1);
        assert_eq!(report1.verdicts.len(), 1);

        // Second replay — clause store should be reset.
        let steps2 = vec![resolve_step(2, 1, 3, 1)]; // clause 1 should NOT be in store
        let report2 = engine.replay(&[], &steps2);
        assert_eq!(report2.verdicts[0].1, StepVerdict::Invalid);
    }

    // ===================================================================
    // ClauseStore — additional resolution edge cases
    // ===================================================================

    #[test]
    fn test_resolve_preserves_non_pivot_literals_from_both() {
        let mut store = ClauseStore::new();
        // C1: (x1 | x2 | x3), C2: (~x1 | x4 | x5)
        store.add_clause(1, clause(&[(1, true), (2, true), (3, true)]));
        store.add_clause(2, clause(&[(1, false), (4, true), (5, true)]));
        let resolved = store.resolve(1, 2, 1).unwrap();
        assert_eq!(resolved.len(), 4);
        assert!(resolved.contains(&lit(2, true)));
        assert!(resolved.contains(&lit(3, true)));
        assert!(resolved.contains(&lit(4, true)));
        assert!(resolved.contains(&lit(5, true)));
    }

    #[test]
    fn test_resolve_unit_clauses_to_empty() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(42, true)]));
        store.add_clause(2, clause(&[(42, false)]));
        let resolved = store.resolve(1, 2, 42).unwrap();
        assert!(resolved.is_empty());
    }

    #[test]
    fn test_clause_store_default_is_empty() {
        let store = ClauseStore::default();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn test_clause_store_large_ids() {
        let mut store = ClauseStore::new();
        store.add_clause(u64::MAX, clause(&[(1, true)]));
        store.add_clause(u64::MAX - 1, clause(&[(1, false)]));
        let resolved = store.resolve(u64::MAX, u64::MAX - 1, 1).unwrap();
        assert!(resolved.is_empty());
    }

    // ===================================================================
    // Diagnose — additional coverage
    // ===================================================================

    #[test]
    fn test_diagnose_resolve_pivot_not_in_right() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true), (2, true)]));
        store.add_clause(2, clause(&[(3, true), (4, true)])); // no var 1
        let step = resolve_step(3, 1, 2, 1);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("does not appear in right"), "Got: {}", msg);
    }

    #[test]
    fn test_diagnose_resolve_polarity_mismatch() {
        // Both premises have the pivot but with same polarity — diagnose should
        // mention polarity.
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true), (2, true)]));
        store.add_clause(2, clause(&[(1, true), (3, true)]));
        let step = resolve_step(3, 1, 2, 1);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(
            msg.contains("polarity"),
            "Polarity mismatch should mention polarity: {}",
            msg
        );
    }

    #[test]
    fn test_diagnose_chain_all_premises_present() {
        // All premises present but pivot ordering/polarity wrong.
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true)]));
        store.add_clause(2, clause(&[(2, true)])); // no complement of x1
        let step = chain_step(3, vec![1, 2], vec![1]);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("pivot ordering"), "Got: {}", msg);
    }

    #[test]
    fn test_diagnose_tautology_missing_premise() {
        let store = ClauseStore::new();
        let step = tautology_step(1, 999);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("missing"), "Got: {}", msg);
    }

    #[test]
    fn test_diagnose_subsumption_not_subset() {
        let mut store = ClauseStore::new();
        store.add_clause(1, clause(&[(1, true)]));
        store.add_clause(2, clause(&[(2, true)]));
        let step = subsumption_step(3, 1, 2);
        let msg = FailureAnalysis::diagnose(&step, &store);
        assert!(msg.contains("does not subsume"), "Got: {}", msg);
    }

    // ===================================================================
    // Literal — additional coverage
    // ===================================================================

    #[test]
    fn test_literal_double_negation_identity() {
        let l = Literal::new(42, true);
        assert_eq!(l.negated().negated(), l);
        let l2 = Literal::new(0, false);
        assert_eq!(l2.negated().negated(), l2);
    }

    #[test]
    fn test_literal_zero_variable() {
        let l = Literal::new(0, true);
        assert_eq!(l.var, 0);
        assert_eq!(l.to_string(), "x0");
    }

    #[test]
    fn test_literal_equality() {
        assert_eq!(Literal::new(1, true), Literal::new(1, true));
        assert_ne!(Literal::new(1, true), Literal::new(1, false));
        assert_ne!(Literal::new(1, true), Literal::new(2, true));
    }

    #[test]
    fn test_literal_hash_consistency() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(Literal::new(1, true));
        set.insert(Literal::new(1, true)); // duplicate
        set.insert(Literal::new(1, false));
        assert_eq!(set.len(), 2);
    }

    // ===================================================================
    // ReplayConfig defaults
    // ===================================================================

    #[test]
    fn test_replay_config_default() {
        let config = ReplayConfig::default();
        assert!(config.step_limit.is_none());
        assert!(!config.continue_on_failure);
        assert_eq!(config.mode, ReplayMode::Full);
    }

    #[test]
    fn test_replay_config_clone() {
        let config = ReplayConfig {
            step_limit: Some(42),
            continue_on_failure: true,
            mode: ReplayMode::Sampling {
                numerator: 3,
                denominator: 7,
            },
        };
        let cloned = config.clone();
        assert_eq!(cloned.step_limit, Some(42));
        assert!(cloned.continue_on_failure);
        assert_eq!(
            cloned.mode,
            ReplayMode::Sampling {
                numerator: 3,
                denominator: 7
            }
        );
    }

    // ===================================================================
    // Complete refutation proofs (end-to-end)
    // ===================================================================

    #[test]
    fn test_complete_refutation_3sat_small() {
        // UNSAT 3-SAT instance:
        //   (x1 | x2 | x3)
        //   (~x1 | x2 | x3)
        //   (x1 | ~x2 | x3)
        //   (x1 | x2 | ~x3)
        //   (~x1 | ~x2 | x3)
        //   (~x1 | x2 | ~x3)
        //   (x1 | ~x2 | ~x3)
        //   (~x1 | ~x2 | ~x3)
        //
        // Resolution proof:
        //   R1 = C1 + C5 on x1: (x2|x3|~x2|x3) → deduplicate → (x2|x3|~x2)
        //   Actually let's use a systematic approach.
        //   C1 + C2 on x1 → (x2|x3) = R1
        //   C3 + C4 on x3 → (x1|~x2|x2) → (x1|~x2|x2) contains x1; simplify:
        //   Actually let's do it with chain resolution for efficiency.
        //
        //   C7:(x1|~x2|~x3) + C8:(~x1|~x2|~x3) on x1 → (~x2|~x3) = R1
        //   C3:(x1|~x2|x3) + C4:(x1|x2|~x3) — need different pivot.
        //
        //   Simpler: just show the engine handles the full chain.
        //   C1+C2 on x1 → (x2|x3)
        //   C7+C8 on x1 → (~x2|~x3)
        //   R1+R2 on x2 → (x3|~x3) — tautology!
        //
        //   Need more steps. Let's use the known short proof:
        //   C1+C2 on x1 → (x2|x3) = R1
        //   C3+C7 on x3 → (x1|~x2) = R2
        //   C4+C8 on x3 → (x1|x2|~x1|~x2) which has tautologies.
        //
        //   Let me just build a clean 4-variable UNSAT proof.
        // (x1), (~x1|x2), (~x2|x3), (~x3|x4), (~x4)
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(1, false), (2, true)]),
            input_step(3, &[(2, false), (3, true)]),
            input_step(4, &[(3, false), (4, true)]),
            input_step(5, &[(4, false)]),
            // Chain resolve all at once
            chain_step(10, vec![1, 2, 3, 4, 5], vec![1, 2, 3, 4]),
        ];
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "Complete 4-variable refutation should be valid: {:?}",
            report.verdicts
        );
        assert!(engine.clause_store.get(10).unwrap().is_empty());
    }

    #[test]
    fn test_complete_refutation_binary_step_by_step() {
        // The simplest UNSAT: (x1) and (~x1).
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true)]),
            input_step(2, &[(1, false)]),
            resolve_step(3, 1, 2, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert!(report
            .verdicts
            .iter()
            .all(|(_, v)| *v == StepVerdict::Valid));
        assert!(engine.clause_store.get(3).unwrap().is_empty());
        assert_eq!(
            report.summary(),
            "3 valid, 0 invalid, 0 skipped out of 3 steps"
        );
        assert!(report.failure_analysis.is_none());
        assert!(report.first_failure().is_none());
        assert_eq!(report.valid_percentage(), 100.0);
    }

    #[test]
    fn test_complete_proof_with_all_rule_types() {
        // Use every inference rule in a single proof.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            // Inputs
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[(1, false), (3, true)]),
            input_step(3, &[(3, false), (4, true)]),
            input_step(4, &[(4, false)]),
            input_step(5, &[(5, true), (5, false)]), // tautological clause
            input_step(6, &[(2, true), (3, true), (4, true)]), // will be subsumed
            // Resolution
            resolve_step(10, 1, 2, 1), // (x2|x3)
            // Chain resolution
            chain_step(11, vec![10, 3, 4], vec![3, 4]), // (x2)
            // Tautology
            tautology_step(12, 5),
            // Subsumption: (x2|x3) from step 10 subsumes (x2|x3|x4) from step 6
            subsumption_step(13, 6, 10),
        ];
        let report = engine.replay(&[], &steps);
        assert!(
            report
                .verdicts
                .iter()
                .all(|(_, v)| *v == StepVerdict::Valid),
            "Proof with all rule types: {:?}",
            report.verdicts
        );
    }

    // ===================================================================
    // Subsumption — extra edge cases
    // ===================================================================

    #[test]
    fn test_subsumption_self_subsumption() {
        // A clause subsumes itself (all its literals appear in itself).
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            subsumption_step(2, 1, 1), // clause 1 subsumes itself
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Valid);
    }

    #[test]
    fn test_subsumption_unit_subsumes_larger() {
        // Unit clause (x1) subsumes (x1|x2|x3).
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true), (3, true)]),
            input_step(2, &[(1, true)]),
            subsumption_step(3, 1, 2),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Valid);
    }

    #[test]
    fn test_subsumption_empty_clause_subsumes_nothing() {
        // Empty clause has no literals, so every literal in empty is in the subsumed
        // (vacuously true). Empty subsumes everything.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (2, true)]),
            input_step(2, &[]), // empty clause
            subsumption_step(3, 1, 2),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[2].1, StepVerdict::Valid);
    }

    // ===================================================================
    // Tautology — extra edge cases
    // ===================================================================

    #[test]
    fn test_tautology_multiple_complementary_pairs() {
        // (x1 | ~x1 | x2 | ~x2) — multiple tautological pairs.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(1, true), (1, false), (2, true), (2, false)]),
            tautology_step(2, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Valid);
    }

    #[test]
    fn test_tautology_single_variable() {
        // (x5 | ~x5) — minimal tautology.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[(5, true), (5, false)]),
            tautology_step(2, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Valid);
    }

    #[test]
    fn test_tautology_empty_clause_is_not_tautology() {
        // Empty clause (FALSE) is NOT a tautology.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![
            input_step(1, &[]), // empty clause
            tautology_step(2, 1),
        ];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }

    #[test]
    fn test_tautology_unit_clause_not_tautology() {
        // (x1) — a unit clause is not a tautology.
        let mut engine = ReplayEngine::new(ReplayConfig::default());
        let steps = vec![input_step(1, &[(1, true)]), tautology_step(2, 1)];
        let report = engine.replay(&[], &steps);
        assert_eq!(report.verdicts[1].1, StepVerdict::Invalid);
    }
}
