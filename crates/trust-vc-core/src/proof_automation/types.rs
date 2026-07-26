// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::fmt;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A lemma that can be applied during proof search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Lemma {
    pub(crate) name: String,
    pub(crate) hypotheses: Vec<Expr>,
    pub(crate) conclusion: Expr,
}

impl Lemma {
    pub(crate) fn new(name: &str, hypotheses: Vec<Expr>, conclusion: Expr) -> Self {
        Self {
            name: name.to_owned(),
            hypotheses,
            conclusion,
        }
    }
}

/// Database of available lemmas for proof search.
#[derive(Debug, Clone, Default)]
pub(crate) struct LemmaDatabase {
    lemmas: Vec<Lemma>,
}

impl LemmaDatabase {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn add_lemma(&mut self, lemma: Lemma) {
        self.lemmas.push(lemma);
    }

    /// Search for lemmas whose conclusion mentions any of the given variable names
    /// or whose name contains the pattern substring.
    pub(crate) fn search(&self, pattern: &str) -> Vec<&Lemma> {
        self.lemmas
            .iter()
            .filter(|lem| {
                lem.name.contains(pattern)
                    || lem
                        .conclusion
                        .free_vars()
                        .iter()
                        .any(|v| v.contains(pattern))
            })
            .collect()
    }

    pub(crate) fn all(&self) -> &[Lemma] {
        &self.lemmas
    }

    pub(crate) fn len(&self) -> usize {
        self.lemmas.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }
}

/// What we are trying to prove: an expression under a set of hypotheses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofGoal {
    pub(crate) expression: Expr,
    pub(crate) hypotheses: Vec<Expr>,
    pub(crate) available_lemmas: Vec<String>,
    pub(crate) label: String,
}

impl ProofGoal {
    pub(crate) fn new(expression: Expr) -> Self {
        Self {
            expression,
            hypotheses: Vec::new(),
            available_lemmas: Vec::new(),
            label: String::new(),
        }
    }

    pub(crate) fn with_hypotheses(mut self, hyps: Vec<Expr>) -> Self {
        self.hypotheses = hyps;
        self
    }

    pub(crate) fn with_lemmas(mut self, lemmas: Vec<String>) -> Self {
        self.available_lemmas = lemmas;
        self
    }

    pub(crate) fn with_label(mut self, label: &str) -> Self {
        self.label = label.to_owned();
        self
    }

    /// Goal complexity: sum of expression + hypothesis complexities.
    pub(crate) fn complexity(&self) -> usize {
        self.expression.complexity()
            + self
                .hypotheses
                .iter()
                .map(|h| h.complexity())
                .sum::<usize>()
    }
}

// ---------------------------------------------------------------------------
// Induction
// ---------------------------------------------------------------------------

/// A well-founded ordering for termination of induction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum WellFoundedOrder {
    /// Natural number ordering (n > 0 => n-1 < n).
    Natural,
    /// Lexicographic ordering over multiple components.
    Lexicographic(Vec<String>),
    /// Custom measure function name.
    Measure(String),
}

/// An induction scheme specifying how to decompose a proof inductively.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InductionScheme {
    pub(crate) variable: String,
    pub(crate) base_case: Expr,
    pub(crate) inductive_step: Expr,
    pub(crate) well_founded_order: WellFoundedOrder,
}

impl InductionScheme {
    pub(crate) fn natural(variable: &str) -> Self {
        let var = Expr::var(variable);
        Self {
            variable: variable.to_owned(),
            base_case: Expr::eq(var.clone(), Expr::int(0)),
            inductive_step: Expr::gt(var, Expr::int(0)),
            well_founded_order: WellFoundedOrder::Natural,
        }
    }

    pub(crate) fn with_base(mut self, base: Expr) -> Self {
        self.base_case = base;
        self
    }

    pub(crate) fn with_step(mut self, step: Expr) -> Self {
        self.inductive_step = step;
        self
    }
}

// ---------------------------------------------------------------------------
// Tactics
// ---------------------------------------------------------------------------

/// A proof tactic that can be applied to transform a goal.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ProofTactic {
    /// Automatic: try a cascade of built-in strategies.
    Auto,
    /// Arithmetic-specific reasoning (linear/nonlinear).
    Arith,
    /// Induction on a variable with a given scheme.
    Induction(InductionScheme),
    /// Split a goal into cases (e.g., on a boolean condition).
    SplitCases,
    /// Simplify the goal expression (constant folding, identity removal).
    Simplify,
    /// Rewrite using a named equality lemma.
    Rewrite(String),
    /// Apply a named lemma.
    Apply(String),
    /// Unfold a named definition.
    Unfold(String),
    /// Derive a contradiction from the hypotheses.
    Contradiction,
}

impl fmt::Display for ProofTactic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Auto => write!(f, "auto"),
            Self::Arith => write!(f, "arith"),
            Self::Induction(scheme) => write!(f, "induction({})", scheme.variable),
            Self::SplitCases => write!(f, "split_cases"),
            Self::Simplify => write!(f, "simplify"),
            Self::Rewrite(name) => write!(f, "rewrite({name})"),
            Self::Apply(name) => write!(f, "apply({name})"),
            Self::Unfold(name) => write!(f, "unfold({name})"),
            Self::Contradiction => write!(f, "contradiction"),
        }
    }
}

/// Outcome of applying a tactic to a goal.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TacticResult {
    /// The goal was fully proved.
    Proved,
    /// The goal was decomposed into simpler sub-goals.
    Reduced(Vec<ProofGoal>),
    /// The tactic made progress but did not finish (transformed goal).
    Progress(ProofGoal),
    /// The tactic could not be applied.
    Failed(String),
}

impl TacticResult {
    pub(crate) fn is_proved(&self) -> bool {
        matches!(self, Self::Proved)
    }

    pub(crate) fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// ---------------------------------------------------------------------------
// Proof scripts
// ---------------------------------------------------------------------------

/// A proof script is a structured sequence of tactics, potentially branching.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofScript {
    steps: Vec<ProofScriptStep>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProofScriptStep {
    Tactic(ProofTactic),
    Branch(Vec<ProofScript>),
}

impl ProofScript {
    pub(crate) fn new() -> Self {
        Self { steps: Vec::new() }
    }

    #[must_use]
    pub(crate) fn then(mut self, tactic: ProofTactic) -> Self {
        self.steps.push(ProofScriptStep::Tactic(tactic));
        self
    }

    #[must_use]
    pub(crate) fn branch(mut self, scripts: Vec<ProofScript>) -> Self {
        self.steps.push(ProofScriptStep::Branch(scripts));
        self
    }

    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Execute the script against a goal, producing a tactic result.
    pub(crate) fn execute(&self, goal: &ProofGoal) -> TacticResult {
        let mut current = goal.clone();
        for step in &self.steps {
            match step {
                ProofScriptStep::Tactic(tactic) => {
                    let result = apply_tactic_to_goal(&current, tactic);
                    match result {
                        TacticResult::Proved => return TacticResult::Proved,
                        TacticResult::Progress(g) => current = g,
                        TacticResult::Reduced(sub) => {
                            // All sub-goals must be solved for the script to succeed.
                            // For a linear script we only continue if there is one sub-goal.
                            if let [goal] = sub.as_slice() {
                                current = goal.clone();
                            } else {
                                return TacticResult::Reduced(sub);
                            }
                        }
                        TacticResult::Failed(msg) => return TacticResult::Failed(msg),
                    }
                }
                ProofScriptStep::Branch(scripts) => {
                    // Each branch attempts to prove the current goal independently.
                    let mut all_proved = true;
                    let mut remaining = Vec::new();
                    for script in scripts {
                        let r = script.execute(&current);
                        match r {
                            TacticResult::Proved => {}
                            TacticResult::Failed(msg) => {
                                return TacticResult::Failed(msg);
                            }
                            TacticResult::Progress(g) => {
                                all_proved = false;
                                remaining.push(g);
                            }
                            TacticResult::Reduced(gs) => {
                                all_proved = false;
                                remaining.extend(gs);
                            }
                        }
                    }
                    if all_proved {
                        return TacticResult::Proved;
                    }
                    return TacticResult::Reduced(remaining);
                }
            }
        }
        // Exhausted the script without proving — return whatever we have.
        TacticResult::Progress(current)
    }
}

impl Default for ProofScript {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Proof state
// ---------------------------------------------------------------------------

/// Tracks the current set of goals and solved goals during proof construction.
#[derive(Debug, Clone)]
pub(crate) struct ProofState {
    open_goals: Vec<ProofGoal>,
    solved: Vec<ProofGoal>,
    available_hypotheses: Vec<Expr>,
}

impl ProofState {
    pub(crate) fn new(goal: ProofGoal) -> Self {
        let hyps = goal.hypotheses.clone();
        Self {
            open_goals: vec![goal],
            solved: Vec::new(),
            available_hypotheses: hyps,
        }
    }

    /// Apply a tactic to the first open goal.
    pub(crate) fn apply(&mut self, tactic: &ProofTactic) -> TacticResult {
        let goal = match self.open_goals.first() {
            Some(g) => g.clone(),
            None => return TacticResult::Failed("no open goals".to_owned()),
        };
        let result = apply_tactic_to_goal(&goal, tactic);
        match &result {
            TacticResult::Proved => {
                let g = self.open_goals.remove(0);
                self.solved.push(g);
            }
            TacticResult::Progress(new_goal) => {
                self.open_goals[0] = new_goal.clone();
            }
            TacticResult::Reduced(sub_goals) => {
                self.open_goals.remove(0);
                // Prepend sub-goals so they are addressed first.
                for (i, sg) in sub_goals.iter().enumerate() {
                    self.open_goals.insert(i, sg.clone());
                }
            }
            TacticResult::Failed(_) => {}
        }
        result
    }

    pub(crate) fn is_solved(&self) -> bool {
        self.open_goals.is_empty()
    }

    pub(crate) fn open_goal_count(&self) -> usize {
        self.open_goals.len()
    }

    pub(crate) fn solved_count(&self) -> usize {
        self.solved.len()
    }

    pub(crate) fn current_goal(&self) -> Option<&ProofGoal> {
        self.open_goals.first()
    }
}

// ---------------------------------------------------------------------------
// Automation hints
// ---------------------------------------------------------------------------

/// User-provided hints to guide proof search towards particular strategies.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum AutomationHint {
    /// Suggest induction on a named variable.
    UseInduction(String),
    /// Suggest applying a specific lemma.
    UseLemma(String),
    /// Suggest unfolding a specific definition.
    UseUnfold(String),
    /// Suggest case-splitting.
    UseSplit,
    /// Suggest arithmetic reasoning.
    UseArith,
    /// Limit search depth.
    MaxDepth(usize),
}

// ---------------------------------------------------------------------------
// Tactic library
// ---------------------------------------------------------------------------

/// Predicate that determines whether a tactic is applicable to a goal.
type ApplicabilityFn = Box<dyn Fn(&ProofGoal) -> bool + Send + Sync>;
/// Function that executes a tactic on a goal.
type TacticFn = Box<dyn Fn(&ProofGoal) -> TacticResult + Send + Sync>;

/// An entry in the tactic library.
struct TacticEntry {
    name: String,
    tactic: ProofTactic,
    is_applicable: ApplicabilityFn,
    execute: TacticFn,
}

// Manual Debug — closures are not Debug.
impl fmt::Debug for TacticEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TacticEntry")
            .field("name", &self.name)
            .field("tactic", &self.tactic)
            .finish_non_exhaustive()
    }
}

/// Collection of registered tactics with applicability predicates.
pub(crate) struct TacticLibrary {
    entries: Vec<TacticEntry>,
}

impl fmt::Debug for TacticLibrary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TacticLibrary")
            .field("count", &self.entries.len())
            .finish()
    }
}

impl TacticLibrary {
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Register a tactic with an applicability predicate and an execution function.
    pub(crate) fn register(
        &mut self,
        name: &str,
        tactic: ProofTactic,
        is_applicable: impl Fn(&ProofGoal) -> bool + Send + Sync + 'static,
        execute: impl Fn(&ProofGoal) -> TacticResult + Send + Sync + 'static,
    ) {
        self.entries.push(TacticEntry {
            name: name.to_owned(),
            tactic,
            is_applicable: Box::new(is_applicable),
            execute: Box::new(execute),
        });
    }

    /// Return the tactics applicable to a given goal.
    pub(crate) fn applicable_tactics(&self, goal: &ProofGoal) -> Vec<ProofTactic> {
        self.entries
            .iter()
            .filter(|e| (e.is_applicable)(goal))
            .map(|e| e.tactic.clone())
            .collect()
    }

    /// Execute a registered tactic by name on a goal.
    pub(crate) fn execute_by_name(&self, name: &str, goal: &ProofGoal) -> TacticResult {
        for entry in &self.entries {
            if entry.name == name {
                return (entry.execute)(goal);
            }
        }
        TacticResult::Failed(format!("tactic not found: {name}"))
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

impl Default for TacticLibrary {
    fn default() -> Self {
        Self::new()
    }
}
