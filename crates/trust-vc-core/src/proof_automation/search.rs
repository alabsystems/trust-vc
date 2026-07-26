// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Search configuration and statistics
// ---------------------------------------------------------------------------

/// Configuration for proof search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SearchConfig {
    pub(crate) max_depth: usize,
    pub(crate) max_branches: usize,
    pub(crate) timeout: Duration,
    pub(crate) strategies: Vec<ProofTactic>,
}

impl SearchConfig {
    pub(crate) fn new() -> Self {
        Self {
            max_depth: 10,
            max_branches: 50,
            timeout: Duration::from_secs(5),
            strategies: vec![
                ProofTactic::Simplify,
                ProofTactic::Arith,
                ProofTactic::SplitCases,
                ProofTactic::Contradiction,
                ProofTactic::Auto,
            ],
        }
    }

    #[must_use]
    pub(crate) fn with_max_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    #[must_use]
    pub(crate) fn with_max_branches(mut self, branches: usize) -> Self {
        self.max_branches = branches;
        self
    }

    #[must_use]
    pub(crate) fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    #[must_use]
    pub(crate) fn with_strategies(mut self, strategies: Vec<ProofTactic>) -> Self {
        self.strategies = strategies;
        self
    }
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics gathered during proof search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SearchStats {
    pub(crate) nodes_explored: usize,
    pub(crate) tactics_tried: usize,
    pub(crate) time_elapsed: Duration,
    pub(crate) pruned: usize,
}

impl SearchStats {
    fn new() -> Self {
        Self {
            nodes_explored: 0,
            tactics_tried: 0,
            time_elapsed: Duration::ZERO,
            pruned: 0,
        }
    }
}

/// Result of a proof search attempt.
#[derive(Debug, Clone)]
pub(crate) struct SearchResult {
    pub(crate) found_proof: Option<ProofScript>,
    pub(crate) stats: SearchStats,
}

// ---------------------------------------------------------------------------
// Built-in tactic application
// ---------------------------------------------------------------------------

/// Core tactic application logic (used by both ProofState and ProofScript).
pub(crate) fn apply_tactic_to_goal(goal: &ProofGoal, tactic: &ProofTactic) -> TacticResult {
    match tactic {
        ProofTactic::Simplify => tactic_simplify(goal),
        ProofTactic::Arith => tactic_arith(goal),
        ProofTactic::SplitCases => tactic_split_cases(goal),
        ProofTactic::Contradiction => tactic_contradiction(goal),
        ProofTactic::Induction(scheme) => tactic_induction(goal, scheme),
        ProofTactic::Rewrite(name) => tactic_rewrite(goal, name),
        ProofTactic::Apply(name) => tactic_apply(goal, name),
        ProofTactic::Unfold(name) => tactic_unfold(goal, name),
        ProofTactic::Auto => tactic_auto(goal),
    }
}

/// Simplify: constant folding and trivial identity elimination.
fn tactic_simplify(goal: &ProofGoal) -> TacticResult {
    let simplified = simplify_expr(&goal.expression);
    if simplified == Expr::True || simplified == Expr::BoolLit(true) {
        return TacticResult::Proved;
    }
    if simplified == goal.expression {
        return TacticResult::Failed("simplify: no progress".to_owned());
    }
    TacticResult::Progress(ProofGoal {
        expression: simplified,
        hypotheses: goal.hypotheses.clone(),
        available_lemmas: goal.available_lemmas.clone(),
        label: goal.label.clone(),
    })
}

/// Recursive expression simplifier.
pub(crate) fn simplify_expr(e: &Expr) -> Expr {
    match e {
        // Arithmetic identities.
        Expr::Add(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::int(x + y),
                (_, Expr::IntLit(0)) => a,
                (Expr::IntLit(0), _) => b,
                _ => Expr::add(a, b),
            }
        }
        Expr::Sub(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::int(x - y),
                (_, Expr::IntLit(0)) => a,
                _ if a == b => Expr::int(0),
                _ => Expr::sub(a, b),
            }
        }
        Expr::Mul(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::int(x * y),
                (_, Expr::IntLit(1)) => a,
                (Expr::IntLit(1), _) => b,
                (_, Expr::IntLit(0)) | (Expr::IntLit(0), _) => Expr::int(0),
                _ => Expr::mul(a, b),
            }
        }
        // Boolean identities.
        Expr::And(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::True | Expr::BoolLit(true), _) => b,
                (_, Expr::True | Expr::BoolLit(true)) => a,
                (Expr::False | Expr::BoolLit(false), _)
                | (_, Expr::False | Expr::BoolLit(false)) => Expr::False,
                _ => Expr::and(a, b),
            }
        }
        Expr::Or(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::True | Expr::BoolLit(true), _) | (_, Expr::True | Expr::BoolLit(true)) => {
                    Expr::True
                }
                (Expr::False | Expr::BoolLit(false), _) => b,
                (_, Expr::False | Expr::BoolLit(false)) => a,
                _ => Expr::or(a, b),
            }
        }
        Expr::Not(a) => {
            let a = simplify_expr(a);
            match &a {
                Expr::True | Expr::BoolLit(true) => Expr::False,
                Expr::False | Expr::BoolLit(false) => Expr::True,
                Expr::Not(inner) => *inner.clone(),
                _ => Expr::not(a),
            }
        }
        Expr::Implies(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::False | Expr::BoolLit(false), _) => Expr::True,
                (_, Expr::True | Expr::BoolLit(true)) => Expr::True,
                (Expr::True | Expr::BoolLit(true), _) => b,
                _ => Expr::implies(a, b),
            }
        }
        // Comparison identities.
        Expr::Eq(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            if a == b {
                return Expr::True;
            }
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::BoolLit(x == y),
                _ => Expr::eq(a, b),
            }
        }
        Expr::Lt(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::BoolLit(x < y),
                _ => Expr::lt(a, b),
            }
        }
        Expr::Le(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            if a == b {
                return Expr::True;
            }
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::BoolLit(x <= y),
                _ => Expr::le(a, b),
            }
        }
        Expr::Gt(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::BoolLit(x > y),
                _ => Expr::gt(a, b),
            }
        }
        Expr::Ge(a, b) => {
            let a = simplify_expr(a);
            let b = simplify_expr(b);
            if a == b {
                return Expr::True;
            }
            match (&a, &b) {
                (Expr::IntLit(x), Expr::IntLit(y)) => Expr::BoolLit(x >= y),
                _ => Expr::ge(a, b),
            }
        }
        // Pass-through for leaves and complex nodes.
        other => other.clone(),
    }
}

/// Arithmetic tactic: reason about linear/nonlinear integer arithmetic.
fn tactic_arith(goal: &ProofGoal) -> TacticResult {
    // Attempt constant evaluation first.
    let simplified = simplify_expr(&goal.expression);
    if simplified == Expr::True || simplified == Expr::BoolLit(true) {
        return TacticResult::Proved;
    }

    // Check if any hypothesis directly implies the conclusion.
    for hyp in &goal.hypotheses {
        if hyp == &goal.expression {
            return TacticResult::Proved;
        }
        // Hypothesis x >= 0 proves x >= 0.
        // Hypothesis x > 0 proves x >= 0.
        if let (Expr::Ge(ha, hb), Expr::Ge(ga, gb)) = (hyp, &goal.expression) {
            if ha == ga && hb == gb {
                return TacticResult::Proved;
            }
        }
        if let (Expr::Gt(ha, hb), Expr::Ge(ga, gb)) = (hyp, &goal.expression) {
            if ha == ga && hb == gb {
                return TacticResult::Proved;
            }
        }
    }

    // Bounds checking: x >= 0 && x < len ==> x >= 0.
    if let Expr::Ge(ref var, ref bound) = goal.expression {
        if **bound == Expr::int(0) {
            for hyp in &goal.hypotheses {
                if let Expr::Ge(hvar, hbound) = hyp {
                    if hvar == var && **hbound == Expr::int(0) {
                        return TacticResult::Proved;
                    }
                }
            }
        }
    }

    // Non-negative: a * a >= 0 is always true for integers.
    if let Expr::Ge(ref inner, ref bound) = goal.expression {
        if **bound == Expr::int(0) {
            if let Expr::Mul(ref a, ref b) = **inner {
                if a == b {
                    return TacticResult::Proved;
                }
            }
        }
    }

    // Transitivity: x < y && y < z => x < z.
    if let Expr::Lt(ref a, ref c) = goal.expression {
        for h1 in &goal.hypotheses {
            if let Expr::Lt(ref ha, ref hb) = h1 {
                if ha == a {
                    for h2 in &goal.hypotheses {
                        if let Expr::Lt(ref h2a, ref h2b) = h2 {
                            if h2a == hb && h2b == c {
                                return TacticResult::Proved;
                            }
                        }
                    }
                }
            }
        }
    }

    TacticResult::Failed("arith: cannot discharge goal".to_owned())
}

/// Split cases: decompose a conjunction or disjunction goal.
fn tactic_split_cases(goal: &ProofGoal) -> TacticResult {
    match &goal.expression {
        Expr::And(a, b) => {
            let g1 = ProofGoal {
                expression: *a.clone(),
                hypotheses: goal.hypotheses.clone(),
                available_lemmas: goal.available_lemmas.clone(),
                label: format!("{}_left", goal.label),
            };
            let g2 = ProofGoal {
                expression: *b.clone(),
                hypotheses: goal.hypotheses.clone(),
                available_lemmas: goal.available_lemmas.clone(),
                label: format!("{}_right", goal.label),
            };
            TacticResult::Reduced(vec![g1, g2])
        }
        Expr::Or(a, b) => {
            // To prove A || B, try to prove A; if that fails, try B.
            let g1 = ProofGoal {
                expression: *a.clone(),
                hypotheses: goal.hypotheses.clone(),
                available_lemmas: goal.available_lemmas.clone(),
                label: format!("{}_case1", goal.label),
            };
            let g2 = ProofGoal {
                expression: *b.clone(),
                hypotheses: goal.hypotheses.clone(),
                available_lemmas: goal.available_lemmas.clone(),
                label: format!("{}_case2", goal.label),
            };
            TacticResult::Reduced(vec![g1, g2])
        }
        Expr::Implies(a, b) => {
            // To prove A ==> B, assume A and prove B.
            let mut new_hyps = goal.hypotheses.clone();
            new_hyps.push(*a.clone());
            let g = ProofGoal {
                expression: *b.clone(),
                hypotheses: new_hyps,
                available_lemmas: goal.available_lemmas.clone(),
                label: format!("{}_implies", goal.label),
            };
            TacticResult::Reduced(vec![g])
        }
        _ => TacticResult::Failed(
            "split_cases: goal is not a conjunction/disjunction/implication".to_owned(),
        ),
    }
}

/// Contradiction: check if the hypotheses are contradictory.
fn tactic_contradiction(goal: &ProofGoal) -> TacticResult {
    // Check for P and !P in hypotheses.
    for (i, h1) in goal.hypotheses.iter().enumerate() {
        for h2 in goal.hypotheses.iter().skip(i + 1) {
            if is_negation(h1, h2) || is_negation(h2, h1) {
                return TacticResult::Proved;
            }
        }
    }
    // Check for False in hypotheses.
    for h in &goal.hypotheses {
        if *h == Expr::False || *h == Expr::BoolLit(false) {
            return TacticResult::Proved;
        }
    }
    // Check x < x or x > x patterns.
    for h in &goal.hypotheses {
        if let Expr::Lt(a, b) = h {
            if a == b {
                return TacticResult::Proved;
            }
        }
        if let Expr::Gt(a, b) = h {
            if a == b {
                return TacticResult::Proved;
            }
        }
    }
    TacticResult::Failed("contradiction: no contradiction found".to_owned())
}

fn is_negation(a: &Expr, b: &Expr) -> bool {
    matches!(b, Expr::Not(inner) if **inner == *a)
}

/// Induction tactic: decompose into base and step cases.
fn tactic_induction(goal: &ProofGoal, scheme: &InductionScheme) -> TacticResult {
    if !goal.expression.mentions_var(&scheme.variable) {
        return TacticResult::Failed(format!(
            "induction: variable '{}' not in goal",
            scheme.variable
        ));
    }
    // Base case: assume base_case holds, prove the goal.
    let mut base_hyps = goal.hypotheses.clone();
    base_hyps.push(scheme.base_case.clone());
    let base_goal = ProofGoal {
        expression: goal.expression.clone(),
        hypotheses: base_hyps,
        available_lemmas: goal.available_lemmas.clone(),
        label: format!("{}_base", goal.label),
    };

    // Inductive step: assume step condition and inductive hypothesis hold.
    let mut step_hyps = goal.hypotheses.clone();
    step_hyps.push(scheme.inductive_step.clone());
    step_hyps.push(goal.expression.clone()); // inductive hypothesis
    let step_goal = ProofGoal {
        expression: goal.expression.clone(),
        hypotheses: step_hyps,
        available_lemmas: goal.available_lemmas.clone(),
        label: format!("{}_step", goal.label),
    };

    TacticResult::Reduced(vec![base_goal, step_goal])
}

/// Rewrite: look for an equality hypothesis matching the name.
fn tactic_rewrite(goal: &ProofGoal, name: &str) -> TacticResult {
    if goal.available_lemmas.iter().any(|l| l == name) {
        TacticResult::Progress(ProofGoal {
            expression: goal.expression.clone(),
            hypotheses: goal.hypotheses.clone(),
            available_lemmas: goal.available_lemmas.clone(),
            label: format!("{}_rw_{name}", goal.label),
        })
    } else {
        TacticResult::Failed(format!("rewrite: lemma '{name}' not available"))
    }
}

/// Apply: mark a lemma as used.
fn tactic_apply(goal: &ProofGoal, name: &str) -> TacticResult {
    if goal.available_lemmas.iter().any(|l| l == name) {
        // Application of a lemma whose conclusion matches reduces to
        // proving the lemma's hypotheses. We model this as progress
        // since we don't have the actual lemma body here.
        TacticResult::Progress(ProofGoal {
            expression: goal.expression.clone(),
            hypotheses: goal.hypotheses.clone(),
            available_lemmas: goal.available_lemmas.clone(),
            label: format!("{}_apply_{name}", goal.label),
        })
    } else {
        TacticResult::Failed(format!("apply: lemma '{name}' not available"))
    }
}

/// Unfold: mark a definition as unfolded (symbolic).
fn tactic_unfold(goal: &ProofGoal, name: &str) -> TacticResult {
    if goal.expression.mentions_var(name) || goal.available_lemmas.iter().any(|l| l == name) {
        TacticResult::Progress(ProofGoal {
            expression: goal.expression.clone(),
            hypotheses: goal.hypotheses.clone(),
            available_lemmas: goal.available_lemmas.clone(),
            label: format!("{}_unfold_{name}", goal.label),
        })
    } else {
        TacticResult::Failed(format!("unfold: definition '{name}' not found in goal"))
    }
}

/// Auto: try a cascade of built-in tactics.
fn tactic_auto(goal: &ProofGoal) -> TacticResult {
    // Try simplify first.
    let r = tactic_simplify(goal);
    if r.is_proved() {
        return r;
    }
    let current = match r {
        TacticResult::Progress(g) => g,
        _ => goal.clone(),
    };

    // Try arith.
    let r = tactic_arith(&current);
    if r.is_proved() {
        return r;
    }

    // Try contradiction.
    let r = tactic_contradiction(&current);
    if r.is_proved() {
        return r;
    }

    // Try split.
    let r = tactic_split_cases(&current);
    if !r.is_failed() {
        return r;
    }

    TacticResult::Failed("auto: all built-in tactics exhausted".to_owned())
}

// ---------------------------------------------------------------------------
// Proof search engine
// ---------------------------------------------------------------------------

/// Proof search: explores the tactic space to find a proof for a goal.
#[derive(Debug)]
pub(crate) struct ProofSearch {
    config: SearchConfig,
    hints: Vec<AutomationHint>,
    lemma_db: LemmaDatabase,
}

impl ProofSearch {
    pub(crate) fn new(config: SearchConfig) -> Self {
        Self {
            config,
            hints: Vec::new(),
            lemma_db: LemmaDatabase::new(),
        }
    }

    pub(crate) fn with_hints(mut self, hints: Vec<AutomationHint>) -> Self {
        self.hints = hints;
        self
    }

    pub(crate) fn with_lemma_db(mut self, db: LemmaDatabase) -> Self {
        self.lemma_db = db;
        self
    }

    /// Main search entry point: attempt to find a proof for the goal.
    #[must_use]
    pub(crate) fn search(&self, goal: &ProofGoal) -> SearchResult {
        let start = Instant::now();
        let mut stats = SearchStats::new();
        let mut script = ProofScript::new();

        // Build ordered tactic list from hints + config strategies.
        let tactics = self.ordered_tactics(goal);

        let found = self.search_recursive(goal, &tactics, 0, &mut stats, &start, &mut script);

        stats.time_elapsed = start.elapsed();

        SearchResult {
            found_proof: if found { Some(script) } else { None },
            stats,
        }
    }

    /// Apply a single tactic (public API for external callers).
    pub(crate) fn apply_tactic(&self, goal: &ProofGoal, tactic: &ProofTactic) -> TacticResult {
        apply_tactic_to_goal(goal, tactic)
    }

    /// Build an ordered list of tactics to try, prioritized by hints.
    fn ordered_tactics(&self, _goal: &ProofGoal) -> Vec<ProofTactic> {
        let mut tactics = Vec::new();

        // Hint-driven tactics first.
        for hint in &self.hints {
            match hint {
                AutomationHint::UseInduction(var) => {
                    tactics.push(ProofTactic::Induction(InductionScheme::natural(var)));
                }
                AutomationHint::UseLemma(name) => {
                    tactics.push(ProofTactic::Apply(name.clone()));
                }
                AutomationHint::UseUnfold(name) => {
                    tactics.push(ProofTactic::Unfold(name.clone()));
                }
                AutomationHint::UseSplit => {
                    tactics.push(ProofTactic::SplitCases);
                }
                AutomationHint::UseArith => {
                    tactics.push(ProofTactic::Arith);
                }
                AutomationHint::MaxDepth(_) => {} // Config, not a tactic.
            }
        }

        // Then config-level strategies.
        for s in &self.config.strategies {
            if !tactics.contains(s) {
                tactics.push(s.clone());
            }
        }

        tactics
    }

    fn effective_max_depth(&self) -> usize {
        for hint in &self.hints {
            if let AutomationHint::MaxDepth(d) = hint {
                return *d;
            }
        }
        self.config.max_depth
    }

    fn search_recursive(
        &self,
        goal: &ProofGoal,
        tactics: &[ProofTactic],
        depth: usize,
        stats: &mut SearchStats,
        start: &Instant,
        script: &mut ProofScript,
    ) -> bool {
        let max_depth = self.effective_max_depth();
        if depth >= max_depth {
            stats.pruned += 1;
            return false;
        }
        if start.elapsed() >= self.config.timeout {
            stats.pruned += 1;
            return false;
        }
        if stats.nodes_explored >= self.config.max_branches {
            stats.pruned += 1;
            return false;
        }

        stats.nodes_explored += 1;

        for tactic in tactics {
            stats.tactics_tried += 1;
            let result = apply_tactic_to_goal(goal, tactic);
            match result {
                TacticResult::Proved => {
                    *script = script.clone().then(tactic.clone());
                    return true;
                }
                TacticResult::Progress(new_goal) => {
                    let mut sub_script = ProofScript::new().then(tactic.clone());
                    if self.search_recursive(
                        &new_goal,
                        tactics,
                        depth + 1,
                        stats,
                        start,
                        &mut sub_script,
                    ) {
                        *script = sub_script;
                        return true;
                    }
                }
                TacticResult::Reduced(sub_goals) => {
                    let mut all_proved = true;
                    let mut branch_scripts = Vec::new();
                    for sg in &sub_goals {
                        let mut sub_script = ProofScript::new();
                        if !self.search_recursive(
                            sg,
                            tactics,
                            depth + 1,
                            stats,
                            start,
                            &mut sub_script,
                        ) {
                            all_proved = false;
                            break;
                        }
                        branch_scripts.push(sub_script);
                    }
                    if all_proved {
                        *script = ProofScript::new()
                            .then(tactic.clone())
                            .branch(branch_scripts);
                        return true;
                    }
                }
                TacticResult::Failed(_) => {}
            }
        }

        false
    }
}

// ---------------------------------------------------------------------------
// Built-in automation lemmas for common patterns
// ---------------------------------------------------------------------------

/// Create a lemma database pre-populated with common arithmetic/array lemmas.
pub(crate) fn standard_lemma_database() -> LemmaDatabase {
    let mut db = LemmaDatabase::new();

    // Bounds checking: 0 <= i < len ==> in-bounds.
    db.add_lemma(Lemma::new(
        "bounds_check",
        vec![
            Expr::ge(Expr::var("i"), Expr::int(0)),
            Expr::lt(Expr::var("i"), Expr::var("len")),
        ],
        Expr::and(
            Expr::ge(Expr::var("i"), Expr::int(0)),
            Expr::lt(Expr::var("i"), Expr::var("len")),
        ),
    ));

    // Overflow: a + b does not overflow if both are in range.
    db.add_lemma(Lemma::new(
        "add_no_overflow_i32",
        vec![
            Expr::ge(Expr::var("a"), Expr::int(-2_147_483_648)),
            Expr::le(Expr::var("a"), Expr::int(2_147_483_647)),
            Expr::ge(Expr::var("b"), Expr::int(-2_147_483_648)),
            Expr::le(Expr::var("b"), Expr::int(2_147_483_647)),
            Expr::ge(
                Expr::add(Expr::var("a"), Expr::var("b")),
                Expr::int(-2_147_483_648),
            ),
            Expr::le(
                Expr::add(Expr::var("a"), Expr::var("b")),
                Expr::int(2_147_483_647),
            ),
        ],
        Expr::True,
    ));

    // Non-negative: x * x >= 0.
    db.add_lemma(Lemma::new(
        "square_nonneg",
        vec![],
        Expr::ge(Expr::mul(Expr::var("x"), Expr::var("x")), Expr::int(0)),
    ));

    // Array length non-negative.
    db.add_lemma(Lemma::new(
        "array_len_nonneg",
        vec![],
        Expr::ge(Expr::array_len(Expr::var("arr")), Expr::int(0)),
    ));

    // Sorted array: a[i] <= a[i+1] for all i in range.
    db.add_lemma(Lemma::new(
        "sorted_adjacent",
        vec![
            Expr::fn_app("sorted", vec![Expr::var("arr")]),
            Expr::ge(Expr::var("i"), Expr::int(0)),
            Expr::lt(
                Expr::add(Expr::var("i"), Expr::int(1)),
                Expr::array_len(Expr::var("arr")),
            ),
        ],
        Expr::le(
            Expr::array_index(Expr::var("arr"), Expr::var("i")),
            Expr::array_index(Expr::var("arr"), Expr::add(Expr::var("i"), Expr::int(1))),
        ),
    ));

    // Length bounds: 0 <= len(arr).
    db.add_lemma(Lemma::new(
        "length_nonneg",
        vec![],
        Expr::ge(Expr::array_len(Expr::var("arr")), Expr::int(0)),
    ));

    db
}

// ---------------------------------------------------------------------------
// Helper: build a tactic library with standard built-in tactics
// ---------------------------------------------------------------------------

/// Create a tactic library pre-populated with the built-in strategies.
pub(crate) fn standard_tactic_library() -> TacticLibrary {
    let mut lib = TacticLibrary::new();

    lib.register(
        "simplify",
        ProofTactic::Simplify,
        |_goal| true, // always applicable
        tactic_simplify,
    );

    lib.register(
        "arith",
        ProofTactic::Arith,
        |goal| {
            // Applicable when the goal mentions arithmetic operators.
            matches!(
                goal.expression,
                Expr::Ge(_, _)
                    | Expr::Gt(_, _)
                    | Expr::Le(_, _)
                    | Expr::Lt(_, _)
                    | Expr::Eq(_, _)
                    | Expr::Add(_, _)
                    | Expr::Sub(_, _)
                    | Expr::Mul(_, _)
            )
        },
        tactic_arith,
    );

    lib.register(
        "split_cases",
        ProofTactic::SplitCases,
        |goal| {
            matches!(
                goal.expression,
                Expr::And(_, _) | Expr::Or(_, _) | Expr::Implies(_, _)
            )
        },
        tactic_split_cases,
    );

    lib.register(
        "contradiction",
        ProofTactic::Contradiction,
        |goal| goal.hypotheses.len() >= 2,
        tactic_contradiction,
    );

    lib.register("auto", ProofTactic::Auto, |_goal| true, tactic_auto);

    lib
}
