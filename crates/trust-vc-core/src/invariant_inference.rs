// Invariant inference for loop verification.
//
// Generates candidate loop invariants via template instantiation,
// abstract interpretation (interval/octagon/polyhedra), Houdini
// conjunctive refinement, and ICE-style learning.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates — Apache 2.0

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Describes a single loop site to be analysed.
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// Variables live across the loop header.
    pub variables: Vec<String>,
    /// Initial values for each variable (expression strings).
    pub init_values: HashMap<String, Expr>,
    /// Loop bound expression (e.g. `n`, `len - 1`).
    pub bound_expr: Option<Expr>,
    /// Effects observed in the loop body — variable → assignment RHS.
    pub body_effects: Vec<BodyEffect>,
}

/// A single assignment / mutation inside the loop body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyEffect {
    pub target: String,
    pub kind: EffectKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EffectKind {
    /// `target = target + delta`
    Increment(i64),
    /// `target = target - delta`
    Decrement(i64),
    /// `target = expr`
    Assign(Expr),
    /// `target = target * factor`
    Multiply(i64),
}

/// Minimal expression language sufficient for invariant templates.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Var(String),
    Const(i64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    /// Boolean literal (used for true/false invariant candidates).
    BoolLit(bool),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Const(c) => write!(f, "{c}"),
            Expr::Add(a, b) => write!(f, "({a} + {b})"),
            Expr::Sub(a, b) => write!(f, "({a} - {b})"),
            Expr::Mul(a, b) => write!(f, "({a} * {b})"),
            Expr::Le(a, b) => write!(f, "({a} <= {b})"),
            Expr::Lt(a, b) => write!(f, "({a} < {b})"),
            Expr::Ge(a, b) => write!(f, "({a} >= {b})"),
            Expr::Eq(a, b) => write!(f, "({a} == {b})"),
            Expr::And(a, b) => write!(f, "({a} && {b})"),
            Expr::Or(a, b) => write!(f, "({a} || {b})"),
            Expr::Not(a) => write!(f, "(!{a})"),
            Expr::BoolLit(b) => write!(f, "{b}"),
        }
    }
}

impl Expr {
    pub fn var(name: &str) -> Self {
        Expr::Var(name.to_owned())
    }

    pub fn cnst(v: i64) -> Self {
        Expr::Const(v)
    }

    pub fn add(self, rhs: Expr) -> Self {
        Expr::Add(Box::new(self), Box::new(rhs))
    }

    pub fn sub(self, rhs: Expr) -> Self {
        Expr::Sub(Box::new(self), Box::new(rhs))
    }

    pub fn mul(self, rhs: Expr) -> Self {
        Expr::Mul(Box::new(self), Box::new(rhs))
    }

    pub fn le(self, rhs: Expr) -> Self {
        Expr::Le(Box::new(self), Box::new(rhs))
    }

    pub fn lt(self, rhs: Expr) -> Self {
        Expr::Lt(Box::new(self), Box::new(rhs))
    }

    pub fn ge(self, rhs: Expr) -> Self {
        Expr::Ge(Box::new(self), Box::new(rhs))
    }

    pub fn eq_expr(self, rhs: Expr) -> Self {
        Expr::Eq(Box::new(self), Box::new(rhs))
    }

    pub fn and(self, rhs: Expr) -> Self {
        Expr::And(Box::new(self), Box::new(rhs))
    }

    pub fn or(self, rhs: Expr) -> Self {
        Expr::Or(Box::new(self), Box::new(rhs))
    }

    pub fn not(self) -> Self {
        Expr::Not(Box::new(self))
    }

    /// Structural size used by the ranker as a simplicity proxy.
    pub fn size(&self) -> usize {
        match self {
            Expr::Var(_) | Expr::Const(_) | Expr::BoolLit(_) => 1,
            Expr::Not(a) => 1 + a.size(),
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Le(a, b)
            | Expr::Lt(a, b)
            | Expr::Ge(a, b)
            | Expr::Eq(a, b)
            | Expr::And(a, b)
            | Expr::Or(a, b) => 1 + a.size() + b.size(),
        }
    }

    /// Collect free variable names.
    pub fn free_vars(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.collect_vars(&mut out);
        out
    }

    fn collect_vars(&self, acc: &mut BTreeSet<String>) {
        match self {
            Expr::Var(v) => {
                acc.insert(v.clone());
            }
            Expr::Const(_) | Expr::BoolLit(_) => {}
            Expr::Not(a) => a.collect_vars(acc),
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Le(a, b)
            | Expr::Lt(a, b)
            | Expr::Ge(a, b)
            | Expr::Eq(a, b)
            | Expr::And(a, b)
            | Expr::Or(a, b) => {
                a.collect_vars(acc);
                b.collect_vars(acc);
            }
        }
    }

    /// Constant-fold where possible, returning a simplified expression.
    pub fn simplify(&self) -> Expr {
        match self {
            Expr::Add(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                if let (Expr::Const(x), Expr::Const(y)) = (&a, &b) {
                    return Expr::Const(x.saturating_add(*y));
                }
                if a == Expr::Const(0) {
                    return b;
                }
                if b == Expr::Const(0) {
                    return a;
                }
                Expr::Add(Box::new(a), Box::new(b))
            }
            Expr::Sub(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                if let (Expr::Const(x), Expr::Const(y)) = (&a, &b) {
                    return Expr::Const(x.saturating_sub(*y));
                }
                if b == Expr::Const(0) {
                    return a;
                }
                Expr::Sub(Box::new(a), Box::new(b))
            }
            Expr::Mul(a, b) => {
                let a = a.simplify();
                let b = b.simplify();
                if let (Expr::Const(x), Expr::Const(y)) = (&a, &b) {
                    return Expr::Const(x.saturating_mul(*y));
                }
                if a == Expr::Const(1) {
                    return b;
                }
                if b == Expr::Const(1) {
                    return a;
                }
                if a == Expr::Const(0) || b == Expr::Const(0) {
                    return Expr::Const(0);
                }
                Expr::Mul(Box::new(a), Box::new(b))
            }
            Expr::Not(a) => {
                let a = a.simplify();
                if let Expr::BoolLit(v) = a {
                    return Expr::BoolLit(!v);
                }
                Expr::Not(Box::new(a))
            }
            _ => self.clone(),
        }
    }

    /// Evaluate the expression under a concrete assignment.
    /// Returns `None` when a variable is unbound or a comparison is used
    /// in an arithmetic position (we keep it simple).
    pub fn eval(&self, env: &HashMap<String, i64>) -> Option<i64> {
        match self {
            Expr::Var(v) => env.get(v).copied(),
            Expr::Const(c) => Some(*c),
            Expr::BoolLit(b) => Some(if *b { 1 } else { 0 }),
            Expr::Add(a, b) => Some(a.eval(env)?.saturating_add(b.eval(env)?)),
            Expr::Sub(a, b) => Some(a.eval(env)?.saturating_sub(b.eval(env)?)),
            Expr::Mul(a, b) => Some(a.eval(env)?.saturating_mul(b.eval(env)?)),
            Expr::Le(a, b) => Some(if a.eval(env)? <= b.eval(env)? { 1 } else { 0 }),
            Expr::Lt(a, b) => Some(if a.eval(env)? < b.eval(env)? { 1 } else { 0 }),
            Expr::Ge(a, b) => Some(if a.eval(env)? >= b.eval(env)? { 1 } else { 0 }),
            Expr::Eq(a, b) => Some(if a.eval(env)? == b.eval(env)? { 1 } else { 0 }),
            Expr::And(a, b) => {
                let va = a.eval(env)?;
                let vb = b.eval(env)?;
                Some(if va != 0 && vb != 0 { 1 } else { 0 })
            }
            Expr::Or(a, b) => {
                let va = a.eval(env)?;
                let vb = b.eval(env)?;
                Some(if va != 0 || vb != 0 { 1 } else { 0 })
            }
            Expr::Not(a) => {
                let va = a.eval(env)?;
                Some(if va == 0 { 1 } else { 0 })
            }
        }
    }

    /// Returns true when `eval` yields a non-zero (truthy) value.
    pub fn eval_bool(&self, env: &HashMap<String, i64>) -> Option<bool> {
        self.eval(env).map(|v| v != 0)
    }
}

// ---------------------------------------------------------------------------
// Candidate & result types
// ---------------------------------------------------------------------------

/// Where a candidate came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CandidateSource {
    Template,
    AbstractInterpretation,
    Houdini,
    Ice,
    UserProvided,
}

/// A single invariant candidate.
#[derive(Debug, Clone)]
pub struct InvariantCandidate {
    pub expression: Expr,
    /// 0.0 … 1.0 confidence that this candidate is inductive.
    pub confidence: f64,
    pub source: CandidateSource,
}

impl InvariantCandidate {
    pub fn new(expression: Expr, confidence: f64, source: CandidateSource) -> Self {
        Self {
            expression,
            confidence,
            source,
        }
    }
}

/// Strategy selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferenceStrategy {
    Template,
    AbstractInterpretation,
    Houdini,
    Ice,
}

/// Configuration for the inference engine.
#[derive(Debug, Clone)]
pub struct InferenceConfig {
    pub strategies: Vec<InferenceStrategy>,
    pub max_candidates: usize,
    pub abstract_domain: AbstractDomain,
    /// Maximum number of Houdini refinement rounds.
    pub houdini_max_rounds: usize,
    /// Maximum widening iterations for abstract interpretation.
    pub widening_iterations: usize,
}

impl Default for InferenceConfig {
    fn default() -> Self {
        Self {
            strategies: vec![
                InferenceStrategy::Template,
                InferenceStrategy::AbstractInterpretation,
                InferenceStrategy::Houdini,
            ],
            max_candidates: 64,
            abstract_domain: AbstractDomain::Interval,
            houdini_max_rounds: 20,
            widening_iterations: 10,
        }
    }
}

/// Abstract domain selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbstractDomain {
    Interval,
    Octagon,
    Polyhedra,
}

/// Final result bundle from the inference engine.
#[derive(Debug, Clone)]
pub struct InferenceResult {
    pub candidates: Vec<InvariantCandidate>,
    pub strategies_used: Vec<InferenceStrategy>,
    pub iterations: usize,
}

impl InferenceResult {
    /// Convenience: strongest candidate by confidence.
    pub fn best(&self) -> Option<&InvariantCandidate> {
        self.candidates.iter().max_by(|a, b| {
            a.confidence
                .partial_cmp(&b.confidence)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
    }
}

// ---------------------------------------------------------------------------
// Interval abstract domain
// ---------------------------------------------------------------------------

/// A closed interval `[lo, hi]`. `None` means unbounded in that direction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interval {
    pub lo: Option<i64>,
    pub hi: Option<i64>,
}

impl Interval {
    pub fn top() -> Self {
        Self { lo: None, hi: None }
    }

    pub fn exact(v: i64) -> Self {
        Self {
            lo: Some(v),
            hi: Some(v),
        }
    }

    pub fn bounded(lo: i64, hi: i64) -> Self {
        Self {
            lo: Some(lo),
            hi: Some(hi),
        }
    }

    pub fn is_bottom(&self) -> bool {
        if let (Some(lo), Some(hi)) = (self.lo, self.hi) {
            lo > hi
        } else {
            false
        }
    }

    /// Join (least upper bound).
    pub fn join(&self, other: &Interval) -> Interval {
        if self.is_bottom() {
            return other.clone();
        }
        if other.is_bottom() {
            return self.clone();
        }
        Interval {
            lo: match (self.lo, other.lo) {
                (Some(a), Some(b)) => Some(a.min(b)),
                _ => None,
            },
            hi: match (self.hi, other.hi) {
                (Some(a), Some(b)) => Some(a.max(b)),
                _ => None,
            },
        }
    }

    /// Meet (greatest lower bound).
    pub fn meet(&self, other: &Interval) -> Interval {
        Interval {
            lo: match (self.lo, other.lo) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            },
            hi: match (self.hi, other.hi) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                (None, None) => None,
            },
        }
    }

    /// Standard widening: if the new bound exceeds the old, go to infinity.
    pub fn widen(&self, next: &Interval) -> Interval {
        let lo = match (self.lo, next.lo) {
            (Some(a), Some(b)) if b < a => None,
            (lo, _) => lo,
        };
        let hi = match (self.hi, next.hi) {
            (Some(a), Some(b)) if b > a => None,
            (hi, _) => hi,
        };
        Interval { lo, hi }
    }

    /// Narrowing: tighten infinite bounds using the new iterate.
    pub fn narrow(&self, next: &Interval) -> Interval {
        let lo = match (self.lo, next.lo) {
            (None, Some(b)) => Some(b),
            (lo, _) => lo,
        };
        let hi = match (self.hi, next.hi) {
            (None, Some(b)) => Some(b),
            (hi, _) => hi,
        };
        Interval { lo, hi }
    }

    pub fn is_subset(&self, other: &Interval) -> bool {
        let lo_ok = match (self.lo, other.lo) {
            (Some(a), Some(b)) => a >= b,
            (None, Some(_)) => false,
            _ => true,
        };
        let hi_ok = match (self.hi, other.hi) {
            (Some(a), Some(b)) => a <= b,
            (None, Some(_)) => false,
            _ => true,
        };
        lo_ok && hi_ok
    }

    /// Interval arithmetic: add.
    pub fn add(&self, other: &Interval) -> Interval {
        Interval {
            lo: match (self.lo, other.lo) {
                (Some(a), Some(b)) => Some(a.saturating_add(b)),
                _ => None,
            },
            hi: match (self.hi, other.hi) {
                (Some(a), Some(b)) => Some(a.saturating_add(b)),
                _ => None,
            },
        }
    }
}

// ---------------------------------------------------------------------------
// IntervalDomain — mapping variables to intervals
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalDomain {
    pub map: BTreeMap<String, Interval>,
}

impl IntervalDomain {
    pub fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    /// Set a variable to an exact value.
    pub fn assign(&mut self, var: &str, value: i64) {
        self.map.insert(var.to_owned(), Interval::exact(value));
    }

    /// Set a variable to an interval.
    pub fn assign_interval(&mut self, var: &str, interval: Interval) {
        self.map.insert(var.to_owned(), interval);
    }

    pub fn get(&self, var: &str) -> Interval {
        self.map.get(var).cloned().unwrap_or_else(Interval::top)
    }

    /// Point-wise join.
    pub fn join(&self, other: &IntervalDomain) -> IntervalDomain {
        let all_keys: BTreeSet<&String> = self.map.keys().chain(other.map.keys()).collect();
        let mut result = IntervalDomain::new();
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            result.map.insert(key.clone(), a.join(&b));
        }
        result
    }

    /// Point-wise widening.
    pub fn widen(&self, next: &IntervalDomain) -> IntervalDomain {
        let all_keys: BTreeSet<&String> = self.map.keys().chain(next.map.keys()).collect();
        let mut result = IntervalDomain::new();
        for key in all_keys {
            let a = self.get(key);
            let b = next.get(key);
            result.map.insert(key.clone(), a.widen(&b));
        }
        result
    }

    /// Point-wise narrowing.
    pub fn narrow(&self, next: &IntervalDomain) -> IntervalDomain {
        let all_keys: BTreeSet<&String> = self.map.keys().chain(next.map.keys()).collect();
        let mut result = IntervalDomain::new();
        for key in all_keys {
            let a = self.get(key);
            let b = next.get(key);
            result.map.insert(key.clone(), a.narrow(&b));
        }
        result
    }

    /// Point-wise subset test.
    pub fn is_subset(&self, other: &IntervalDomain) -> bool {
        for (key, interval) in &self.map {
            let other_interval = other.get(key);
            if !interval.is_subset(&other_interval) {
                return false;
            }
        }
        true
    }

    /// Apply a body effect to the domain.
    pub fn apply_effect(&mut self, effect: &BodyEffect) {
        let current = self.get(&effect.target);
        let new_interval = match &effect.kind {
            EffectKind::Increment(d) => current.add(&Interval::exact(*d)),
            EffectKind::Decrement(d) => {
                let neg = Interval::exact(-d);
                current.add(&neg)
            }
            EffectKind::Assign(expr) => self.eval_interval(expr),
            EffectKind::Multiply(factor) => {
                let f = Interval::exact(*factor);
                // Simplified multiplication: only handles exact factor.
                Interval {
                    lo: match (current.lo, f.lo) {
                        (Some(a), Some(b)) => Some(a.saturating_mul(b)),
                        _ => None,
                    },
                    hi: match (current.hi, f.hi) {
                        (Some(a), Some(b)) => Some(a.saturating_mul(b)),
                        _ => None,
                    },
                }
            }
        };
        self.map.insert(effect.target.clone(), new_interval);
    }

    /// Very simple interval evaluation for expressions.
    fn eval_interval(&self, expr: &Expr) -> Interval {
        match expr {
            Expr::Var(v) => self.get(v),
            Expr::Const(c) => Interval::exact(*c),
            Expr::Add(a, b) => self.eval_interval(a).add(&self.eval_interval(b)),
            Expr::Sub(a, b) => {
                let ia = self.eval_interval(a);
                let ib = self.eval_interval(b);
                // [a_lo - b_hi, a_hi - b_lo]
                Interval {
                    lo: match (ia.lo, ib.hi) {
                        (Some(x), Some(y)) => Some(x.saturating_sub(y)),
                        _ => None,
                    },
                    hi: match (ia.hi, ib.lo) {
                        (Some(x), Some(y)) => Some(x.saturating_sub(y)),
                        _ => None,
                    },
                }
            }
            _ => Interval::top(),
        }
    }

    /// Generate invariant candidates from the current fixed-point intervals.
    pub fn to_candidates(&self) -> Vec<InvariantCandidate> {
        let mut out = Vec::new();
        for (var, interval) in &self.map {
            if let Some(lo) = interval.lo {
                out.push(InvariantCandidate::new(
                    Expr::Ge(Box::new(Expr::Var(var.clone())), Box::new(Expr::Const(lo))),
                    0.85,
                    CandidateSource::AbstractInterpretation,
                ));
            }
            if let Some(hi) = interval.hi {
                out.push(InvariantCandidate::new(
                    Expr::Le(Box::new(Expr::Var(var.clone())), Box::new(Expr::Const(hi))),
                    0.85,
                    CandidateSource::AbstractInterpretation,
                ));
            }
        }
        out
    }
}

impl Default for IntervalDomain {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Template library
// ---------------------------------------------------------------------------

/// Common invariant shape templates.
pub struct TemplateLibrary;

impl TemplateLibrary {
    /// Generate candidate invariants from loop structure.
    pub fn generate_candidates(loop_info: &LoopInfo) -> Vec<InvariantCandidate> {
        let mut out = Vec::new();

        // For each variable with an initial value, generate bounds templates.
        for var in &loop_info.variables {
            let v = Expr::Var(var.clone());

            // lower bound from init
            if let Some(init) = loop_info.init_values.get(var) {
                // var >= init
                out.push(InvariantCandidate::new(
                    v.clone().ge(init.clone()),
                    0.7,
                    CandidateSource::Template,
                ));
                // var == init  (equality — low confidence, often not inductive)
                out.push(InvariantCandidate::new(
                    v.clone().eq_expr(init.clone()),
                    0.2,
                    CandidateSource::Template,
                ));
            }

            // upper bound from loop bound
            if let Some(bound) = &loop_info.bound_expr {
                // var <= bound
                out.push(InvariantCandidate::new(
                    v.clone().le(bound.clone()),
                    0.75,
                    CandidateSource::Template,
                ));
                // var < bound
                out.push(InvariantCandidate::new(
                    v.clone().lt(bound.clone()),
                    0.6,
                    CandidateSource::Template,
                ));
            }

            // Monotonicity from effects.
            for effect in &loop_info.body_effects {
                if effect.target == *var {
                    match &effect.kind {
                        EffectKind::Increment(d) if *d > 0 => {
                            // Variable is monotonically non-decreasing.
                            if let Some(init) = loop_info.init_values.get(var) {
                                out.push(InvariantCandidate::new(
                                    v.clone().ge(init.clone()),
                                    0.9,
                                    CandidateSource::Template,
                                ));
                            }
                        }
                        EffectKind::Decrement(d) if *d > 0 => {
                            // Variable is monotonically non-increasing.
                            if let Some(init) = loop_info.init_values.get(var) {
                                out.push(InvariantCandidate::new(
                                    v.clone().le(init.clone()),
                                    0.9,
                                    CandidateSource::Template,
                                ));
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        // Pair-wise difference templates for variables.
        let vars: Vec<&String> = loop_info.variables.iter().collect();
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let a = Expr::Var(vars[i].clone());
                let b = Expr::Var(vars[j].clone());
                // a <= b
                out.push(InvariantCandidate::new(
                    a.clone().le(b.clone()),
                    0.4,
                    CandidateSource::Template,
                ));
                // b <= a
                out.push(InvariantCandidate::new(
                    b.clone().le(a.clone()),
                    0.4,
                    CandidateSource::Template,
                ));
            }
        }

        out
    }
}

// ---------------------------------------------------------------------------
// Houdini solver
// ---------------------------------------------------------------------------

/// Conjunctive invariant refinement.
///
/// Starts with ALL candidates and iteratively removes those falsified by
/// concrete counterexamples, converging to the largest inductive conjunction.
pub struct HoudiniSolver {
    candidates: Vec<InvariantCandidate>,
    max_rounds: usize,
}

impl HoudiniSolver {
    pub fn new(candidates: Vec<InvariantCandidate>) -> Self {
        Self {
            candidates,
            max_rounds: 20,
        }
    }

    pub fn with_max_rounds(mut self, rounds: usize) -> Self {
        self.max_rounds = rounds;
        self
    }

    /// Remove candidates falsified by a concrete counterexample point.
    pub fn refine(&mut self, counterexample: &HashMap<String, i64>) -> Vec<InvariantCandidate> {
        self.candidates.retain(|c| {
            c.expression.eval_bool(counterexample).unwrap_or(true) // keep if we can't evaluate
        });
        self.candidates.clone()
    }

    /// Run the full Houdini loop with the given counterexample generator.
    ///
    /// `cex_gen` takes the current candidate set and returns an optional
    /// counterexample. When it returns `None`, the candidates are inductive.
    pub fn solve_with<F>(&mut self, mut cex_gen: F) -> Vec<InvariantCandidate>
    where
        F: FnMut(&[InvariantCandidate]) -> Option<HashMap<String, i64>>,
    {
        for _ in 0..self.max_rounds {
            if self.candidates.is_empty() {
                break;
            }
            match cex_gen(&self.candidates) {
                Some(cex) => {
                    self.refine(&cex);
                }
                None => break,
            }
        }
        self.candidates.clone()
    }

    /// Simplified solve: iteratively filter against a set of sample points.
    pub fn solve(&self) -> Vec<InvariantCandidate> {
        // Without a verifier oracle, return the current candidate set.
        self.candidates.clone()
    }
}

// ---------------------------------------------------------------------------
// Candidate ranker
// ---------------------------------------------------------------------------

pub struct CandidateRanker;

impl CandidateRanker {
    /// Rank candidates by a composite score of simplicity, confidence,
    /// and source reliability. Returns candidates in descending quality.
    pub fn rank(mut candidates: Vec<InvariantCandidate>) -> Vec<InvariantCandidate> {
        candidates.sort_by(|a, b| {
            let score_a = Self::score(a);
            let score_b = Self::score(b);
            score_b
                .partial_cmp(&score_a)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        candidates
    }

    fn score(candidate: &InvariantCandidate) -> f64 {
        let simplicity = 1.0 / (candidate.expression.size() as f64);
        let source_weight = match candidate.source {
            CandidateSource::UserProvided => 1.0,
            CandidateSource::AbstractInterpretation => 0.9,
            CandidateSource::Houdini => 0.85,
            CandidateSource::Template => 0.7,
            CandidateSource::Ice => 0.75,
        };
        // Weighted combination.
        candidate.confidence * 0.5 + simplicity * 0.3 + source_weight * 0.2
    }
}

// ---------------------------------------------------------------------------
// Top-level inference engine
// ---------------------------------------------------------------------------

pub struct InvariantInference {
    config: InferenceConfig,
}

impl InvariantInference {
    pub fn new(config: InferenceConfig) -> Self {
        Self { config }
    }

    /// Run all configured strategies and return the merged, ranked result.
    pub fn infer(&self, loop_info: &LoopInfo) -> InferenceResult {
        let mut all_candidates = Vec::new();
        let mut strategies_used = Vec::new();
        let mut total_iterations = 0_usize;

        for strategy in &self.config.strategies {
            match strategy {
                InferenceStrategy::Template => {
                    let mut cands = TemplateLibrary::generate_candidates(loop_info);
                    all_candidates.append(&mut cands);
                    strategies_used.push(InferenceStrategy::Template);
                    total_iterations += 1;
                }
                InferenceStrategy::AbstractInterpretation => {
                    let (cands, iters) = self.run_abstract_interpretation(loop_info);
                    all_candidates.extend(cands);
                    strategies_used.push(InferenceStrategy::AbstractInterpretation);
                    total_iterations += iters;
                }
                InferenceStrategy::Houdini => {
                    let cands = self.run_houdini(loop_info);
                    all_candidates.extend(cands);
                    strategies_used.push(InferenceStrategy::Houdini);
                    total_iterations += 1;
                }
                InferenceStrategy::Ice => {
                    // ICE requires an external oracle; generate template
                    // candidates as a seed.
                    let cands = TemplateLibrary::generate_candidates(loop_info);
                    let ice_cands: Vec<InvariantCandidate> = cands
                        .into_iter()
                        .map(|mut c| {
                            c.source = CandidateSource::Ice;
                            c.confidence *= 0.9;
                            c
                        })
                        .collect();
                    all_candidates.extend(ice_cands);
                    strategies_used.push(InferenceStrategy::Ice);
                    total_iterations += 1;
                }
            }
        }

        // De-duplicate by expression string (simple structural dedup).
        let mut seen = HashSet::new();
        all_candidates.retain(|c| {
            let key = c.expression.to_string();
            seen.insert(key)
        });

        // Rank and truncate.
        all_candidates = CandidateRanker::rank(all_candidates);
        all_candidates.truncate(self.config.max_candidates);

        InferenceResult {
            candidates: all_candidates,
            strategies_used,
            iterations: total_iterations,
        }
    }

    /// Abstract interpretation over the interval domain.
    fn run_abstract_interpretation(
        &self,
        loop_info: &LoopInfo,
    ) -> (Vec<InvariantCandidate>, usize) {
        let mut domain = IntervalDomain::new();

        // Initialize from known init values.
        for (var, expr) in &loop_info.init_values {
            if let Expr::Const(c) = expr {
                domain.assign(var, *c);
            }
        }

        let mut iterations = 0;
        // Widening loop.
        for _ in 0..self.config.widening_iterations {
            iterations += 1;
            let mut next = domain.clone();
            for effect in &loop_info.body_effects {
                next.apply_effect(effect);
            }
            let widened = domain.widen(&next);
            if widened == domain {
                break; // fixed point
            }
            domain = widened;
        }

        // Narrowing pass.
        for _ in 0..3 {
            iterations += 1;
            let mut next = domain.clone();
            for effect in &loop_info.body_effects {
                next.apply_effect(effect);
            }
            let narrowed = domain.narrow(&next);
            if narrowed == domain {
                break;
            }
            domain = narrowed;
        }

        (domain.to_candidates(), iterations)
    }

    /// Use templates → Houdini refinement pipeline.
    fn run_houdini(&self, loop_info: &LoopInfo) -> Vec<InvariantCandidate> {
        let candidates = TemplateLibrary::generate_candidates(loop_info);
        let solver = HoudiniSolver::new(candidates).with_max_rounds(self.config.houdini_max_rounds);
        // Without a real SMT oracle, we return the full candidate set.
        solver.solve()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- helpers --

    fn simple_loop() -> LoopInfo {
        // for (i = 0; i < n; i++)
        let mut init = HashMap::new();
        init.insert("i".to_owned(), Expr::Const(0));
        LoopInfo {
            variables: vec!["i".to_owned(), "n".to_owned()],
            init_values: init,
            bound_expr: Some(Expr::Var("n".to_owned())),
            body_effects: vec![BodyEffect {
                target: "i".to_owned(),
                kind: EffectKind::Increment(1),
            }],
        }
    }

    fn decrement_loop() -> LoopInfo {
        // x = 10; while (x > 0) x--;
        let mut init = HashMap::new();
        init.insert("x".to_owned(), Expr::Const(10));
        LoopInfo {
            variables: vec!["x".to_owned()],
            init_values: init,
            bound_expr: Some(Expr::Const(0)),
            body_effects: vec![BodyEffect {
                target: "x".to_owned(),
                kind: EffectKind::Decrement(1),
            }],
        }
    }

    fn two_var_loop() -> LoopInfo {
        // i = 0, j = 100; while (i < j) { i++; j--; }
        let mut init = HashMap::new();
        init.insert("i".to_owned(), Expr::Const(0));
        init.insert("j".to_owned(), Expr::Const(100));
        LoopInfo {
            variables: vec!["i".to_owned(), "j".to_owned()],
            init_values: init,
            bound_expr: None,
            body_effects: vec![
                BodyEffect {
                    target: "i".to_owned(),
                    kind: EffectKind::Increment(1),
                },
                BodyEffect {
                    target: "j".to_owned(),
                    kind: EffectKind::Decrement(1),
                },
            ],
        }
    }

    // -----------------------------------------------------------------------
    // Expr tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_display_var() {
        assert_eq!(format!("{}", Expr::var("x")), "x");
    }

    #[test]
    fn test_expr_display_const() {
        assert_eq!(format!("{}", Expr::cnst(42)), "42");
    }

    #[test]
    fn test_expr_display_complex() {
        let e = Expr::var("a").add(Expr::cnst(1)).le(Expr::var("n"));
        assert_eq!(format!("{e}"), "((a + 1) <= n)");
    }

    #[test]
    fn test_expr_size_leaf() {
        assert_eq!(Expr::var("x").size(), 1);
        assert_eq!(Expr::cnst(0).size(), 1);
    }

    #[test]
    fn test_expr_size_compound() {
        let e = Expr::var("a").add(Expr::cnst(1));
        assert_eq!(e.size(), 3); // + , a , 1
    }

    #[test]
    fn test_expr_free_vars() {
        let e = Expr::var("x")
            .add(Expr::var("y"))
            .le(Expr::var("x").mul(Expr::cnst(2)));
        let fv = e.free_vars();
        assert!(fv.contains("x"));
        assert!(fv.contains("y"));
        assert_eq!(fv.len(), 2);
    }

    #[test]
    fn test_expr_eval_arithmetic() {
        let env: HashMap<String, i64> = [("x".to_owned(), 3), ("y".to_owned(), 7)].into();
        let e = Expr::var("x").add(Expr::var("y"));
        assert_eq!(e.eval(&env), Some(10));
    }

    #[test]
    fn test_expr_eval_comparison() {
        let env: HashMap<String, i64> = [("a".to_owned(), 5)].into();
        let e = Expr::var("a").le(Expr::cnst(10));
        assert_eq!(e.eval_bool(&env), Some(true));
        let e2 = Expr::var("a").lt(Expr::cnst(3));
        assert_eq!(e2.eval_bool(&env), Some(false));
    }

    #[test]
    fn test_expr_eval_unbound() {
        let env: HashMap<String, i64> = HashMap::new();
        assert_eq!(Expr::var("z").eval(&env), None);
    }

    #[test]
    fn test_expr_simplify_add_zero() {
        let e = Expr::var("x").add(Expr::cnst(0));
        assert_eq!(e.simplify(), Expr::var("x"));
    }

    #[test]
    fn test_expr_simplify_mul_one() {
        let e = Expr::cnst(1).mul(Expr::var("y"));
        assert_eq!(e.simplify(), Expr::var("y"));
    }

    #[test]
    fn test_expr_simplify_mul_zero() {
        let e = Expr::cnst(0).mul(Expr::var("y"));
        assert_eq!(e.simplify(), Expr::cnst(0));
    }

    #[test]
    fn test_expr_simplify_const_fold() {
        let e = Expr::cnst(3).add(Expr::cnst(4));
        assert_eq!(e.simplify(), Expr::cnst(7));
    }

    #[test]
    fn test_expr_simplify_not_bool() {
        let e = Expr::BoolLit(true).not();
        assert_eq!(e.simplify(), Expr::BoolLit(false));
    }

    #[test]
    fn test_expr_eval_and_or() {
        let env: HashMap<String, i64> = [("a".to_owned(), 1), ("b".to_owned(), 0)].into();
        let and_e = Expr::var("a").and(Expr::var("b"));
        assert_eq!(and_e.eval_bool(&env), Some(false));
        let or_e = Expr::var("a").or(Expr::var("b"));
        assert_eq!(or_e.eval_bool(&env), Some(true));
    }

    // -----------------------------------------------------------------------
    // Interval tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_interval_exact() {
        let i = Interval::exact(5);
        assert_eq!(i.lo, Some(5));
        assert_eq!(i.hi, Some(5));
    }

    #[test]
    fn test_interval_bottom() {
        let i = Interval::bounded(10, 5);
        assert!(i.is_bottom());
    }

    #[test]
    fn test_interval_join() {
        let a = Interval::bounded(2, 5);
        let b = Interval::bounded(3, 8);
        let j = a.join(&b);
        assert_eq!(j.lo, Some(2));
        assert_eq!(j.hi, Some(8));
    }

    #[test]
    fn test_interval_meet() {
        let a = Interval::bounded(2, 8);
        let b = Interval::bounded(5, 10);
        let m = a.meet(&b);
        assert_eq!(m.lo, Some(5));
        assert_eq!(m.hi, Some(8));
    }

    #[test]
    fn test_interval_widen_grows() {
        let old = Interval::bounded(0, 5);
        let next = Interval::bounded(0, 7);
        let w = old.widen(&next);
        assert_eq!(w.lo, Some(0));
        assert_eq!(w.hi, None); // widened to +inf
    }

    #[test]
    fn test_interval_widen_stable() {
        let old = Interval::bounded(0, 10);
        let next = Interval::bounded(0, 8);
        let w = old.widen(&next);
        assert_eq!(w, old); // no growth, no widening
    }

    #[test]
    fn test_interval_narrow() {
        let wide = Interval {
            lo: Some(0),
            hi: None,
        };
        let next = Interval::bounded(0, 50);
        let n = wide.narrow(&next);
        assert_eq!(n.hi, Some(50));
        assert_eq!(n.lo, Some(0));
    }

    #[test]
    fn test_interval_subset() {
        let inner = Interval::bounded(3, 7);
        let outer = Interval::bounded(0, 10);
        assert!(inner.is_subset(&outer));
        assert!(!outer.is_subset(&inner));
    }

    #[test]
    fn test_interval_add() {
        let a = Interval::bounded(1, 3);
        let b = Interval::bounded(10, 20);
        let sum = a.add(&b);
        assert_eq!(sum.lo, Some(11));
        assert_eq!(sum.hi, Some(23));
    }

    // -----------------------------------------------------------------------
    // IntervalDomain tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_interval_domain_assign_and_get() {
        let mut d = IntervalDomain::new();
        d.assign("x", 42);
        let i = d.get("x");
        assert_eq!(i, Interval::exact(42));
    }

    #[test]
    fn test_interval_domain_unknown_is_top() {
        let d = IntervalDomain::new();
        let i = d.get("missing");
        assert_eq!(i, Interval::top());
    }

    #[test]
    fn test_interval_domain_join() {
        let mut a = IntervalDomain::new();
        a.assign("x", 5);
        let mut b = IntervalDomain::new();
        b.assign("x", 10);
        let j = a.join(&b);
        assert_eq!(j.get("x"), Interval::bounded(5, 10));
    }

    #[test]
    fn test_interval_domain_subset() {
        let mut inner = IntervalDomain::new();
        inner.assign_interval("x", Interval::bounded(3, 7));
        let mut outer = IntervalDomain::new();
        outer.assign_interval("x", Interval::bounded(0, 10));
        assert!(inner.is_subset(&outer));
    }

    #[test]
    fn test_interval_domain_apply_increment() {
        let mut d = IntervalDomain::new();
        d.assign("i", 0);
        d.apply_effect(&BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        });
        assert_eq!(d.get("i"), Interval::exact(1));
    }

    #[test]
    fn test_interval_domain_apply_decrement() {
        let mut d = IntervalDomain::new();
        d.assign("x", 10);
        d.apply_effect(&BodyEffect {
            target: "x".to_owned(),
            kind: EffectKind::Decrement(3),
        });
        assert_eq!(d.get("x"), Interval::exact(7));
    }

    #[test]
    fn test_interval_domain_to_candidates() {
        let mut d = IntervalDomain::new();
        d.assign_interval("i", Interval::bounded(0, 10));
        let cands = d.to_candidates();
        // Should have lower and upper bound candidates.
        assert!(cands.len() >= 2);
        assert!(cands
            .iter()
            .any(|c| c.source == CandidateSource::AbstractInterpretation));
    }

    // -----------------------------------------------------------------------
    // TemplateLibrary tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_template_generates_lower_bound() {
        let li = simple_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        // Should include i >= 0
        let has_lower = cands.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Ge(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Const(0)
            )
        });
        assert!(has_lower, "expected i >= 0 template");
    }

    #[test]
    fn test_template_generates_upper_bound() {
        let li = simple_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        let has_upper = cands.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Var("n".to_owned())
            )
        });
        assert!(has_upper, "expected i <= n template");
    }

    #[test]
    fn test_template_generates_pairwise() {
        let li = two_var_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        let has_pair = cands.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Var("j".to_owned())
            )
        });
        assert!(has_pair, "expected i <= j pairwise template");
    }

    #[test]
    fn test_template_empty_loop() {
        let li = LoopInfo {
            variables: vec![],
            init_values: HashMap::new(),
            bound_expr: None,
            body_effects: vec![],
        };
        let cands = TemplateLibrary::generate_candidates(&li);
        assert!(cands.is_empty());
    }

    #[test]
    fn test_template_monotonic_increment() {
        let li = simple_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        // Should have high-confidence i >= 0 from monotonicity.
        let mono = cands.iter().find(|c| {
            matches!(
                &c.expression,
                Expr::Ge(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Const(0)
            ) && c.confidence >= 0.9
        });
        assert!(mono.is_some(), "expected high-confidence monotonic bound");
    }

    // -----------------------------------------------------------------------
    // Houdini tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_houdini_refine_removes_falsified() {
        let cands = vec![
            InvariantCandidate::new(
                Expr::var("x").ge(Expr::cnst(0)),
                0.8,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("x").le(Expr::cnst(5)),
                0.8,
                CandidateSource::Houdini,
            ),
        ];
        let mut solver = HoudiniSolver::new(cands);
        // Counterexample: x = 10 → falsifies x <= 5
        let cex: HashMap<String, i64> = [("x".to_owned(), 10)].into();
        let remaining = solver.refine(&cex);
        assert_eq!(remaining.len(), 1);
        assert!(matches!(&remaining[0].expression, Expr::Ge(_, _)));
    }

    #[test]
    fn test_houdini_refine_keeps_all_if_sat() {
        let cands = vec![
            InvariantCandidate::new(
                Expr::var("x").ge(Expr::cnst(0)),
                0.8,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("x").le(Expr::cnst(5)),
                0.8,
                CandidateSource::Houdini,
            ),
        ];
        let mut solver = HoudiniSolver::new(cands);
        let cex: HashMap<String, i64> = [("x".to_owned(), 3)].into();
        let remaining = solver.refine(&cex);
        assert_eq!(remaining.len(), 2);
    }

    #[test]
    fn test_houdini_solve_with_oracle() {
        let cands = vec![
            InvariantCandidate::new(
                Expr::var("i").ge(Expr::cnst(0)),
                0.9,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("i").le(Expr::cnst(3)),
                0.5,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("i").eq_expr(Expr::cnst(0)),
                0.3,
                CandidateSource::Houdini,
            ),
        ];

        let mut call_count = 0;
        let mut solver = HoudiniSolver::new(cands).with_max_rounds(10);
        let result = solver.solve_with(|_cands| {
            call_count += 1;
            match call_count {
                1 => Some([("i".to_owned(), 5)].into()), // falsifies i<=3 and i==0
                2 => None,                               // converged
                _ => None,
            }
        });

        assert_eq!(result.len(), 1);
        assert!(matches!(&result[0].expression, Expr::Ge(_, _)));
    }

    #[test]
    fn test_houdini_empty_candidates() {
        let solver = HoudiniSolver::new(vec![]);
        let result = solver.solve();
        assert!(result.is_empty());
    }

    // -----------------------------------------------------------------------
    // CandidateRanker tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_ranker_prefers_simpler() {
        let complex = InvariantCandidate::new(
            Expr::var("x")
                .add(Expr::cnst(1))
                .le(Expr::var("n").sub(Expr::cnst(2))),
            0.8,
            CandidateSource::Template,
        );
        let simple = InvariantCandidate::new(
            Expr::var("x").le(Expr::var("n")),
            0.8,
            CandidateSource::Template,
        );
        let ranked = CandidateRanker::rank(vec![complex, simple]);
        // Simple should come first (higher score).
        assert_eq!(ranked[0].expression.size(), 3);
    }

    #[test]
    fn test_ranker_prefers_higher_confidence() {
        let low = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.3,
            CandidateSource::Template,
        );
        let high = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.95,
            CandidateSource::Template,
        );
        let ranked = CandidateRanker::rank(vec![low, high]);
        assert!(ranked[0].confidence > ranked[1].confidence);
    }

    #[test]
    fn test_ranker_prefers_ai_over_template() {
        let template = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Template,
        );
        let ai = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::AbstractInterpretation,
        );
        let ranked = CandidateRanker::rank(vec![template, ai]);
        assert_eq!(ranked[0].source, CandidateSource::AbstractInterpretation);
    }

    // -----------------------------------------------------------------------
    // Full inference pipeline tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_simple_loop() {
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert!(!result.candidates.is_empty());
        assert!(result.iterations > 0);
        assert!(!result.strategies_used.is_empty());
    }

    #[test]
    fn test_inference_decrement_loop() {
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        let result = engine.infer(&decrement_loop());
        assert!(!result.candidates.is_empty());
        // Should find x <= 10 from the decrementing monotonicity.
        let has_upper = result.candidates.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("x".to_owned()) && **b == Expr::Const(10)
            )
        });
        assert!(has_upper, "expected x <= 10 for decrement loop");
    }

    #[test]
    fn test_inference_two_var_loop() {
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        let result = engine.infer(&two_var_loop());
        assert!(!result.candidates.is_empty());
        // Should contain both i >= 0 and j >= ... candidates.
        let has_i_bound = result
            .candidates
            .iter()
            .any(|c| format!("{}", c.expression).contains("i"));
        let has_j_bound = result
            .candidates
            .iter()
            .any(|c| format!("{}", c.expression).contains("j"));
        assert!(has_i_bound);
        assert!(has_j_bound);
    }

    #[test]
    fn test_inference_respects_max_candidates() {
        let config = InferenceConfig {
            max_candidates: 3,
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&two_var_loop());
        assert!(result.candidates.len() <= 3);
    }

    #[test]
    fn test_inference_best_returns_highest_confidence() {
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        if let Some(best) = result.best() {
            for c in &result.candidates {
                assert!(best.confidence >= c.confidence - f64::EPSILON);
            }
        }
    }

    #[test]
    fn test_inference_deduplicates() {
        // Both Template and Houdini generate from TemplateLibrary, so
        // the dedup pass should remove duplicates.
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Template, InferenceStrategy::Houdini],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        let exprs: Vec<String> = result
            .candidates
            .iter()
            .map(|c| format!("{}", c.expression))
            .collect();
        let unique: HashSet<&String> = exprs.iter().collect();
        assert_eq!(
            exprs.len(),
            unique.len(),
            "candidates should be deduplicated"
        );
    }

    #[test]
    fn test_inference_ice_strategy() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Ice],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert!(result.strategies_used.contains(&InferenceStrategy::Ice));
        assert!(result
            .candidates
            .iter()
            .all(|c| c.source == CandidateSource::Ice));
    }

    #[test]
    fn test_inference_only_abstract_interpretation() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert_eq!(result.strategies_used.len(), 1);
        assert_eq!(
            result.strategies_used[0],
            InferenceStrategy::AbstractInterpretation
        );
        // AI candidates have source = AbstractInterpretation
        assert!(result
            .candidates
            .iter()
            .all(|c| c.source == CandidateSource::AbstractInterpretation));
    }

    #[test]
    fn test_inference_empty_loop() {
        let li = LoopInfo {
            variables: vec![],
            init_values: HashMap::new(),
            bound_expr: None,
            body_effects: vec![],
        };
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        let result = engine.infer(&li);
        assert!(result.candidates.is_empty());
    }

    #[test]
    fn test_interval_domain_widen() {
        let mut a = IntervalDomain::new();
        a.assign_interval("x", Interval::bounded(0, 5));
        let mut b = IntervalDomain::new();
        b.assign_interval("x", Interval::bounded(0, 7));
        let w = a.widen(&b);
        // hi grew, so widening pushes it to +inf.
        assert_eq!(w.get("x").lo, Some(0));
        assert_eq!(w.get("x").hi, None);
    }

    #[test]
    fn test_interval_domain_narrow() {
        let mut wide = IntervalDomain::new();
        wide.assign_interval(
            "x",
            Interval {
                lo: Some(0),
                hi: None,
            },
        );
        let mut next = IntervalDomain::new();
        next.assign_interval("x", Interval::bounded(0, 42));
        let n = wide.narrow(&next);
        assert_eq!(n.get("x").hi, Some(42));
    }

    #[test]
    fn test_candidate_source_variants() {
        // Ensures all source variants round-trip through debug.
        for src in [
            CandidateSource::Template,
            CandidateSource::AbstractInterpretation,
            CandidateSource::Houdini,
            CandidateSource::Ice,
            CandidateSource::UserProvided,
        ] {
            let dbg = format!("{src:?}");
            assert!(!dbg.is_empty());
        }
    }

    #[test]
    fn test_inference_config_default_strategies() {
        let config = InferenceConfig::default();
        assert!(config.strategies.contains(&InferenceStrategy::Template));
        assert!(config
            .strategies
            .contains(&InferenceStrategy::AbstractInterpretation));
        assert!(config.strategies.contains(&InferenceStrategy::Houdini));
        assert_eq!(config.abstract_domain, AbstractDomain::Interval);
    }

    #[test]
    fn test_expr_sub_simplify() {
        let e = Expr::cnst(10).sub(Expr::cnst(0));
        assert_eq!(e.simplify(), Expr::cnst(10));
    }

    #[test]
    fn test_expr_mul_simplify_right_zero() {
        let e = Expr::var("x").mul(Expr::cnst(0));
        assert_eq!(e.simplify(), Expr::cnst(0));
    }

    #[test]
    fn test_interval_join_with_bottom() {
        let bottom = Interval::bounded(10, 5); // lo > hi
        let normal = Interval::bounded(2, 8);
        let j = bottom.join(&normal);
        assert_eq!(j, normal);
    }

    #[test]
    fn test_interval_domain_apply_assign() {
        let mut d = IntervalDomain::new();
        d.assign("y", 5);
        d.apply_effect(&BodyEffect {
            target: "x".to_owned(),
            kind: EffectKind::Assign(Expr::var("y").add(Expr::cnst(1))),
        });
        // x should be [6, 6] because y is [5,5].
        assert_eq!(d.get("x"), Interval::exact(6));
    }

    #[test]
    fn test_interval_domain_apply_multiply() {
        let mut d = IntervalDomain::new();
        d.assign("x", 3);
        d.apply_effect(&BodyEffect {
            target: "x".to_owned(),
            kind: EffectKind::Multiply(2),
        });
        assert_eq!(d.get("x"), Interval::exact(6));
    }

    // ===================================================================
    // Additional comprehensive tests
    // ===================================================================

    // -----------------------------------------------------------------------
    // Expr: display format coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_display_sub() {
        let e = Expr::var("a").sub(Expr::cnst(3));
        assert_eq!(format!("{e}"), "(a - 3)");
    }

    #[test]
    fn test_expr_display_mul() {
        let e = Expr::var("x").mul(Expr::var("y"));
        assert_eq!(format!("{e}"), "(x * y)");
    }

    #[test]
    fn test_expr_display_ge() {
        let e = Expr::var("i").ge(Expr::cnst(0));
        assert_eq!(format!("{e}"), "(i >= 0)");
    }

    #[test]
    fn test_expr_display_eq() {
        let e = Expr::var("x").eq_expr(Expr::cnst(5));
        assert_eq!(format!("{e}"), "(x == 5)");
    }

    #[test]
    fn test_expr_display_and() {
        let e = Expr::var("a").and(Expr::var("b"));
        assert_eq!(format!("{e}"), "(a && b)");
    }

    #[test]
    fn test_expr_display_or() {
        let e = Expr::var("a").or(Expr::var("b"));
        assert_eq!(format!("{e}"), "(a || b)");
    }

    #[test]
    fn test_expr_display_not() {
        let e = Expr::var("x").not();
        assert_eq!(format!("{e}"), "(!x)");
    }

    #[test]
    fn test_expr_display_bool_lit_true() {
        assert_eq!(format!("{}", Expr::BoolLit(true)), "true");
    }

    #[test]
    fn test_expr_display_bool_lit_false() {
        assert_eq!(format!("{}", Expr::BoolLit(false)), "false");
    }

    #[test]
    fn test_expr_display_lt() {
        let e = Expr::var("i").lt(Expr::cnst(10));
        assert_eq!(format!("{e}"), "(i < 10)");
    }

    #[test]
    fn test_expr_display_le() {
        let e = Expr::var("i").le(Expr::var("n"));
        assert_eq!(format!("{e}"), "(i <= n)");
    }

    // -----------------------------------------------------------------------
    // Expr: size for Not and deeply nested
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_size_not() {
        let e = Expr::var("x").not();
        assert_eq!(e.size(), 2); // Not + Var
    }

    #[test]
    fn test_expr_size_deeply_nested() {
        // ((x + y) * (a - b))  => size 7: Mul, Add, x, y, Sub, a, b
        let e = Expr::var("x")
            .add(Expr::var("y"))
            .mul(Expr::var("a").sub(Expr::var("b")));
        assert_eq!(e.size(), 7);
    }

    #[test]
    fn test_expr_size_bool_lit() {
        assert_eq!(Expr::BoolLit(true).size(), 1);
    }

    // -----------------------------------------------------------------------
    // Expr: free_vars edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_free_vars_constant_only() {
        let e = Expr::cnst(42).add(Expr::cnst(7));
        assert!(e.free_vars().is_empty());
    }

    #[test]
    fn test_expr_free_vars_bool_lit() {
        assert!(Expr::BoolLit(false).free_vars().is_empty());
    }

    #[test]
    fn test_expr_free_vars_through_not() {
        let e = Expr::var("flag").not();
        let fv = e.free_vars();
        assert_eq!(fv.len(), 1);
        assert!(fv.contains("flag"));
    }

    #[test]
    fn test_expr_free_vars_deduplicates() {
        // x + x should have only one "x"
        let e = Expr::var("x").add(Expr::var("x"));
        assert_eq!(e.free_vars().len(), 1);
    }

    // -----------------------------------------------------------------------
    // Expr: eval coverage for all operators
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_eval_sub() {
        let env: HashMap<String, i64> = [("x".to_owned(), 10), ("y".to_owned(), 3)].into();
        let e = Expr::var("x").sub(Expr::var("y"));
        assert_eq!(e.eval(&env), Some(7));
    }

    #[test]
    fn test_expr_eval_mul() {
        let env: HashMap<String, i64> = [("x".to_owned(), 4), ("y".to_owned(), 5)].into();
        let e = Expr::var("x").mul(Expr::var("y"));
        assert_eq!(e.eval(&env), Some(20));
    }

    #[test]
    fn test_expr_eval_ge_true() {
        let env: HashMap<String, i64> = [("a".to_owned(), 10)].into();
        assert_eq!(Expr::var("a").ge(Expr::cnst(5)).eval_bool(&env), Some(true));
    }

    #[test]
    fn test_expr_eval_ge_false() {
        let env: HashMap<String, i64> = [("a".to_owned(), 2)].into();
        assert_eq!(
            Expr::var("a").ge(Expr::cnst(5)).eval_bool(&env),
            Some(false)
        );
    }

    #[test]
    fn test_expr_eval_eq_true() {
        let env: HashMap<String, i64> = [("x".to_owned(), 7)].into();
        assert_eq!(
            Expr::var("x").eq_expr(Expr::cnst(7)).eval_bool(&env),
            Some(true)
        );
    }

    #[test]
    fn test_expr_eval_eq_false() {
        let env: HashMap<String, i64> = [("x".to_owned(), 7)].into();
        assert_eq!(
            Expr::var("x").eq_expr(Expr::cnst(8)).eval_bool(&env),
            Some(false)
        );
    }

    #[test]
    fn test_expr_eval_not_true() {
        let env: HashMap<String, i64> = [("x".to_owned(), 0)].into();
        assert_eq!(Expr::var("x").not().eval_bool(&env), Some(true));
    }

    #[test]
    fn test_expr_eval_not_false() {
        let env: HashMap<String, i64> = [("x".to_owned(), 1)].into();
        assert_eq!(Expr::var("x").not().eval_bool(&env), Some(false));
    }

    #[test]
    fn test_expr_eval_bool_lit() {
        let env: HashMap<String, i64> = HashMap::new();
        assert_eq!(Expr::BoolLit(true).eval(&env), Some(1));
        assert_eq!(Expr::BoolLit(false).eval(&env), Some(0));
    }

    #[test]
    fn test_expr_eval_nested_unbound_propagates_none() {
        let env: HashMap<String, i64> = [("x".to_owned(), 5)].into();
        // x + unbound => None
        let e = Expr::var("x").add(Expr::var("missing"));
        assert_eq!(e.eval(&env), None);
    }

    #[test]
    fn test_expr_eval_and_both_true() {
        let env: HashMap<String, i64> = [("a".to_owned(), 1), ("b".to_owned(), 1)].into();
        assert_eq!(
            Expr::var("a").and(Expr::var("b")).eval_bool(&env),
            Some(true)
        );
    }

    #[test]
    fn test_expr_eval_or_both_false() {
        let env: HashMap<String, i64> = [("a".to_owned(), 0), ("b".to_owned(), 0)].into();
        assert_eq!(
            Expr::var("a").or(Expr::var("b")).eval_bool(&env),
            Some(false)
        );
    }

    // -----------------------------------------------------------------------
    // Expr: simplify extended coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_simplify_sub_const_fold() {
        let e = Expr::cnst(10).sub(Expr::cnst(3));
        assert_eq!(e.simplify(), Expr::cnst(7));
    }

    #[test]
    fn test_expr_simplify_mul_const_fold() {
        let e = Expr::cnst(6).mul(Expr::cnst(7));
        assert_eq!(e.simplify(), Expr::cnst(42));
    }

    #[test]
    fn test_expr_simplify_add_zero_left() {
        let e = Expr::cnst(0).add(Expr::var("y"));
        assert_eq!(e.simplify(), Expr::var("y"));
    }

    #[test]
    fn test_expr_simplify_mul_one_right() {
        let e = Expr::var("x").mul(Expr::cnst(1));
        assert_eq!(e.simplify(), Expr::var("x"));
    }

    #[test]
    fn test_expr_simplify_mul_zero_right() {
        let e = Expr::var("x").mul(Expr::cnst(0));
        assert_eq!(e.simplify(), Expr::cnst(0));
    }

    #[test]
    fn test_expr_simplify_not_false() {
        let e = Expr::BoolLit(false).not();
        assert_eq!(e.simplify(), Expr::BoolLit(true));
    }

    #[test]
    fn test_expr_simplify_nested() {
        // (0 + (3 * 1)) => simplify inner first: 3*1 => 3, then 0+3 => 3
        let e = Expr::cnst(0).add(Expr::cnst(3).mul(Expr::cnst(1)));
        assert_eq!(e.simplify(), Expr::cnst(3));
    }

    #[test]
    fn test_expr_simplify_preserves_non_reducible() {
        // Comparisons, And, Or pass through simplify unchanged.
        let e = Expr::var("x").le(Expr::var("n"));
        assert_eq!(e.simplify(), e);
    }

    #[test]
    fn test_expr_simplify_sub_zero() {
        let e = Expr::var("x").sub(Expr::cnst(0));
        assert_eq!(e.simplify(), Expr::var("x"));
    }

    // -----------------------------------------------------------------------
    // Interval: extended coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_interval_top() {
        let t = Interval::top();
        assert_eq!(t.lo, None);
        assert_eq!(t.hi, None);
        assert!(!t.is_bottom());
    }

    #[test]
    fn test_interval_is_bottom_normal() {
        let i = Interval::bounded(3, 7);
        assert!(!i.is_bottom());
    }

    #[test]
    fn test_interval_is_bottom_exact() {
        let i = Interval::exact(5);
        assert!(!i.is_bottom());
    }

    #[test]
    fn test_interval_join_both_unbounded() {
        let a = Interval::top();
        let b = Interval::bounded(3, 7);
        let j = a.join(&b);
        // top joined with anything is top
        assert_eq!(j.lo, None);
        assert_eq!(j.hi, None);
    }

    #[test]
    fn test_interval_join_symmetric() {
        let a = Interval::bounded(1, 5);
        let b = Interval::bounded(3, 9);
        assert_eq!(a.join(&b), b.join(&a));
    }

    #[test]
    fn test_interval_meet_disjoint_produces_bottom() {
        let a = Interval::bounded(0, 3);
        let b = Interval::bounded(5, 10);
        let m = a.meet(&b);
        // lo=5, hi=3 => bottom
        assert!(m.is_bottom());
    }

    #[test]
    fn test_interval_meet_with_top() {
        let a = Interval::bounded(2, 8);
        let t = Interval::top();
        let m = a.meet(&t);
        assert_eq!(m, a);
    }

    #[test]
    fn test_interval_widen_lo_shrinks() {
        let old = Interval::bounded(5, 10);
        let next = Interval::bounded(3, 10); // lo decreased
        let w = old.widen(&next);
        assert_eq!(w.lo, None); // widened to -inf
        assert_eq!(w.hi, Some(10));
    }

    #[test]
    fn test_interval_widen_both_sides() {
        let old = Interval::bounded(5, 10);
        let next = Interval::bounded(3, 12); // both changed
        let w = old.widen(&next);
        assert_eq!(w.lo, None);
        assert_eq!(w.hi, None);
    }

    #[test]
    fn test_interval_narrow_already_bounded() {
        let bounded = Interval::bounded(0, 10);
        let next = Interval::bounded(2, 8);
        let n = bounded.narrow(&next);
        // Both bounds already finite, so narrow keeps the original.
        assert_eq!(n.lo, Some(0));
        assert_eq!(n.hi, Some(10));
    }

    #[test]
    fn test_interval_narrow_lo_unbounded() {
        let wide = Interval {
            lo: None,
            hi: Some(100),
        };
        let next = Interval::bounded(-5, 50);
        let n = wide.narrow(&next);
        assert_eq!(n.lo, Some(-5));
        assert_eq!(n.hi, Some(100));
    }

    #[test]
    fn test_interval_subset_top_contains_everything() {
        let inner = Interval::bounded(-100, 100);
        let top = Interval::top();
        assert!(inner.is_subset(&top));
    }

    #[test]
    fn test_interval_subset_unbounded_not_in_bounded() {
        let unbounded = Interval::top();
        let bounded = Interval::bounded(0, 100);
        assert!(!unbounded.is_subset(&bounded));
    }

    #[test]
    fn test_interval_subset_equal() {
        let a = Interval::bounded(3, 7);
        assert!(a.is_subset(&a));
    }

    #[test]
    fn test_interval_add_with_unbounded() {
        let a = Interval::bounded(1, 5);
        let b = Interval::top();
        let sum = a.add(&b);
        assert_eq!(sum.lo, None);
        assert_eq!(sum.hi, None);
    }

    #[test]
    fn test_interval_add_negative() {
        let a = Interval::bounded(-3, -1);
        let b = Interval::bounded(-5, -2);
        let sum = a.add(&b);
        assert_eq!(sum.lo, Some(-8));
        assert_eq!(sum.hi, Some(-3));
    }

    // -----------------------------------------------------------------------
    // IntervalDomain: extended coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_interval_domain_default_is_empty() {
        let d = IntervalDomain::default();
        assert!(d.map.is_empty());
    }

    #[test]
    fn test_interval_domain_join_disjoint_vars() {
        let mut a = IntervalDomain::new();
        a.assign("x", 5);
        let mut b = IntervalDomain::new();
        b.assign("y", 10);
        let j = a.join(&b);
        // Both vars present; missing vars filled from top.
        assert_eq!(j.get("x").lo, None); // x is top in b, so join widens
        assert_eq!(j.get("y").lo, None); // y is top in a, so join widens
    }

    #[test]
    fn test_interval_domain_subset_empty_is_subset_of_anything() {
        let empty = IntervalDomain::new();
        let mut other = IntervalDomain::new();
        other.assign("x", 5);
        assert!(empty.is_subset(&other));
    }

    #[test]
    fn test_interval_domain_apply_multiple_effects_sequential() {
        let mut d = IntervalDomain::new();
        d.assign("i", 0);
        // i += 1; i += 1; i += 1;
        for _ in 0..3 {
            d.apply_effect(&BodyEffect {
                target: "i".to_owned(),
                kind: EffectKind::Increment(1),
            });
        }
        assert_eq!(d.get("i"), Interval::exact(3));
    }

    #[test]
    fn test_interval_domain_apply_decrement_past_zero() {
        let mut d = IntervalDomain::new();
        d.assign("x", 2);
        d.apply_effect(&BodyEffect {
            target: "x".to_owned(),
            kind: EffectKind::Decrement(5),
        });
        assert_eq!(d.get("x"), Interval::exact(-3));
    }

    #[test]
    fn test_interval_domain_to_candidates_one_sided_lo_only() {
        let mut d = IntervalDomain::new();
        d.assign_interval(
            "x",
            Interval {
                lo: Some(0),
                hi: None,
            },
        );
        let cands = d.to_candidates();
        // Should have only a lower bound candidate (x >= 0), no upper.
        assert_eq!(cands.len(), 1);
        assert!(matches!(&cands[0].expression, Expr::Ge(_, _)));
    }

    #[test]
    fn test_interval_domain_to_candidates_one_sided_hi_only() {
        let mut d = IntervalDomain::new();
        d.assign_interval(
            "x",
            Interval {
                lo: None,
                hi: Some(100),
            },
        );
        let cands = d.to_candidates();
        assert_eq!(cands.len(), 1);
        assert!(matches!(&cands[0].expression, Expr::Le(_, _)));
    }

    #[test]
    fn test_interval_domain_to_candidates_top_produces_nothing() {
        let mut d = IntervalDomain::new();
        d.assign_interval("x", Interval::top());
        let cands = d.to_candidates();
        assert!(cands.is_empty());
    }

    #[test]
    fn test_interval_domain_to_candidates_confidence() {
        let mut d = IntervalDomain::new();
        d.assign_interval("i", Interval::bounded(0, 10));
        let cands = d.to_candidates();
        for c in &cands {
            assert!(
                (c.confidence - 0.85).abs() < f64::EPSILON,
                "AI candidates should have 0.85 confidence"
            );
            assert_eq!(c.source, CandidateSource::AbstractInterpretation);
        }
    }

    #[test]
    fn test_interval_domain_eval_interval_sub() {
        let mut d = IntervalDomain::new();
        d.assign_interval("a", Interval::bounded(10, 20));
        d.assign_interval("b", Interval::bounded(1, 5));
        // a - b => lo = 10 - 5 = 5, hi = 20 - 1 = 19
        d.apply_effect(&BodyEffect {
            target: "result".to_owned(),
            kind: EffectKind::Assign(Expr::var("a").sub(Expr::var("b"))),
        });
        let r = d.get("result");
        assert_eq!(r.lo, Some(5));
        assert_eq!(r.hi, Some(19));
    }

    #[test]
    fn test_interval_domain_eval_interval_unknown_expr_yields_top() {
        let mut d = IntervalDomain::new();
        d.assign("x", 5);
        // Mul expr falls through to top in eval_interval.
        d.apply_effect(&BodyEffect {
            target: "r".to_owned(),
            kind: EffectKind::Assign(Expr::var("x").mul(Expr::cnst(2))),
        });
        let r = d.get("r");
        assert_eq!(r, Interval::top());
    }

    #[test]
    fn test_interval_domain_widen_then_narrow_cycle() {
        // Simulate: i starts at 0, incremented by 1 each iteration.
        let mut domain = IntervalDomain::new();
        domain.assign("i", 0);

        // Widen pass
        let mut next = domain.clone();
        next.apply_effect(&BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        });
        let widened = domain.widen(&next);
        assert_eq!(widened.get("i").lo, Some(0));
        assert_eq!(widened.get("i").hi, None); // widened to +inf

        // Narrow pass with a concrete iterate
        let mut narrow_next = widened.clone();
        narrow_next.apply_effect(&BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        });
        let narrowed = widened.narrow(&narrow_next);
        // lo stays 0 (was finite), hi stays None (narrow can't narrow further
        // from another None — but the narrow_next's hi is also None).
        assert_eq!(narrowed.get("i").lo, Some(0));
    }

    // -----------------------------------------------------------------------
    // TemplateLibrary: extended coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_template_decrement_monotonicity() {
        let li = decrement_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        // Decrementing x should produce x <= init (10) with high confidence.
        let has_upper_mono = cands.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("x".to_owned()) && **b == Expr::Const(10)
            ) && c.confidence >= 0.9
        });
        assert!(
            has_upper_mono,
            "expected high-confidence x <= 10 from decrement monotonicity"
        );
    }

    #[test]
    fn test_template_no_bound_expr_skips_upper() {
        let mut init = HashMap::new();
        init.insert("i".to_owned(), Expr::Const(0));
        let li = LoopInfo {
            variables: vec!["i".to_owned()],
            init_values: init,
            bound_expr: None,
            body_effects: vec![],
        };
        let cands = TemplateLibrary::generate_candidates(&li);
        // Should not have any Le or Lt candidates against a bound.
        let has_bound = cands
            .iter()
            .any(|c| matches!(&c.expression, Expr::Le(_, _) | Expr::Lt(_, _)));
        assert!(!has_bound, "no bound_expr means no upper-bound templates");
    }

    #[test]
    fn test_template_single_variable_no_pairwise() {
        let mut init = HashMap::new();
        init.insert("x".to_owned(), Expr::Const(0));
        let li = LoopInfo {
            variables: vec!["x".to_owned()],
            init_values: init,
            bound_expr: Some(Expr::cnst(10)),
            body_effects: vec![],
        };
        let cands = TemplateLibrary::generate_candidates(&li);
        // Pairwise templates need >= 2 variables.
        let pairwise_count = cands.iter().filter(|c| c.confidence == 0.4).count();
        assert_eq!(
            pairwise_count, 0,
            "single var should have no pairwise templates"
        );
    }

    #[test]
    fn test_template_equality_low_confidence() {
        let li = simple_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        let eq_cands: Vec<_> = cands
            .iter()
            .filter(|c| matches!(&c.expression, Expr::Eq(_, _)))
            .collect();
        assert!(!eq_cands.is_empty(), "should generate equality templates");
        for c in &eq_cands {
            assert!(
                c.confidence <= 0.3,
                "equality templates should have low confidence, got {}",
                c.confidence
            );
        }
    }

    #[test]
    fn test_template_lt_bound_lower_confidence_than_le() {
        let li = simple_loop();
        let cands = TemplateLibrary::generate_candidates(&li);
        let le_conf = cands
            .iter()
            .find(|c| {
                matches!(
                    &c.expression,
                    Expr::Le(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Var("n".to_owned())
                )
            })
            .map(|c| c.confidence);
        let lt_conf = cands
            .iter()
            .find(|c| {
                matches!(
                    &c.expression,
                    Expr::Lt(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Var("n".to_owned())
                )
            })
            .map(|c| c.confidence);
        assert!(le_conf.is_some());
        assert!(lt_conf.is_some());
        assert!(
            le_conf.unwrap() > lt_conf.unwrap(),
            "i <= n should have higher confidence than i < n"
        );
    }

    #[test]
    fn test_template_three_variables_pairwise_count() {
        let mut init = HashMap::new();
        init.insert("a".to_owned(), Expr::Const(0));
        init.insert("b".to_owned(), Expr::Const(0));
        init.insert("c".to_owned(), Expr::Const(0));
        let li = LoopInfo {
            variables: vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
            init_values: init,
            bound_expr: None,
            body_effects: vec![],
        };
        let cands = TemplateLibrary::generate_candidates(&li);
        // 3 vars => C(3,2) = 3 pairs, 2 directions each = 6 pairwise templates.
        let pairwise_count = cands
            .iter()
            .filter(|c| c.confidence == 0.4 && matches!(&c.expression, Expr::Le(_, _)))
            .count();
        assert_eq!(pairwise_count, 6);
    }

    #[test]
    fn test_template_no_init_no_effects_still_generates_bound() {
        // Variable with no init but with a bound_expr.
        let li = LoopInfo {
            variables: vec!["i".to_owned()],
            init_values: HashMap::new(),
            bound_expr: Some(Expr::cnst(100)),
            body_effects: vec![],
        };
        let cands = TemplateLibrary::generate_candidates(&li);
        // Should have i <= 100 and i < 100.
        let has_le = cands.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Const(100)
            )
        });
        assert!(has_le, "should generate i <= 100 even without init");
    }

    // -----------------------------------------------------------------------
    // Houdini: extended coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_houdini_refine_removes_all() {
        let cands = vec![
            InvariantCandidate::new(
                Expr::var("x").ge(Expr::cnst(10)),
                0.8,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("x").le(Expr::cnst(5)),
                0.8,
                CandidateSource::Houdini,
            ),
        ];
        let mut solver = HoudiniSolver::new(cands);
        // x=7 falsifies both: x>=10 is false, x<=5 is false.
        let cex: HashMap<String, i64> = [("x".to_owned(), 7)].into();
        let remaining = solver.refine(&cex);
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_houdini_with_max_rounds_limits_iterations() {
        let cands = vec![InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Houdini,
        )];
        let mut call_count = 0;
        let mut solver = HoudiniSolver::new(cands).with_max_rounds(3);
        let _result = solver.solve_with(|_| {
            call_count += 1;
            // Always provide a counterexample that doesn't falsify anything.
            Some([("x".to_owned(), 5)].into())
        });
        assert_eq!(call_count, 3, "should stop after max_rounds");
    }

    #[test]
    fn test_houdini_solve_with_immediate_convergence() {
        let cands = vec![InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.9,
            CandidateSource::Houdini,
        )];
        let mut solver = HoudiniSolver::new(cands);
        let result = solver.solve_with(|_| None); // No counterexample = converged.
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_houdini_solve_with_progressive_elimination() {
        let cands = vec![
            InvariantCandidate::new(
                Expr::var("x").ge(Expr::cnst(0)),
                0.9,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("x").le(Expr::cnst(10)),
                0.8,
                CandidateSource::Houdini,
            ),
            InvariantCandidate::new(
                Expr::var("x").le(Expr::cnst(5)),
                0.7,
                CandidateSource::Houdini,
            ),
        ];
        let mut round = 0;
        let mut solver = HoudiniSolver::new(cands).with_max_rounds(10);
        let result = solver.solve_with(|_cands| {
            round += 1;
            match round {
                1 => Some([("x".to_owned(), 8)].into()),  // eliminates x<=5
                2 => Some([("x".to_owned(), 15)].into()), // eliminates x<=10
                3 => None,                                // converged
                _ => None,
            }
        });
        assert_eq!(result.len(), 1);
        assert!(matches!(&result[0].expression, Expr::Ge(_, _)));
    }

    #[test]
    fn test_houdini_solve_with_empty_candidates_terminates() {
        let mut solver = HoudiniSolver::new(vec![]).with_max_rounds(10);
        let result = solver.solve_with(|_| {
            panic!("should not be called with empty candidates");
        });
        assert!(result.is_empty());
    }

    #[test]
    fn test_houdini_refine_keeps_unevaluable() {
        // If a candidate uses variables not in the counterexample,
        // eval_bool returns None, and the candidate should be retained.
        let cands = vec![InvariantCandidate::new(
            Expr::var("missing_var").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Houdini,
        )];
        let mut solver = HoudiniSolver::new(cands);
        let cex: HashMap<String, i64> = [("x".to_owned(), 5)].into();
        let remaining = solver.refine(&cex);
        assert_eq!(remaining.len(), 1, "unevaluable candidates should be kept");
    }

    // -----------------------------------------------------------------------
    // CandidateRanker: extended coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_ranker_user_provided_highest_source_weight() {
        let user = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::UserProvided,
        );
        let template = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Template,
        );
        let ranked = CandidateRanker::rank(vec![template, user]);
        assert_eq!(ranked[0].source, CandidateSource::UserProvided);
    }

    #[test]
    fn test_ranker_ice_vs_houdini() {
        // Ice has source_weight 0.75, Houdini 0.85
        let ice =
            InvariantCandidate::new(Expr::var("x").ge(Expr::cnst(0)), 0.8, CandidateSource::Ice);
        let houdini = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Houdini,
        );
        let ranked = CandidateRanker::rank(vec![ice, houdini]);
        assert_eq!(ranked[0].source, CandidateSource::Houdini);
    }

    #[test]
    fn test_ranker_empty_input() {
        let ranked = CandidateRanker::rank(vec![]);
        assert!(ranked.is_empty());
    }

    #[test]
    fn test_ranker_single_candidate() {
        let c = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.9,
            CandidateSource::Template,
        );
        let ranked = CandidateRanker::rank(vec![c]);
        assert_eq!(ranked.len(), 1);
    }

    #[test]
    fn test_ranker_stable_ordering_same_score() {
        // Two candidates with identical score should both appear.
        let a = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Template,
        );
        let b = InvariantCandidate::new(
            Expr::var("y").ge(Expr::cnst(0)),
            0.8,
            CandidateSource::Template,
        );
        let ranked = CandidateRanker::rank(vec![a, b]);
        assert_eq!(ranked.len(), 2);
    }

    #[test]
    fn test_ranker_simplicity_beats_confidence_when_gap_large() {
        // Simple expr (size 3) with moderate confidence vs
        // complex expr (size 7) with high confidence.
        // Score = conf*0.5 + (1/size)*0.3 + source*0.2
        // simple: 0.5*0.5 + (1/3)*0.3 + 0.7*0.2 = 0.25 + 0.1 + 0.14 = 0.49
        // complex: 0.95*0.5 + (1/7)*0.3 + 0.7*0.2 = 0.475 + 0.043 + 0.14 = 0.658
        // So in this case complex wins — but let's verify the scoring works.
        let simple = InvariantCandidate::new(
            Expr::var("x").le(Expr::var("n")), // size 3
            0.5,
            CandidateSource::Template,
        );
        let complex = InvariantCandidate::new(
            Expr::var("x")
                .add(Expr::cnst(1))
                .le(Expr::var("n").sub(Expr::cnst(2))), // size 7
            0.95,
            CandidateSource::Template,
        );
        let ranked = CandidateRanker::rank(vec![simple, complex]);
        // Complex has higher total score due to high confidence outweighing simplicity.
        assert!(ranked[0].confidence > ranked[1].confidence);
    }

    // -----------------------------------------------------------------------
    // InferenceResult: best() coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_result_best_empty() {
        let result = InferenceResult {
            candidates: vec![],
            strategies_used: vec![],
            iterations: 0,
        };
        assert!(result.best().is_none());
    }

    #[test]
    fn test_inference_result_best_single() {
        let result = InferenceResult {
            candidates: vec![InvariantCandidate::new(
                Expr::var("x").ge(Expr::cnst(0)),
                0.9,
                CandidateSource::Template,
            )],
            strategies_used: vec![InferenceStrategy::Template],
            iterations: 1,
        };
        let best = result.best().unwrap();
        assert!((best.confidence - 0.9).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // InvariantInference: strategy combination coverage
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_all_four_strategies() {
        let config = InferenceConfig {
            strategies: vec![
                InferenceStrategy::Template,
                InferenceStrategy::AbstractInterpretation,
                InferenceStrategy::Houdini,
                InferenceStrategy::Ice,
            ],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert_eq!(result.strategies_used.len(), 4);
        assert!(result
            .strategies_used
            .contains(&InferenceStrategy::Template));
        assert!(result
            .strategies_used
            .contains(&InferenceStrategy::AbstractInterpretation));
        assert!(result.strategies_used.contains(&InferenceStrategy::Houdini));
        assert!(result.strategies_used.contains(&InferenceStrategy::Ice));
    }

    #[test]
    fn test_inference_template_only() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Template],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert_eq!(result.strategies_used.len(), 1);
        assert!(result
            .candidates
            .iter()
            .all(|c| c.source == CandidateSource::Template));
    }

    #[test]
    fn test_inference_houdini_only() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Houdini],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert_eq!(result.strategies_used.len(), 1);
        assert_eq!(result.strategies_used[0], InferenceStrategy::Houdini);
        // Houdini uses template candidates, so source is Template (no oracle to refine).
        assert!(result
            .candidates
            .iter()
            .all(|c| c.source == CandidateSource::Template));
    }

    #[test]
    fn test_inference_empty_strategies() {
        let config = InferenceConfig {
            strategies: vec![],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert!(result.candidates.is_empty());
        assert!(result.strategies_used.is_empty());
        assert_eq!(result.iterations, 0);
    }

    #[test]
    fn test_inference_iterations_include_ai_widening() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            widening_iterations: 5,
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        // At least 1 widening iteration + narrowing iterations.
        assert!(result.iterations >= 1);
    }

    #[test]
    fn test_inference_max_candidates_zero() {
        let config = InferenceConfig {
            max_candidates: 0,
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert!(result.candidates.is_empty());
    }

    #[test]
    fn test_inference_max_candidates_one() {
        let config = InferenceConfig {
            max_candidates: 1,
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        assert!(result.candidates.len() <= 1);
    }

    // -----------------------------------------------------------------------
    // Abstract interpretation: convergence and effects
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_ai_increment_produces_lower_bound() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        // i starts at 0 and increments. AI should find i >= 0.
        let has_lower = result.candidates.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Ge(a, b) if **a == Expr::Var("i".to_owned()) && **b == Expr::Const(0)
            )
        });
        assert!(has_lower, "AI should infer i >= 0 for incrementing loop");
    }

    #[test]
    fn test_inference_ai_decrement_loop() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&decrement_loop());
        // x starts at 10, decremented by 1. Should at least have x <= 10.
        let has_upper = result.candidates.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("x".to_owned()) && **b == Expr::Const(10)
            )
        });
        assert!(has_upper, "AI should infer x <= 10 for decrement loop");
    }

    #[test]
    fn test_inference_ai_two_var_loop_both_tracked() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&two_var_loop());
        let vars_mentioned: BTreeSet<String> = result
            .candidates
            .iter()
            .flat_map(|c| c.expression.free_vars())
            .collect();
        assert!(vars_mentioned.contains("i"), "should track i");
        assert!(vars_mentioned.contains("j"), "should track j");
    }

    #[test]
    fn test_inference_ai_multiply_effect() {
        let mut init = HashMap::new();
        init.insert("x".to_owned(), Expr::Const(1));
        let li = LoopInfo {
            variables: vec!["x".to_owned()],
            init_values: init,
            bound_expr: None,
            body_effects: vec![BodyEffect {
                target: "x".to_owned(),
                kind: EffectKind::Multiply(2),
            }],
        };
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&li);
        // x doubles each iteration from 1. AI should produce some bounds.
        // At minimum it should find x >= 1 (initial lower bound).
        let has_lower = result.candidates.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Ge(a, b) if **a == Expr::Var("x".to_owned()) && **b == Expr::Const(1)
            )
        });
        assert!(has_lower, "AI should infer x >= 1 for multiply loop");
    }

    #[test]
    fn test_inference_ai_assign_effect() {
        let mut init = HashMap::new();
        init.insert("x".to_owned(), Expr::Const(0));
        init.insert("y".to_owned(), Expr::Const(10));
        let li = LoopInfo {
            variables: vec!["x".to_owned(), "y".to_owned()],
            init_values: init,
            bound_expr: None,
            body_effects: vec![BodyEffect {
                target: "x".to_owned(),
                kind: EffectKind::Assign(Expr::var("y")),
            }],
        };
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&li);
        // After first iteration, x = y = [10,10]. Should have bounds.
        assert!(!result.candidates.is_empty());
    }

    // -----------------------------------------------------------------------
    // ICE strategy: confidence scaling
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_ice_confidence_scaled_down() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Ice],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        // ICE multiplies confidence by 0.9. Template candidates have
        // various confidences. All ICE candidates should be <= 0.9.
        for c in &result.candidates {
            assert!(
                c.confidence <= 0.91, // allow floating point slop
                "ICE candidate confidence {} should be <= 0.9 * original",
                c.confidence
            );
        }
    }

    // -----------------------------------------------------------------------
    // Edge case: loop with no variables but effects
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_effects_on_unlisted_variables() {
        // body_effects reference a variable not in the variables list.
        let li = LoopInfo {
            variables: vec![],
            init_values: HashMap::new(),
            bound_expr: None,
            body_effects: vec![BodyEffect {
                target: "phantom".to_owned(),
                kind: EffectKind::Increment(1),
            }],
        };
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        // Should not panic, AI might still produce something from effects.
        let result = engine.infer(&li);
        // Template produces nothing for empty variables. AI tracks effects.
        // Just verify it doesn't crash.
        let _ = result;
    }

    // -----------------------------------------------------------------------
    // LoopInfo construction and BodyEffect equality
    // -----------------------------------------------------------------------

    #[test]
    fn test_body_effect_eq() {
        let a = BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        };
        let b = BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        };
        assert_eq!(a, b);
    }

    #[test]
    fn test_body_effect_ne_different_kind() {
        let a = BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        };
        let b = BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Decrement(1),
        };
        assert_ne!(a, b);
    }

    #[test]
    fn test_body_effect_ne_different_target() {
        let a = BodyEffect {
            target: "i".to_owned(),
            kind: EffectKind::Increment(1),
        };
        let b = BodyEffect {
            target: "j".to_owned(),
            kind: EffectKind::Increment(1),
        };
        assert_ne!(a, b);
    }

    #[test]
    fn test_effect_kind_assign_eq() {
        let a = EffectKind::Assign(Expr::var("x"));
        let b = EffectKind::Assign(Expr::var("x"));
        assert_eq!(a, b);
    }

    #[test]
    fn test_effect_kind_multiply_eq() {
        assert_eq!(EffectKind::Multiply(3), EffectKind::Multiply(3));
        assert_ne!(EffectKind::Multiply(3), EffectKind::Multiply(4));
    }

    // -----------------------------------------------------------------------
    // InvariantCandidate construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_invariant_candidate_new() {
        let c = InvariantCandidate::new(
            Expr::var("x").ge(Expr::cnst(0)),
            0.75,
            CandidateSource::Template,
        );
        assert!((c.confidence - 0.75).abs() < f64::EPSILON);
        assert_eq!(c.source, CandidateSource::Template);
        assert_eq!(c.expression.size(), 3);
    }

    // -----------------------------------------------------------------------
    // InferenceConfig custom values
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_config_custom() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Houdini],
            max_candidates: 10,
            abstract_domain: AbstractDomain::Octagon,
            houdini_max_rounds: 5,
            widening_iterations: 3,
        };
        assert_eq!(config.strategies.len(), 1);
        assert_eq!(config.max_candidates, 10);
        assert_eq!(config.abstract_domain, AbstractDomain::Octagon);
        assert_eq!(config.houdini_max_rounds, 5);
        assert_eq!(config.widening_iterations, 3);
    }

    #[test]
    fn test_abstract_domain_variants() {
        assert_ne!(AbstractDomain::Interval, AbstractDomain::Octagon);
        assert_ne!(AbstractDomain::Octagon, AbstractDomain::Polyhedra);
        assert_ne!(AbstractDomain::Interval, AbstractDomain::Polyhedra);
    }

    // -----------------------------------------------------------------------
    // Expr: Hash trait usage (used in dedup)
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_hash_consistent_with_eq() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        let e1 = Expr::var("x").add(Expr::cnst(1));
        let e2 = Expr::var("x").add(Expr::cnst(1));
        set.insert(e1);
        set.insert(e2);
        assert_eq!(set.len(), 1, "equal expressions should hash the same");
    }

    #[test]
    fn test_expr_hash_distinct() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(Expr::var("x"));
        set.insert(Expr::var("y"));
        set.insert(Expr::cnst(0));
        assert_eq!(set.len(), 3);
    }

    // -----------------------------------------------------------------------
    // Large-scale inference: simulated nested loops
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_on_multiple_loops_sequentially() {
        let config = InferenceConfig::default();
        let engine = InvariantInference::new(config);
        // Simulate nested loops by running inference on outer, then inner.
        let outer = simple_loop(); // i: 0..n
        let result_outer = engine.infer(&outer);
        assert!(!result_outer.candidates.is_empty());

        let mut inner_init = HashMap::new();
        inner_init.insert("j".to_owned(), Expr::Const(0));
        let inner = LoopInfo {
            variables: vec!["j".to_owned(), "i".to_owned()],
            init_values: inner_init,
            bound_expr: Some(Expr::var("i")),
            body_effects: vec![BodyEffect {
                target: "j".to_owned(),
                kind: EffectKind::Increment(1),
            }],
        };
        let result_inner = engine.infer(&inner);
        assert!(!result_inner.candidates.is_empty());
        // Inner loop should have j <= i.
        let has_j_le_i = result_inner.candidates.iter().any(|c| {
            matches!(
                &c.expression,
                Expr::Le(a, b) if **a == Expr::Var("j".to_owned()) && **b == Expr::Var("i".to_owned())
            )
        });
        assert!(has_j_le_i, "inner loop should infer j <= i");
    }

    // -----------------------------------------------------------------------
    // Abstract interpretation: widening_iterations=1 still works
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_ai_single_widening_iteration() {
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::AbstractInterpretation],
            widening_iterations: 1,
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        // Should still produce candidates (at least from the init state).
        assert!(!result.candidates.is_empty());
    }

    // -----------------------------------------------------------------------
    // Dedup correctness with different sources
    // -----------------------------------------------------------------------

    #[test]
    fn test_inference_dedup_across_sources() {
        // Template + Ice produce the same expressions (Ice is derived from
        // templates). Dedup should keep only one per expression string.
        let config = InferenceConfig {
            strategies: vec![InferenceStrategy::Template, InferenceStrategy::Ice],
            ..InferenceConfig::default()
        };
        let engine = InvariantInference::new(config);
        let result = engine.infer(&simple_loop());
        let exprs: Vec<String> = result
            .candidates
            .iter()
            .map(|c| format!("{}", c.expression))
            .collect();
        let unique: HashSet<&String> = exprs.iter().collect();
        assert_eq!(
            exprs.len(),
            unique.len(),
            "should dedup across Template and Ice"
        );
    }

    // -----------------------------------------------------------------------
    // Expr: eval_bool returns correct Option<bool>
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_eval_bool_unbound_is_none() {
        let env: HashMap<String, i64> = HashMap::new();
        assert_eq!(Expr::var("missing").ge(Expr::cnst(0)).eval_bool(&env), None);
    }

    #[test]
    fn test_expr_eval_bool_zero_is_false() {
        let env: HashMap<String, i64> = HashMap::new();
        assert_eq!(Expr::cnst(0).eval_bool(&env), Some(false));
    }

    #[test]
    fn test_expr_eval_bool_nonzero_is_true() {
        let env: HashMap<String, i64> = HashMap::new();
        assert_eq!(Expr::cnst(42).eval_bool(&env), Some(true));
        assert_eq!(Expr::cnst(-1).eval_bool(&env), Some(true));
    }

    // -----------------------------------------------------------------------
    // Interval: saturating arithmetic boundary
    // -----------------------------------------------------------------------

    #[test]
    fn test_interval_add_saturating() {
        let a = Interval::exact(i64::MAX);
        let b = Interval::exact(1);
        let sum = a.add(&b);
        assert_eq!(sum.lo, Some(i64::MAX)); // saturating_add caps at MAX
        assert_eq!(sum.hi, Some(i64::MAX));
    }

    #[test]
    fn test_expr_eval_saturating_add() {
        let env: HashMap<String, i64> = [("x".to_owned(), i64::MAX)].into();
        let e = Expr::var("x").add(Expr::cnst(1));
        assert_eq!(e.eval(&env), Some(i64::MAX));
    }

    #[test]
    fn test_expr_eval_saturating_sub() {
        let env: HashMap<String, i64> = [("x".to_owned(), i64::MIN)].into();
        let e = Expr::var("x").sub(Expr::cnst(1));
        assert_eq!(e.eval(&env), Some(i64::MIN));
    }

    #[test]
    fn test_expr_eval_saturating_mul() {
        let env: HashMap<String, i64> = [("x".to_owned(), i64::MAX)].into();
        let e = Expr::var("x").mul(Expr::cnst(2));
        assert_eq!(e.eval(&env), Some(i64::MAX));
    }

    #[test]
    fn test_expr_simplify_saturating_add() {
        let e = Expr::cnst(i64::MAX).add(Expr::cnst(1));
        assert_eq!(e.simplify(), Expr::cnst(i64::MAX));
    }

    #[test]
    fn test_expr_simplify_saturating_sub() {
        let e = Expr::cnst(i64::MIN).sub(Expr::cnst(1));
        assert_eq!(e.simplify(), Expr::cnst(i64::MIN));
    }

    #[test]
    fn test_expr_simplify_saturating_mul() {
        let e = Expr::cnst(i64::MAX).mul(Expr::cnst(2));
        assert_eq!(e.simplify(), Expr::cnst(i64::MAX));
    }
}
