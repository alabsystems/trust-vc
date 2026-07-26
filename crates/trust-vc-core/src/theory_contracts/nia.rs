// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::lra::CmpKind;
use std::collections::{HashMap, HashSet};

// ===========================================================================
// Contract 4: NIA (Nonlinear Integer Arithmetic)
// ===========================================================================

/// An interval bound (inclusive).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Interval {
    pub(crate) lo: i64,
    pub(crate) hi: i64,
}

impl Interval {
    /// Create a new interval.
    #[must_use]
    pub(crate) fn new(lo: i64, hi: i64) -> Self {
        Self { lo, hi }
    }

    /// Check if this interval is empty (lo > hi).
    #[must_use]
    pub(crate) fn is_empty(self) -> bool {
        self.lo > self.hi
    }

    /// Check if a value is contained in this interval.
    #[must_use]
    pub(crate) fn contains(self, v: i64) -> bool {
        v >= self.lo && v <= self.hi
    }

    /// Intersect two intervals.
    #[must_use]
    pub(crate) fn intersect(self, other: Self) -> Self {
        Self {
            lo: self.lo.max(other.lo),
            hi: self.hi.min(other.hi),
        }
    }

    /// Add two intervals.
    #[must_use]
    pub(crate) fn add(self, other: Self) -> Self {
        Self {
            lo: self.lo.saturating_add(other.lo),
            hi: self.hi.saturating_add(other.hi),
        }
    }

    /// Multiply two intervals (all four products, take min/max).
    #[must_use]
    pub(crate) fn mul(self, other: Self) -> Self {
        let products = [
            self.lo.saturating_mul(other.lo),
            self.lo.saturating_mul(other.hi),
            self.hi.saturating_mul(other.lo),
            self.hi.saturating_mul(other.hi),
        ];
        let [first, rest @ ..] = products;
        Self {
            lo: rest.iter().copied().fold(first, i64::min),
            hi: rest.iter().copied().fold(first, i64::max),
        }
    }
}

/// A nonlinear constraint term: coefficient * product(variables).
#[derive(Debug, Clone)]
pub(crate) struct NlTerm {
    pub(crate) coeff: i64,
    /// Variable indices in this monomial (may repeat for powers).
    pub(crate) vars: Vec<u32>,
}

/// A nonlinear constraint: sum(terms) <cmp> bound.
#[derive(Debug, Clone)]
pub(crate) struct NlConstraint {
    pub(crate) terms: Vec<NlTerm>,
    pub(crate) cmp: CmpKind,
    pub(crate) bound: i64,
}

/// Result of NIA constraint checking.
#[derive(Debug, Clone)]
pub(crate) enum NiaResult {
    /// Model satisfies all constraints.
    Satisfiable { model: HashMap<u32, i64> },
    /// No satisfying integer assignment exists within the checked bounds.
    Unsatisfiable {
        /// Conflicting constraint indices.
        conflict: Vec<usize>,
    },
    /// Solver cannot determine satisfiability (incomplete).
    Unknown,
}

/// Contract trait for NIA theory solver.
///
/// Captures the pre/postconditions of nonlinear integer constraint checking:
///
/// ```text
/// fn check_nonlinear(constraints: &[NlConstraint]) -> NiaResult
///
/// requires: true
///
/// ensures |result|:
///   Satisfiable(m) => forall c in constraints: m satisfies c
///   Unsatisfiable(conflict) => conflict indices are valid
///   // interval arithmetic bounds are sound
/// ```
pub(crate) trait ContractNia {
    /// Check nonlinear integer constraints.
    fn check_nonlinear(&self, constraints: &[NlConstraint]) -> NiaResult;
}

/// Reference NIA implementation using interval arithmetic and enumeration.
pub(crate) struct ReferenceNia {
    /// Variable bounds for interval arithmetic.
    pub(crate) bounds: HashMap<u32, Interval>,
}

impl ReferenceNia {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            bounds: HashMap::new(),
        }
    }

    pub(crate) fn set_bound(&mut self, var: u32, interval: Interval) {
        self.bounds.insert(var, interval);
    }

    /// Evaluate a nonlinear constraint at a given model.
    #[must_use]
    pub(crate) fn evaluate_constraint(constraint: &NlConstraint, model: &HashMap<u32, i64>) -> i64 {
        let mut sum: i64 = 0;
        for term in &constraint.terms {
            let mut product: i64 = term.coeff;
            for &var in &term.vars {
                let val = model.get(&var).copied().unwrap_or(0);
                product = product.saturating_mul(val);
            }
            sum = sum.saturating_add(product);
        }
        sum
    }

    /// Check if a constraint is satisfied by a model.
    #[must_use]
    pub(crate) fn satisfies(constraint: &NlConstraint, model: &HashMap<u32, i64>) -> bool {
        let lhs = Self::evaluate_constraint(constraint, model);
        match constraint.cmp {
            CmpKind::Le => lhs <= constraint.bound,
            CmpKind::Ge => lhs >= constraint.bound,
            CmpKind::Eq => lhs == constraint.bound,
        }
    }

    /// Compute the interval of possible values for a nonlinear constraint.
    #[must_use]
    pub(crate) fn constraint_interval(&self, constraint: &NlConstraint) -> Interval {
        let default_bound = Interval::new(-1000, 1000);
        let mut sum = Interval::new(0, 0);
        for term in &constraint.terms {
            let mut product = Interval::new(term.coeff, term.coeff);
            for &var in &term.vars {
                let var_interval = self.bounds.get(&var).copied().unwrap_or(default_bound);
                product = product.mul(var_interval);
            }
            sum = sum.add(product);
        }
        sum
    }
}

impl ContractNia for ReferenceNia {
    fn check_nonlinear(&self, constraints: &[NlConstraint]) -> NiaResult {
        // Collect all variables.
        let mut vars = HashSet::new();
        for c in constraints {
            for term in &c.terms {
                for &v in &term.vars {
                    vars.insert(v);
                }
            }
        }

        // Try zero assignment (only if 0 is within bounds for every variable).
        let zero_in_bounds = vars
            .iter()
            .all(|v| self.bounds.get(v).is_none_or(|iv| iv.lo <= 0 && 0 <= iv.hi));
        if zero_in_bounds {
            let zero_model: HashMap<u32, i64> = vars.iter().map(|&v| (v, 0)).collect();
            if constraints.iter().all(|c| Self::satisfies(c, &zero_model)) {
                return NiaResult::Satisfiable { model: zero_model };
            }
        }

        // Interval arithmetic: check if any constraint is unsatisfiable
        // based on interval bounds.
        for (i, c) in constraints.iter().enumerate() {
            let interval = self.constraint_interval(c);
            let infeasible = match c.cmp {
                CmpKind::Le => interval.lo > c.bound,
                CmpKind::Ge => interval.hi < c.bound,
                CmpKind::Eq => interval.lo > c.bound || interval.hi < c.bound,
            };
            if infeasible {
                return NiaResult::Unsatisfiable { conflict: vec![i] };
            }
        }

        // For small variable domains, try enumeration.
        let default_bound = Interval::new(-1000, 1000);
        let sorted_vars: Vec<u32> = vars.into_iter().collect();

        if sorted_vars.len() <= 2 {
            let domains: Vec<Interval> = sorted_vars
                .iter()
                .map(|v| self.bounds.get(v).copied().unwrap_or(default_bound))
                .collect();

            // Only enumerate if domains are small enough.
            let total: u64 = domains
                .iter()
                .map(|d| {
                    if d.is_empty() {
                        0
                    } else {
                        (d.hi - d.lo + 1) as u64
                    }
                })
                .product();

            if total <= 10000 {
                return self.enumerate(&sorted_vars, &domains, constraints);
            }
        }

        NiaResult::Unknown
    }
}

impl ReferenceNia {
    /// Enumerate all variable assignments within domains.
    pub(crate) fn enumerate(
        &self,
        vars: &[u32],
        domains: &[Interval],
        constraints: &[NlConstraint],
    ) -> NiaResult {
        if vars.is_empty() {
            let model = HashMap::new();
            if constraints.iter().all(|c| Self::satisfies(c, &model)) {
                return NiaResult::Satisfiable { model };
            }
            return NiaResult::Unsatisfiable {
                conflict: (0..constraints.len()).collect(),
            };
        }

        let first_var = vars[0];
        let domain = domains[0];

        for val in domain.lo..=domain.hi {
            let mut model = HashMap::new();
            model.insert(first_var, val);

            if vars.len() == 1 {
                if constraints.iter().all(|c| Self::satisfies(c, &model)) {
                    return NiaResult::Satisfiable { model };
                }
            } else {
                // Recursive enumeration for remaining variables.
                let sub_result = self.enumerate(&vars[1..], &domains[1..], constraints);
                if let NiaResult::Satisfiable {
                    model: mut sub_model,
                } = sub_result
                {
                    sub_model.insert(first_var, val);
                    if constraints.iter().all(|c| Self::satisfies(c, &sub_model)) {
                        return NiaResult::Satisfiable { model: sub_model };
                    }
                }
            }
        }

        NiaResult::Unsatisfiable {
            conflict: (0..constraints.len()).collect(),
        }
    }
}

/// Validates NIA postconditions.
///
/// Checks:
/// 1. Satisfiable: model satisfies all constraints.
/// 2. Unsatisfiable: conflict indices are valid.
/// 3. Interval arithmetic is sound: model values are within declared bounds.
#[must_use]
pub(crate) fn validate_nia_postcondition(
    constraints: &[NlConstraint],
    bounds: &HashMap<u32, Interval>,
    result: &NiaResult,
) -> bool {
    match result {
        NiaResult::Satisfiable { model } => {
            // Every constraint must be satisfied.
            for c in constraints {
                if !ReferenceNia::satisfies(c, model) {
                    return false;
                }
            }
            // Model values must be within declared bounds.
            for (&var, &val) in model {
                if let Some(&interval) = bounds.get(&var) {
                    if !interval.contains(val) {
                        return false;
                    }
                }
            }
            true
        }
        NiaResult::Unsatisfiable { conflict } => {
            // All conflict indices must be valid.
            for &idx in conflict {
                if idx >= constraints.len() {
                    return false;
                }
            }
            // Conflict must be non-empty.
            !conflict.is_empty()
        }
        NiaResult::Unknown => {
            // Unknown is always a valid (conservative) result.
            true
        }
    }
}

/// Validates that interval arithmetic is sound for a monomial.
///
/// Given variable bounds, the interval of a monomial must contain the
/// actual evaluated value for any assignment within bounds.
#[must_use]
pub(crate) fn validate_interval_soundness(
    bounds: &HashMap<u32, Interval>,
    vars: &[u32],
    coeff: i64,
    model: &HashMap<u32, i64>,
) -> bool {
    // Compute actual value.
    let mut actual: i64 = coeff;
    for &v in vars {
        let val = model.get(&v).copied().unwrap_or(0);
        actual = actual.saturating_mul(val);
    }

    // Compute interval.
    let default_bound = Interval::new(-1000, 1000);
    let mut interval = Interval::new(coeff, coeff);
    for &v in vars {
        let var_interval = bounds.get(&v).copied().unwrap_or(default_bound);
        interval = interval.mul(var_interval);
    }

    interval.contains(actual)
}

/// Registers the NIA checking contract as an extern_spec entry.
pub(crate) fn register_nia_checking_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_dpll::theory::nia::NiaSolver::check",
        &["true".to_string()],
        &[
            "satisfiable(m) ==> all_satisfied(constraints, m)".to_string(),
            "unsatisfiable(c) ==> valid_indices(c, constraints)".to_string(),
            "interval_sound(bounds, result)".to_string(),
        ],
    );
}
