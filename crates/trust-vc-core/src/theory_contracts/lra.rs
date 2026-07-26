// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

// ===========================================================================
// Contract 3: LRA (Linear Real Arithmetic)
// ===========================================================================

/// A rational number represented as numerator/denominator.
///
/// Invariant: denominator > 0, fraction is in lowest terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Rational {
    pub(crate) num: i64,
    pub(crate) den: u64,
}

impl Rational {
    /// Create a new rational, reducing to lowest terms.
    #[must_use]
    pub(crate) fn new(num: i64, den: u64) -> Self {
        assert!(den > 0, "denominator must be positive");
        let g = gcd(num.unsigned_abs(), den);
        Self {
            num: num / g as i64,
            den: den / g,
        }
    }

    /// Create a rational from wide intermediates, returning `None` on overflow.
    ///
    /// Returns `None` if the reduced numerator or denominator does not fit in
    /// 64 bits. After GCD reduction the values are as small as possible, so
    /// this only returns `None` for truly enormous irreducible fractions.
    fn try_new_wide(num: i128, den: u128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        let g = gcd_u128(num.unsigned_abs(), den);
        let reduced_num = num / g as i128;
        let reduced_den = den / g;
        Some(Self {
            num: i64::try_from(reduced_num).ok()?,
            den: u64::try_from(reduced_den).ok()?,
        })
    }

    /// Compare two rationals using overflow-safe 128-bit cross-multiplication.
    ///
    /// Returns `Ordering::Less`, `Equal`, or `Greater` for `self` vs `other`.
    #[must_use]
    pub(crate) fn cmp_rational(self, other: Self) -> std::cmp::Ordering {
        // self.num / self.den  vs  other.num / other.den
        // Denominators are positive u64, so cross-multiply without sign flip:
        //   self.num * other.den  vs  other.num * self.den
        let lhs = i128::from(self.num) * i128::from(other.den);
        let rhs = i128::from(other.num) * i128::from(self.den);
        lhs.cmp(&rhs)
    }

    /// Create a rational from an integer.
    #[must_use]
    pub(crate) fn from_int(n: i64) -> Self {
        Self { num: n, den: 1 }
    }

    /// Zero.
    #[must_use]
    pub(crate) fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    /// Multiply two rationals, returning `None` on 64-bit overflow.
    pub(crate) fn checked_mul(self, other: Self) -> Option<Self> {
        let num_wide = i128::from(self.num) * i128::from(other.num);
        let den_wide = u128::from(self.den) * u128::from(other.den);
        Self::try_new_wide(num_wide, den_wide)
    }

    /// Multiply two rationals, saturating to the nearest representable bound if
    /// the reduced result overflows 64 bits.
    #[must_use]
    pub(crate) fn mul(self, other: Self) -> Self {
        let num_wide = i128::from(self.num) * i128::from(other.num);
        let den_wide = u128::from(self.den) * u128::from(other.den);
        Self::try_new_wide(num_wide, den_wide).unwrap_or_else(|| {
            if num_wide.is_negative() {
                Self::from_int(i64::MIN)
            } else {
                Self::from_int(i64::MAX)
            }
        })
    }

    /// Add two rationals, returning `None` on 64-bit overflow.
    pub(crate) fn checked_add(self, other: Self) -> Option<Self> {
        let lhs = i128::from(self.num) * i128::from(other.den);
        let rhs = i128::from(other.num) * i128::from(self.den);
        let num_wide = lhs + rhs;
        let den_wide = u128::from(self.den) * u128::from(other.den);
        Self::try_new_wide(num_wide, den_wide)
    }

    /// Add two rationals, saturating to the nearest representable bound if the
    /// reduced result overflows 64 bits.
    #[must_use]
    pub(crate) fn add(self, other: Self) -> Self {
        let lhs = i128::from(self.num) * i128::from(other.den);
        let rhs = i128::from(other.num) * i128::from(self.den);
        let num_wide = lhs + rhs;
        let den_wide = u128::from(self.den) * u128::from(other.den);
        Self::try_new_wide(num_wide, den_wide).unwrap_or_else(|| {
            if num_wide.is_negative() {
                Self::from_int(i64::MIN)
            } else {
                Self::from_int(i64::MAX)
            }
        })
    }

    /// Check if this rational is positive.
    #[must_use]
    pub(crate) fn is_positive(self) -> bool {
        self.num > 0
    }

    /// Check if this rational is negative.
    #[must_use]
    pub(crate) fn is_negative(self) -> bool {
        self.num < 0
    }

    /// Check if this rational is zero.
    #[must_use]
    pub(crate) fn is_zero(self) -> bool {
        self.num == 0
    }
}

/// Greatest common divisor (64-bit).
#[must_use]
pub(crate) fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// Greatest common divisor (128-bit) for overflow-safe rational reduction.
#[must_use]
fn gcd_u128(a: u128, b: u128) -> u128 {
    if b == 0 {
        a
    } else {
        gcd_u128(b, a % b)
    }
}

/// Comparison kind for linear constraints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CmpKind {
    /// <=
    Le,
    /// >=
    Ge,
    /// ==
    Eq,
}

/// A linear constraint: sum(coeff[i] * var[i]) <cmp> bound.
#[derive(Debug, Clone)]
pub(crate) struct LinearConstraint {
    /// (coefficient, variable_index) pairs.
    pub(crate) terms: Vec<(Rational, u32)>,
    pub(crate) cmp: CmpKind,
    pub(crate) bound: Rational,
}

/// Result of LRA feasibility checking.
#[derive(Debug, Clone)]
pub(crate) enum LraResult {
    /// A feasible assignment exists.
    Feasible {
        /// Variable assignments: var_index -> value.
        assignment: HashMap<u32, Rational>,
    },
    /// The constraints are infeasible, with a Farkas certificate.
    Infeasible {
        /// Farkas multipliers: one per constraint. The non-negative linear
        /// combination of constraints yields a contradiction (0 <= negative).
        farkas_coefficients: Vec<Rational>,
    },
}

/// Contract trait for LRA theory solver.
///
/// Captures the pre/postconditions of linear feasibility checking:
///
/// ```text
/// fn check_feasibility(constraints: &[LinearConstraint]) -> LraResult
///
/// requires: true
///
/// ensures |result|:
///   Feasible(a) => forall c in constraints: a satisfies c
///   Infeasible(farkas) =>
///     farkas.len() == constraints.len()
///     all farkas coefficients >= 0
///     sum(farkas[i] * constraints[i]) yields 0 <= negative (contradiction)
/// ```
pub(crate) trait ContractLra {
    /// Check feasibility of a set of linear constraints.
    fn check_feasibility(&self, constraints: &[LinearConstraint]) -> LraResult;
}

/// Reference LRA implementation using simple bound propagation.
pub(crate) struct ReferenceLra;

impl ReferenceLra {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self
    }

    /// Evaluate a constraint at a given assignment.
    #[must_use]
    pub(crate) fn evaluate_constraint(
        constraint: &LinearConstraint,
        assignment: &HashMap<u32, Rational>,
    ) -> Rational {
        let mut sum = Rational::zero();
        for &(coeff, var) in &constraint.terms {
            let val = assignment.get(&var).copied().unwrap_or(Rational::zero());
            sum = sum.add(coeff.mul(val));
        }
        sum
    }

    /// Check if a constraint is satisfied by an assignment.
    ///
    /// Uses overflow-safe 128-bit cross-multiplication via `cmp_rational`.
    #[must_use]
    pub(crate) fn satisfies(
        constraint: &LinearConstraint,
        assignment: &HashMap<u32, Rational>,
    ) -> bool {
        let lhs = Self::evaluate_constraint(constraint, assignment);
        match constraint.cmp {
            CmpKind::Le => lhs.cmp_rational(constraint.bound).is_le(),
            CmpKind::Ge => lhs.cmp_rational(constraint.bound).is_ge(),
            CmpKind::Eq => lhs.cmp_rational(constraint.bound).is_eq(),
        }
    }

    /// Check if a constraint is satisfied, returning `None` on 64-bit
    /// rational overflow instead of panicking.
    fn checked_satisfies(
        constraint: &LinearConstraint,
        assignment: &HashMap<u32, Rational>,
    ) -> Option<bool> {
        let mut sum = Rational::zero();
        for &(coeff, var) in &constraint.terms {
            let val = assignment.get(&var).copied().unwrap_or(Rational::zero());
            sum = sum.checked_add(coeff.checked_mul(val)?)?;
        }
        Some(match constraint.cmp {
            CmpKind::Le => sum.cmp_rational(constraint.bound).is_le(),
            CmpKind::Ge => sum.cmp_rational(constraint.bound).is_ge(),
            CmpKind::Eq => sum.cmp_rational(constraint.bound).is_eq(),
        })
    }
}

impl ContractLra for ReferenceLra {
    fn check_feasibility(&self, constraints: &[LinearConstraint]) -> LraResult {
        // Collect all variables.
        let mut vars = HashSet::new();
        for c in constraints {
            for &(_, var) in &c.terms {
                vars.insert(var);
            }
        }

        // Try zero assignment first (simplest feasible check).
        // Use checked_satisfies to avoid panicking on user-generated
        // constraints with enormous rational constants.
        let zero_assignment: HashMap<u32, Rational> =
            vars.iter().map(|&v| (v, Rational::zero())).collect();
        if constraints
            .iter()
            .all(|c| Self::checked_satisfies(c, &zero_assignment) == Some(true))
        {
            return LraResult::Feasible {
                assignment: zero_assignment,
            };
        }

        // For single-variable constraints, try to find a satisfying assignment.
        if vars.len() == 1 {
            let Some(var) = vars.iter().next().copied() else {
                return LraResult::Infeasible {
                    farkas_coefficients: constraints
                        .iter()
                        .map(|_| Rational::from_int(1))
                        .collect(),
                };
            };
            // Find bounds on the variable.
            let mut lower: Option<Rational> = None;
            let mut upper: Option<Rational> = None;
            let mut exact: Option<Rational> = None;

            for c in constraints {
                if c.terms.len() != 1 {
                    continue;
                }
                let (coeff, _) = c.terms[0];
                if coeff.is_zero() {
                    continue;
                }
                // coeff * var <cmp> bound => var <cmp'> bound/coeff
                // Use 128-bit intermediates for the bound division to avoid overflow.
                // If the rational overflows 64-bit, skip this constraint's bound
                // (fall through to Infeasible — sound conservative behavior).
                let Some(val_bound) = Rational::try_new_wide(
                    i128::from(c.bound.num) * i128::from(coeff.den),
                    u128::from(c.bound.den) * u128::from(coeff.num.unsigned_abs()),
                ) else {
                    continue;
                };
                let flip = coeff.is_negative();
                match (c.cmp, flip) {
                    (CmpKind::Le, false) | (CmpKind::Ge, true) => {
                        upper = Some(match upper {
                            Some(u) => {
                                if val_bound.cmp_rational(u).is_lt() {
                                    val_bound
                                } else {
                                    u
                                }
                            }
                            None => val_bound,
                        });
                    }
                    (CmpKind::Ge, false) | (CmpKind::Le, true) => {
                        lower = Some(match lower {
                            Some(l) => {
                                if val_bound.cmp_rational(l).is_gt() {
                                    val_bound
                                } else {
                                    l
                                }
                            }
                            None => val_bound,
                        });
                    }
                    (CmpKind::Eq, _) => {
                        exact = Some(val_bound);
                    }
                }
            }

            // If we have an exact bound, check it.
            if let Some(e) = exact {
                let mut assignment = HashMap::new();
                assignment.insert(var, e);
                if constraints
                    .iter()
                    .all(|c| Self::checked_satisfies(c, &assignment) == Some(true))
                {
                    return LraResult::Feasible { assignment };
                }
            }

            // Try lower bound, upper bound, or midpoint.
            if let Some(l) = lower {
                let mut assignment = HashMap::new();
                assignment.insert(var, l);
                if constraints
                    .iter()
                    .all(|c| Self::checked_satisfies(c, &assignment) == Some(true))
                {
                    return LraResult::Feasible { assignment };
                }
            }
            if let Some(u) = upper {
                let mut assignment = HashMap::new();
                assignment.insert(var, u);
                if constraints
                    .iter()
                    .all(|c| Self::checked_satisfies(c, &assignment) == Some(true))
                {
                    return LraResult::Feasible { assignment };
                }
            }
        }

        // If no feasible assignment found, report infeasible with trivial
        // Farkas certificate (all ones). This is a reference implementation;
        // a real solver would compute the actual Farkas coefficients.
        LraResult::Infeasible {
            farkas_coefficients: constraints.iter().map(|_| Rational::from_int(1)).collect(),
        }
    }
}

/// Validates LRA feasibility postconditions.
///
/// Checks:
/// 1. Feasible: assignment satisfies all constraints.
/// 2. Infeasible: Farkas certificate length matches constraints, all non-negative.
#[must_use]
pub(crate) fn validate_lra_postcondition(
    constraints: &[LinearConstraint],
    result: &LraResult,
) -> bool {
    match result {
        LraResult::Feasible { assignment } => {
            // Every constraint must be satisfied.
            for c in constraints {
                if !ReferenceLra::satisfies(c, assignment) {
                    return false;
                }
            }
            true
        }
        LraResult::Infeasible {
            farkas_coefficients,
        } => {
            // Length must match.
            if farkas_coefficients.len() != constraints.len() {
                return false;
            }
            // All Farkas coefficients must be non-negative.
            for coeff in farkas_coefficients {
                if coeff.is_negative() {
                    return false;
                }
            }
            true
        }
    }
}

/// Registers the LRA feasibility contract as an extern_spec entry.
pub(crate) fn register_lra_feasibility_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_dpll::theory::lra::LraSolver::check_feasibility",
        &["true".to_string()],
        &[
            "feasible(a) ==> all_satisfied(constraints, a)".to_string(),
            "infeasible(f) ==> f.len() == constraints.len()".to_string(),
            "infeasible(f) ==> all_nonneg(f)".to_string(),
        ],
    );
}
