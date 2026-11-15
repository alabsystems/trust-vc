//! Scalar terms: the logic every generated query is written in.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Terms have `Bool`, `Int` (mathematical integers), and nominal carrier
//! sorts declared in the query's registry. Machine
//! integers never appear: their values are `Int` terms and their ranges are
//! explicit facts. Division and remainder are Euclidean, as in Verus spec
//! code and SMT-LIB. Calls name declared functions of the query.
//!
//! The constructors below simplify as they build (constant folding, unit
//! laws of `&&`/`||`, double negation). Every rewrite preserves meaning; they
//! only keep queries small and make linear arithmetic recognisable.

use std::ops::{Neg, Not};

/// The sort of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    /// Booleans.
    Bool,
    /// Mathematical integers.
    Int,
    /// An uninterpreted carrier; index into `Query::nominal_types`.
    Nominal(u32),
    /// Boxed values, independent of their type identities.
    Poly,
    /// Undecorated logical type identities.
    TypeId,
    /// Logical type decorations, including shared references.
    Decoration,
}

/// Comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CmpOp {
    /// `==`, on two terms of one sort.
    Eq,
    /// `<`, on integers.
    Lt,
    /// `<=`, on integers.
    Le,
}

/// Integer operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOp {
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `*`.
    Mul,
    /// Euclidean division.
    Div,
    /// Euclidean remainder.
    Mod,
}

/// A term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A boolean literal.
    Bool(bool),
    /// An integer literal.
    Int(i128),
    /// A declared symbol, or a definition parameter.
    Var {
        /// Its name.
        name: String,
        /// Its sort.
        sort: Sort,
    },
    /// Negation.
    Not(Box<Term>),
    /// Conjunction; empty means `true`.
    And(Vec<Term>),
    /// Disjunction; empty means `false`.
    Or(Vec<Term>),
    /// Implication.
    Implies(Box<Term>, Box<Term>),
    /// A comparison.
    Cmp(CmpOp, Box<Term>, Box<Term>),
    /// Integer arithmetic.
    Arith(ArithOp, Box<Term>, Box<Term>),
    /// Integer negation.
    Neg(Box<Term>),
    /// `if c then a else b`, of the given sort.
    Ite(Box<Term>, Box<Term>, Box<Term>, Sort),
    /// A call of a declared function.
    Call {
        /// The function.
        name: String,
        /// Arguments.
        args: Vec<Term>,
        /// Result sort.
        sort: Sort,
    },
}

impl Term {
    /// A variable.
    #[must_use]
    pub fn var(name: impl Into<String>, sort: Sort) -> Self {
        Self::Var {
            name: name.into(),
            sort,
        }
    }

    /// The integer literal's value, if this is one.
    #[must_use]
    pub const fn as_int(&self) -> Option<i128> {
        match self {
            Self::Int(value) => Some(*value),
            _ => None,
        }
    }

    /// The boolean literal's value, if this is one.
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    /// A literal or a variable: something not worth naming.
    #[must_use]
    pub const fn is_atomic(&self) -> bool {
        matches!(self, Self::Bool(_) | Self::Int(_) | Self::Var { .. })
    }

    /// The sort of a well-formed term.
    #[must_use]
    pub fn sort(&self) -> Sort {
        match self {
            Self::Bool(_)
            | Self::Not(_)
            | Self::And(_)
            | Self::Or(_)
            | Self::Implies(..)
            | Self::Cmp(..) => Sort::Bool,
            Self::Int(_) | Self::Arith(..) | Self::Neg(_) => Sort::Int,
            Self::Var { sort, .. } | Self::Ite(.., sort) | Self::Call { sort, .. } => *sort,
        }
    }

    /// The conjunction of `terms`.
    #[must_use]
    pub fn and(terms: impl IntoIterator<Item = Self>) -> Self {
        let mut out = Vec::new();
        for term in terms {
            match term {
                Self::Bool(true) => {}
                Self::Bool(false) => return Self::Bool(false),
                Self::And(inner) => out.extend(inner),
                other => out.push(other),
            }
        }
        match out.len() {
            0 => Self::Bool(true),
            1 => out.pop().unwrap_or(Self::Bool(true)),
            _ => Self::And(out),
        }
    }

    /// The disjunction of `terms`.
    #[must_use]
    pub fn or(terms: impl IntoIterator<Item = Self>) -> Self {
        let mut out = Vec::new();
        for term in terms {
            match term {
                Self::Bool(false) => {}
                Self::Bool(true) => return Self::Bool(true),
                Self::Or(inner) => out.extend(inner),
                other => out.push(other),
            }
        }
        match out.len() {
            0 => Self::Bool(false),
            1 => out.pop().unwrap_or(Self::Bool(false)),
            _ => Self::Or(out),
        }
    }

    /// `premise ==> conclusion`.
    #[must_use]
    pub fn implies(premise: Self, conclusion: Self) -> Self {
        match (premise, conclusion) {
            (Self::Bool(true), conclusion) => conclusion,
            (Self::Bool(false), _) | (_, Self::Bool(true)) => Self::Bool(true),
            (premise, Self::Bool(false)) => premise.not(),
            (premise, conclusion) => Self::Implies(Box::new(premise), Box::new(conclusion)),
        }
    }

    /// `guard ==> self`, where `guard` is a conjunction given as a list.
    #[must_use]
    pub fn guarded(self, guard: &[Self]) -> Self {
        Self::implies(Self::and(guard.iter().cloned()), self)
    }

    /// `lhs == rhs`, on two terms of one sort.
    #[must_use]
    pub fn eq(lhs: Self, rhs: Self) -> Self {
        if lhs == rhs {
            return Self::Bool(true);
        }
        match (&lhs, &rhs) {
            (Self::Int(a), Self::Int(b)) => Self::Bool(a == b),
            (Self::Bool(a), Self::Bool(b)) => Self::Bool(a == b),
            (Self::Bool(true), _) => rhs,
            (_, Self::Bool(true)) => lhs,
            (Self::Bool(false), _) => rhs.not(),
            (_, Self::Bool(false)) => lhs.not(),
            _ => Self::Cmp(CmpOp::Eq, Box::new(lhs), Box::new(rhs)),
        }
    }

    /// `lhs < rhs`.
    #[must_use]
    pub fn lt(lhs: Self, rhs: Self) -> Self {
        match (lhs.as_int(), rhs.as_int()) {
            (Some(a), Some(b)) => Self::Bool(a < b),
            _ => Self::Cmp(CmpOp::Lt, Box::new(lhs), Box::new(rhs)),
        }
    }

    /// `lhs <= rhs`.
    #[must_use]
    pub fn le(lhs: Self, rhs: Self) -> Self {
        match (lhs.as_int(), rhs.as_int()) {
            (Some(a), Some(b)) => Self::Bool(a <= b),
            _ => Self::Cmp(CmpOp::Le, Box::new(lhs), Box::new(rhs)),
        }
    }

    /// `lo <= self && self <= hi`, with either bound optional.
    #[must_use]
    pub fn within(&self, lo: Option<i128>, hi: Option<i128>) -> Self {
        let lower = lo.map(|lo| Self::le(Self::Int(lo), self.clone()));
        let upper = hi.map(|hi| Self::le(self.clone(), Self::Int(hi)));
        Self::and(lower.into_iter().chain(upper))
    }

    /// An exact nonnegative literal through `u128::MAX`, expressed using
    /// existing mathematical Int literals. No machine or BV cast is involved.
    #[must_use]
    pub fn unsigned(value: u128) -> Self {
        if let Ok(small) = i128::try_from(value) {
            return Self::Int(small);
        }
        let high = Self::Int((value >> 64) as i128);
        let low = Self::Int((value & u128::from(u64::MAX)) as i128);
        Self::arith(
            ArithOp::Add,
            Self::arith(ArithOp::Mul, high, Self::Int(1i128 << 64)),
            low,
        )
    }

    /// A source integer-type invariant. Machine upper bounds are nonnegative
    /// and may exceed i128; the ordinary general `within` API remains intact.
    #[must_use]
    pub fn within_type_bounds(&self, lo: Option<i128>, hi: Option<u128>) -> Self {
        let lower = lo.map(|lo| Self::le(Self::Int(lo), self.clone()));
        let upper = hi.map(|hi| Self::le(self.clone(), Self::unsigned(hi)));
        Self::and(lower.into_iter().chain(upper))
    }

    /// Integer arithmetic, folded when both operands are literals and the
    /// result is exact in `i128`.
    #[must_use]
    pub fn arith(op: ArithOp, lhs: Self, rhs: Self) -> Self {
        if let (Some(a), Some(b)) = (lhs.as_int(), rhs.as_int()) {
            let folded = match op {
                ArithOp::Add => a.checked_add(b),
                ArithOp::Sub => a.checked_sub(b),
                ArithOp::Mul => a.checked_mul(b),
                // Euclidean division by zero is unspecified; leave it to the
                // solver's reading.
                ArithOp::Div => (b != 0).then(|| a.checked_div_euclid(b)).flatten(),
                ArithOp::Mod => (b != 0).then(|| a.checked_rem_euclid(b)).flatten(),
            };
            if let Some(value) = folded {
                return Self::Int(value);
            }
        }
        match (op, lhs.as_int(), rhs.as_int()) {
            (ArithOp::Add, Some(0), _) => return rhs,
            (ArithOp::Add | ArithOp::Sub, _, Some(0))
            | (ArithOp::Mul | ArithOp::Div, _, Some(1)) => return lhs,
            (ArithOp::Mul, Some(1), _) => return rhs,
            _ => {}
        }
        Self::Arith(op, Box::new(lhs), Box::new(rhs))
    }

    /// `if cond then a else b`.
    #[must_use]
    pub fn ite(cond: Self, a: Self, b: Self) -> Self {
        match cond {
            Self::Bool(true) => a,
            Self::Bool(false) => b,
            _ if a == b => a,
            cond => {
                let sort = a.sort();
                Self::Ite(Box::new(cond), Box::new(a), Box::new(b), sort)
            }
        }
    }

    /// A call of a declared function.
    #[must_use]
    pub fn call(name: impl Into<String>, args: Vec<Self>, sort: Sort) -> Self {
        Self::Call {
            name: name.into(),
            args,
            sort,
        }
    }

    /// Call `f` on every call node in the term, innermost first.
    pub fn for_each_call<'t>(&'t self, f: &mut dyn FnMut(&'t str, &'t [Self])) {
        match self {
            Self::Bool(_) | Self::Int(_) | Self::Var { .. } => {}
            Self::Not(inner) | Self::Neg(inner) => inner.for_each_call(f),
            Self::And(terms) | Self::Or(terms) => {
                for term in terms {
                    term.for_each_call(f);
                }
            }
            Self::Implies(a, b) | Self::Cmp(_, a, b) | Self::Arith(_, a, b) => {
                a.for_each_call(f);
                b.for_each_call(f);
            }
            Self::Ite(c, a, b, _) => {
                c.for_each_call(f);
                a.for_each_call(f);
                b.for_each_call(f);
            }
            Self::Call { name, args, .. } => {
                for arg in args {
                    arg.for_each_call(f);
                }
                f(name, args);
            }
        }
    }

    /// Calls in the same postorder, including their actual result sorts.
    pub(crate) fn for_each_typed_call<'t>(&'t self, f: &mut dyn FnMut(&'t str, &'t [Self], Sort)) {
        match self {
            Self::Bool(_) | Self::Int(_) | Self::Var { .. } => {}
            Self::Not(inner) | Self::Neg(inner) => inner.for_each_typed_call(f),
            Self::And(terms) | Self::Or(terms) => {
                for term in terms {
                    term.for_each_typed_call(f);
                }
            }
            Self::Implies(a, b) | Self::Cmp(_, a, b) | Self::Arith(_, a, b) => {
                a.for_each_typed_call(f);
                b.for_each_typed_call(f);
            }
            Self::Ite(c, a, b, _) => {
                c.for_each_typed_call(f);
                a.for_each_typed_call(f);
                b.for_each_typed_call(f);
            }
            Self::Call { name, args, sort } => {
                for arg in args {
                    arg.for_each_typed_call(f);
                }
                f(name, args, *sort);
            }
        }
    }
}

/// A rewrite of call nodes, for [`Term::map_calls`].
pub type CallMap<'f, E> = dyn FnMut(&str, Vec<Term>, Sort) -> Result<Term, E> + 'f;

impl std::ops::Not for Term {
    type Output = Self;

    /// Negation, simplified.
    fn not(self) -> Self {
        match self {
            Self::Bool(value) => Self::Bool(!value),
            Self::Not(inner) => *inner,
            other => Self::Not(Box::new(other)),
        }
    }
}

impl std::ops::Neg for Term {
    type Output = Self;

    /// Integer negation, folded on literals.
    fn neg(self) -> Self {
        match self {
            Self::Int(value) => match value.checked_neg() {
                Some(negated) => Self::Int(negated),
                None => Self::Neg(Box::new(Self::Int(value))),
            },
            Self::Neg(inner) => *inner,
            other => Self::Neg(Box::new(other)),
        }
    }
}

impl Term {
    /// Rebuild the term bottom-up, replacing every call by `f(name, args,
    /// sort)` applied to the already rebuilt arguments.
    pub fn map_calls<E>(&self, f: &mut CallMap<'_, E>) -> Result<Self, E> {
        Ok(match self {
            Self::Bool(_) | Self::Int(_) | Self::Var { .. } => self.clone(),
            Self::Not(inner) => inner.map_calls(f)?.not(),
            Self::Neg(inner) => inner.map_calls(f)?.neg(),
            Self::And(terms) => {
                let mut out = Vec::new();
                for term in terms {
                    out.push(term.map_calls(f)?);
                }
                Self::and(out)
            }
            Self::Or(terms) => {
                let mut out = Vec::new();
                for term in terms {
                    out.push(term.map_calls(f)?);
                }
                Self::or(out)
            }
            Self::Implies(a, b) => Self::implies(a.map_calls(f)?, b.map_calls(f)?),
            Self::Cmp(op, a, b) => {
                let (a, b) = (a.map_calls(f)?, b.map_calls(f)?);
                match op {
                    CmpOp::Eq => Self::eq(a, b),
                    CmpOp::Lt => Self::lt(a, b),
                    CmpOp::Le => Self::le(a, b),
                }
            }
            Self::Arith(op, a, b) => Self::arith(*op, a.map_calls(f)?, b.map_calls(f)?),
            Self::Ite(c, a, b, _) => Self::ite(c.map_calls(f)?, a.map_calls(f)?, b.map_calls(f)?),
            Self::Call { name, args, sort } => {
                let mut out = Vec::new();
                for arg in args {
                    out.push(arg.map_calls(f)?);
                }
                f(name, out, *sort)?
            }
        })
    }

    /// Replace variables by terms. Terms have no binders, so nothing can be
    /// captured.
    #[must_use]
    pub fn substitute(&self, map: &std::collections::HashMap<&str, Self>) -> Self {
        match self {
            Self::Var { name, .. } => map
                .get(name.as_str())
                .cloned()
                .unwrap_or_else(|| self.clone()),
            Self::Bool(_) | Self::Int(_) => self.clone(),
            Self::Not(inner) => inner.substitute(map).not(),
            Self::Neg(inner) => inner.substitute(map).neg(),
            Self::And(terms) => Self::and(terms.iter().map(|t| t.substitute(map))),
            Self::Or(terms) => Self::or(terms.iter().map(|t| t.substitute(map))),
            Self::Implies(a, b) => Self::implies(a.substitute(map), b.substitute(map)),
            Self::Cmp(op, a, b) => {
                let (a, b) = (a.substitute(map), b.substitute(map));
                match op {
                    CmpOp::Eq => Self::eq(a, b),
                    CmpOp::Lt => Self::lt(a, b),
                    CmpOp::Le => Self::le(a, b),
                }
            }
            Self::Arith(op, a, b) => Self::arith(*op, a.substitute(map), b.substitute(map)),
            Self::Ite(c, a, b, _) => {
                Self::ite(c.substitute(map), a.substitute(map), b.substitute(map))
            }
            Self::Call { name, args, sort } => Self::Call {
                name: name.clone(),
                args: args.iter().map(|t| t.substitute(map)).collect(),
                sort: *sort,
            },
        }
    }

    /// Number of nodes, saturating at `usize::MAX`.
    #[must_use]
    pub fn size(&self) -> usize {
        let children = match self {
            Self::Bool(_) | Self::Int(_) | Self::Var { .. } => 0,
            Self::Not(inner) | Self::Neg(inner) => inner.size(),
            Self::And(terms) | Self::Or(terms) | Self::Call { args: terms, .. } => terms
                .iter()
                .fold(0usize, |total, term| total.saturating_add(term.size())),
            Self::Implies(a, b) | Self::Cmp(_, a, b) | Self::Arith(_, a, b) => {
                a.size().saturating_add(b.size())
            }
            Self::Ite(c, a, b, _) => c.size().saturating_add(a.size()).saturating_add(b.size()),
        };
        children.saturating_add(1)
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn list(f: &mut std::fmt::Formatter<'_>, op: &str, terms: &[Term]) -> std::fmt::Result {
            write!(f, "({op}")?;
            for term in terms {
                write!(f, " {term}")?;
            }
            write!(f, ")")
        }
        match self {
            Self::Bool(value) => write!(f, "{value}"),
            Self::Int(value) if *value < 0 => write!(f, "(- {})", value.unsigned_abs()),
            Self::Int(value) => write!(f, "{value}"),
            Self::Var { name, .. } => write!(f, "{name}"),
            Self::Not(inner) => write!(f, "(not {inner})"),
            Self::And(terms) => list(f, "and", terms),
            Self::Or(terms) => list(f, "or", terms),
            Self::Implies(a, b) => write!(f, "(=> {a} {b})"),
            Self::Cmp(op, a, b) => {
                let op = match op {
                    CmpOp::Eq => "=",
                    CmpOp::Lt => "<",
                    CmpOp::Le => "<=",
                };
                write!(f, "({op} {a} {b})")
            }
            Self::Arith(op, a, b) => {
                let op = match op {
                    ArithOp::Add => "+",
                    ArithOp::Sub => "-",
                    ArithOp::Mul => "*",
                    ArithOp::Div => "div",
                    ArithOp::Mod => "mod",
                };
                write!(f, "({op} {a} {b})")
            }
            Self::Neg(inner) => write!(f, "(- {inner})"),
            Self::Ite(c, a, b, _) => write!(f, "(ite {c} {a} {b})"),
            Self::Call { name, args, .. } => list(f, name, args),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> Term {
        Term::var("x", Sort::Int)
    }

    #[test]
    fn folding_keeps_meaning() {
        assert_eq!(
            Term::arith(ArithOp::Add, Term::Int(2), Term::Int(3)),
            Term::Int(5)
        );
        assert_eq!(
            Term::arith(ArithOp::Div, Term::Int(-7), Term::Int(2)),
            Term::Int(-4)
        );
        assert_eq!(
            Term::arith(ArithOp::Mod, Term::Int(-7), Term::Int(2)),
            Term::Int(1)
        );
        // Division by zero is left to the solver.
        assert!(matches!(
            Term::arith(ArithOp::Div, Term::Int(1), Term::Int(0)),
            Term::Arith(..)
        ));
        // Overflowing folds are left unfolded.
        assert!(matches!(
            Term::arith(ArithOp::Mul, Term::Int(i128::MAX), Term::Int(2)),
            Term::Arith(..)
        ));
        assert_eq!(Term::arith(ArithOp::Add, x(), Term::Int(0)), x());
        assert_eq!(
            Term::Int(i128::MIN).neg(),
            Term::Neg(Box::new(Term::Int(i128::MIN)))
        );
    }

    #[test]
    fn logic_units() {
        let p = Term::var("p", Sort::Bool);
        assert_eq!(Term::and([Term::Bool(true), p.clone()]), p);
        assert_eq!(Term::and([Term::Bool(false), p.clone()]), Term::Bool(false));
        assert_eq!(Term::and(Vec::new()), Term::Bool(true));
        assert_eq!(Term::or([Term::Bool(false), p.clone()]), p);
        assert_eq!(p.clone().not().not(), p);
        assert_eq!(Term::implies(Term::Bool(true), p.clone()), p);
        assert_eq!(Term::implies(p.clone(), Term::Bool(false)), p.clone().not());
        assert_eq!(Term::eq(p.clone(), Term::Bool(false)), p.not());
        assert_eq!(Term::le(Term::Int(1), Term::Int(0)), Term::Bool(false));
    }
}
