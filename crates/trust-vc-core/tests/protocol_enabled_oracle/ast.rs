// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The oracle's own syntax tree for the TLA+ fragment it generates.
//!
//! One tree is printed as TLA+ for TY ([`super::print`]) and evaluated by the
//! independent model ([`super::model`]), so the two can never read different
//! modules. Nothing here, or in the model, uses TY's parser, AST or
//! evaluator.

/// The three state variables and their universes (the model's
/// [`super::model::universe`]): `x \in 0..3`, `y \in SUBSET (1..3)`,
/// `z \in (1..2) \X (1..2)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Var {
    X,
    Y,
    Z,
}

pub const VARS: [Var; 3] = [Var::X, Var::Y, Var::Z];

impl Var {
    pub fn name(self) -> &'static str {
        match self {
            Var::X => "x",
            Var::Y => "y",
            Var::Z => "z",
        }
    }

    pub fn index(self) -> usize {
        match self {
            Var::X => 0,
            Var::Y => 1,
            Var::Z => 2,
        }
    }
}

/// A binder: one name, or a TLA+ tuple pattern `<<a, c>>` (TLA+ tuple
/// patterns are flat identifier tuples).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pat {
    One(String),
    Tup(Vec<String>),
}

impl Pat {
    pub fn names(&self) -> Vec<String> {
        match self {
            Pat::One(n) => vec![n.clone()],
            Pat::Tup(ns) => ns.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum E {
    Int(i64),
    Bool(bool),
    Var(Var),
    Prime(Box<E>),
    /// A bound variable, an operator parameter, or a zero-arity definition
    /// (module or LET).
    Name(String),
    /// Application of a module or LET operator with parameters.
    Apply(String, Vec<E>),
    Add(Box<E>, Box<E>),
    Mod(Box<E>, i64),
    Card(Box<E>),
    /// `t[i]` on a tuple.
    Index(Box<E>, i64),
    Tuple(Vec<E>),
    SetEnum(Vec<E>),
    Range(i64, i64),
    Cup(Box<E>, Box<E>),
    Cap(Box<E>, Box<E>),
    Diff(Box<E>, Box<E>),
    Subset(Box<E>),
    Times(Box<E>, Box<E>),
    /// `{pat \in S : P}`.
    Filter(Pat, Box<E>, Box<E>),
    Eq(Box<E>, Box<E>),
    Lt(Box<E>, Box<E>),
    In(Box<E>, Box<E>),
    NotIn(Box<E>, Box<E>),
    Subseteq(Box<E>, Box<E>),
    Not(Box<E>),
    And(Vec<E>),
    Or(Vec<E>),
    If(Box<E>, Box<E>, Box<E>),
    Exists(Pat, Box<E>, Box<E>),
    Forall(Pat, Box<E>, Box<E>),
    Let(Vec<Def>, Box<E>),
    Enabled(Box<E>),
    Unchanged(Var),
    /// `UNCHANGED e` of any expression over the variables: a tuple, a
    /// definition naming one, nested (`e' = e`).
    UnchangedE(Box<E>),
    /// `<<A>>_e`: `A /\ ~(e' = e)`.
    AngleAction(Box<E>, Box<E>),
    /// `LAMBDA params : body`, only as the actual of an operator parameter.
    Lambda(Vec<String>, Box<E>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Def {
    pub name: String,
    pub params: Vec<String>,
    /// The arity of each parameter (`F(_)` has arity 1); empty when every
    /// parameter is an ordinary value parameter.
    pub arities: Vec<usize>,
    pub body: E,
}

impl Def {
    /// The arity of parameter `i` (0: a value parameter).
    pub fn arity(&self, i: usize) -> usize {
        self.arities.get(i).copied().unwrap_or(0)
    }
}

/// A value of the fragment. The derived order is only a canonical order for
/// sets; it is not TLA+'s.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum V {
    Bool(bool),
    Int(i64),
    Tup(Vec<V>),
    Set(std::collections::BTreeSet<V>),
}

/// One state: the values of `x`, `y`, `z`.
pub type St = [V; 3];

/// A generated module: definitions, one initial state, `Next`, `Inv`.
#[derive(Clone, Debug)]
pub struct Module {
    pub defs: Vec<Def>,
    pub init: St,
    pub next: E,
    pub inv: E,
}

// ---- builders (used by the generator and by the hand-written shapes) ----

pub fn b(e: E) -> Box<E> {
    Box::new(e)
}
pub fn int(i: i64) -> E {
    E::Int(i)
}
pub fn x() -> E {
    E::Var(Var::X)
}
pub fn y() -> E {
    E::Var(Var::Y)
}
pub fn z() -> E {
    E::Var(Var::Z)
}
pub fn prime(e: E) -> E {
    E::Prime(b(e))
}
pub fn name(n: &str) -> E {
    E::Name(n.to_string())
}
pub fn apply(op: &str, args: Vec<E>) -> E {
    E::Apply(op.to_string(), args)
}
pub fn add(a: E, c: E) -> E {
    E::Add(b(a), b(c))
}
pub fn modulo(a: E, m: i64) -> E {
    E::Mod(b(a), m)
}
pub fn card(s: E) -> E {
    E::Card(b(s))
}
pub fn index(t: E, i: i64) -> E {
    E::Index(b(t), i)
}
pub fn tuple(es: Vec<E>) -> E {
    E::Tuple(es)
}
pub fn set(es: Vec<E>) -> E {
    E::SetEnum(es)
}
pub fn range(lo: i64, hi: i64) -> E {
    E::Range(lo, hi)
}
pub fn cup(a: E, c: E) -> E {
    E::Cup(b(a), b(c))
}
pub fn cap(a: E, c: E) -> E {
    E::Cap(b(a), b(c))
}
pub fn diff(a: E, c: E) -> E {
    E::Diff(b(a), b(c))
}
pub fn subset(s: E) -> E {
    E::Subset(b(s))
}
pub fn times(a: E, c: E) -> E {
    E::Times(b(a), b(c))
}
pub fn one(n: &str) -> Pat {
    Pat::One(n.to_string())
}
pub fn tup(ns: &[&str]) -> Pat {
    Pat::Tup(ns.iter().map(|n| n.to_string()).collect())
}
pub fn filter(p: Pat, s: E, pred: E) -> E {
    E::Filter(p, b(s), b(pred))
}
pub fn eq(a: E, c: E) -> E {
    E::Eq(b(a), b(c))
}
pub fn lt(a: E, c: E) -> E {
    E::Lt(b(a), b(c))
}
pub fn elem(a: E, s: E) -> E {
    E::In(b(a), b(s))
}
pub fn notin(a: E, s: E) -> E {
    E::NotIn(b(a), b(s))
}
pub fn subseteq(a: E, s: E) -> E {
    E::Subseteq(b(a), b(s))
}
pub fn not(a: E) -> E {
    E::Not(b(a))
}
pub fn and(es: Vec<E>) -> E {
    E::And(es)
}
pub fn or(es: Vec<E>) -> E {
    E::Or(es)
}
pub fn ite(c: E, t: E, e: E) -> E {
    E::If(b(c), b(t), b(e))
}
pub fn exists(p: Pat, s: E, body: E) -> E {
    E::Exists(p, b(s), b(body))
}
pub fn forall(p: Pat, s: E, body: E) -> E {
    E::Forall(p, b(s), b(body))
}
pub fn let_in(defs: Vec<Def>, body: E) -> E {
    E::Let(defs, b(body))
}
pub fn def(n: &str, params: &[&str], body: E) -> Def {
    Def {
        name: n.to_string(),
        params: params.iter().map(|p| p.to_string()).collect(),
        arities: Vec::new(),
        body,
    }
}
/// A definition whose parameters carry arities (`F(_)` is `("F", 1)`).
pub fn def_ho(n: &str, params: &[(&str, usize)], body: E) -> Def {
    Def {
        name: n.to_string(),
        params: params.iter().map(|(p, _)| p.to_string()).collect(),
        arities: params.iter().map(|(_, a)| *a).collect(),
        body,
    }
}
pub fn unchanged_e(e: E) -> E {
    E::UnchangedE(b(e))
}
pub fn angle(a: E, sub: E) -> E {
    E::AngleAction(b(a), b(sub))
}
pub fn lambda(params: &[&str], body: E) -> E {
    E::Lambda(params.iter().map(|p| p.to_string()).collect(), b(body))
}
pub fn enabled(a: E) -> E {
    E::Enabled(b(a))
}
pub fn unchanged(v: Var) -> E {
    E::Unchanged(v)
}
pub fn pair(i: i64, j: i64) -> E {
    tuple(vec![int(i), int(j)])
}
/// `SUBSET (1..3)`.
pub fn subsets() -> E {
    subset(range(1, 3))
}
/// `(1..2) \X (1..2)`.
pub fn pairs() -> E {
    times(range(1, 2), range(1, 2))
}

/// `x' \in 0..3 /\ y' \in SUBSET (1..3) /\ z' \in (1..2) \X (1..2)`: every
/// generated ENABLED operand ends with it, so a successor the operand admits
/// lies in the model's finite universe and brute force over that universe
/// is exactly TLA+'s `ENABLED` (see the module docs of the oracle).
pub fn type_ok_primed() -> Vec<E> {
    vec![
        elem(prime(x()), range(0, 3)),
        elem(prime(y()), subsets()),
        elem(prime(z()), pairs()),
    ]
}

pub fn int_v(i: i64) -> V {
    V::Int(i)
}
pub fn set_v(items: &[i64]) -> V {
    V::Set(items.iter().map(|i| V::Int(*i)).collect())
}
pub fn pair_v(i: i64, j: i64) -> V {
    V::Tup(vec![V::Int(i), V::Int(j)])
}
