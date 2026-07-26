// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;
use std::fmt;

// ---------------------------------------------------------------------------
// Expression representation (self-contained, no sibling imports)
// ---------------------------------------------------------------------------

/// A logical expression used in proof goals and lemma statements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Expr {
    Var(String),
    IntLit(i128),
    BoolLit(bool),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Implies(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),
    Forall(String, Box<Expr>),
    Exists(String, Box<Expr>),
    FnApp(String, Vec<Expr>),
    ArrayIndex(Box<Expr>, Box<Expr>),
    ArrayLen(Box<Expr>),
    True,
    False,
}

impl Expr {
    pub(crate) fn var(name: &str) -> Self {
        Self::Var(name.to_owned())
    }

    pub(crate) fn int(v: i128) -> Self {
        Self::IntLit(v)
    }

    pub(crate) fn add(lhs: Expr, rhs: Expr) -> Self {
        Self::Add(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn sub(lhs: Expr, rhs: Expr) -> Self {
        Self::Sub(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn mul(lhs: Expr, rhs: Expr) -> Self {
        Self::Mul(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn and(lhs: Expr, rhs: Expr) -> Self {
        Self::And(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn or(lhs: Expr, rhs: Expr) -> Self {
        Self::Or(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn not(e: Expr) -> Self {
        Self::Not(Box::new(e))
    }

    pub(crate) fn implies(lhs: Expr, rhs: Expr) -> Self {
        Self::Implies(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn eq(lhs: Expr, rhs: Expr) -> Self {
        Self::Eq(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn lt(lhs: Expr, rhs: Expr) -> Self {
        Self::Lt(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn le(lhs: Expr, rhs: Expr) -> Self {
        Self::Le(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn gt(lhs: Expr, rhs: Expr) -> Self {
        Self::Gt(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn ge(lhs: Expr, rhs: Expr) -> Self {
        Self::Ge(Box::new(lhs), Box::new(rhs))
    }

    pub(crate) fn forall(var: &str, body: Expr) -> Self {
        Self::Forall(var.to_owned(), Box::new(body))
    }

    pub(crate) fn array_index(arr: Expr, idx: Expr) -> Self {
        Self::ArrayIndex(Box::new(arr), Box::new(idx))
    }

    pub(crate) fn array_len(arr: Expr) -> Self {
        Self::ArrayLen(Box::new(arr))
    }

    pub(crate) fn fn_app(name: &str, args: Vec<Expr>) -> Self {
        Self::FnApp(name.to_owned(), args)
    }

    /// Collect free variable names (not bound by quantifiers).
    pub(crate) fn free_vars(&self) -> Vec<String> {
        let mut result = Vec::new();
        self.collect_free_vars(&mut result, &mut Vec::new());
        let unique = result.into_iter().collect::<HashSet<_>>();
        let mut result = unique.into_iter().collect::<Vec<_>>();
        result.sort();
        result
    }

    fn collect_free_vars(&self, out: &mut Vec<String>, bound: &mut Vec<String>) {
        match self {
            Self::Var(n) => {
                if !bound.contains(n) {
                    out.push(n.clone());
                }
            }
            Self::IntLit(_) | Self::BoolLit(_) | Self::True | Self::False => {}
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::Mul(a, b)
            | Self::Div(a, b)
            | Self::Mod(a, b)
            | Self::And(a, b)
            | Self::Or(a, b)
            | Self::Implies(a, b)
            | Self::Eq(a, b)
            | Self::Lt(a, b)
            | Self::Le(a, b)
            | Self::Gt(a, b)
            | Self::Ge(a, b)
            | Self::ArrayIndex(a, b) => {
                a.collect_free_vars(out, bound);
                b.collect_free_vars(out, bound);
            }
            Self::Neg(a) | Self::Not(a) | Self::ArrayLen(a) => {
                a.collect_free_vars(out, bound);
            }
            Self::Forall(v, body) | Self::Exists(v, body) => {
                bound.push(v.clone());
                body.collect_free_vars(out, bound);
                bound.pop();
            }
            Self::FnApp(_, args) => {
                for a in args {
                    a.collect_free_vars(out, bound);
                }
            }
        }
    }

    /// Return true if this expression references the given variable name.
    pub(crate) fn mentions_var(&self, name: &str) -> bool {
        self.free_vars().iter().any(|v| v == name)
    }

    /// Structural complexity measure used for search pruning.
    pub(crate) fn complexity(&self) -> usize {
        match self {
            Self::Var(_) | Self::IntLit(_) | Self::BoolLit(_) | Self::True | Self::False => 1,
            Self::Add(a, b)
            | Self::Sub(a, b)
            | Self::Mul(a, b)
            | Self::Div(a, b)
            | Self::Mod(a, b)
            | Self::And(a, b)
            | Self::Or(a, b)
            | Self::Implies(a, b)
            | Self::Eq(a, b)
            | Self::Lt(a, b)
            | Self::Le(a, b)
            | Self::Gt(a, b)
            | Self::Ge(a, b)
            | Self::ArrayIndex(a, b) => 1 + a.complexity() + b.complexity(),
            Self::Neg(a) | Self::Not(a) | Self::ArrayLen(a) => 1 + a.complexity(),
            Self::Forall(_, body) | Self::Exists(_, body) => 2 + body.complexity(),
            Self::FnApp(_, args) => 1 + args.iter().map(|a| a.complexity()).sum::<usize>(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(n) => write!(f, "{n}"),
            Self::IntLit(v) => write!(f, "{v}"),
            Self::BoolLit(b) => write!(f, "{b}"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Add(a, b) => write!(f, "({a} + {b})"),
            Self::Sub(a, b) => write!(f, "({a} - {b})"),
            Self::Mul(a, b) => write!(f, "({a} * {b})"),
            Self::Div(a, b) => write!(f, "({a} / {b})"),
            Self::Mod(a, b) => write!(f, "({a} % {b})"),
            Self::Neg(a) => write!(f, "(-{a})"),
            Self::And(a, b) => write!(f, "({a} && {b})"),
            Self::Or(a, b) => write!(f, "({a} || {b})"),
            Self::Not(a) => write!(f, "(!{a})"),
            Self::Implies(a, b) => write!(f, "({a} ==> {b})"),
            Self::Eq(a, b) => write!(f, "({a} == {b})"),
            Self::Lt(a, b) => write!(f, "({a} < {b})"),
            Self::Le(a, b) => write!(f, "({a} <= {b})"),
            Self::Gt(a, b) => write!(f, "({a} > {b})"),
            Self::Ge(a, b) => write!(f, "({a} >= {b})"),
            Self::Forall(v, body) => write!(f, "(forall {v}. {body})"),
            Self::Exists(v, body) => write!(f, "(exists {v}. {body})"),
            Self::FnApp(name, args) => {
                write!(f, "{name}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Self::ArrayIndex(arr, idx) => write!(f, "{arr}[{idx}]"),
            Self::ArrayLen(arr) => write!(f, "len({arr})"),
        }
    }
}
