// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors produced by the spec language parser.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
#[error("parse error at offset {offset}: {message}")]
pub struct ParseError {
    pub message: String,
    pub offset: usize,
}

impl ParseError {
    #[must_use]
    pub fn new(message: impl Into<String>, offset: usize) -> Self {
        Self {
            message: message.into(),
            offset,
        }
    }
}

// ---------------------------------------------------------------------------
// AST types
// ---------------------------------------------------------------------------

/// Binary operator kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
}

/// Unary operator kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnaryOpKind {
    Not,
    Neg,
}

/// Quantifier kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum QuantKind {
    Forall,
    Exists,
}

/// A specification expression AST node.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SpecExpr {
    Variable(String),
    IntLit(i64),
    BoolLit(bool),
    BinOp(Box<SpecExpr>, BinOpKind, Box<SpecExpr>),
    UnaryOp(UnaryOpKind, Box<SpecExpr>),
    FnCall(String, Vec<SpecExpr>),
    Quantifier(QuantKind, Vec<(String, String)>, Box<SpecExpr>),
    FieldAccess(Box<SpecExpr>, String),
    IndexAccess(Box<SpecExpr>, Box<SpecExpr>),
    IfThenElse(Box<SpecExpr>, Box<SpecExpr>, Box<SpecExpr>),
    Old(Box<SpecExpr>),
}

/// A specification clause attached to a function.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SpecClause {
    Requires(SpecExpr),
    Ensures(SpecExpr),
    Invariant(SpecExpr),
    Decreases(SpecExpr),
}

/// A complete function specification: name, parameters, return type, and clauses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSpec {
    pub name: String,
    pub params: Vec<(String, String)>,
    pub return_type: Option<String>,
    pub clauses: Vec<SpecClause>,
}

// ---------------------------------------------------------------------------
// SpecExpr methods
// ---------------------------------------------------------------------------

impl SpecExpr {
    /// Collect all free (unbound) variable names in this expression.
    #[must_use]
    pub fn free_variables(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        self.collect_free_vars(&mut vars, &HashSet::new());
        vars
    }

    fn collect_free_vars(&self, acc: &mut HashSet<String>, bound: &HashSet<String>) {
        match self {
            Self::Variable(name) => {
                if !bound.contains(name) {
                    acc.insert(name.clone());
                }
            }
            Self::IntLit(_) | Self::BoolLit(_) => {}
            Self::BinOp(lhs, _, rhs) => {
                lhs.collect_free_vars(acc, bound);
                rhs.collect_free_vars(acc, bound);
            }
            Self::UnaryOp(_, inner) => inner.collect_free_vars(acc, bound),
            Self::FnCall(_, args) => {
                for arg in args {
                    arg.collect_free_vars(acc, bound);
                }
            }
            Self::Quantifier(_, bindings, body) => {
                let mut inner_bound = bound.clone();
                for (name, _) in bindings {
                    inner_bound.insert(name.clone());
                }
                body.collect_free_vars(acc, &inner_bound);
            }
            Self::FieldAccess(base, _) => base.collect_free_vars(acc, bound),
            Self::IndexAccess(base, index) => {
                base.collect_free_vars(acc, bound);
                index.collect_free_vars(acc, bound);
            }
            Self::IfThenElse(cond, then_br, else_br) => {
                cond.collect_free_vars(acc, bound);
                then_br.collect_free_vars(acc, bound);
                else_br.collect_free_vars(acc, bound);
            }
            Self::Old(inner) => inner.collect_free_vars(acc, bound),
        }
    }

    /// Maximum nesting depth of the expression tree.
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Self::Variable(_) | Self::IntLit(_) | Self::BoolLit(_) => 1,
            Self::BinOp(lhs, _, rhs) => 1 + lhs.depth().max(rhs.depth()),
            Self::UnaryOp(_, inner) | Self::Old(inner) => 1 + inner.depth(),
            Self::FnCall(_, args) => 1 + args.iter().map(Self::depth).max().unwrap_or(0),
            Self::Quantifier(_, _, body) => 1 + body.depth(),
            Self::FieldAccess(base, _) => 1 + base.depth(),
            Self::IndexAccess(base, index) => 1 + base.depth().max(index.depth()),
            Self::IfThenElse(c, t, e) => 1 + c.depth().max(t.depth()).max(e.depth()),
        }
    }

    /// Total number of AST nodes in the expression.
    #[must_use]
    pub fn complexity(&self) -> usize {
        match self {
            Self::Variable(_) | Self::IntLit(_) | Self::BoolLit(_) => 1,
            Self::BinOp(lhs, _, rhs) => 1 + lhs.complexity() + rhs.complexity(),
            Self::UnaryOp(_, inner) | Self::Old(inner) => 1 + inner.complexity(),
            Self::FnCall(_, args) => 1 + args.iter().map(Self::complexity).sum::<usize>(),
            Self::Quantifier(_, _, body) => 1 + body.complexity(),
            Self::FieldAccess(base, _) => 1 + base.complexity(),
            Self::IndexAccess(base, index) => 1 + base.complexity() + index.complexity(),
            Self::IfThenElse(c, t, e) => 1 + c.complexity() + t.complexity() + e.complexity(),
        }
    }
}

// ---------------------------------------------------------------------------
// FunctionSpec methods
// ---------------------------------------------------------------------------

impl FunctionSpec {
    /// Merge another `FunctionSpec` into this one, combining clauses.
    ///
    /// Both specs must share the same function name. Parameters and return type
    /// from `other` are adopted when `self` lacks them.
    #[must_use]
    pub fn merge(&self, other: &FunctionSpec) -> FunctionSpec {
        let params = if self.params.is_empty() {
            other.params.clone()
        } else {
            self.params.clone()
        };
        let return_type = self
            .return_type
            .clone()
            .or_else(|| other.return_type.clone());
        let mut clauses = self.clauses.clone();
        clauses.extend(other.clauses.iter().cloned());
        FunctionSpec {
            name: self.name.clone(),
            params,
            return_type,
            clauses,
        }
    }

    /// Validate consistency of the spec, returning a list of warnings.
    ///
    /// Checks performed:
    /// - At least one clause is present.
    /// - Ensures clauses reference variables that are either params or `result`.
    /// - Decreases clauses appear at most once.
    #[must_use]
    pub fn validate(&self) -> Vec<String> {
        let mut warnings = Vec::new();

        if self.clauses.is_empty() {
            warnings.push("no specification clauses".to_string());
        }

        let param_names: HashSet<String> = self.params.iter().map(|(n, _)| n.clone()).collect();

        for clause in &self.clauses {
            let expr = match clause {
                SpecClause::Requires(e)
                | SpecClause::Ensures(e)
                | SpecClause::Invariant(e)
                | SpecClause::Decreases(e) => e,
            };
            let fv = expr.free_variables();
            for var in &fv {
                if var != "result" && !param_names.contains(var) {
                    warnings.push(format!(
                        "variable `{var}` in clause is not a parameter or `result`"
                    ));
                }
            }
        }

        let decreases_count = self
            .clauses
            .iter()
            .filter(|c| matches!(c, SpecClause::Decreases(_)))
            .count();
        if decreases_count > 1 {
            warnings.push(format!("multiple decreases clauses ({decreases_count})"));
        }

        warnings
    }
}
