// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// VC expression AST
// ---------------------------------------------------------------------------

/// Simplified representation of a verification condition expression.
///
/// This is intentionally a lightweight AST for analysis purposes — it does
/// not carry the full fidelity of the ay term graph. The encoder lowers
/// `TrustVcExpr` into `VcExpression` for pre-solving analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VcExpression {
    /// Boolean literal.
    Literal(bool),
    /// Named variable reference.
    Variable(String),
    /// Logical conjunction.
    And(Vec<VcExpression>),
    /// Logical disjunction.
    Or(Vec<VcExpression>),
    /// Logical negation.
    Not(Box<VcExpression>),
    /// Implication (antecedent, consequent).
    Implies(Box<VcExpression>, Box<VcExpression>),
    /// Universal quantifier (bound variable names, body).
    Forall(Vec<String>, Box<VcExpression>),
    /// Existential quantifier (bound variable names, body).
    Exists(Vec<String>, Box<VcExpression>),
    /// Arithmetic operation (operator tag, operands).
    Arith(ArithOp, Vec<VcExpression>),
    /// Bitvector operation (operator tag, width, operands).
    BvOp(BvOp, u32, Vec<VcExpression>),
    /// Array/sequence operation (operator tag, operands).
    ArrayOp(ArrayOp, Vec<VcExpression>),
    /// Uninterpreted function application (name, arguments).
    UfApp(String, Vec<VcExpression>),
    /// Comparison (operator tag, lhs, rhs).
    Compare(CompareOp, Box<VcExpression>, Box<VcExpression>),
    /// If-then-else (condition, then-branch, else-branch).
    Ite(Box<VcExpression>, Box<VcExpression>, Box<VcExpression>),
    /// Integer constant.
    IntConst(i128),
}

/// Arithmetic operation tags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,
}

/// Bitvector operation tags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BvOp {
    BvAnd,
    BvOr,
    BvXor,
    BvNot,
    Shl,
    Shr,
    RotateLeft,
    RotateRight,
    Extract,
    ZeroExtend,
    SignExtend,
    BvAdd,
    BvSub,
    BvMul,
}

/// Array/sequence operation tags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArrayOp {
    Select,
    Store,
    SeqLen,
    SeqConcat,
    SeqNth,
    SeqPush,
    ConstArray,
}

/// Comparison operation tags.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl VcExpression {
    /// Maximum depth of the expression tree.
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Self::Literal(_) | Self::Variable(_) | Self::IntConst(_) => 1,
            Self::Not(e) => 1 + e.depth(),
            Self::And(es) | Self::Or(es) => 1 + es.iter().map(Self::depth).max().unwrap_or(0),
            Self::Implies(a, b) => 1 + a.depth().max(b.depth()),
            Self::Forall(_, body) | Self::Exists(_, body) => 1 + body.depth(),
            Self::Arith(_, es) | Self::ArrayOp(_, es) | Self::UfApp(_, es) => {
                1 + es.iter().map(Self::depth).max().unwrap_or(0)
            }
            Self::BvOp(_, _, es) => 1 + es.iter().map(Self::depth).max().unwrap_or(0),
            Self::Compare(_, a, b) => 1 + a.depth().max(b.depth()),
            Self::Ite(c, t, e) => 1 + c.depth().max(t.depth()).max(e.depth()),
        }
    }

    /// Total number of nodes in the expression tree.
    #[must_use]
    pub fn node_count(&self) -> usize {
        match self {
            Self::Literal(_) | Self::Variable(_) | Self::IntConst(_) => 1,
            Self::Not(e) => 1 + e.node_count(),
            Self::And(es) | Self::Or(es) => 1 + es.iter().map(Self::node_count).sum::<usize>(),
            Self::Implies(a, b) => 1 + a.node_count() + b.node_count(),
            Self::Forall(_, body) | Self::Exists(_, body) => 1 + body.node_count(),
            Self::Arith(_, es) | Self::ArrayOp(_, es) | Self::UfApp(_, es) => {
                1 + es.iter().map(Self::node_count).sum::<usize>()
            }
            Self::BvOp(_, _, es) => 1 + es.iter().map(Self::node_count).sum::<usize>(),
            Self::Compare(_, a, b) => 1 + a.node_count() + b.node_count(),
            Self::Ite(c, t, e) => 1 + c.node_count() + t.node_count() + e.node_count(),
        }
    }

    /// Collect all free variable names (does not recurse into quantifier-bound names).
    #[must_use]
    pub fn variable_names(&self) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        self.collect_variables(&mut names, &BTreeSet::new());
        names
    }

    fn collect_variables(&self, acc: &mut BTreeSet<String>, bound: &BTreeSet<String>) {
        match self {
            Self::Literal(_) | Self::IntConst(_) => {}
            Self::Variable(name) => {
                if !bound.contains(name) {
                    acc.insert(name.clone());
                }
            }
            Self::Not(e) => e.collect_variables(acc, bound),
            Self::And(es) | Self::Or(es) => {
                for e in es {
                    e.collect_variables(acc, bound);
                }
            }
            Self::Implies(a, b) => {
                a.collect_variables(acc, bound);
                b.collect_variables(acc, bound);
            }
            Self::Forall(vars, body) | Self::Exists(vars, body) => {
                let mut inner_bound = bound.clone();
                for v in vars {
                    inner_bound.insert(v.clone());
                }
                body.collect_variables(acc, &inner_bound);
            }
            Self::Arith(_, es) | Self::ArrayOp(_, es) | Self::UfApp(_, es) => {
                for e in es {
                    e.collect_variables(acc, bound);
                }
            }
            Self::BvOp(_, _, es) => {
                for e in es {
                    e.collect_variables(acc, bound);
                }
            }
            Self::Compare(_, a, b) => {
                a.collect_variables(acc, bound);
                b.collect_variables(acc, bound);
            }
            Self::Ite(c, t, e) => {
                c.collect_variables(acc, bound);
                t.collect_variables(acc, bound);
                e.collect_variables(acc, bound);
            }
        }
    }

    /// Returns `true` if the expression tree contains any node from the
    /// specified theory.
    #[must_use]
    pub fn contains_theory(&self, theory: Theory) -> bool {
        match self {
            Self::Literal(_) | Self::Variable(_) | Self::IntConst(_) => false,
            Self::Not(e) => e.contains_theory(theory),
            Self::And(es) | Self::Or(es) => es.iter().any(|e| e.contains_theory(theory)),
            Self::Implies(a, b) => a.contains_theory(theory) || b.contains_theory(theory),
            Self::Forall(_, body) | Self::Exists(_, body) => {
                matches!(theory, Theory::Quantifier) || body.contains_theory(theory)
            }
            Self::Arith(..) => {
                matches!(theory, Theory::Arithmetic)
            }
            Self::BvOp(..) => {
                matches!(theory, Theory::BitVector)
            }
            Self::ArrayOp(..) => {
                matches!(theory, Theory::Array)
            }
            Self::UfApp(_, args) => {
                if matches!(theory, Theory::UninterpretedFunction) {
                    return true;
                }
                args.iter().any(|a| a.contains_theory(theory))
            }
            Self::Compare(_, a, b) => a.contains_theory(theory) || b.contains_theory(theory),
            Self::Ite(c, t, e) => {
                c.contains_theory(theory) || t.contains_theory(theory) || e.contains_theory(theory)
            }
        }
    }
}

/// SMT theory tags for `contains_theory` queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Theory {
    Arithmetic,
    BitVector,
    Array,
    UninterpretedFunction,
    Quantifier,
}
