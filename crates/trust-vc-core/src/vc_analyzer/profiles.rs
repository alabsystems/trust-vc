// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::ast::*;
use std::collections::{BTreeSet, HashMap};

// ---------------------------------------------------------------------------
// Theory profile
// ---------------------------------------------------------------------------

/// Summarizes which SMT theories are exercised and their relative weight.
#[derive(Debug, Clone, Default)]
pub struct TheoryProfile {
    pub arithmetic_weight: f64,
    pub bitvector_weight: f64,
    pub array_weight: f64,
    pub uf_weight: f64,
    pub quantifier_weight: f64,
    pub boolean_weight: f64,
    pub total_nodes: usize,
}

impl TheoryProfile {
    /// Build a theory profile by traversing the expression.
    #[must_use]
    pub fn from_expr(expr: &VcExpression) -> Self {
        let mut profile = Self {
            total_nodes: expr.node_count(),
            ..Self::default()
        };
        Self::walk(expr, &mut profile);

        // Normalize weights to [0, 1].
        if profile.total_nodes > 0 {
            let n = profile.total_nodes as f64;
            profile.arithmetic_weight /= n;
            profile.bitvector_weight /= n;
            profile.array_weight /= n;
            profile.uf_weight /= n;
            profile.quantifier_weight /= n;
            profile.boolean_weight /= n;
        }
        profile
    }

    fn walk(expr: &VcExpression, profile: &mut Self) {
        match expr {
            VcExpression::Literal(_) => {
                profile.boolean_weight += 1.0;
            }
            VcExpression::IntConst(_) | VcExpression::Variable(_) => {
                // Neutral leaves — don't contribute to any specific theory weight.
            }
            VcExpression::Not(e) => {
                profile.boolean_weight += 1.0;
                Self::walk(e, profile);
            }
            VcExpression::And(es) | VcExpression::Or(es) => {
                profile.boolean_weight += 1.0;
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::Implies(a, b) => {
                profile.boolean_weight += 1.0;
                Self::walk(a, profile);
                Self::walk(b, profile);
            }
            VcExpression::Forall(_, body) | VcExpression::Exists(_, body) => {
                profile.quantifier_weight += 1.0;
                Self::walk(body, profile);
            }
            VcExpression::Arith(_, es) => {
                profile.arithmetic_weight += 1.0;
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::BvOp(_, _, es) => {
                profile.bitvector_weight += 1.0;
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::ArrayOp(_, es) => {
                profile.array_weight += 1.0;
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::UfApp(_, args) => {
                profile.uf_weight += 1.0;
                for a in args {
                    Self::walk(a, profile);
                }
            }
            VcExpression::Compare(_, a, b) => {
                profile.boolean_weight += 1.0;
                Self::walk(a, profile);
                Self::walk(b, profile);
            }
            VcExpression::Ite(c, t, e) => {
                profile.boolean_weight += 1.0;
                Self::walk(c, profile);
                Self::walk(t, profile);
                Self::walk(e, profile);
            }
        }
    }

    /// Returns the dominant theory by weight.
    #[must_use]
    pub fn dominant_theory(&self) -> Theory {
        let candidates = [
            (self.arithmetic_weight, Theory::Arithmetic),
            (self.bitvector_weight, Theory::BitVector),
            (self.array_weight, Theory::Array),
            (self.uf_weight, Theory::UninterpretedFunction),
            (self.quantifier_weight, Theory::Quantifier),
        ];
        candidates
            .iter()
            .max_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal))
            .map(|&(_, t)| t)
            .unwrap_or(Theory::Arithmetic)
    }
}

// ---------------------------------------------------------------------------
// Quantifier profile
// ---------------------------------------------------------------------------

/// Analysis of the quantifier structure in a VC.
#[derive(Debug, Clone, Default)]
pub struct QuantifierProfile {
    /// Maximum quantifier nesting depth.
    pub max_depth: usize,
    /// Total number of quantifiers.
    pub count: usize,
    /// Number of forall quantifiers.
    pub forall_count: usize,
    /// Number of exists quantifiers.
    pub exists_count: usize,
    /// Quantifier alternation count (forall-exists or exists-forall transitions).
    pub alternation_count: usize,
    /// Total number of bound variables across all quantifiers.
    pub bound_variable_count: usize,
    /// Whether any quantifier has an associated trigger/pattern.
    pub has_patterns: bool,
}

impl QuantifierProfile {
    /// Build a quantifier profile from an expression.
    #[must_use]
    pub fn from_expr(expr: &VcExpression) -> Self {
        let mut profile = Self::default();
        Self::walk(expr, 0, None, &mut profile);
        profile
    }

    fn walk(expr: &VcExpression, depth: usize, last_quant: Option<QuantKind>, profile: &mut Self) {
        match expr {
            VcExpression::Forall(vars, body) => {
                let new_depth = depth + 1;
                profile.count += 1;
                profile.forall_count += 1;
                profile.bound_variable_count += vars.len();
                profile.max_depth = profile.max_depth.max(new_depth);
                if last_quant == Some(QuantKind::Exists) {
                    profile.alternation_count += 1;
                }
                Self::walk(body, new_depth, Some(QuantKind::Forall), profile);
            }
            VcExpression::Exists(vars, body) => {
                let new_depth = depth + 1;
                profile.count += 1;
                profile.exists_count += 1;
                profile.bound_variable_count += vars.len();
                profile.max_depth = profile.max_depth.max(new_depth);
                if last_quant == Some(QuantKind::Forall) {
                    profile.alternation_count += 1;
                }
                Self::walk(body, new_depth, Some(QuantKind::Exists), profile);
            }
            VcExpression::Not(e) => Self::walk(e, depth, last_quant, profile),
            VcExpression::And(es) | VcExpression::Or(es) => {
                for e in es {
                    Self::walk(e, depth, last_quant, profile);
                }
            }
            VcExpression::Implies(a, b) => {
                Self::walk(a, depth, last_quant, profile);
                Self::walk(b, depth, last_quant, profile);
            }
            VcExpression::Arith(_, es)
            | VcExpression::ArrayOp(_, es)
            | VcExpression::UfApp(_, es) => {
                for e in es {
                    Self::walk(e, depth, last_quant, profile);
                }
            }
            VcExpression::BvOp(_, _, es) => {
                for e in es {
                    Self::walk(e, depth, last_quant, profile);
                }
            }
            VcExpression::Compare(_, a, b) => {
                Self::walk(a, depth, last_quant, profile);
                Self::walk(b, depth, last_quant, profile);
            }
            VcExpression::Ite(c, t, e) => {
                Self::walk(c, depth, last_quant, profile);
                Self::walk(t, depth, last_quant, profile);
                Self::walk(e, depth, last_quant, profile);
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QuantKind {
    Forall,
    Exists,
}

// ---------------------------------------------------------------------------
// Arithmetic profile
// ---------------------------------------------------------------------------

/// Analysis of the arithmetic content of a VC.
#[derive(Debug, Clone, Default)]
pub struct ArithProfile {
    /// Whether the VC contains linear arithmetic (add, sub, const * var).
    pub has_linear: bool,
    /// Whether the VC contains nonlinear arithmetic (var * var, div, mod).
    pub has_nonlinear: bool,
    /// Whether integer arithmetic is used.
    pub has_integer: bool,
    /// Whether real arithmetic is used (inferred from division).
    pub has_real: bool,
    /// Whether division is present.
    pub has_division: bool,
    /// Whether modulus is present.
    pub has_modulus: bool,
    /// Total count of arithmetic operations.
    pub op_count: usize,
    /// Distribution of operations by tag.
    pub op_distribution: HashMap<ArithOp, usize>,
}

impl ArithProfile {
    /// Build an arithmetic profile from an expression.
    #[must_use]
    pub fn from_expr(expr: &VcExpression) -> Self {
        let mut profile = Self {
            has_integer: true, // default assumption — all trust_vc arith is integer
            ..Self::default()
        };
        Self::walk(expr, &mut profile);
        // If we found no arithmetic ops at all, clear the integer flag.
        if profile.op_count == 0 {
            profile.has_integer = false;
        }
        profile
    }

    fn walk(expr: &VcExpression, profile: &mut Self) {
        match expr {
            VcExpression::Arith(op, operands) => {
                profile.op_count += 1;
                *profile.op_distribution.entry(*op).or_insert(0) += 1;

                match op {
                    ArithOp::Add | ArithOp::Sub | ArithOp::Neg => {
                        profile.has_linear = true;
                    }
                    ArithOp::Mul => {
                        // Nonlinear if both operands are non-constant.
                        let non_const_count = operands
                            .iter()
                            .filter(|o| {
                                !matches!(o, VcExpression::IntConst(_) | VcExpression::Literal(_))
                            })
                            .count();
                        if non_const_count >= 2 {
                            profile.has_nonlinear = true;
                        } else {
                            profile.has_linear = true;
                        }
                    }
                    ArithOp::Div => {
                        profile.has_nonlinear = true;
                        profile.has_division = true;
                        profile.has_real = true;
                    }
                    ArithOp::Mod => {
                        profile.has_nonlinear = true;
                        profile.has_modulus = true;
                    }
                }

                for o in operands {
                    Self::walk(o, profile);
                }
            }
            VcExpression::Not(e) => Self::walk(e, profile),
            VcExpression::And(es) | VcExpression::Or(es) => {
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::Implies(a, b) => {
                Self::walk(a, profile);
                Self::walk(b, profile);
            }
            VcExpression::Forall(_, body) | VcExpression::Exists(_, body) => {
                Self::walk(body, profile);
            }
            VcExpression::BvOp(_, _, es) => {
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::ArrayOp(_, es) | VcExpression::UfApp(_, es) => {
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::Compare(_, a, b) => {
                Self::walk(a, profile);
                Self::walk(b, profile);
            }
            VcExpression::Ite(c, t, e) => {
                Self::walk(c, profile);
                Self::walk(t, profile);
                Self::walk(e, profile);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Bitvector profile
// ---------------------------------------------------------------------------

/// Analysis of the bitvector content of a VC.
#[derive(Debug, Clone, Default)]
pub struct BvProfile {
    /// All bitvector widths observed.
    pub widths_used: BTreeSet<u32>,
    /// Maximum bitvector width.
    pub max_width: u32,
    /// Whether shift operations are present.
    pub has_shift: bool,
    /// Whether rotate operations are present.
    pub has_rotate: bool,
    /// Whether extract/extend operations are present.
    pub has_extract: bool,
    /// Total count of bitvector operations.
    pub op_count: usize,
    /// Distribution of operations by tag.
    pub op_distribution: HashMap<BvOp, usize>,
}

impl BvProfile {
    /// Build a bitvector profile from an expression.
    #[must_use]
    pub fn from_expr(expr: &VcExpression) -> Self {
        let mut profile = Self::default();
        Self::walk(expr, &mut profile);
        profile
    }

    fn walk(expr: &VcExpression, profile: &mut Self) {
        match expr {
            VcExpression::BvOp(op, width, operands) => {
                profile.op_count += 1;
                profile.widths_used.insert(*width);
                profile.max_width = profile.max_width.max(*width);
                *profile.op_distribution.entry(*op).or_insert(0) += 1;

                match op {
                    BvOp::Shl | BvOp::Shr => profile.has_shift = true,
                    BvOp::RotateLeft | BvOp::RotateRight => profile.has_rotate = true,
                    BvOp::Extract | BvOp::ZeroExtend | BvOp::SignExtend => {
                        profile.has_extract = true;
                    }
                    _ => {}
                }

                for o in operands {
                    Self::walk(o, profile);
                }
            }
            VcExpression::Not(e) => Self::walk(e, profile),
            VcExpression::And(es) | VcExpression::Or(es) => {
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::Implies(a, b) => {
                Self::walk(a, profile);
                Self::walk(b, profile);
            }
            VcExpression::Forall(_, body) | VcExpression::Exists(_, body) => {
                Self::walk(body, profile);
            }
            VcExpression::Arith(_, es)
            | VcExpression::ArrayOp(_, es)
            | VcExpression::UfApp(_, es) => {
                for e in es {
                    Self::walk(e, profile);
                }
            }
            VcExpression::Compare(_, a, b) => {
                Self::walk(a, profile);
                Self::walk(b, profile);
            }
            VcExpression::Ite(c, t, e) => {
                Self::walk(c, profile);
                Self::walk(t, profile);
                Self::walk(e, profile);
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// VC statistics
// ---------------------------------------------------------------------------

/// Aggregate size metrics for a VC expression tree.
#[derive(Debug, Clone, Default)]
pub struct VcStatistics {
    /// Total number of AST nodes.
    pub node_count: usize,
    /// Maximum tree depth.
    pub depth: usize,
    /// Number of distinct free variables.
    pub variable_count: usize,
    /// Number of And/Or clauses (top-level conjuncts/disjuncts).
    pub clause_count: usize,
    /// Number of quantifiers.
    pub quantifier_count: usize,
    /// Number of UF applications.
    pub uf_app_count: usize,
    /// Number of arithmetic operations.
    pub arith_op_count: usize,
    /// Number of bitvector operations.
    pub bv_op_count: usize,
    /// Number of array operations.
    pub array_op_count: usize,
}

impl VcStatistics {
    /// Compute statistics for an expression.
    #[must_use]
    pub fn compute(expr: &VcExpression) -> Self {
        let mut stats = Self {
            node_count: expr.node_count(),
            depth: expr.depth(),
            variable_count: expr.variable_names().len(),
            ..Default::default()
        };
        Self::walk(expr, &mut stats);
        stats
    }

    fn walk(expr: &VcExpression, stats: &mut Self) {
        match expr {
            VcExpression::And(es) => {
                stats.clause_count += es.len();
                for e in es {
                    Self::walk(e, stats);
                }
            }
            VcExpression::Or(es) => {
                stats.clause_count += es.len();
                for e in es {
                    Self::walk(e, stats);
                }
            }
            VcExpression::Not(e) => Self::walk(e, stats),
            VcExpression::Implies(a, b) => {
                Self::walk(a, stats);
                Self::walk(b, stats);
            }
            VcExpression::Forall(_, body) | VcExpression::Exists(_, body) => {
                stats.quantifier_count += 1;
                Self::walk(body, stats);
            }
            VcExpression::Arith(_, es) => {
                stats.arith_op_count += 1;
                for e in es {
                    Self::walk(e, stats);
                }
            }
            VcExpression::BvOp(_, _, es) => {
                stats.bv_op_count += 1;
                for e in es {
                    Self::walk(e, stats);
                }
            }
            VcExpression::ArrayOp(_, es) => {
                stats.array_op_count += 1;
                for e in es {
                    Self::walk(e, stats);
                }
            }
            VcExpression::UfApp(_, args) => {
                stats.uf_app_count += 1;
                for a in args {
                    Self::walk(a, stats);
                }
            }
            VcExpression::Compare(_, a, b) => {
                Self::walk(a, stats);
                Self::walk(b, stats);
            }
            VcExpression::Ite(c, t, e) => {
                Self::walk(c, stats);
                Self::walk(t, stats);
                Self::walk(e, stats);
            }
            _ => {}
        }
    }
}
