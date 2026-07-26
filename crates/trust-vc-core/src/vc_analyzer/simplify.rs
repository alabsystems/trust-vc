// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// VC simplification
// ---------------------------------------------------------------------------

/// Statistics about what simplifications were applied.
#[derive(Debug, Clone, Default)]
pub struct SimplificationStats {
    /// Number of constant-folding reductions.
    pub constant_folds: usize,
    /// Number of double-negation eliminations.
    pub double_negations: usize,
    /// Number of trivial bound eliminations (And(true, x) -> x, etc.).
    pub trivial_bounds: usize,
    /// Number of identity eliminations (Or(false, x) -> x, etc.).
    pub identity_eliminations: usize,
    /// Original node count before simplification.
    pub original_nodes: usize,
    /// Final node count after simplification.
    pub final_nodes: usize,
}

impl SimplificationStats {
    /// The total number of simplification steps applied.
    #[must_use]
    pub fn total_reductions(&self) -> usize {
        self.constant_folds
            + self.double_negations
            + self.trivial_bounds
            + self.identity_eliminations
    }

    /// Fraction of nodes eliminated, in `[0.0, 1.0]`.
    #[must_use]
    pub fn reduction_ratio(&self) -> f64 {
        if self.original_nodes == 0 {
            return 0.0;
        }
        1.0 - (self.final_nodes as f64 / self.original_nodes as f64)
    }
}

/// Lightweight VC simplifier: constant folding, double-negation elimination,
/// trivial conjunction/disjunction pruning.
pub struct VcSimplifier;

impl VcSimplifier {
    /// Simplify an expression and return the result with stats.
    #[must_use]
    pub fn simplify(expr: &VcExpression) -> (VcExpression, SimplificationStats) {
        let original_nodes = expr.node_count();
        let mut stats = SimplificationStats {
            original_nodes,
            ..Default::default()
        };
        let result = Self::simplify_inner(expr, &mut stats);
        stats.final_nodes = result.node_count();
        (result, stats)
    }

    fn simplify_inner(expr: &VcExpression, stats: &mut SimplificationStats) -> VcExpression {
        match expr {
            VcExpression::Not(inner) => {
                let simplified_inner = Self::simplify_inner(inner, stats);
                // Double negation: Not(Not(x)) -> x.
                if let VcExpression::Not(double_inner) = &simplified_inner {
                    stats.double_negations += 1;
                    return *double_inner.clone();
                }
                // Not(true) -> false, Not(false) -> true.
                if let VcExpression::Literal(b) = simplified_inner {
                    stats.constant_folds += 1;
                    return VcExpression::Literal(!b);
                }
                VcExpression::Not(Box::new(simplified_inner))
            }
            VcExpression::And(conjuncts) => {
                let simplified: Vec<VcExpression> = conjuncts
                    .iter()
                    .map(|c| Self::simplify_inner(c, stats))
                    .collect();

                // Short-circuit: And([..., false, ...]) -> false.
                if simplified
                    .iter()
                    .any(|c| matches!(c, VcExpression::Literal(false)))
                {
                    stats.constant_folds += 1;
                    return VcExpression::Literal(false);
                }

                // Remove true literals: And([true, x, true]) -> And([x]) -> x.
                let filtered: Vec<VcExpression> = simplified
                    .into_iter()
                    .filter(|c| {
                        if matches!(c, VcExpression::Literal(true)) {
                            stats.trivial_bounds += 1;
                            false
                        } else {
                            true
                        }
                    })
                    .collect();

                match filtered.len() {
                    0 => VcExpression::Literal(true),
                    1 => filtered
                        .into_iter()
                        .next()
                        .unwrap_or(VcExpression::Literal(true)),
                    _ => VcExpression::And(filtered),
                }
            }
            VcExpression::Or(disjuncts) => {
                let simplified: Vec<VcExpression> = disjuncts
                    .iter()
                    .map(|d| Self::simplify_inner(d, stats))
                    .collect();

                // Short-circuit: Or([..., true, ...]) -> true.
                if simplified
                    .iter()
                    .any(|d| matches!(d, VcExpression::Literal(true)))
                {
                    stats.constant_folds += 1;
                    return VcExpression::Literal(true);
                }

                // Remove false literals.
                let filtered: Vec<VcExpression> = simplified
                    .into_iter()
                    .filter(|d| {
                        if matches!(d, VcExpression::Literal(false)) {
                            stats.identity_eliminations += 1;
                            false
                        } else {
                            true
                        }
                    })
                    .collect();

                match filtered.len() {
                    0 => VcExpression::Literal(false),
                    1 => filtered
                        .into_iter()
                        .next()
                        .unwrap_or(VcExpression::Literal(false)),
                    _ => VcExpression::Or(filtered),
                }
            }
            VcExpression::Implies(a, b) => {
                let sa = Self::simplify_inner(a, stats);
                let sb = Self::simplify_inner(b, stats);
                // true => b -> b.
                if matches!(&sa, VcExpression::Literal(true)) {
                    stats.trivial_bounds += 1;
                    return sb;
                }
                // false => b -> true.
                if matches!(&sa, VcExpression::Literal(false)) {
                    stats.constant_folds += 1;
                    return VcExpression::Literal(true);
                }
                // a => true -> true.
                if matches!(&sb, VcExpression::Literal(true)) {
                    stats.constant_folds += 1;
                    return VcExpression::Literal(true);
                }
                VcExpression::Implies(Box::new(sa), Box::new(sb))
            }
            VcExpression::Forall(vars, body) => {
                let sb = Self::simplify_inner(body, stats);
                VcExpression::Forall(vars.clone(), Box::new(sb))
            }
            VcExpression::Exists(vars, body) => {
                let sb = Self::simplify_inner(body, stats);
                VcExpression::Exists(vars.clone(), Box::new(sb))
            }
            VcExpression::Ite(c, t, e) => {
                let sc = Self::simplify_inner(c, stats);
                let st = Self::simplify_inner(t, stats);
                let se = Self::simplify_inner(e, stats);
                // ite(true, t, e) -> t.
                if matches!(&sc, VcExpression::Literal(true)) {
                    stats.constant_folds += 1;
                    return st;
                }
                // ite(false, t, e) -> e.
                if matches!(&sc, VcExpression::Literal(false)) {
                    stats.constant_folds += 1;
                    return se;
                }
                VcExpression::Ite(Box::new(sc), Box::new(st), Box::new(se))
            }
            // Non-reducible nodes: return as-is.
            other => other.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Full VC analysis
// ---------------------------------------------------------------------------

/// Complete analysis result for a verification condition.
#[derive(Debug, Clone)]
pub struct VcAnalysis {
    pub theory_profile: TheoryProfile,
    pub quantifier_profile: QuantifierProfile,
    pub arith_profile: ArithProfile,
    pub bv_profile: BvProfile,
    pub statistics: VcStatistics,
    pub patterns: Vec<DetectedPattern>,
}

impl VcAnalysis {
    /// Perform a full analysis of a VC expression.
    #[must_use]
    pub fn analyze(expr: &VcExpression) -> Self {
        Self {
            theory_profile: TheoryProfile::from_expr(expr),
            quantifier_profile: QuantifierProfile::from_expr(expr),
            arith_profile: ArithProfile::from_expr(expr),
            bv_profile: BvProfile::from_expr(expr),
            statistics: VcStatistics::compute(expr),
            patterns: PatternDetector::detect(expr),
        }
    }
}
