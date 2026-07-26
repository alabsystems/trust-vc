// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// Pattern detection
// ---------------------------------------------------------------------------

/// A detected proof-obligation pattern.
#[derive(Debug, Clone)]
pub struct DetectedPattern {
    /// Human-readable pattern name (e.g. "bounds_check", "overflow_guard").
    pub name: String,
    /// Confidence in detection, in `[0.0, 1.0]`.
    pub confidence: f64,
    /// Approximate depth in the expression tree where the pattern was found.
    pub location_depth: usize,
    /// Brief description of the detected pattern.
    pub description: String,
}

/// Detects common verification-condition patterns.
pub struct PatternDetector;

impl PatternDetector {
    /// Scan an expression for known VC patterns.
    #[must_use]
    pub fn detect(expr: &VcExpression) -> Vec<DetectedPattern> {
        let mut patterns = Vec::new();
        Self::walk(expr, 0, &mut patterns);
        patterns
    }

    fn walk(expr: &VcExpression, depth: usize, patterns: &mut Vec<DetectedPattern>) {
        // Pattern: bounds check — `0 <= x && x < len` or `x >= 0 && x < N`.
        if Self::is_bounds_check(expr) {
            patterns.push(DetectedPattern {
                name: "bounds_check".into(),
                confidence: 0.9,
                location_depth: depth,
                description: "Array/sequence bounds check pattern".into(),
            });
        }

        // Pattern: overflow guard — comparison against min/max constants.
        if Self::is_overflow_guard(expr) {
            patterns.push(DetectedPattern {
                name: "overflow_guard".into(),
                confidence: 0.85,
                location_depth: depth,
                description: "Integer overflow prevention check".into(),
            });
        }

        // Pattern: null/option check — `x != null` or `is_some(x)`.
        if Self::is_null_check(expr) {
            patterns.push(DetectedPattern {
                name: "null_check".into(),
                confidence: 0.8,
                location_depth: depth,
                description: "Null/None/option validity check".into(),
            });
        }

        // Pattern: division safety — divisor != 0.
        if Self::is_division_safety(expr) {
            patterns.push(DetectedPattern {
                name: "division_safety".into(),
                confidence: 0.95,
                location_depth: depth,
                description: "Division-by-zero prevention guard".into(),
            });
        }

        // Pattern: loop invariant — forall with implies and comparison.
        if Self::is_loop_invariant_shape(expr) {
            patterns.push(DetectedPattern {
                name: "loop_invariant".into(),
                confidence: 0.7,
                location_depth: depth,
                description: "Loop invariant preservation shape".into(),
            });
        }

        // Recurse.
        match expr {
            VcExpression::Not(e) => Self::walk(e, depth + 1, patterns),
            VcExpression::And(es) | VcExpression::Or(es) => {
                for e in es {
                    Self::walk(e, depth + 1, patterns);
                }
            }
            VcExpression::Implies(a, b) => {
                Self::walk(a, depth + 1, patterns);
                Self::walk(b, depth + 1, patterns);
            }
            VcExpression::Forall(_, body) | VcExpression::Exists(_, body) => {
                Self::walk(body, depth + 1, patterns);
            }
            VcExpression::Arith(_, es)
            | VcExpression::ArrayOp(_, es)
            | VcExpression::UfApp(_, es) => {
                for e in es {
                    Self::walk(e, depth + 1, patterns);
                }
            }
            VcExpression::BvOp(_, _, es) => {
                for e in es {
                    Self::walk(e, depth + 1, patterns);
                }
            }
            VcExpression::Compare(_, a, b) => {
                Self::walk(a, depth + 1, patterns);
                Self::walk(b, depth + 1, patterns);
            }
            VcExpression::Ite(c, t, e) => {
                Self::walk(c, depth + 1, patterns);
                Self::walk(t, depth + 1, patterns);
                Self::walk(e, depth + 1, patterns);
            }
            _ => {}
        }
    }

    /// Heuristic: `And([Compare(Ge, x, 0), Compare(Lt, x, len)])` shape.
    fn is_bounds_check(expr: &VcExpression) -> bool {
        if let VcExpression::And(conjuncts) = expr {
            if conjuncts.len() == 2 {
                let has_lower = conjuncts.iter().any(|c| {
                    matches!(
                        c,
                        VcExpression::Compare(CompareOp::Ge | CompareOp::Le, _, _)
                    )
                });
                let has_upper = conjuncts.iter().any(|c| {
                    matches!(
                        c,
                        VcExpression::Compare(CompareOp::Lt | CompareOp::Le, _, _)
                    )
                });
                return has_lower && has_upper;
            }
        }
        false
    }

    /// Heuristic: comparison with well-known min/max constants.
    fn is_overflow_guard(expr: &VcExpression) -> bool {
        match expr {
            VcExpression::And(conjuncts) => conjuncts.iter().any(Self::is_overflow_guard),
            VcExpression::Compare(_, a, b) => {
                Self::is_bound_constant(a) || Self::is_bound_constant(b)
            }
            _ => false,
        }
    }

    fn is_bound_constant(expr: &VcExpression) -> bool {
        if let VcExpression::IntConst(v) = expr {
            let abs = v.unsigned_abs();
            // Common boundary values for integer types.
            matches!(
                abs,
                127 | 128
                    | 255
                    | 256
                    | 32767
                    | 32768
                    | 65535
                    | 65536
                    | 2_147_483_647
                    | 2_147_483_648
                    | 4_294_967_295
                    | 4_294_967_296
                    | 9_223_372_036_854_775_807
                    | 9_223_372_036_854_775_808
            )
        } else {
            false
        }
    }

    /// Heuristic: `Compare(Ne, x, null_sentinel)` or UF named `is_some`/`is_none`.
    fn is_null_check(expr: &VcExpression) -> bool {
        match expr {
            VcExpression::UfApp(name, _) => {
                let lower = name.to_lowercase();
                lower.contains("is_some")
                    || lower.contains("is_none")
                    || lower.contains("is_null")
                    || lower.contains("nonnull")
            }
            VcExpression::Compare(CompareOp::Ne, _, b) => {
                matches!(b.as_ref(), VcExpression::IntConst(0))
            }
            _ => false,
        }
    }

    /// Heuristic: `Compare(Ne, divisor, 0)` guard.
    fn is_division_safety(expr: &VcExpression) -> bool {
        if let VcExpression::Implies(antecedent, consequent) = expr {
            // Guard pattern: implies(divisor != 0, ... /divisor ...)
            let guard_ne_zero = matches!(
                antecedent.as_ref(),
                VcExpression::Compare(CompareOp::Ne, _, _)
            );
            let body_has_div = Self::contains_div(consequent);
            return guard_ne_zero && body_has_div;
        }
        // Direct guard: and([divisor != 0, ...])
        if let VcExpression::And(conjuncts) = expr {
            let has_ne_zero = conjuncts.iter().any(|c| {
                matches!(c, VcExpression::Compare(CompareOp::Ne, _, b) if matches!(b.as_ref(), VcExpression::IntConst(0)))
            });
            let has_div = conjuncts.iter().any(Self::contains_div);
            return has_ne_zero && has_div;
        }
        false
    }

    fn contains_div(expr: &VcExpression) -> bool {
        match expr {
            VcExpression::Arith(ArithOp::Div | ArithOp::Mod, _) => true,
            VcExpression::And(es) | VcExpression::Or(es) => es.iter().any(Self::contains_div),
            VcExpression::Not(e) => Self::contains_div(e),
            VcExpression::Implies(a, b) => Self::contains_div(a) || Self::contains_div(b),
            VcExpression::Arith(_, es)
            | VcExpression::ArrayOp(_, es)
            | VcExpression::UfApp(_, es) => es.iter().any(Self::contains_div),
            VcExpression::BvOp(_, _, es) => es.iter().any(Self::contains_div),
            VcExpression::Compare(_, a, b) => Self::contains_div(a) || Self::contains_div(b),
            VcExpression::Forall(_, body) | VcExpression::Exists(_, body) => {
                Self::contains_div(body)
            }
            VcExpression::Ite(c, t, e) => {
                Self::contains_div(c) || Self::contains_div(t) || Self::contains_div(e)
            }
            _ => false,
        }
    }

    /// Heuristic: `Forall(vars, Implies(guard, body))` where guard has comparisons.
    fn is_loop_invariant_shape(expr: &VcExpression) -> bool {
        if let VcExpression::Forall(_, body) = expr {
            if let VcExpression::Implies(guard, _) = body.as_ref() {
                return Self::has_comparison(guard);
            }
        }
        false
    }

    fn has_comparison(expr: &VcExpression) -> bool {
        match expr {
            VcExpression::Compare(..) => true,
            VcExpression::And(es) | VcExpression::Or(es) => es.iter().any(Self::has_comparison),
            VcExpression::Not(e) => Self::has_comparison(e),
            _ => false,
        }
    }
}
