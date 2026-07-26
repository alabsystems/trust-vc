//! Helper methods on `TrustVcExpr` — containment checks and tree operations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `ir_expr.rs` for the 500-line limit (#2621).

use crate::ir::{LogicOp, MatchArm, QuantifierKind, SpecialArithOp, TrustVcExpr, WrappingMode};
use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

impl TrustVcExpr {
    /// Returns `true` only when this tree is definitely free of runtime
    /// variables for the BV-compare constant-folding guard.
    ///
    /// This is intentionally conservative: any unclassified variant returns
    /// `false` so the caller does not incorrectly treat a complex expression as
    /// a constant-only tree after equality-assumption substitution.
    #[must_use]
    pub(crate) fn is_definitely_var_free_for_bv_compare(&self) -> bool {
        match self {
            TrustVcExpr::UnitLit
            | TrustVcExpr::BoolLit(_)
            | TrustVcExpr::IntLit { .. }
            | TrustVcExpr::IntConst { .. } => true,
            TrustVcExpr::Var { .. } => false,
            TrustVcExpr::Arith { left, right, .. }
            | TrustVcExpr::Compare { left, right, .. }
            | TrustVcExpr::Logic { left, right, .. }
            | TrustVcExpr::WrappingArith { left, right, .. }
            | TrustVcExpr::SpecialArith { left, right, .. } => {
                left.is_definitely_var_free_for_bv_compare()
                    && right.is_definitely_var_free_for_bv_compare()
            }
            TrustVcExpr::Neg(inner)
            | TrustVcExpr::Not(inner)
            | TrustVcExpr::Cast { expr: inner, .. } => {
                inner.is_definitely_var_free_for_bv_compare()
            }
            TrustVcExpr::Implies {
                premise,
                conclusion,
            } => {
                premise.is_definitely_var_free_for_bv_compare()
                    && conclusion.is_definitely_var_free_for_bv_compare()
            }
            TrustVcExpr::Ite {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                cond.is_definitely_var_free_for_bv_compare()
                    && then_branch.is_definitely_var_free_for_bv_compare()
                    && else_branch.is_definitely_var_free_for_bv_compare()
            }
            _ => false,
        }
    }

    /// Returns `true` if this expression or any sub-expression is a quantifier.
    /// Used by the empty-model guard to distinguish ground formulas (where an
    /// empty model on SAT is a legitimate counterexample) from quantified
    /// formulas (where empty model indicates a CEGQI limitation, #2067).
    #[must_use]
    pub fn contains_quantifier(&self) -> bool {
        struct V {
            found: bool,
        }
        impl TrustVcExprVisitor for V {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if self.found {
                    return;
                }
                if matches!(expr, TrustVcExpr::Quantifier { .. }) {
                    self.found = true;
                } else {
                    walk_expr(self, expr);
                }
            }
            fn visit_match_arm(&mut self, arm: &MatchArm) {
                if let Some(guard) = &arm.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&arm.body);
            }
        }
        let mut v = V { found: false };
        v.visit_expr(self);
        v.found
    }

    /// Returns `true` if this expression or any sub-expression is a `forall`
    /// quantifier.
    ///
    /// Used by the existential-refutation router: refuting `exists v. BODY` via
    /// the structural default `not(encode(exists v. BODY))` hands the solver the
    /// alternating negation `forall v. exists … ¬…` whenever BODY contains a
    /// (positive-polarity) `forall`. ay's incomplete CEGQI decides that
    /// alternation UNSOUNDLY (spurious UNSAT -> false-Verified, round8 finding
    /// 17), so such an existential is rerouted to the exact structural negation
    /// instead (`encode_exists_nested_forall_refutation`). An inner `exists`
    /// (no `forall`) negates to a sound `forall`-only goal and stays on the
    /// existing path, so this is scoped to `forall` specifically.
    #[must_use]
    pub fn contains_forall_quantifier(&self) -> bool {
        struct V {
            found: bool,
        }
        impl TrustVcExprVisitor for V {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if self.found {
                    return;
                }
                if matches!(
                    expr,
                    TrustVcExpr::Quantifier {
                        kind: QuantifierKind::Forall,
                        ..
                    }
                ) {
                    self.found = true;
                } else {
                    walk_expr(self, expr);
                }
            }
            fn visit_match_arm(&mut self, arm: &MatchArm) {
                if let Some(guard) = &arm.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&arm.body);
            }
        }
        let mut v = V { found: false };
        v.visit_expr(self);
        v.found
    }

    /// Returns `true` if this expression contains a quantifier that was NOT
    /// Skolemized by the encoder (triggered forall, or exists).
    ///
    /// Trigger-less forall quantifiers are Skolemized at the encoder level
    /// (#2187): their bound variables become fresh unconstrained constants and
    /// the guarded body is asserted as a ground formula. These don't need the
    /// empty-model CEGQI guard because ay can solve the ground formula directly.
    #[must_use]
    pub fn has_non_skolemized_quantifier(&self) -> bool {
        struct V {
            found: bool,
        }
        impl TrustVcExprVisitor for V {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if self.found {
                    return;
                }
                match expr {
                    TrustVcExpr::Quantifier { kind, triggers, .. } => {
                        match kind {
                            QuantifierKind::Forall => {
                                if triggers.as_ref().is_some_and(|t| !t.is_empty()) {
                                    self.found = true;
                                }
                            }
                            QuantifierKind::Exists => {
                                self.found = true;
                            }
                        }
                        // Don't recurse into children — matches current behavior.
                    }
                    _ => walk_expr(self, expr),
                }
            }
            fn visit_match_arm(&mut self, arm: &MatchArm) {
                if let Some(guard) = &arm.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&arm.body);
            }
        }
        let mut v = V { found: false };
        v.visit_expr(self);
        v.found
    }

    /// Returns `true` if this expression references a collection operation
    /// (`CollectionOp`) or collection indexing (`Index`).
    ///
    /// Used to preserve the collection-specific BV path before trigger
    /// inference runs. Trigger-less assertion `forall` can also use BV-sorted
    /// Skolemization once the encoder determines the quantifier will stay
    /// ground, but collection bodies need the decision earlier (#2461, #2669).
    #[must_use]
    pub fn references_collection(&self) -> bool {
        struct V {
            found: bool,
        }
        impl TrustVcExprVisitor for V {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if self.found {
                    return;
                }
                match expr {
                    TrustVcExpr::CollectionOp { .. } | TrustVcExpr::Index { .. } => {
                        self.found = true;
                    }
                    TrustVcExpr::Var { ty, .. } => {
                        if ty.is_collection() {
                            self.found = true;
                        }
                    }
                    TrustVcExpr::FnCall {
                        return_ty, args, ..
                    } => {
                        if return_ty.is_collection() {
                            self.found = true;
                            return;
                        }
                        for arg in args {
                            self.visit_expr(arg);
                            if self.found {
                                return;
                            }
                        }
                    }
                    TrustVcExpr::SpecClosure { body, .. } => {
                        self.visit_expr(body);
                    }
                    // Recurse into body only, not triggers (preserves current semantics).
                    TrustVcExpr::Quantifier { body, .. } => {
                        self.visit_expr(body);
                    }
                    _ => walk_expr(self, expr),
                }
            }
            fn visit_match_arm(&mut self, arm: &MatchArm) {
                if let Some(guard) = &arm.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&arm.body);
            }
        }
        let mut v = V { found: false };
        v.visit_expr(self);
        v.found
    }

    /// Returns `true` if encoding this expression may emit auxiliary
    /// `overflow_checks` side-channel predicates.
    ///
    /// This is a conservative precheck used to avoid building a dedicated
    /// overflow-precheck encoder for assertions like `x == x` that cannot
    /// produce any overflow, shift-bound, division-by-zero, or
    /// collection-bounds predicates. False negatives would be unsound, so this
    /// intentionally over-approximates.
    ///
    /// Note that *partiality* safety predicates — division/remainder
    /// (`div0_behavior`), shift bounds (`bitshift_behavior`), and
    /// collection/index bounds — are gated by behaviors that are independent of
    /// the arithmetic-overflow `check_overflow` flag, so this precheck reports
    /// them unconditionally (the cheap actual encoder then decides whether to
    /// emit an obligation based on the live behavior). Only additive/mul/neg
    /// overflow is gated by `check_overflow`.
    #[must_use]
    pub fn may_emit_overflow_checks(&self, check_overflow: bool) -> bool {
        struct V {
            check_overflow: bool,
            quantifier_depth: usize,
            found: bool,
        }
        impl TrustVcExprVisitor for V {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if self.found {
                    return;
                }
                match expr {
                    // Division and remainder carry a *partiality* (division-by-
                    // zero, and signed MIN/-1) safety obligation that is gated by
                    // `div0_behavior`, NOT by arithmetic-overflow checking. In
                    // BitVector mode (`assert by(bit_vector)`) overflow checks are
                    // disabled (`check_overflow == false`) but div-by-zero must
                    // still fail closed, so the precheck has to over-approximate
                    // here exactly as it already does for shifts below. Gating
                    // Div/Rem on `check_overflow` was a soundness hole: a BV-mode
                    // `x / y == x / y` skipped the `y != 0` obligation and verified
                    // unsoundly. (#div0-bv-precheck)
                    TrustVcExpr::Arith {
                        op: crate::ir::ArithOp::Div | crate::ir::ArithOp::Rem,
                        ..
                    } => {
                        if self.quantifier_depth == 0 {
                            self.found = true;
                        } else {
                            walk_expr(self, expr);
                        }
                    }
                    TrustVcExpr::Arith { .. } | TrustVcExpr::Neg(_) => {
                        if self.check_overflow && self.quantifier_depth == 0 {
                            self.found = true;
                        } else {
                            walk_expr(self, expr);
                        }
                    }
                    TrustVcExpr::CollectionOp { .. } | TrustVcExpr::Index { .. } => {
                        self.found = true;
                    }
                    TrustVcExpr::SpecialArith { op, .. } => {
                        if matches!(op, SpecialArithOp::Shl | SpecialArithOp::Shr)
                            && self.quantifier_depth == 0
                        {
                            self.found = true;
                        } else {
                            walk_expr(self, expr);
                        }
                    }
                    TrustVcExpr::WrappingArith { mode, .. } => {
                        if matches!(mode, WrappingMode::Checked) && self.quantifier_depth == 0 {
                            self.found = true;
                        } else {
                            walk_expr(self, expr);
                        }
                    }
                    // Recurse into body only, not triggers. Arithmetic overflow
                    // side-channel predicates are emitted only outside
                    // quantifier bodies; collection/index predicates are still
                    // discovered by the recursive body visit.
                    TrustVcExpr::Quantifier { body, .. } => {
                        self.quantifier_depth += 1;
                        self.visit_expr(body);
                        self.quantifier_depth -= 1;
                    }
                    _ => walk_expr(self, expr),
                }
            }
            fn visit_match_arm(&mut self, arm: &MatchArm) {
                if let Some(guard) = &arm.guard {
                    self.visit_expr(guard);
                }
                self.visit_expr(&arm.body);
            }
        }
        let mut v = V {
            check_overflow,
            quantifier_depth: 0,
            found: false,
        };
        v.visit_expr(self);
        v.found
    }

    /// Recursively collect the leaf conjuncts of a conjunction tree.
    ///
    /// `a && b && c` (represented as `And(And(a, b), c)`) returns `[a, b, c]`.
    /// Non-conjunction expressions return a single-element vec containing self.
    /// Part of #2485.
    #[must_use]
    pub fn collect_conjuncts(&self) -> Vec<&TrustVcExpr> {
        match self {
            TrustVcExpr::Logic {
                op: LogicOp::And,
                left,
                right,
            } => {
                let mut parts = left.collect_conjuncts();
                parts.extend(right.collect_conjuncts());
                parts
            }
            _ => vec![self],
        }
    }
}
