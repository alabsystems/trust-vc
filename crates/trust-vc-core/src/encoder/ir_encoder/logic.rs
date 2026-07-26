//! Logical operator encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Encodes AND, OR, NOT, NEG, and implication with overflow-check
//! guarding for short-circuit and vacuous-truth semantics.

use ay_dpll::api::{Sort, Term};

use crate::encoder::arith_semantics::resolve_expr_wrap;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{LogicOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    /// Encode logical AND/OR with short-circuit semantics via ITE.
    ///
    /// Overflow checks from the right operand are guarded by the left condition
    /// to match Rust's short-circuit evaluation: for `a && b`, overflow checks
    /// from `b` only apply when `a` is true; for `a || b`, only when `a` is false.
    /// Parity: expressions.rs:234-268 (#2107).
    pub(super) fn encode_logic(
        &mut self,
        op: LogicOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let left_term = self.encode_subexpr(left)?;

        match op {
            // a && b => ite(a, b, false)
            LogicOp::And => {
                // Guard overflow checks from right operand: they only apply
                // when left is true (short-circuit). Parity: expressions.rs:240-248.
                let not_left = self.solver.try_not(left_term).map_err(|e| e.to_string())?;
                let right_term =
                    self.encode_with_overflow_guard(not_left, |s| s.encode_trust_vc_expr(right))?;
                let false_term = self.solver.bool_const(false);
                self.solver
                    .try_ite(left_term, right_term, false_term)
                    .map_err(|e| e.to_string().into())
            }
            // a || b => ite(a, true, b)
            LogicOp::Or => {
                // Guard overflow checks from right operand: they only apply
                // when left is false (short-circuit). Parity: expressions.rs:259-265.
                let right_term =
                    self.encode_with_overflow_guard(left_term, |s| s.encode_trust_vc_expr(right))?;
                let true_term = self.solver.bool_const(true);
                self.solver
                    .try_ite(left_term, true_term, right_term)
                    .map_err(|e| e.to_string().into())
            }
        }
    }

    /// Encode logical NOT.
    ///
    /// Uses `term_widths` metadata to decide between bitvector NOT and boolean
    /// NOT. If the inner term has BV width metadata, it is a bitvector and
    /// `try_bvnot` is used with error propagation. Otherwise, boolean `not`
    /// applies. This prevents silent fallback from BV NOT to boolean NOT when
    /// the inner term has an incorrect sort due to upstream encoding bugs.
    /// Fixes #2174.
    pub(super) fn encode_not(&mut self, inner: &TrustVcExpr) -> TrustVcResult<Term> {
        let inner_term = self.encode_subexpr(inner)?;

        if self.int_mode() {
            return self
                .solver
                .try_not(inner_term)
                .map_err(|e| e.to_string().into());
        }

        // Use term_widths to decide: BV terms have width metadata, boolean
        // terms do not. This avoids the silent BV→bool fallback (#2174).
        if let Some(&width_info) = self.term_widths.get(&inner_term) {
            // Inner term is a bitvector — use BV NOT and propagate errors.
            let result = self
                .solver
                .try_bvnot(inner_term)
                .map_err(|e| format!("BV NOT failed on {}-bit operand: {}", width_info.0, e))?;
            self.term_widths.insert(result, width_info);
            Ok(result)
        } else {
            // No BV metadata — boolean NOT.
            self.solver
                .try_not(inner_term)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Encode arithmetic negation.
    ///
    /// In int_mode, uses `resolve_expr_wrap` to derive wrap context from the
    /// inner expression's type (with quantifier scope fallback), matching the
    /// pattern in `encode_int_arith` and `encode_int_checked/saturating`.
    /// Fixes #2179: previously used scope-only wrap context, which wraps to
    /// the quantifier's narrowest bound-var width instead of the expression's
    /// actual type width.
    pub(super) fn encode_neg(&mut self, inner: &TrustVcExpr) -> TrustVcResult<Term> {
        // Int-mode Neg(IntLit) shortcut for out-of-range values: encode as
        // int_const(-value) directly, matching encode_int_lit which also
        // produces int_const(value) without wrapping. Without this,
        // Neg(IntLit(129, Int{8})) computes 0 - 129 = -129, then
        // wrap_int_with_ctx wraps -129 to 127 for Int{8}, which defeats
        // quantifier range guards: exists(|x: i8| x == -129) incorrectly
        // becomes exists(|x: i8| x == 127). (#2570)
        //
        // Only applied when the negated value is OUTSIDE the type's range
        // (where wrapping changes the mathematical value). For in-range
        // values like -1 in Int{32}, wrapping is a no-op but produces
        // different ay term structures that affect solver reasoning.
        if self.int_mode() {
            if let TrustVcExpr::IntLit { value, ty } = inner {
                if let Some(neg_value) = value.checked_neg() {
                    use crate::encoder::quantifiers::integer_range_bounds;
                    let out_of_range = if let Some((lower, upper)) = integer_range_bounds(ty) {
                        let neg_big = num_bigint::BigInt::from(neg_value);
                        neg_big < lower || neg_big >= upper
                    } else {
                        false
                    };
                    if out_of_range {
                        return if let Ok(v) = i64::try_from(neg_value) {
                            Ok(self.solver.int_const(v))
                        } else {
                            Ok(self
                                .solver
                                .int_const_bigint(&num_bigint::BigInt::from(neg_value)))
                        };
                    }
                }
            }
        }

        // BV-mode `Neg(IntLit)` folding (casts-bitvec literal-width soundness).
        //
        // A negative fixed-width literal such as `-128i8` lowers to
        // `Neg(IntLit { value: 128, ty: Int{8} })`. The inner magnitude `128`
        // does NOT fit the SIGNED `i8` range, so encoding it standalone forces
        // the value-preserving widening in `encode_int_lit` (128 -> BV16),
        // which would then negate at BV16 and inflate the width of any
        // surrounding fixed-width arithmetic (`a - 1` would wrap at 16, not 8),
        // breaking `i8::MIN` semantics. Rust specifically allows `-128i8`
        // (= `i8::MIN`) even though `128i8` is out of range.
        //
        // Fold the negation into the literal and encode the NEGATED value at the
        // literal's own type width — but ONLY when that value is REPRESENTABLE
        // in the signed type (no negation overflow). `-128i8` folds to a faithful
        // BV8 `i8::MIN`, keeping surrounding fixed-width arithmetic at width 8.
        //
        // When negating WOULD overflow the type — i.e. `-(i8::MIN)` where the
        // operand is itself `IntLit { value: -128 }` so the negated value `128`
        // does not fit `i8` — DO NOT fold. Falling through to the wrapping
        // `bvneg` path below preserves the two's-complement wrap
        // (`-(-128i8) == -128i8`, not `+128`); folding here would instead encode
        // the mathematical `128` (widened to BV16) and manufacture a false
        // `Verified` on `-(i8::MIN) >= 0`. Likewise a genuinely out-of-range
        // magnitude like `-200i8` (negated value `-200` ∉ i8) falls through and
        // the inner `200` widens value-preservingly under `bvneg`.
        if !self.int_mode() {
            if let TrustVcExpr::IntLit {
                value,
                ty: ty @ TrustVcType::Int { width },
            } = inner
            {
                if let Some(neg_value) = value.checked_neg() {
                    if crate::encoder::types::fits_in_signed_bv(neg_value, *width) {
                        return self.encode_int_lit(neg_value, ty);
                    }
                }
            }
        }

        let inner_term = self.encode_subexpr(inner)?;

        // Hint-based coercions can promote a negated narrow-int literal onto
        // the MathInt bridge (for example native-seq `s.len() > -1i32`) before
        // this encoder sees it. Respect the actual term sort first so we do not
        // call BV negation on an Int/Real term.
        //
        // Guard: only take this path when the IR type is genuinely math-typed.
        // Inside quantifier bodies, fixed-width ints (e.g. i8) are declared as
        // Sort::Int by quantifier_sort_for_type, but still need BV-wrapping
        // semantics through the int_mode path below. Part of #2700, #2703.
        let ir_ty = crate::ir_lowering::infer_expr_type(inner);
        let is_math_typed = matches!(
            ir_ty,
            TrustVcType::MathInt | TrustVcType::Nat | TrustVcType::Real
        );
        match self.solver.term_sort(inner_term) {
            Sort::Int | Sort::Real if is_math_typed => {
                return self
                    .solver
                    .try_neg(inner_term)
                    .map_err(|e| e.to_string().into());
            }
            Sort::FloatingPoint(_, _) => {
                return self
                    .solver
                    .try_fp_neg(inner_term)
                    .map_err(|e| e.to_string().into());
            }
            _ => {}
        }

        // Real/Int negation: try_neg works for Sort::Real and Sort::Int.
        // (ir_ty already computed above for the sort-based guard.)
        if is_math_typed {
            return self
                .solver
                .try_neg(inner_term)
                .map_err(|e| e.to_string().into());
        }
        if matches!(ir_ty, TrustVcType::Float { .. }) {
            return self
                .solver
                .try_fp_neg(inner_term)
                .map_err(|e| e.to_string().into());
        }

        if self.int_mode() {
            let zero = self.solver.int_const(0);
            let result = self
                .solver
                .try_sub(zero, inner_term)
                .map_err(|e| e.to_string())?;
            // Per-expression type > quantifier scope (#2046, #2179).
            // Skip wrapping in pure math-int mode (termination proofs).
            // (ir_ty already computed above for the sort-based guard.)
            let scope_sem = self.current_quantifier_wrap_semantics();
            let wrap_ctx = if self.use_int_arithmetic {
                None
            } else {
                resolve_expr_wrap(&ir_ty, scope_sem)
            };
            let wrapped = self.wrap_int_with_ctx(result, wrap_ctx)?;
            // #2108: emit overflow check for negation in int_mode.
            // For signed types, -MIN overflows (e.g., -(-128) = 128 not in i8).
            // Guard: only collect at quantifier_depth==0 (#2557 — same as arith add/sub/mul).
            if self.overflow_behavior.should_check()
                && wrap_ctx.is_some()
                && self.quantifier_depth == 0
            {
                if let Some(no_overflow) = self.int_result_in_wrap_range_ctx(result, wrap_ctx)? {
                    self.overflow_checks
                        .push(("negation overflow".into(), no_overflow));
                }
            }
            return Ok(wrapped);
        }

        let result = self
            .solver
            .try_bvneg(inner_term)
            .map_err(|e| e.to_string())?;
        if let Some(&width_info) = self.term_widths.get(&inner_term) {
            self.term_widths.insert(result, width_info);
        }
        if self.overflow_behavior.should_check()
            && self.quantifier_depth == 0
            && !self.try_record_const_fold_neg_overflow(inner)
        {
            let no_overflow = self
                .solver
                .try_bvneg_no_overflow(inner_term)
                .map_err(|e| format!("Failed to create negation overflow check: {}", e))?;
            self.overflow_checks
                .push(("negation overflow".into(), no_overflow));
        }
        Ok(result)
    }

    /// Encode logical implication: premise ==> conclusion.
    pub(super) fn encode_implies(
        &mut self,
        premise: &TrustVcExpr,
        conclusion: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        let p = self.encode_subexpr(premise)?;

        // `p ==> c` is vacuously true when `p` is false, so overflow checks
        // emitted while encoding `c` must only apply under `p`: ¬p ∨ check.
        let not_p = self.solver.try_not(p).map_err(|e| e.to_string())?;
        let c = self.encode_with_overflow_guard(not_p, |s| s.encode_trust_vc_expr(conclusion))?;

        self.solver
            .try_implies(p, c)
            .map_err(|e| e.to_string().into())
    }
}
