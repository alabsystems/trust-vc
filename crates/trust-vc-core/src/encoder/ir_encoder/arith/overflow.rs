//! BV arithmetic overflow checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{ArithOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    /// Try to discharge an arithmetic-overflow obligation by constant folding.
    ///
    /// When `left`/`right` are all-constant operands of a known finite-width
    /// result type, this evaluates the overflow obligation exactly and records a
    /// definite verdict on the `const_fold_overflow_verdicts` side-channel,
    /// returning `true` so the caller skips the symbolic
    /// `bvadd_no_overflow`-style predicate. Returns `false` when the operation
    /// is not all-constant (or the result type is not finite-width), in which
    /// case the caller must emit the usual symbolic check.
    ///
    /// Soundness: a definite-overflow verdict (`overflows == true`) becomes a
    /// counterexample; a definite-safe verdict is dropped (no obligation). The
    /// exact fixed-width semantics live in
    /// `AYEncoder::try_const_fold_arith_overflow`. Non-constant operands are
    /// never folded, so results for symbolic arithmetic are unchanged (#2778).
    pub(super) fn try_record_const_fold_overflow(
        &mut self,
        op: ArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        result_ty: &TrustVcType,
        label: &str,
    ) -> bool {
        let Some(verdict) =
            crate::encoder::AYEncoder::try_const_fold_arith_overflow(op, left, right, result_ty)
        else {
            return false;
        };
        if verdict.overflows {
            self.const_fold_overflow_verdicts
                .push((format!("{} overflow", label).into(), true));
        }
        // A definite-safe verdict needs no recorded obligation: the operation
        // provably does not overflow, so there is nothing left to refute.
        true
    }

    /// Try to discharge a negation-overflow obligation by constant folding.
    ///
    /// `-x` overflows a fixed-width signed type only at `x == TYPE::MIN`
    /// (e.g. `-(i8::MIN)` is `128`, outside `i8`). When `inner` is a constant of
    /// a finite-width type, this evaluates that exactly and records a definite
    /// verdict, returning `true` so the caller skips the symbolic
    /// `bvneg_no_overflow` check. Returns `false` for non-constant operands.
    pub(in crate::encoder::ir_encoder) fn try_record_const_fold_neg_overflow(
        &mut self,
        inner: &TrustVcExpr,
    ) -> bool {
        let Some(value) = crate::encoder::AYEncoder::try_reduce_to_int(inner) else {
            return false;
        };
        let inner_ty = crate::ir_lowering::infer_expr_type(inner);
        match inner_ty {
            TrustVcType::Int { .. } | TrustVcType::Uint { .. } => {}
            _ => return false,
        }
        // Exact negation; if it cannot be represented in i128 (impossible here
        // for widths <= 128 given the operand fits i128) defer to the solver.
        let Some(negated) = value.checked_neg() else {
            return false;
        };
        if !crate::encoder::AYEncoder::value_fits_in_type(negated, &inner_ty) {
            self.const_fold_overflow_verdicts
                .push(("negation overflow".into(), true));
        }
        true
    }

    /// Emit division/remainder by zero overflow check predicate.
    pub(super) fn add_div_by_zero_check(&mut self, divisor: Term, width: u32) -> TrustVcResult<()> {
        let zero = self
            .solver
            .try_bv_const(0, width)
            .map_err(|e| e.to_string())?;
        let eq_zero = self
            .solver
            .try_eq(divisor, zero)
            .map_err(|e| e.to_string())?;
        let not_zero = self.solver.try_not(eq_zero).map_err(|e| e.to_string())?;
        self.overflow_checks
            .push(("division by zero".into(), not_zero));
        Ok(())
    }

    /// BV addition/subtraction overflow check.
    pub(super) fn add_bv_arith_overflow_check(
        &mut self,
        left: Term,
        right: Term,
        unsigned: bool,
        label: &str,
        is_add: bool,
    ) -> TrustVcResult<()> {
        let no_overflow = if is_add {
            if unsigned {
                self.solver
                    .try_bvadd_no_overflow(left, right, false)
                    .map_err(|e| format!("Failed to create {} overflow check: {}", label, e))?
            } else {
                let no_of = self
                    .solver
                    .try_bvadd_no_overflow(left, right, true)
                    .map_err(|e| format!("Failed to create {} overflow check: {}", label, e))?;
                let no_uf = self
                    .solver
                    .try_bvadd_no_underflow(left, right)
                    .map_err(|e| format!("Failed to create {} underflow check: {}", label, e))?;
                self.solver
                    .try_and(no_of, no_uf)
                    .map_err(|e| e.to_string())?
            }
        } else {
            // Subtraction
            if unsigned {
                self.solver
                    .try_bvsub_no_underflow(left, right, false)
                    .map_err(|e| format!("Failed to create {} underflow check: {}", label, e))?
            } else {
                let no_of = self
                    .solver
                    .try_bvsub_no_overflow(left, right)
                    .map_err(|e| format!("Failed to create {} overflow check: {}", label, e))?;
                let no_uf = self
                    .solver
                    .try_bvsub_no_underflow(left, right, true)
                    .map_err(|e| format!("Failed to create {} underflow check: {}", label, e))?;
                self.solver
                    .try_and(no_of, no_uf)
                    .map_err(|e| e.to_string())?
            }
        };
        self.overflow_checks
            .push((format!("{} overflow", label).into(), no_overflow));
        Ok(())
    }

    /// BV multiplication overflow check.
    pub(super) fn add_bv_mul_overflow_check(
        &mut self,
        left: Term,
        right: Term,
        unsigned: bool,
    ) -> TrustVcResult<()> {
        let no_overflow = if unsigned {
            self.solver
                .try_bvmul_no_overflow(left, right, false)
                .map_err(|e| format!("Failed to create multiplication overflow check: {}", e))?
        } else {
            let no_of = self
                .solver
                .try_bvmul_no_overflow(left, right, true)
                .map_err(|e| format!("Failed to create multiplication overflow check: {}", e))?;
            let no_uf = self
                .solver
                .try_bvmul_no_underflow(left, right)
                .map_err(|e| format!("Failed to create multiplication underflow check: {}", e))?;
            self.solver
                .try_and(no_of, no_uf)
                .map_err(|e| e.to_string())?
        };
        self.overflow_checks
            .push(("multiplication overflow".into(), no_overflow));
        Ok(())
    }
}
