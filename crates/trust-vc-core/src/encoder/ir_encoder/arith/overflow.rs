//! BV arithmetic overflow checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Solver, SolverError, Sort, Term};

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{ArithOp, TrustVcExpr, TrustVcType};

/// Exact two's-complement safety predicate for signed subtraction.
///
/// Signed `left - right` overflows exactly when the operands have different
/// sign bits and the wrapped result's sign differs from `left`.  Encoding that
/// criterion directly is equivalent to ay's separate `no_overflow` and
/// `no_underflow` predicates, but avoids expanding subtraction through
/// `left + (-right)`.  The expanded form makes wide source-certificate replay
/// needlessly enormous even when an operand-sign premise decides the query.
fn compact_signed_bvsub_no_overflow(
    solver: &mut Solver,
    left: Term,
    right: Term,
) -> Result<Term, SolverError> {
    // `try_bvsub` authenticates both handles and requires equal BV widths;
    // deriving the width from its result keeps casts/coercions exact rather
    // than trusting the IR's pre-coercion type metadata.
    let result = solver.try_bvsub(left, right)?;
    let width = match solver.term_sort(result) {
        Sort::BitVec(sort) => sort.width,
        other => {
            return Err(SolverError::SortMismatch {
                operation: "signed_bvsub_no_overflow",
                expected: "BitVec",
                got: vec![other],
            });
        }
    };
    if width == 0 {
        return Err(SolverError::InvalidArgument {
            operation: "signed_bvsub_no_overflow",
            message: "bitvector width (0) must be > 0".to_string(),
        });
    }

    let sign_bit = width - 1;
    let left_sign = solver.try_bvextract(left, sign_bit, sign_bit)?;
    let right_sign = solver.try_bvextract(right, sign_bit, sign_bit)?;
    let result_sign = solver.try_bvextract(result, sign_bit, sign_bit)?;
    let operands_have_same_sign = solver.try_eq(left_sign, right_sign)?;
    let result_keeps_left_sign = solver.try_eq(result_sign, left_sign)?;
    solver.try_or(operands_have_same_sign, result_keeps_left_sign)
}

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
                compact_signed_bvsub_no_overflow(self.solver, left, right)
                    .map_err(|e| format!("Failed to create {label} overflow check: {e}"))?
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

#[cfg(test)]
mod tests {
    use super::*;
    use ay_dpll::api::Logic;

    #[test]
    fn compact_signed_subtraction_predicate_matches_ay_builtins() {
        const WIDTH: u32 = 4;
        let mut solver = Solver::new(Logic::QfBv);
        solver.set_timeout(Some(std::time::Duration::from_secs(5)));
        solver.set_produce_unsat_cores(true);
        let left = solver.declare_const("compact_sub_left", Sort::bitvec(WIDTH));
        let right = solver.declare_const("compact_sub_right", Sort::bitvec(WIDTH));

        let compact = compact_signed_bvsub_no_overflow(&mut solver, left, right)
            .expect("compact signed-subtraction predicate should encode");
        let no_overflow = solver
            .try_bvsub_no_overflow(left, right)
            .expect("ay signed overflow predicate should encode");
        let no_underflow = solver
            .try_bvsub_no_underflow(left, right, true)
            .expect("ay signed underflow predicate should encode");
        let expanded = solver
            .try_and(no_overflow, no_underflow)
            .expect("combine ay signed-subtraction predicates");
        let equivalent = solver
            .try_eq(compact, expanded)
            .expect("compare compact and expanded predicates");
        let counterexample = solver
            .try_not(equivalent)
            .expect("negate predicate equivalence");
        solver
            .try_assert_named(counterexample, "compact_sub_equivalence_counterexample")
            .expect("assert predicate-equivalence counterexample");

        let result = solver.check_sat();
        assert!(
            result.is_unsat(),
            "the compact criterion must match ay for every BV4 input, got {result:?}"
        );
    }
}
