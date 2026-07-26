// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Saturating BV arithmetic clamping for TrustVcExpr IR.
//!
//! Extracted from wrapping.rs to stay within the 500-line file limit.
//! Contains the BV-mode saturating clamp logic (`clamp_to_bounds`,
//! `clamp_unsigned`, `clamp_signed`). The Int-mode saturating path
//! remains in wrapping.rs.

use ay_dpll::api::Term;

use crate::ir::ArithOp;

use super::wrapping::{signed_bounds, unsigned_max};
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    /// Clamp a BV arithmetic result to bounds on overflow (saturating semantics).
    pub(super) fn clamp_to_bounds(
        &mut self,
        result: Term,
        left: Term,
        right: Term,
        width: u32,
        unsigned: bool,
        op: ArithOp,
    ) -> TrustVcResult<Term> {
        if unsigned {
            self.clamp_unsigned(result, left, right, width, op)
        } else {
            self.clamp_signed(result, left, right, width, op)
        }
    }

    /// Unsigned saturating clamp: clamp to [0, MAX].
    fn clamp_unsigned(
        &mut self,
        result: Term,
        left: Term,
        right: Term,
        width: u32,
        op: ArithOp,
    ) -> TrustVcResult<Term> {
        let max_bigint = unsigned_max(width);
        let max_term = if let Ok(v) = i64::try_from(&max_bigint) {
            self.solver
                .try_bv_const(v, width)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bv_const_bigint(&max_bigint, width)
                .map_err(|e| e.to_string())?
        };
        let zero = self
            .solver
            .try_bv_const(0, width)
            .map_err(|e| e.to_string())?;

        match op {
            ArithOp::Add => {
                let overflowed = self
                    .solver
                    .try_bvult(result, left)
                    .map_err(|e| e.to_string())?;
                Ok(self
                    .solver
                    .try_ite(overflowed, max_term, result)
                    .map_err(|e| e.to_string())?)
            }
            ArithOp::Sub => {
                let overflowed = self
                    .solver
                    .try_bvugt(result, left)
                    .map_err(|e| e.to_string())?;
                Ok(self
                    .solver
                    .try_ite(overflowed, zero, result)
                    .map_err(|e| e.to_string())?)
            }
            ArithOp::Mul => {
                // Parity with methods.rs saturating_mul: clamp unsigned overflow to MAX.
                let no_overflow = self
                    .solver
                    .try_bvmul_no_overflow(left, right, false)
                    .map_err(|e| e.to_string())?;
                Ok(self
                    .solver
                    .try_ite(no_overflow, result, max_term)
                    .map_err(|e| e.to_string())?)
            }
            ArithOp::Div | ArithOp::Rem => Ok(result), // cannot overflow unsigned
        }
    }

    /// Signed saturating clamp: clamp to [MIN, MAX].
    fn clamp_signed(
        &mut self,
        result: Term,
        left: Term,
        right: Term,
        width: u32,
        op: ArithOp,
    ) -> TrustVcResult<Term> {
        let (min_bigint, max_bigint) = signed_bounds(width);
        let min_term = if let Ok(v) = i64::try_from(&min_bigint) {
            self.solver
                .try_bv_const(v, width)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bv_const_bigint(&min_bigint, width)
                .map_err(|e| e.to_string())?
        };
        let max_term = if let Ok(v) = i64::try_from(&max_bigint) {
            self.solver
                .try_bv_const(v, width)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bv_const_bigint(&max_bigint, width)
                .map_err(|e| e.to_string())?
        };
        let zero = self
            .solver
            .try_bv_const(0, width)
            .map_err(|e| e.to_string())?;

        match op {
            ArithOp::Add => {
                let left_pos = self
                    .solver
                    .try_bvsge(left, zero)
                    .map_err(|e| e.to_string())?;
                let right_pos = self
                    .solver
                    .try_bvsge(right, zero)
                    .map_err(|e| e.to_string())?;
                let result_neg = self
                    .solver
                    .try_bvslt(result, zero)
                    .map_err(|e| e.to_string())?;
                let both_pos = self
                    .solver
                    .try_and(left_pos, right_pos)
                    .map_err(|e| e.to_string())?;
                let pos_overflow = self
                    .solver
                    .try_and(both_pos, result_neg)
                    .map_err(|e| e.to_string())?;

                let left_neg = self.solver.try_not(left_pos).map_err(|e| e.to_string())?;
                let right_neg = self.solver.try_not(right_pos).map_err(|e| e.to_string())?;
                let result_pos = self.solver.try_not(result_neg).map_err(|e| e.to_string())?;
                let both_neg = self
                    .solver
                    .try_and(left_neg, right_neg)
                    .map_err(|e| e.to_string())?;
                let neg_overflow = self
                    .solver
                    .try_and(both_neg, result_pos)
                    .map_err(|e| e.to_string())?;

                let clamped = self
                    .solver
                    .try_ite(pos_overflow, max_term, result)
                    .map_err(|e| e.to_string())?;
                let clamped = self
                    .solver
                    .try_ite(neg_overflow, min_term, clamped)
                    .map_err(|e| e.to_string())?;
                Ok(clamped)
            }
            ArithOp::Sub => {
                let left_pos = self
                    .solver
                    .try_bvsge(left, zero)
                    .map_err(|e| e.to_string())?;
                let right_neg = self
                    .solver
                    .try_bvslt(right, zero)
                    .map_err(|e| e.to_string())?;
                let result_neg = self
                    .solver
                    .try_bvslt(result, zero)
                    .map_err(|e| e.to_string())?;
                let pos_and_neg = self
                    .solver
                    .try_and(left_pos, right_neg)
                    .map_err(|e| e.to_string())?;
                let pos_overflow = self
                    .solver
                    .try_and(pos_and_neg, result_neg)
                    .map_err(|e| e.to_string())?;

                let left_neg = self.solver.try_not(left_pos).map_err(|e| e.to_string())?;
                let right_pos = self.solver.try_not(right_neg).map_err(|e| e.to_string())?;
                let result_pos = self.solver.try_not(result_neg).map_err(|e| e.to_string())?;
                let neg_and_pos = self
                    .solver
                    .try_and(left_neg, right_pos)
                    .map_err(|e| e.to_string())?;
                let neg_overflow = self
                    .solver
                    .try_and(neg_and_pos, result_pos)
                    .map_err(|e| e.to_string())?;

                let clamped = self
                    .solver
                    .try_ite(pos_overflow, max_term, result)
                    .map_err(|e| e.to_string())?;
                let clamped = self
                    .solver
                    .try_ite(neg_overflow, min_term, clamped)
                    .map_err(|e| e.to_string())?;
                Ok(clamped)
            }
            ArithOp::Mul => {
                // Parity with methods.rs saturating_mul: signed overflow clamps to MAX,
                // signed underflow clamps to MIN.
                let no_overflow = self
                    .solver
                    .try_bvmul_no_overflow(left, right, true)
                    .map_err(|e| e.to_string())?;
                let no_underflow = self
                    .solver
                    .try_bvmul_no_underflow(left, right)
                    .map_err(|e| e.to_string())?;
                let no_problem = self
                    .solver
                    .try_and(no_overflow, no_underflow)
                    .map_err(|e| e.to_string())?;
                let on_overflow = self
                    .solver
                    .try_ite(no_overflow, min_term, max_term)
                    .map_err(|e| e.to_string())?;
                Ok(self
                    .solver
                    .try_ite(no_problem, result, on_overflow)
                    .map_err(|e| e.to_string())?)
            }
            ArithOp::Div | ArithOp::Rem => Ok(result), // MIN/-1 handled by checked_div
        }
    }
}
