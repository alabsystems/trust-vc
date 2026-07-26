//! Seq no-duplicates encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term};

use super::super::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    /// Encode Seq::no_duplicates() as an Int-indexed universal formula.
    pub(in crate::encoder) fn encode_seq_no_duplicates(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in no_duplicates()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let pw = crate::ir::pointer_width();
        // Route A (#2779): length is Int directly; bridge to BV for the
        // BV-indexed ground seeds below.
        let len_int = if self.len_is_int(len) {
            len
        } else {
            self.solver.try_bv2int(len).map_err(|e| e.to_string())?
        };
        let len_bv = self.len_as_index_bv(len)?;
        let i = self.solver.fresh_var("__seq_no_dup_i", Sort::Int);
        let j = self.solver.fresh_var("__seq_no_dup_j", Sort::Int);
        let zero = self.solver.int_const(0);
        let i_nonneg = self.solver.try_ge(i, zero).map_err(|e| e.to_string())?;
        let i_lt_j = self.solver.try_lt(i, j).map_err(|e| e.to_string())?;
        let j_lt_len = self.solver.try_lt(j, len_int).map_err(|e| e.to_string())?;
        let range = self
            .solver
            .try_and(i_nonneg, i_lt_j)
            .and_then(|lhs| self.solver.try_and(lhs, j_lt_len))
            .map_err(|e| e.to_string())?;
        let i_bv = self.solver.try_int2bv(i, pw).map_err(|e| e.to_string())?;
        let j_bv = self.solver.try_int2bv(j, pw).map_err(|e| e.to_string())?;
        let left = self
            .solver
            .try_select(receiver, i_bv)
            .map_err(|e| e.to_string())?;
        let right = self
            .solver
            .try_select(receiver, j_bv)
            .map_err(|e| e.to_string())?;
        let left = self.coerce_element_for_int_mode(left, receiver, receiver_name)?;
        let right = self.coerce_element_for_int_mode(right, receiver, receiver_name)?;
        let distinct = self
            .solver
            .try_eq(left, right)
            .and_then(|eq| self.solver.try_not(eq))
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_implies(range, distinct)
            .map_err(|e| e.to_string())?;
        let universal = self
            .solver
            .try_forall(&[i, j], body)
            .map_err(|e| e.to_string())?;
        let mut seeded = self.solver.bool_const(true);
        for i_seed in 0i64..4 {
            for j_seed in (i_seed + 1)..4 {
                let i_bv = self
                    .solver
                    .try_bv_const(i_seed, pw)
                    .map_err(|e| e.to_string())?;
                let j_bv = self
                    .solver
                    .try_bv_const(j_seed, pw)
                    .map_err(|e| e.to_string())?;
                let i_in_range = self
                    .solver
                    .try_bvult(i_bv, len_bv)
                    .map_err(|e| e.to_string())?;
                let j_in_range = self
                    .solver
                    .try_bvult(j_bv, len_bv)
                    .map_err(|e| e.to_string())?;
                let range = self
                    .solver
                    .try_and(i_in_range, j_in_range)
                    .map_err(|e| e.to_string())?;
                let left = self
                    .solver
                    .try_select(receiver, i_bv)
                    .map_err(|e| e.to_string())?;
                let right = self
                    .solver
                    .try_select(receiver, j_bv)
                    .map_err(|e| e.to_string())?;
                let left = self.coerce_element_for_int_mode(left, receiver, receiver_name)?;
                let right = self.coerce_element_for_int_mode(right, receiver, receiver_name)?;
                let distinct = self
                    .solver
                    .try_eq(left, right)
                    .and_then(|eq| self.solver.try_not(eq))
                    .map_err(|e| e.to_string())?;
                let inst = self
                    .solver
                    .try_implies(range, distinct)
                    .map_err(|e| e.to_string())?;
                seeded = self
                    .solver
                    .try_and(seeded, inst)
                    .map_err(|e| e.to_string())?;
            }
        }

        // `len < 5` is a length comparison (Int under Route A #2779).
        let five = self.len_const_like(len, 5)?;
        let small_len = self.len_lt(len, five)?;
        let large_len = self.solver.try_not(small_len).map_err(|e| e.to_string())?;
        let result = self.solver.fresh_var("__seq_no_duplicates", Sort::Bool);
        let result_is_seeded = self
            .solver
            .try_eq(result, seeded)
            .map_err(|e| e.to_string())?;
        let result_small = self
            .solver
            .try_implies(small_len, result_is_seeded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(result_small)
            .map_err(|e| e.to_string())?;
        let result_is_universal = self
            .solver
            .try_eq(result, universal)
            .map_err(|e| e.to_string())?;
        let result_large = self
            .solver
            .try_implies(large_len, result_is_universal)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(result_large)
            .map_err(|e| e.to_string())?;
        Ok(result)
    }
}
