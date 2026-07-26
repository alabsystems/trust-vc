//! Array axiom helpers for Seq encoding robustness (#1979).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from parser_state.rs to keep file sizes under limit.

use ay_dpll::api::{Sort, Term};

use super::parser_state::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    /// Assert explicit element-preservation axiom for store-based Seq operations (#1979).
    ///
    /// `forall i: BV(pw). bvult(i, old_len) => select(result, i) == select(source, i)`
    ///
    /// This makes push encoding robust against ay model validation changes
    /// that may not fully instantiate the built-in read-over-write for BV(pw) indices.
    pub(super) fn assert_store_preservation(
        &mut self,
        result: Term,
        source: Term,
        old_len64: Term,
        label: &str,
    ) -> TrustVcResult<()> {
        let bound = self.solver.fresh_var(
            &format!("__{}_idx", label),
            Sort::bitvec(crate::ir::pointer_width()),
        );
        let res_elem = self
            .solver
            .try_select(result, bound)
            .map_err(|e| e.to_string())?;
        let src_elem = self
            .solver
            .try_select(source, bound)
            .map_err(|e| e.to_string())?;
        let in_range = self
            .solver
            .try_bvult(bound, old_len64)
            .map_err(|e| e.to_string())?;
        let eq = self
            .solver
            .try_eq(res_elem, src_elem)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_implies(in_range, eq)
            .map_err(|e| e.to_string())?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound], body, &[&[res_elem]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    /// Ground instantiations for last(): `len == k+1 => result == select(arr, k)` (#1979).
    /// ay cannot propagate bvsub(len,1) through zext into select congruence.
    pub(super) fn assert_last_ground_insts(
        &mut self,
        receiver: Term,
        len_term: Term,
        result: Term,
    ) -> TrustVcResult<()> {
        let pw = crate::ir::pointer_width();
        for k in 0i64..8 {
            // `len == k+1` is a LENGTH comparison: match the (Int) length sort.
            let len_val = self.len_const_like(len_term, k + 1)?;
            let len_eq = self
                .solver
                .try_eq(len_term, len_val)
                .map_err(|e| e.to_string())?;
            let idx64 = self.solver.try_bv_const(k, pw).map_err(|e| e.to_string())?;
            let sel = self
                .solver
                .try_select(receiver, idx64)
                .map_err(|e| e.to_string())?;
            let eq = self.solver.try_eq(result, sel).map_err(|e| e.to_string())?;
            let inst = self
                .solver
                .try_implies(len_eq, eq)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(inst)
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    /// Assert explicit element-preservation axiom for update operations (#1979).
    ///
    /// `forall i: BV(pw). i != idx => select(result, i) == select(source, i)`
    ///
    /// No longer emitted on the production `.update`/`.set` path: there `result`
    /// is always the literal `store(source, idx, val)`, so this is a pure
    /// read-over-write tautology that ay resolves natively, and emitting it as a
    /// `forall` derailed SAT model generation (see `encode_seq_update`). Retained
    /// (and exercised by the array-axiom hot-path benchmark) for callers that
    /// relate two *independent* arrays, where the preservation is non-trivial.
    #[allow(dead_code)]
    pub(super) fn assert_update_preservation(
        &mut self,
        result: Term,
        source: Term,
        updated_idx: Term,
    ) -> TrustVcResult<()> {
        let bound = self
            .solver
            .fresh_var("__upd_idx", Sort::bitvec(crate::ir::pointer_width()));
        let res_elem = self
            .solver
            .try_select(result, bound)
            .map_err(|e| e.to_string())?;
        let src_elem = self
            .solver
            .try_select(source, bound)
            .map_err(|e| e.to_string())?;
        let idx_eq = self
            .solver
            .try_eq(bound, updated_idx)
            .map_err(|e| e.to_string())?;
        let ne = self.solver.try_not(idx_eq).map_err(|e| e.to_string())?;
        let eq = self
            .solver
            .try_eq(res_elem, src_elem)
            .map_err(|e| e.to_string())?;
        let body = self.solver.try_implies(ne, eq).map_err(|e| e.to_string())?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound], body, &[&[res_elem]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;
        Ok(())
    }
}
