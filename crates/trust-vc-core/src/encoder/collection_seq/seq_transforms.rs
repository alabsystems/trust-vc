//! Seq sequence-level transformation operations: shift, reverse, concat.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `ops.rs` for the 500-line limit (#2621).

use ay_dpll::api::{ArraySort, Sort, Term};

use super::super::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    fn assert_shifted_seq_ground_instance(
        &mut self,
        result: Term,
        source: Term,
        offset64: Term,
        idx: Term,
    ) -> TrustVcResult<()> {
        let shifted = self
            .solver
            .try_bvadd(idx, offset64)
            .map_err(|e| e.to_string())?;
        let r_elem = self
            .solver
            .try_select(result, idx)
            .map_err(|e| e.to_string())?;
        let s_elem = self
            .solver
            .try_select(source, shifted)
            .map_err(|e| e.to_string())?;
        let inst = self
            .solver
            .try_eq(r_elem, s_elem)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(inst)
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    /// `len_bv` is a BV(pw) view of the source length (carrier is BV-indexed).
    fn assert_reverse_seq_ground_instance(
        &mut self,
        result: Term,
        source: Term,
        len_bv: Term,
        idx: Term,
    ) -> TrustVcResult<()> {
        let one = self
            .solver
            .try_bv_const(1, crate::ir::pointer_width())
            .map_err(|e| e.to_string())?;
        let last = self
            .solver
            .try_bvsub(len_bv, one)
            .map_err(|e| e.to_string())?;
        let source_idx = self
            .solver
            .try_bvsub(last, idx)
            .map_err(|e| e.to_string())?;
        let result_elem = self
            .solver
            .try_select(result, idx)
            .map_err(|e| e.to_string())?;
        let source_elem = self
            .solver
            .try_select(source, source_idx)
            .map_err(|e| e.to_string())?;
        let inst = self
            .solver
            .try_eq(result_elem, source_elem)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(inst)
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    /// `lhs_len_bv` is a BV(pw) view of the lhs length (the carrier is
    /// BV-indexed; callers bridge the Int length via `len_as_index_bv`).
    fn assert_concat_seq_ground_instance(
        &mut self,
        result: Term,
        lhs: Term,
        rhs: Term,
        lhs_len_bv: Term,
        idx: Term,
    ) -> TrustVcResult<()> {
        let lhs_elem = self
            .solver
            .try_select(lhs, idx)
            .map_err(|e| e.to_string())?;
        let rhs_offset = self
            .solver
            .try_bvsub(idx, lhs_len_bv)
            .map_err(|e| e.to_string())?;
        let rhs_elem = self
            .solver
            .try_select(rhs, rhs_offset)
            .map_err(|e| e.to_string())?;
        let in_lhs = self
            .solver
            .try_bvult(idx, lhs_len_bv)
            .map_err(|e| e.to_string())?;
        let chosen = self
            .solver
            .try_ite(in_lhs, lhs_elem, rhs_elem)
            .map_err(|e| e.to_string())?;
        let result_elem = self
            .solver
            .try_select(result, idx)
            .map_err(|e| e.to_string())?;
        let inst = self
            .solver
            .try_eq(result_elem, chosen)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(inst)
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    /// Encode an index-shifted Seq: result[i] = source[i + offset] for i in 0..new_len.
    ///
    /// Creates a fresh Seq array and asserts a forall axiom:
    ///   forall i: BV(pw). select(result, i) = select(source, i + offset)
    ///
    /// Also adds ground instantiations for the first few small indices plus the
    /// symbolic tail boundary to work around ay's BV-to-EUF equality
    /// propagation gap (#1979, #2390). Without these, E-matching produces the
    /// correct instantiation but ay cannot close the chain when index
    /// arithmetic involves zero-extended BV terms.
    /// `new_len` is the result LENGTH (Int under Route A #2779, or BV on legacy
    /// paths) and `offset64` is a BV(pw) index offset into `source`. The length
    /// is stored as-is in metadata; a BV view (`new_len_bv`) is derived for the
    /// forall index range guard and the symbolic-tail ground seed, since the
    /// `Array(BV,T)` carrier is BV-indexed.
    pub(in crate::encoder) fn encode_index_shifted_seq(
        &mut self,
        source: Term,
        receiver_name: Option<&str>,
        offset64: Term,
        new_len: Term,
    ) -> TrustVcResult<Term> {
        let new_len_is_int = self.len_is_int(new_len);
        if !new_len_is_int {
            // Legacy BV-length path retains the bounded-width non-negativity guard.
            let zero_pw = self
                .solver
                .try_bv_const(0, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            let nonneg = self
                .solver
                .try_bvuge(new_len, zero_pw)
                .map_err(|e| format!("shifted seq length non-negativity: {}", e))?;
            self.overflow_checks
                .push(("shifted seq non-negative length".into(), nonneg));
        }
        // BV companion of the (Int) result length for the FORALL range guard —
        // kept in pure BV (no `int2bv` subterm) so ay-dpll can model-validate
        // the quantifier (Route A #2779). The result of a shift/take/skip/
        // subrange is no longer than the source, hence representable in the
        // BV(pw)-indexed carrier, so `bv2int(companion)==new_len` adds no real
        // assumption. The symbolic-tail GROUND seed (non-quantified) may use the
        // total `int2bv` view.
        //
        // `new_len` here is a length-DECREASING result (`len - n`, `end - start`,
        // `len - 1`) that goes NEGATIVE exactly when the op's precondition is
        // violated, so use the precondition-guarded companion: an unconditional
        // `bv2int(companion) == new_len` is UNSAT for negative `new_len` and
        // would poison the context into a vacuous proof, masking the
        // precondition guard (#soundness skip/subrange/drop).
        let new_len_bv = self.len_index_companion_maybe_negative(new_len)?;
        let new_len_ground_bv = self.len_as_index_bv(new_len)?;

        let elem_sort = self.seq_element_sort(source, receiver_name)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(crate::ir::pointer_width()),
            element_sort: elem_sort,
        }));
        let result = self.solver.fresh_var("__seq_shifted", result_sort);
        let bound_idx = self
            .solver
            .fresh_var("__seq_idx", Sort::bitvec(crate::ir::pointer_width()));

        let shifted_idx = self
            .solver
            .try_bvadd(bound_idx, offset64)
            .map_err(|e| e.to_string())?;
        let result_elem = self
            .solver
            .try_select(result, bound_idx)
            .map_err(|e| e.to_string())?;
        let source_elem = self
            .solver
            .try_select(source, shifted_idx)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_elem, source_elem)
            .map_err(|e| e.to_string())?;
        // Range guard: only constrain in-bounds indices (#2572). bound_idx is a
        // BV array index, so compare against the BV view of the length.
        let idx_in_range = self
            .solver
            .try_bvult(bound_idx, new_len_bv)
            .map_err(|e| e.to_string())?;
        let guarded_body = self
            .solver
            .try_implies(idx_in_range, body)
            .map_err(|e| e.to_string())?;

        let axiom = self
            .solver
            .try_forall_with_triggers(
                &[bound_idx],
                guarded_body,
                &[&[result_elem], &[source_elem]],
            )
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        for i in 0i64..4 {
            let idx64 = self
                .solver
                .try_bv_const(i, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            self.assert_shifted_seq_ground_instance(result, source, offset64, idx64)?;
        }

        // Seed at new_len - 1 directly (no ITE wrapper). The forall axiom is
        // universal so seeding at any index is correct. When new_len <= 4 this
        // duplicates a concrete seed (harmless); when new_len == 0 it wraps to
        // MAX_BV but adds only a single useless equality. Removing the previous
        // ite(new_len > 4, new_len - 1, 0) wrapper fixes a solver timeout where
        // ay could not resolve the ITE to connect the ground seed with the
        // assertion term (#2494).
        let one = self
            .solver
            .try_bv_const(1, crate::ir::pointer_width())
            .map_err(|e| e.to_string())?;
        let last_idx = self
            .solver
            .try_bvsub(new_len_ground_bv, one)
            .map_err(|e| e.to_string())?;
        self.assert_shifted_seq_ground_instance(result, source, offset64, last_idx)?;

        if let Some(name) = receiver_name {
            self.collection_lengths.insert(name.to_string(), new_len);
        }
        let elem_ty = self.resolve_source_elem_ty(source, receiver_name);
        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(new_len),
                len_guard: None,
                elem_ty,
                key_ty: None,
                dom_term: None,
            },
        );

        Ok(result)
    }

    /// Encode Seq::reverse() as a fresh sequence with mirrored element order.
    pub(in crate::encoder) fn encode_seq_reverse(
        &mut self,
        source: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let len = self
            .lookup_collection_len(source, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in reverse()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let elem_sort = self.seq_element_sort(source, receiver_name)?;
        let pw = crate::ir::pointer_width();
        // BV companion for the FORALL (pure BV, model-validatable) and a total
        // `int2bv` view for the GROUND seeds (Route A #2779). Reverse preserves
        // length, so the result is representable in the BV-indexed carrier and
        // `bv2int(companion)==len` adds no assumption WHEN `len >= 0`. But the
        // SOURCE can itself be a length-DECREASING view (`skip(n>len)`,
        // `subrange(i>j)`) whose length is NEGATIVE exactly when its precondition
        // is violated; the unconditional bridge `bv2int(companion) == -k` is then
        // UNSAT and POISONS the context into a vacuous proof, masking the source
        // precondition (#soundness skip/subrange/drop — reverse consumer site).
        // The guarded companion conditions the bridge on `len >= 0`, leaving it
        // inert for a violated precondition. The Int length is kept unchanged in
        // metadata.
        let len_bv = self.len_index_companion_maybe_negative(len)?;
        let len_ground_bv = self.len_as_index_bv(len)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: elem_sort,
        }));
        let result = self.solver.fresh_var("__seq_reverse", result_sort);
        let bound_idx = self.solver.fresh_var("__seq_reverse_idx", Sort::bitvec(pw));
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
        let last = self
            .solver
            .try_bvsub(len_bv, one)
            .map_err(|e| e.to_string())?;
        let source_idx = self
            .solver
            .try_bvsub(last, bound_idx)
            .map_err(|e| e.to_string())?;
        let result_elem = self
            .solver
            .try_select(result, bound_idx)
            .map_err(|e| e.to_string())?;
        let source_elem = self
            .solver
            .try_select(source, source_idx)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_elem, source_elem)
            .map_err(|e| e.to_string())?;
        let idx_in_range = self
            .solver
            .try_bvult(bound_idx, len_bv)
            .map_err(|e| e.to_string())?;
        let guarded_body = self
            .solver
            .try_implies(idx_in_range, body)
            .map_err(|e| e.to_string())?;
        let axiom = self
            .solver
            .try_forall_with_triggers(
                &[bound_idx],
                guarded_body,
                &[&[result_elem], &[source_elem]],
            )
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        for i in 0i64..4 {
            let idx = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            self.assert_reverse_seq_ground_instance(result, source, len_ground_bv, idx)?;
        }
        let last_idx = self
            .solver
            .try_bvsub(len_ground_bv, one)
            .map_err(|e| e.to_string())?;
        self.assert_reverse_seq_ground_instance(result, source, len_ground_bv, last_idx)?;

        // Reverse preserves length: store the original Int length unchanged.
        self.register_seq_len(result, len, source, receiver_name);
        Ok(result)
    }

    /// Encode Seq::concat: result = self ++ other.
    ///
    /// Creates a fresh Seq array and asserts:
    ///   forall i: result[i] = ite(i < len(self), self[i], other[i - len(self)])
    ///   result_len = len(self) + len(other)
    pub(in crate::encoder) fn encode_seq_concat(
        &mut self,
        lhs: Term,
        rhs: Term,
        lhs_name: &str,
        rhs_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let lhs_len = self
            .lookup_collection_len(lhs, Some(lhs_name))
            .ok_or_else(|| format!("No length tracking for Seq '{}' in concat()", lhs_name))?;
        let rhs_len = self.lookup_collection_len(rhs, rhs_name).ok_or_else(|| {
            format!(
                "Seq::concat() requires length tracking for rhs '{}'",
                rhs_name.unwrap_or("<anonymous>")
            )
        })?;
        // Route A (#2779): result LENGTH is Int addition — monotone, no
        // wraparound; the bounded-width "concat length no overflow" obligation
        // is GONE. The Array(BV,T) carrier is BV-indexed, so derive BV views of
        // the lengths for the index arithmetic / range guard below.
        let new_len = self.len_add(lhs_len, rhs_len)?;
        // Operand lengths get BV companions (bv2int(companion)==len) so the
        // element forall's index arithmetic stays in pure BV — an `int2bv(len)`
        // subterm inside a quantifier forces ay-dpll's model validator to
        // Unknown (Route A #2779). The result-length range bound is the *BV
        // sum* of the operand companions (it may wrap, but only at indices the
        // carrier cannot represent), NOT `int2bv(new_len)`; crucially the
        // result LENGTH itself stays a pure Int (no `< 2^pw` constraint), so
        // `len(a)+len(b)` is never forced to not overflow (that was unsound
        // route B). Ground instances at the symbolic tail still use
        // `len_as_index_bv` since they are not quantified.
        //
        // An OPERAND of concat can itself be a length-DECREASING view
        // (`subrange(2,1)` -> `-1`, `skip(5)` on len 3 -> `-2`, `drop_first`/
        // `drop_last` on empty -> `-1`) whose length goes NEGATIVE exactly when
        // its Verus precondition is violated. The unconditional
        // `len_index_companion` asserts `bv2int(companion) == lhs_len`, which is
        // UNSAT for a negative operand length and POISONS the whole context
        // into a vacuous proof — discharging BOTH the violated operand
        // precondition AND any downstream claim (e.g. a false `.len() == 999`).
        // `encode_index_shifted_seq` already registers the shifted RESULT length
        // with the guarded companion (above); the same guard is required here
        // where that negative length is re-bridged as a concat OPERAND. The
        // guard conditions the bridge on `len >= 0`, so valid (non-negative)
        // operands are unchanged while a violated precondition leaves the bridge
        // inert and refutes (#soundness skip/subrange/drop — concat operand
        // bridge site).
        let lhs_len_bv = self.len_index_companion_maybe_negative(lhs_len)?;
        let rhs_len_bv = self.len_index_companion_maybe_negative(rhs_len)?;
        let new_len_bv = self
            .solver
            .try_bvadd(lhs_len_bv, rhs_len_bv)
            .map_err(|e| e.to_string())?;
        self.term_widths
            .insert(new_len_bv, (crate::ir::pointer_width(), false));

        let elem_sort = self.seq_element_sort(lhs, Some(lhs_name))?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(crate::ir::pointer_width()),
            element_sort: elem_sort,
        }));
        let result = self.solver.fresh_var("__seq_concat", result_sort);
        let bound_idx = self
            .solver
            .fresh_var("__concat_idx", Sort::bitvec(crate::ir::pointer_width()));

        let lhs_elem = self
            .solver
            .try_select(lhs, bound_idx)
            .map_err(|e| e.to_string())?;
        let rhs_offset = self
            .solver
            .try_bvsub(bound_idx, lhs_len_bv)
            .map_err(|e| e.to_string())?;
        let rhs_elem = self
            .solver
            .try_select(rhs, rhs_offset)
            .map_err(|e| e.to_string())?;
        let in_lhs = self
            .solver
            .try_bvult(bound_idx, lhs_len_bv)
            .map_err(|e| e.to_string())?;
        let chosen = self
            .solver
            .try_ite(in_lhs, lhs_elem, rhs_elem)
            .map_err(|e| e.to_string())?;
        let result_elem = self
            .solver
            .try_select(result, bound_idx)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_elem, chosen)
            .map_err(|e| e.to_string())?;
        // Range guard: only constrain in-bounds indices (#2572).
        let idx_in_range = self
            .solver
            .try_bvult(bound_idx, new_len_bv)
            .map_err(|e| e.to_string())?;
        let guarded_body = self
            .solver
            .try_implies(idx_in_range, body)
            .map_err(|e| e.to_string())?;

        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound_idx], guarded_body, &[&[result_elem]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        let pw = crate::ir::pointer_width();
        for i in 0i64..4 {
            let idx = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            self.assert_concat_seq_ground_instance(result, lhs, rhs, lhs_len_bv, idx)?;
        }
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
        let last_idx = self
            .solver
            .try_bvsub(new_len_bv, one)
            .map_err(|e| e.to_string())?;
        self.assert_concat_seq_ground_instance(result, lhs, rhs, lhs_len_bv, last_idx)?;

        if !self.len_is_int(new_len) {
            // Legacy BV-length path keeps the bounded-width guards.
            let zero = self
                .solver
                .try_bv_const(0, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            let nonneg = self
                .solver
                .try_bvuge(new_len, zero)
                .map_err(|e| format!("concat length non-negativity: {}", e))?;
            self.overflow_checks
                .push(("concat length non-negative".into(), nonneg));
            let no_overflow = self
                .solver
                .try_bvuge(new_len, lhs_len)
                .map_err(|e| format!("concat length overflow: {}", e))?;
            self.overflow_checks
                .push(("concat length no overflow".into(), no_overflow));
        }
        let elem_ty = self.resolve_source_elem_ty(lhs, Some(lhs_name));
        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(new_len),
                len_guard: None,
                elem_ty,
                key_ty: None,
                dom_term: None,
            },
        );
        self.assert_concat_length_axiom(new_len, lhs_len, rhs_len)?;

        Ok(result)
    }
}
