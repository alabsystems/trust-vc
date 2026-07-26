//! Shared helpers for native Seq encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term, TermKind};

use super::super::parser_state::{CollectionKind, CollectionMeta};
use super::super::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    /// Get the Int-sorted length of a native Seq via `seq.len(s)`.
    ///
    /// For named variables, returns the pre-computed `seq.len(s)` stored in
    /// `collection_lengths` at declaration time. For anonymous/derived terms,
    /// computes `seq.len(s)` on demand.
    pub(super) fn native_seq_len(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        if let Some(len) = self
            .collection_meta_by_term
            .get(&receiver)
            .and_then(|meta| meta.len_term)
        {
            return Ok(len);
        }
        if let Some(len) = receiver_name.and_then(|n| self.collection_lengths.get(n).copied()) {
            return Ok(len);
        }
        // Alias the raw seq.len result with a plain Int variable so the model
        // validator can evaluate it (ay-dpll's Seq theory skips model eval).
        let raw_len = self
            .solver
            .try_seq_len(receiver)
            .map_err(|e| format!("native seq.len: {e}"))?;
        let alias = self.solver.fresh_var("__native_seq_len_derived", Sort::Int);
        self.assert_eq_axiom(alias, raw_len, "native seq.len alias")?;
        Ok(alias)
    }

    /// Assert `0 <= idx < seq.len(s)` as an overflow check (Int domain).
    pub(super) fn native_seq_bounds_check(
        &mut self,
        seq: Term,
        seq_name: Option<&str>,
        idx: Term,
        method: &str,
    ) -> TrustVcResult<()> {
        let len = self.native_seq_len(seq, seq_name)?;
        let zero = self.solver.int_const(0);
        let idx_nonneg = self
            .solver
            .try_ge(idx, zero)
            .map_err(|e| format!("native Seq::{method} bounds nonneg: {e}"))?;
        let idx_lt_len = self
            .solver
            .try_lt(idx, len)
            .map_err(|e| format!("native Seq::{method} bounds lt: {e}"))?;
        let in_bounds = self
            .solver
            .try_and(idx_nonneg, idx_lt_len)
            .map_err(|e| format!("native Seq::{method} bounds: {e}"))?;
        self.overflow_checks.push((
            format!("Seq::{method}(i) requires 0 <= i < len").into(),
            in_bounds,
        ));
        Ok(())
    }

    /// Assert `seq.len(s) >= 1` as an overflow check (Int domain).
    pub(super) fn native_seq_nonempty_check(
        &mut self,
        seq: Term,
        seq_name: Option<&str>,
        method: &str,
    ) -> TrustVcResult<Term> {
        let len = self.native_seq_len(seq, seq_name)?;
        let one = self.solver.int_const(1);
        let nonempty = self
            .solver
            .try_ge(len, one)
            .map_err(|e| format!("native Seq::{method} nonempty: {e}"))?;
        self.overflow_checks.push((
            format!("Seq::{method}() requires len >= 1").into(),
            nonempty,
        ));
        Ok(nonempty)
    }

    /// Assert `idx >= 0` as an overflow check in the Int domain.
    pub(super) fn native_seq_nonnegative_index_check(
        &mut self,
        idx: Term,
        method: &str,
    ) -> TrustVcResult<Term> {
        let zero = self.solver.int_const(0);
        let nonnegative = self
            .solver
            .try_ge(idx, zero)
            .map_err(|e| format!("native Seq::{method} nonnegative: {e}"))?;
        self.overflow_checks.push((
            format!("Seq::{method}(i) requires 0 <= i").into(),
            nonnegative,
        ));
        Ok(nonnegative)
    }

    pub(super) fn native_seq_grounded_nth_index(
        &mut self,
        term: Term,
        receiver: Term,
        max_len: usize,
    ) -> Option<usize> {
        match self.solver.term_kind(term) {
            TermKind::App { ref name, num_args } if name == "seq.nth" && num_args == 2 => {
                let children = self.solver.term_children(term);
                if children[0] != receiver {
                    return None;
                }
                for idx in 0..max_len {
                    if children[1] == self.solver.int_const(idx as i64) {
                        return Some(idx);
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub(super) fn native_seq_grounded_alias_index(
        &mut self,
        term: Term,
        receiver: Term,
        max_len: usize,
    ) -> Option<usize> {
        if let Some(idx) = self.native_seq_grounded_nth_index(term, receiver, max_len) {
            return Some(idx);
        }

        for assertion in self.solver.assertions() {
            let TermKind::App { ref name, num_args } = self.solver.term_kind(assertion) else {
                continue;
            };
            if name != "=" || num_args != 2 {
                continue;
            }
            let children = self.solver.term_children(assertion);
            for (lhs, rhs) in [(children[0], children[1]), (children[1], children[0])] {
                if lhs != term {
                    continue;
                }
                if let Some(idx) = self.native_seq_grounded_nth_index(rhs, receiver, max_len) {
                    return Some(idx);
                }
            }
        }

        None
    }

    pub(super) fn native_seq_grounded_elements(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        max_len: usize,
    ) -> TrustVcResult<Option<Vec<Term>>> {
        let len = self.native_seq_len(receiver, receiver_name)?;
        let assertions = self.solver.assertions();
        let mut concrete_len = None;
        'find_len: for &assertion in &assertions {
            let TermKind::App { ref name, num_args } = self.solver.term_kind(assertion) else {
                continue;
            };
            if name != "=" || num_args != 2 {
                continue;
            }
            let children = self.solver.term_children(assertion);
            for idx in 0..=max_len {
                let idx_term = self.solver.int_const(idx as i64);
                if (children[0] == len && children[1] == idx_term)
                    || (children[1] == len && children[0] == idx_term)
                {
                    concrete_len = Some(idx);
                    break 'find_len;
                }
            }
        }
        let Some(concrete_len) = concrete_len else {
            return Ok(None);
        };

        let mut elements = vec![None; concrete_len];
        for assertion in assertions {
            let TermKind::App { ref name, num_args } = self.solver.term_kind(assertion) else {
                continue;
            };
            if name != "=" || num_args != 2 {
                continue;
            }
            let children = self.solver.term_children(assertion);
            for (lhs, rhs) in [(children[0], children[1]), (children[1], children[0])] {
                if !matches!(self.solver.term_kind(rhs), TermKind::Const) {
                    continue;
                }
                let Some(idx) = self.native_seq_grounded_alias_index(lhs, receiver, concrete_len)
                else {
                    continue;
                };
                elements[idx] = Some(rhs);
            }
        }

        Ok(elements.into_iter().collect())
    }

    /// Coerce a TrustVcExpr argument to an Int-sorted index term.
    ///
    /// For literal integers, creates MathInt literals directly to avoid
    /// bv2int cross-theory terms. For BV-sorted variables, converts to
    /// Int with the declared signedness preserved.
    pub(super) fn native_seq_coerce_to_int_index(
        &mut self,
        arg: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        if let TrustVcExpr::IntLit { value, .. } = arg {
            return self.encode_subexpr(&TrustVcExpr::IntLit {
                value: *value,
                ty: TrustVcType::MathInt,
            });
        }
        if let TrustVcExpr::Neg(inner) = arg {
            if let TrustVcExpr::IntLit { value, .. } = inner.as_ref() {
                return self.encode_subexpr(&TrustVcExpr::Neg(Box::new(TrustVcExpr::IntLit {
                    value: *value,
                    ty: TrustVcType::MathInt,
                })));
            }
        }

        let arg_ty = crate::ir_lowering::infer_expr_type(arg);
        let term = self.encode_subexpr(arg)?;
        if matches!(self.solver.term_sort(term), Sort::BitVec(_)) {
            let converted = if arg_ty.is_unsigned() {
                self.solver.try_bv2int(term)
            } else {
                self.solver.try_bv2int_signed(term)
            }
            .map_err(|e| format!("native seq index to Int: {e}"))?;
            self.term_widths.remove(&converted);
            return Ok(converted);
        }
        Ok(term)
    }

    pub(super) fn native_seq_ground_element_alias(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        idx: Term,
        concrete_idx: i128,
        method: &str,
    ) -> TrustVcResult<Term> {
        if let Some(alias) = self
            .native_seq_ground_element_aliases
            .get(&(receiver, concrete_idx))
            .copied()
        {
            return Ok(alias);
        }

        let elem_sort = self.seq_element_sort(receiver, receiver_name)?;
        let alias = self.solver.fresh_var("__native_seq_ground_elem", elem_sort);
        let nth = self
            .solver
            .try_seq_nth(receiver, idx)
            .map_err(|e| format!("native seq.nth for {method}: {e}"))?;
        self.assert_eq_axiom(alias, nth, &format!("native seq ground alias for {method}"))?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(alias, info);
        }
        self.native_seq_ground_element_aliases
            .insert((receiver, concrete_idx), alias);
        Ok(alias)
    }

    /// Cache Int-sorted length metadata for a derived native Seq term.
    ///
    /// Unlike `register_seq_len`, this path intentionally does NOT record the
    /// length term in `term_widths`. Native-seq lengths are Sort::Int, not BV.
    pub(super) fn register_native_seq_len(
        &mut self,
        term: Term,
        len_term: Term,
        source: Term,
        source_name: Option<&str>,
    ) {
        let elem_ty = self.resolve_source_elem_ty(source, source_name);
        self.collection_meta_by_term.insert(
            term,
            CollectionMeta {
                kind: CollectionKind::Seq,
                len_term: Some(len_term),
                len_guard: None,
                elem_ty,
                key_ty: None,
                dom_term: None,
            },
        );
    }

    /// Register `seq.len(result)` metadata and assert an arithmetic length
    /// summary only when the slice precondition guard holds.
    pub(super) fn register_guarded_native_seq_len(
        &mut self,
        result: Term,
        expected_len: Term,
        guard: Term,
        source: Term,
        source_name: Option<&str>,
        method: &str,
    ) -> TrustVcResult<()> {
        let actual_len = self
            .solver
            .try_seq_len(result)
            .map_err(|e| format!("native seq {method} result len: {e}"))?;
        let result_len = self.solver.fresh_var("__native_seq_len", Sort::Int);
        self.assert_eq_axiom(
            result_len,
            actual_len,
            &format!("native seq {method} result len eq"),
        )?;
        let zero = self.solver.int_const(0);
        let nonnegative = self
            .solver
            .try_ge(result_len, zero)
            .map_err(|e| format!("native seq {method} result len nonnegative: {e}"))?;
        self.solver
            .try_assert_term(nonnegative)
            .map_err(|e| format!("native seq {method} assert result len nonnegative: {e}"))?;
        let len_eq = self
            .solver
            .try_eq(result_len, expected_len)
            .map_err(|e| format!("native seq {method} len eq: {e}"))?;
        let guarded = self
            .solver
            .try_implies(guard, len_eq)
            .map_err(|e| format!("native seq {method} len implication: {e}"))?;
        self.solver
            .try_assert_term(guarded)
            .map_err(|e| format!("native seq {method} assert len implication: {e}"))?;
        self.register_native_seq_len(result, result_len, source, source_name);
        Ok(())
    }

    /// Assert the guarded `nth(extract(...))` bridge that ay-dpll currently
    /// misses for native Seq slices.
    pub(super) fn emit_nth_extract_bridge_axiom(
        &mut self,
        source: Term,
        start: Term,
        extract_len: Term,
        result: Term,
        guard: Option<Term>,
        method: &str,
    ) -> TrustVcResult<()> {
        let bound_idx = self.solver.fresh_var("__native_seq_extract_idx", Sort::Int);
        let mut in_range = self.int_range_guard(
            bound_idx,
            extract_len,
            &format!("native seq {method} bridge"),
        )?;
        if let Some(guard) = guard {
            in_range = self
                .solver
                .try_and(guard, in_range)
                .map_err(|e| format!("native seq {method} bridge guard: {e}"))?;
        }

        let result_elem = self
            .solver
            .try_seq_nth(result, bound_idx)
            .map_err(|e| format!("native seq {method} bridge result nth: {e}"))?;
        let source_idx = self
            .solver
            .try_add(start, bound_idx)
            .map_err(|e| format!("native seq {method} bridge source idx: {e}"))?;
        let source_elem = self
            .solver
            .try_seq_nth(source, source_idx)
            .map_err(|e| format!("native seq {method} bridge source nth: {e}"))?;
        let elem_eq = self
            .solver
            .try_eq(result_elem, source_elem)
            .map_err(|e| format!("native seq {method} bridge eq: {e}"))?;
        let body = self
            .solver
            .try_implies(in_range, elem_eq)
            .map_err(|e| format!("native seq {method} bridge implies: {e}"))?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound_idx], body, &[&[result_elem]])
            .map_err(|e| format!("native seq {method} bridge forall: {e}"))?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| format!("native seq {method} bridge assert: {e}"))?;
        Ok(())
    }

    /// Assert `a == b` as a solver axiom in one step.
    ///
    /// Combines the common `try_eq` + `try_assert_term` pair that appears
    /// throughout the native-seq encoding. The `context` string is used for
    /// error messages on both the equality construction and the assertion.
    pub(super) fn assert_eq_axiom(&mut self, a: Term, b: Term, context: &str) -> TrustVcResult<()> {
        let eq = self
            .solver
            .try_eq(a, b)
            .map_err(|e| format!("{context}: {e}"))?;
        self.solver
            .try_assert_term(eq)
            .map_err(|e| format!("{context} assert: {e}"))?;
        Ok(())
    }

    /// Build the guard term `0 <= idx < len` for Int-sorted index variables.
    ///
    /// Returns the conjunction `idx >= 0 && idx < len`. This is the range
    /// predicate used in virtually every quantified axiom over sequences.
    pub(super) fn int_range_guard(
        &mut self,
        idx: Term,
        len: Term,
        context: &str,
    ) -> TrustVcResult<Term> {
        let zero = self.solver.int_const(0);
        let nonneg = self
            .solver
            .try_ge(idx, zero)
            .map_err(|e| format!("{context} nonneg: {e}"))?;
        let lt_len = self
            .solver
            .try_lt(idx, len)
            .map_err(|e| format!("{context} lt len: {e}"))?;
        let range = self
            .solver
            .try_and(nonneg, lt_len)
            .map_err(|e| format!("{context} range: {e}"))?;
        Ok(range)
    }

    /// Assert `forall bound. (0 <= bound < len) => body` with the given triggers.
    ///
    /// Combines range guard construction, implication, quantification, and
    /// assertion into a single call. Used by map, map_values, fold, count, etc.
    pub(super) fn assert_guarded_forall(
        &mut self,
        bound: Term,
        len: Term,
        body: Term,
        triggers: &[&[Term]],
        context: &str,
    ) -> TrustVcResult<()> {
        let in_range = self.int_range_guard(bound, len, context)?;
        let guarded = self
            .solver
            .try_implies(in_range, body)
            .map_err(|e| format!("{context} implies: {e}"))?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound], guarded, triggers)
            .map_err(|e| format!("{context} forall: {e}"))?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| format!("{context} assert: {e}"))?;
        Ok(())
    }

    /// Assert `(0 <= idx < len) => body` as a ground (non-quantified) axiom.
    ///
    /// Used in ground seeding loops where a concrete index is substituted.
    pub(super) fn assert_guarded_ground(
        &mut self,
        idx: Term,
        len: Term,
        body: Term,
        context: &str,
    ) -> TrustVcResult<()> {
        let in_range = self.int_range_guard(idx, len, context)?;
        let guarded = self
            .solver
            .try_implies(in_range, body)
            .map_err(|e| format!("{context} implies: {e}"))?;
        self.solver
            .try_assert_term(guarded)
            .map_err(|e| format!("{context} assert: {e}"))?;
        Ok(())
    }
}
