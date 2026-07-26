//! Core native Seq operations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term};

use super::super::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;

impl<'a> AstExpressionParser<'a> {
    /// `Seq::is_empty()` → `seq.len(s) == 0`.
    pub(super) fn native_seq_is_empty(&mut self, receiver: Term) -> TrustVcResult<Term> {
        let len = self.native_seq_len(receiver, None)?;
        let zero = self.solver.int_const(0);
        self.solver
            .try_eq(len, zero)
            .map_err(|e| format!("native seq is_empty: {e}").into())
    }

    /// `Seq::index(i)` / `Seq::get(i)` → `seq.nth(s, i)`.
    pub(super) fn native_seq_get(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("get() expects 1 argument, got {}", args.len()).into());
        }
        let idx = self.native_seq_coerce_to_int_index(&args[0])?;
        self.native_seq_bounds_check(receiver, receiver_name, idx, "index")?;
        if let Some(concrete_idx) = crate::encoder::AYEncoder::try_reduce_to_int(&args[0]) {
            return self.native_seq_ground_element_alias(
                receiver,
                receiver_name,
                idx,
                concrete_idx,
                "index",
            );
        }
        self.solver
            .try_seq_nth(receiver, idx)
            .map_err(|e| format!("native seq.nth: {e}").into())
    }

    /// `Seq::push(v)` → `seq.++(s, seq.unit(v))`.
    pub(super) fn native_seq_push(
        &mut self,
        receiver: Term,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("push() expects 1 argument, got {}", args.len()).into());
        }
        let len = self.native_seq_len(receiver, None)?;
        let val = self.encode_subexpr(&args[0])?;
        let unit = self
            .solver
            .try_seq_unit(val)
            .map_err(|e| format!("native seq.unit for push: {e}"))?;
        let result = self
            .solver
            .try_seq_concat(receiver, unit)
            .map_err(|e| format!("native seq.concat for push: {e}"))?;
        let one = self.solver.int_const(1);
        let new_len = self
            .solver
            .try_add(len, one)
            .map_err(|e| format!("native seq push len: {e}"))?;
        self.register_native_seq_len(result, new_len, receiver, None);
        Ok(result)
    }

    /// `Seq::first()` → `seq.nth(s, 0)` with nonempty check.
    pub(super) fn native_seq_first(&mut self, receiver: Term) -> TrustVcResult<Term> {
        self.native_seq_nonempty_check(receiver, None, "first")?;
        let zero = self.solver.int_const(0);
        // Reuse ground element alias if index 0 is already registered.
        if let Some(&alias) = self.native_seq_ground_element_aliases.get(&(receiver, 0)) {
            return Ok(alias);
        }
        // Alias the raw seq.nth result so the model validator can evaluate it.
        let nth = self
            .solver
            .try_seq_nth(receiver, zero)
            .map_err(|e| format!("native seq.nth for first: {e}"))?;
        let elem_sort = self.solver.term_sort(nth);
        let alias = self.solver.fresh_var("__native_seq_first", elem_sort);
        self.assert_eq_axiom(alias, nth, "native seq first alias")?;
        Ok(alias)
    }

    /// `Seq::last()` → `seq.nth(s, seq.len(s) - 1)` with nonempty check.
    ///
    /// Emits bridge axioms connecting the result to ground element aliases
    /// when available. ay-dpll's Seq theory can't derive the connection
    /// between `seq.nth(s, sub(len, 1))` and `seq.nth(s, k)` even when
    /// `len == k + 1` is implied by constraints, because the required
    /// LIA↔Seq theory combination is incomplete. The bridge axioms
    /// provide a direct propositional path: `(len == k + 1) → last == alias_k`.
    pub(super) fn native_seq_last(&mut self, receiver: Term) -> TrustVcResult<Term> {
        self.native_seq_nonempty_check(receiver, None, "last")?;
        let len = self.native_seq_len(receiver, None)?;
        let one = self.solver.int_const(1);
        let last_idx = self
            .solver
            .try_sub(len, one)
            .map_err(|e| format!("native seq last index: {e}"))?;
        let nth = self
            .solver
            .try_seq_nth(receiver, last_idx)
            .map_err(|e| format!("native seq.nth for last: {e}"))?;
        // Alias the raw seq.nth result so the model validator can evaluate it.
        let elem_sort = self.solver.term_sort(nth);
        let last_alias = self.solver.fresh_var("__native_seq_last", elem_sort);
        self.assert_eq_axiom(last_alias, nth, "native seq last alias")?;
        // Bridge axioms: for each known ground element alias at index k,
        // emit (len == k + 1) → last_alias == ground_alias_k.
        // This gives the solver a propositional path that doesn't require
        // incomplete LIA↔Seq theory combination.
        let ground_aliases: Vec<(i128, Term)> = self
            .native_seq_ground_element_aliases
            .iter()
            .filter(|((r, _), _)| *r == receiver)
            .map(|((_, k), alias)| (*k, *alias))
            .collect();
        for (k, ground_alias) in ground_aliases {
            let Ok(k_plus_1_i64) = i64::try_from(k + 1) else {
                continue;
            };
            let k_plus_1 = self.solver.int_const(k_plus_1_i64);
            if let (Ok(len_eq_k1), Ok(alias_eq_ground)) = (
                self.solver.try_eq(len, k_plus_1),
                self.solver.try_eq(last_alias, ground_alias),
            ) {
                if let Ok(bridge) = self.solver.try_implies(len_eq_k1, alias_eq_ground) {
                    let _ = self.solver.try_assert_term(bridge);
                }
            }
        }
        Ok(last_alias)
    }

    /// `Seq::contains(v)` → `seq.contains(s, seq.unit(v))`.
    pub(super) fn native_seq_contains(
        &mut self,
        receiver: Term,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("contains() expects 1 argument, got {}", args.len()).into());
        }
        let val = self.encode_subexpr(&args[0])?;
        let unit = self
            .solver
            .try_seq_unit(val)
            .map_err(|e| format!("native seq.unit for contains: {e}"))?;
        self.solver
            .try_seq_contains(receiver, unit)
            .map_err(|e| format!("native seq.contains: {e}").into())
    }

    /// `Seq::update(i, v)` → `extract(s,0,i) ++ unit(v) ++ extract(s,i+1,len-i-1)`.
    pub(super) fn native_seq_update(
        &mut self,
        receiver: Term,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!("update() expects 2 arguments, got {}", args.len()).into());
        }
        let idx = self.native_seq_coerce_to_int_index(&args[0])?;
        let val = self.encode_subexpr(&args[1])?;
        self.native_seq_bounds_check(receiver, None, idx, "update")?;

        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        let len = self.native_seq_len(receiver, None)?;

        let prefix = self
            .solver
            .try_seq_extract(receiver, zero, idx)
            .map_err(|e| format!("native seq update prefix: {e}"))?;
        self.emit_nth_extract_bridge_axiom(receiver, zero, idx, prefix, None, "update_prefix")?;
        let middle = self
            .solver
            .try_seq_unit(val)
            .map_err(|e| format!("native seq update unit: {e}"))?;
        let suffix_start = self
            .solver
            .try_add(idx, one)
            .map_err(|e| format!("native seq update suffix start: {e}"))?;
        let suffix_len = self
            .solver
            .try_sub(len, suffix_start)
            .map_err(|e| format!("native seq update suffix len: {e}"))?;
        let suffix = self
            .solver
            .try_seq_extract(receiver, suffix_start, suffix_len)
            .map_err(|e| format!("native seq update suffix: {e}"))?;
        self.emit_nth_extract_bridge_axiom(
            receiver,
            suffix_start,
            suffix_len,
            suffix,
            None,
            "update_suffix",
        )?;

        let prefix_middle = self
            .solver
            .try_seq_concat(prefix, middle)
            .map_err(|e| format!("native seq update concat1: {e}"))?;
        let result = self
            .solver
            .try_seq_concat(prefix_middle, suffix)
            .map_err(|e| format!("native seq update concat2: {e}"))?;
        self.register_native_seq_len(result, len, receiver, None);
        Ok(result)
    }

    /// `Seq::reverse()` — encoded via quantifier axiom over `seq.nth`.
    pub(super) fn native_seq_reverse(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let len = self.native_seq_len(receiver, None)?;
        let elem_sort = self.seq_element_sort(receiver, receiver_name)?;
        let result = self
            .solver
            .fresh_var("__seq_reverse_native", Sort::seq(elem_sort));

        let result_len = self
            .solver
            .try_seq_len(result)
            .map_err(|e| format!("native seq reverse result len: {e}"))?;
        self.assert_eq_axiom(result_len, len, "native seq reverse len")?;

        let bound_idx = self.solver.fresh_var("__rev_idx", Sort::Int);
        let one = self.solver.int_const(1);

        let result_elem = self
            .solver
            .try_seq_nth(result, bound_idx)
            .map_err(|e| format!("native seq reverse nth result: {e}"))?;
        let mirror = self
            .solver
            .try_sub(len, one)
            .map_err(|e| format!("native seq reverse mirror: {e}"))?;
        let mirror_idx = self
            .solver
            .try_sub(mirror, bound_idx)
            .map_err(|e| format!("native seq reverse mirror idx: {e}"))?;
        let source_elem = self
            .solver
            .try_seq_nth(receiver, mirror_idx)
            .map_err(|e| format!("native seq reverse nth source: {e}"))?;
        let elem_eq = self
            .solver
            .try_eq(result_elem, source_elem)
            .map_err(|e| format!("native seq reverse elem eq: {e}"))?;
        // Note: reverse uses two trigger groups (result_elem and source_elem)
        let in_range = self.int_range_guard(bound_idx, len, "native seq reverse")?;
        let guarded = self
            .solver
            .try_implies(in_range, elem_eq)
            .map_err(|e| format!("native seq reverse implies: {e}"))?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[bound_idx], guarded, &[&[result_elem], &[source_elem]])
            .map_err(|e| format!("native seq reverse forall: {e}"))?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| format!("native seq reverse assert: {e}"))?;

        self.register_native_seq_len(result, len, receiver, receiver_name);
        Ok(result)
    }

    /// `Seq::no_duplicates()` — quantifier axiom.
    pub(super) fn native_seq_no_duplicates(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        // Fully grounded small sequences are cheaper and more trustworthy to
        // discharge directly than through seq.nth equality chains.
        if let Some(grounded) = self.native_seq_grounded_elements(receiver, receiver_name, 5)? {
            let mut result = self.solver.bool_const(true);
            for i in 0..grounded.len() {
                for j in (i + 1)..grounded.len() {
                    let distinct = self
                        .solver
                        .try_neq(grounded[i], grounded[j])
                        .map_err(|e| format!("native seq nodup grounded neq: {e}"))?;
                    result = self
                        .solver
                        .try_and(result, distinct)
                        .map_err(|e| format!("native seq nodup grounded and: {e}"))?;
                }
            }
            return Ok(result);
        }

        let len = self.native_seq_len(receiver, receiver_name)?;
        let zero = self.solver.int_const(0);
        let i = self.solver.fresh_var("__nodup_i", Sort::Int);
        let j = self.solver.fresh_var("__nodup_j", Sort::Int);
        let i_ge_zero = self
            .solver
            .try_ge(i, zero)
            .map_err(|e| format!("native seq nodup: {e}"))?;
        let i_lt_j = self
            .solver
            .try_lt(i, j)
            .map_err(|e| format!("native seq nodup: {e}"))?;
        let j_lt_len = self
            .solver
            .try_lt(j, len)
            .map_err(|e| format!("native seq nodup: {e}"))?;

        let range = self
            .solver
            .try_and(i_ge_zero, i_lt_j)
            .map_err(|e| format!("native seq nodup: {e}"))?;
        let range = self
            .solver
            .try_and(range, j_lt_len)
            .map_err(|e| format!("native seq nodup: {e}"))?;

        let elem_i = self
            .solver
            .try_seq_nth(receiver, i)
            .map_err(|e| format!("native seq nodup nth: {e}"))?;
        let elem_j = self
            .solver
            .try_seq_nth(receiver, j)
            .map_err(|e| format!("native seq nodup nth: {e}"))?;
        let neq = self
            .solver
            .try_neq(elem_i, elem_j)
            .map_err(|e| format!("native seq nodup neq: {e}"))?;

        let body = self
            .solver
            .try_implies(range, neq)
            .map_err(|e| format!("native seq nodup implies: {e}"))?;
        let universal = self
            .solver
            .try_forall_with_triggers(&[i, j], body, &[&[elem_i, elem_j]])
            .map_err(|e| format!("native seq nodup forall: {e}"))?;

        let mut seed_values = Vec::with_capacity(5);
        for i_seed in 0i64..5 {
            let i_int = self.solver.int_const(i_seed);
            let elem = self
                .solver
                .try_seq_nth(receiver, i_int)
                .map_err(|e| format!("native seq nodup seed nth: {e}"))?;
            let seed = self
                .solver
                .fresh_var("__nodup_seed", self.solver.term_sort(elem));
            self.assert_eq_axiom(seed, elem, "native seq nodup seed")?;
            seed_values.push(seed);
        }

        let mut seeded = self.solver.bool_const(true);
        for i_seed in 0i64..5 {
            for j_seed in (i_seed + 1)..5 {
                let i_int = self.solver.int_const(i_seed);
                let j_int = self.solver.int_const(j_seed);
                let i_in_range = self
                    .solver
                    .try_lt(i_int, len)
                    .map_err(|e| format!("native seq nodup seed range: {e}"))?;
                let j_in_range = self
                    .solver
                    .try_lt(j_int, len)
                    .map_err(|e| format!("native seq nodup seed range: {e}"))?;
                let range = self
                    .solver
                    .try_and(i_in_range, j_in_range)
                    .map_err(|e| format!("native seq nodup seed range: {e}"))?;
                let distinct = self
                    .solver
                    .try_neq(seed_values[i_seed as usize], seed_values[j_seed as usize])
                    .map_err(|e| format!("native seq nodup seed neq: {e}"))?;
                let inst = self
                    .solver
                    .try_implies(range, distinct)
                    .map_err(|e| format!("native seq nodup seed implies: {e}"))?;
                seeded = self
                    .solver
                    .try_and(seeded, inst)
                    .map_err(|e| format!("native seq nodup seed and: {e}"))?;
            }
        }

        let six = self.solver.int_const(6);
        let small_len = self
            .solver
            .try_lt(len, six)
            .map_err(|e| format!("native seq nodup small len: {e}"))?;
        let large_len = self
            .solver
            .try_not(small_len)
            .map_err(|e| format!("native seq nodup large len: {e}"))?;
        let result = self.solver.fresh_var("__seq_no_duplicates", Sort::Bool);
        let result_is_seeded = self
            .solver
            .try_eq(result, seeded)
            .map_err(|e| format!("native seq nodup result seeded: {e}"))?;
        let result_small = self
            .solver
            .try_implies(small_len, result_is_seeded)
            .map_err(|e| format!("native seq nodup result small: {e}"))?;
        self.solver
            .try_assert_term(result_small)
            .map_err(|e| format!("native seq nodup assert small: {e}"))?;
        let result_is_universal = self
            .solver
            .try_eq(result, universal)
            .map_err(|e| format!("native seq nodup result universal: {e}"))?;
        let result_large = self
            .solver
            .try_implies(large_len, result_is_universal)
            .map_err(|e| format!("native seq nodup result large: {e}"))?;
        self.solver
            .try_assert_term(result_large)
            .map_err(|e| format!("native seq nodup assert large: {e}"))?;

        Ok(result)
    }
}
