//! Higher-order Set operations: mk_map and fold.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from `collection_set.rs` for the 500-line limit (#2621).

use ay_dpll::api::{ArraySort, Sort, Term, TermKind};

use super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;

impl<'a> AstExpressionParser<'a> {
    /// Encode `Set::mk_map(f)` as a fresh map whose domain matches the set.
    ///
    /// Encoding:
    ///   result.dom == self
    ///   result.len == self.len    (when tracked)
    ///   forall x. self[x] => result[x] == f(x)
    #[allow(clippy::indexing_slicing)] // invariant: `params[0]` is only used after matching one closure arg and `params.len() == 1`
    pub(super) fn encode_set_mk_map(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [crate::ir::TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Set::mk_map expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        if params.len() != 1 {
            return Err("Set::mk_map requires a unary SpecFn".to_string().into());
        }
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Set::mk_map requires a SpecFn argument".to_string().into());
        };
        let (param_name, param_ty) = &params[0];

        let elem_sort = self.set_element_sort(receiver, receiver_name)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort.clone(),
            element_sort: sort_for_type(ret_ty),
        }));

        // key_ty for the resulting Map is the Set's element type (#2507).
        let set_key_ty = self
            .collection_meta_by_term
            .get(&receiver)
            .and_then(|m| m.elem_ty.clone())
            .or_else(|| {
                receiver_name
                    .and_then(|n| self.var_types.get(n))
                    .and_then(|ty| ty.collection_elem())
            });
        let set_len = self.lookup_collection_len(receiver, receiver_name);

        if let Some(inserted_elems) = self.finite_empty_set_insert_chain(receiver) {
            let mut finite_result = self
                .solver
                .fresh_var("__set_mk_map_finite_base", result_sort.clone());
            for elem in inserted_elems {
                let mapped = self.with_closure_body_bindings(
                    [(param_name.clone(), elem, param_ty.clone())],
                    |s| s.encode_trust_vc_expr(body),
                )?;
                finite_result = self
                    .solver
                    .try_store(finite_result, elem, mapped)
                    .map_err(|e| e.to_string())?;
            }
            self.register_collection_meta(
                finite_result,
                super::parser_state::CollectionMeta {
                    kind: super::parser_state::CollectionKind::Map,
                    len_term: set_len,
                    len_guard: None,
                    elem_ty: Some(ret_ty.as_ref().clone()),
                    key_ty: set_key_ty,
                    dom_term: Some(receiver),
                },
            );
            if set_len.is_none() {
                // The source set declined its cardinality (e.g. `s.filter(p)`),
                // so the map built over it has none either — propagate the
                // decline instead of letting the name fallback resolve the
                // ORIGINAL set's length through the chained receiver name.
                self.decline_collection_len(finite_result);
            }
            return Ok(finite_result);
        }

        let result = self.solver.fresh_var("__set_mk_map", result_sort);
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Map,
                len_term: set_len,
                len_guard: None,
                elem_ty: Some(ret_ty.as_ref().clone()),
                key_ty: set_key_ty,
                dom_term: Some(receiver),
            },
        );
        if set_len.is_none() {
            // See the finite-chain arm above: a declined source cardinality must
            // not be re-acquired through the chained receiver name.
            self.decline_collection_len(result);
        }

        // Safe quantification via helper — native-sorted bound var (#2531)
        let elem_ty_resolved = self.set_element_trust_vc_type(receiver, receiver_name)?;
        let (quant_var, elem_term) =
            self.safe_element_quantifier("__set_mk_map_x", &elem_ty_resolved)?;
        let self_has = self
            .solver
            .try_select(receiver, elem_term)
            .map_err(|e| e.to_string())?;

        // Bind closure parameter to the quantifier-bound element term
        let mapped = self.with_closure_body_bindings(
            [(param_name.clone(), elem_term, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_val = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let val_eq = self
            .solver
            .try_eq(result_val, mapped)
            .map_err(|e| e.to_string())?;
        let mk_map_body = self
            .solver
            .try_implies(self_has, val_eq)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&elem_ty_resolved, quant_var, mk_map_body)?;
        let axiom = self
            .solver
            .try_forall(&[quant_var], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    fn finite_empty_set_insert_chain(&mut self, receiver: Term) -> Option<Vec<Term>> {
        let true_term = self.solver.bool_const(true);
        let mut current = receiver;
        let mut elems = Vec::new();

        loop {
            match self.solver.term_kind(current) {
                TermKind::App { name, num_args } if name == "store" && num_args == 3 => {
                    let children = self.solver.term_children(current);
                    let [base, elem, value] = children.as_slice() else {
                        return None;
                    };
                    if *value != true_term {
                        return None;
                    }
                    elems.push(*elem);
                    current = *base;
                }
                TermKind::Var { name }
                    if name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
                        && name.ends_with("_empty") =>
                {
                    elems.reverse();
                    return Some(elems);
                }
                _ => return None,
            }
        }
    }

    /// Encode `Set::fold(init, f)` via linearization + state-array accumulation.
    ///
    /// Encoding:
    ///   1. Introduce a fresh "ordering" array that linearizes set elements
    ///      into indexed positions [0..len).
    ///   2. Assert: forall i < len. set.contains(ordering[i])
    ///   3. Assert: forall i,j < len. i != j => ordering[i] != ordering[j]
    ///   4. Fold the ordering via a state-array:
    ///      state[0] == init
    ///      forall i < len. state[i+1] == f(state[i], ordering[i])
    ///      result == state[len]
    ///
    /// Requires tracked set length. Fail-closed on untracked length.
    /// Collection-valued accumulators are rejected (same as Seq fold).
    #[allow(clippy::indexing_slicing)] // invariant: `params[0]`/`params[1]` are only used after matching the closure arg and `params.len() == 2`
    pub(super) fn encode_set_fold(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [init_expr, crate::ir::TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Set::fold expects an initial accumulator plus SpecFn::new(...)"
                    .to_string()
                    .into(),
            );
        };
        if params.len() != 2 {
            return Err(
                "Set::fold requires a 2-parameter SpecFn (accumulator, element)"
                    .to_string()
                    .into(),
            );
        }
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Set::fold requires a SpecFn argument".to_string().into());
        };
        let acc_ty = ret_ty.as_ref();
        if matches!(
            acc_ty,
            TrustVcType::Seq(_)
                | TrustVcType::Array(_, _)
                | TrustVcType::Set(_)
                | TrustVcType::Multiset(_)
                | TrustVcType::Map(_, _)
                | TrustVcType::String
                | TrustVcType::StrSlice
        ) {
            return Err(
                "Set::fold currently supports non-collection accumulator/result types only"
                    .to_string()
                    .into(),
            );
        }
        let (acc_param_name, acc_param_ty) = &params[0];
        let (elem_param_name, elem_param_ty) = &params[1];
        let pw = crate::ir::pointer_width();

        let set_len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Set '{}' in fold()", rname))?;
        // Set cardinality is Int (Route A #2779); the linearization ordering is
        // a BV-indexed array, so use a BV view for the index range/select below.
        let set_len_bv = self.len_as_index_bv(set_len)?;
        let elem_ty = self.set_element_trust_vc_type(receiver, receiver_name)?;
        let elem_sort = self.set_element_sort(receiver, receiver_name)?;

        // Step 1: Linearize the set into a fresh ordering array
        let ordering_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: elem_sort.clone(),
        }));
        let ordering = self.solver.fresh_var("__set_fold_ordering", ordering_sort);

        let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;

        // Step 2: Ground membership — for each ground index i < ground_depth,
        // assert set.contains(ordering[i]) (guarded by i < len).
        // No quantified membership to avoid E-matching loops with surjection.
        for i in 0i64..4 {
            let ci = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            let oi = self
                .solver
                .try_select(ordering, ci)
                .map_err(|e| e.to_string())?;
            let set_has = self
                .solver
                .try_select(receiver, oi)
                .map_err(|e| e.to_string())?;
            let in_range = self
                .solver
                .try_bvult(ci, set_len_bv)
                .map_err(|e| e.to_string())?;
            let guarded = self
                .solver
                .try_implies(in_range, set_has)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(guarded)
                .map_err(|e| e.to_string())?;
        }

        // Step 3: Ground injectivity for small indices.
        // Avoids the expensive bi-quantified forall i,j axiom. For sets up to
        // the ground depth (4), these constraints + surjection are sufficient.
        for i in 0i64..4 {
            for j in (i + 1)..4 {
                let ci = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
                let cj = self.solver.try_bv_const(j, pw).map_err(|e| e.to_string())?;
                let oi = self
                    .solver
                    .try_select(ordering, ci)
                    .map_err(|e| e.to_string())?;
                let oj = self
                    .solver
                    .try_select(ordering, cj)
                    .map_err(|e| e.to_string())?;
                let elems_ne = self
                    .solver
                    .try_distinct(&[oi, oj])
                    .map_err(|e| e.to_string())?;
                let i_ok = self
                    .solver
                    .try_bvult(ci, set_len_bv)
                    .map_err(|e| e.to_string())?;
                let j_ok = self
                    .solver
                    .try_bvult(cj, set_len_bv)
                    .map_err(|e| e.to_string())?;
                let both_ok = self.solver.try_and(i_ok, j_ok).map_err(|e| e.to_string())?;
                let guarded = self
                    .solver
                    .try_implies(both_ok, elems_ne)
                    .map_err(|e| e.to_string())?;
                self.solver
                    .try_assert_term(guarded)
                    .map_err(|e| e.to_string())?;
            }
        }

        // Step 3b: Surjection — every set element has a position in the ordering.
        // Uses a Skolem "inverse" array: inv[x] < len && ordering[inv[x]] == x
        // Safe quantification via helper — native-sorted bound var (#2531)
        let inv_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort.clone(),
            element_sort: Sort::bitvec(pw),
        }));
        let inv = self.solver.fresh_var("__set_fold_inv", inv_sort);
        let (quant_x, elem_x) = self.safe_element_quantifier("__set_fold_surj_x", &elem_ty)?;
        let set_has_x = self
            .solver
            .try_select(receiver, elem_x)
            .map_err(|e| e.to_string())?;
        let inv_x = self
            .solver
            .try_select(inv, elem_x)
            .map_err(|e| e.to_string())?;
        let inv_in_range = self
            .solver
            .try_bvult(inv_x, set_len_bv)
            .map_err(|e| e.to_string())?;
        let ordering_at_inv = self
            .solver
            .try_select(ordering, inv_x)
            .map_err(|e| e.to_string())?;
        let ordering_eq_x = self
            .solver
            .try_eq(ordering_at_inv, elem_x)
            .map_err(|e| e.to_string())?;
        let surj_consequent = self
            .solver
            .try_and(inv_in_range, ordering_eq_x)
            .map_err(|e| e.to_string())?;
        let surj_body = self
            .solver
            .try_implies(set_has_x, surj_consequent)
            .map_err(|e| e.to_string())?;
        let guarded_surj = self.guard_element_quantifier(&elem_ty, quant_x, surj_body)?;
        let surj_axiom = self
            .solver
            .try_forall(&[quant_x], guarded_surj)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(surj_axiom)
            .map_err(|e| e.to_string())?;

        // Step 4: State-array fold over the linearized ordering
        let state_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: sort_for_type(acc_ty),
        }));
        let states = self.solver.fresh_var("__set_fold_state", state_sort);

        let init_value = self.encode_subexpr(init_expr)?;
        let init_value = self.coerce_value_for_seq_elem_ty(init_value, acc_ty)?;
        let state_zero = self
            .solver
            .try_select(states, zero)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(state_zero, acc_ty);
        let init_eq = self
            .solver
            .try_eq(state_zero, init_value)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(init_eq)
            .map_err(|e| e.to_string())?;

        // Quantified step: forall i < len. state[i+1] == f(state[i], ordering[i])
        let fold_i = self.solver.fresh_var("__set_fold_step_i", Sort::bitvec(pw));
        let state_i_raw = self
            .solver
            .try_select(states, fold_i)
            .map_err(|e| e.to_string())?;
        let acc_value = self.coerce_term_for_declared_type_in_int_mode(state_i_raw, acc_ty)?;
        let ord_elem = self
            .solver
            .try_select(ordering, fold_i)
            .map_err(|e| e.to_string())?;
        if let Some(width) = elem_ty.bit_width() {
            if width > 0 {
                self.term_widths
                    .insert(ord_elem, (width, !elem_ty.is_unsigned()));
            }
        }
        let step_value = self.bind_seq_fold_body(
            (acc_param_name, acc_param_ty, acc_value),
            (elem_param_name, elem_param_ty, ord_elem),
            body,
            acc_ty,
        )?;

        let next_i = self
            .solver
            .try_bvadd(fold_i, one)
            .map_err(|e| e.to_string())?;
        let state_next_raw = self
            .solver
            .try_select(states, next_i)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(state_next_raw, acc_ty);
        let step_eq = self
            .solver
            .try_eq(state_next_raw, step_value)
            .map_err(|e| e.to_string())?;
        let fi_in_range = self
            .solver
            .try_bvult(fold_i, set_len_bv)
            .map_err(|e| e.to_string())?;
        let step_guarded = self
            .solver
            .try_implies(fi_in_range, step_eq)
            .map_err(|e| e.to_string())?;
        let step_axiom = self
            .solver
            .try_forall_with_triggers(&[fold_i], step_guarded, &[&[state_next_raw]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(step_axiom)
            .map_err(|e| e.to_string())?;

        // Ground instantiation for small indices (same pattern as Seq fold)
        for i in 0i64..4 {
            let i_const = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            let state_i_raw = self
                .solver
                .try_select(states, i_const)
                .map_err(|e| e.to_string())?;
            let acc_value = self.coerce_term_for_declared_type_in_int_mode(state_i_raw, acc_ty)?;
            let ord_elem = self
                .solver
                .try_select(ordering, i_const)
                .map_err(|e| e.to_string())?;
            if let Some(width) = elem_ty.bit_width() {
                if width > 0 {
                    self.term_widths
                        .insert(ord_elem, (width, !elem_ty.is_unsigned()));
                }
            }
            let step_value = self.bind_seq_fold_body(
                (acc_param_name, acc_param_ty, acc_value),
                (elem_param_name, elem_param_ty, ord_elem),
                body,
                acc_ty,
            )?;
            let next_i = self
                .solver
                .try_bvadd(i_const, one)
                .map_err(|e| e.to_string())?;
            let state_next_raw = self
                .solver
                .try_select(states, next_i)
                .map_err(|e| e.to_string())?;
            self.register_term_width_for_declared_type(state_next_raw, acc_ty);
            let step_eq = self
                .solver
                .try_eq(state_next_raw, step_value)
                .map_err(|e| e.to_string())?;
            let fi_in_range = self
                .solver
                .try_bvult(i_const, set_len_bv)
                .map_err(|e| e.to_string())?;
            let step_guarded = self
                .solver
                .try_implies(fi_in_range, step_eq)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(step_guarded)
                .map_err(|e| e.to_string())?;
        }

        // Result is state[len]
        let result = self
            .solver
            .try_select(states, set_len_bv)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(result, acc_ty);
        Ok(result)
    }
}
