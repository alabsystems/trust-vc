//! Seq fold encoders.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{ArraySort, Sort, Term};

use super::super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    pub(in crate::encoder) fn bind_seq_fold_body(
        &mut self,
        first_binding: (&str, &TrustVcType, Term),
        second_binding: (&str, &TrustVcType, Term),
        body: &TrustVcExpr,
        result_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let (first_name, first_ty, first_value) = first_binding;
        let (second_name, second_ty, second_value) = second_binding;

        let body_result = self.with_closure_body_bindings(
            [
                (first_name.to_string(), first_value, first_ty.clone()),
                (second_name.to_string(), second_value, second_ty.clone()),
            ],
            |s| s.encode_trust_vc_expr(body),
        )?;

        self.coerce_value_for_seq_elem_ty(body_result, result_ty)
    }

    /// Apply the fold closure once over the concrete element `select(receiver,
    /// bv#j)`, threading `acc` (in `acc_ty` form) as the accumulator.
    ///
    /// Mirrors the per-index coercion of the ground-seed loop, but feeds the
    /// accumulator directly instead of reading it from the state array. The
    /// returned term is the closure body coerced back to `acc_ty` (so it can be
    /// threaded into the next step). `fold_right` swaps the binding order
    /// `(element, accumulator)` to match `Seq::fold_right`.
    #[allow(clippy::too_many_arguments)]
    fn seq_fold_apply_concrete_step(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        acc: Term,
        j: i64,
        acc_param: (&str, &TrustVcType),
        elem_param: (&str, &TrustVcType),
        body: &TrustVcExpr,
        acc_ty: &TrustVcType,
        fold_right: bool,
    ) -> TrustVcResult<Term> {
        let pw = crate::ir::pointer_width();
        let acc_value = self.coerce_term_for_declared_type_in_int_mode(acc, acc_ty)?;
        let idx = self.solver.try_bv_const(j, pw).map_err(|e| e.to_string())?;
        let source_elem = self
            .solver
            .try_select(receiver, idx)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let elem_value = self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;
        let (acc_param_name, acc_param_ty) = acc_param;
        let (elem_param_name, elem_param_ty) = elem_param;
        if fold_right {
            self.bind_seq_fold_body(
                (elem_param_name, elem_param_ty, elem_value),
                (acc_param_name, acc_param_ty, acc_value),
                body,
                acc_ty,
            )
        } else {
            self.bind_seq_fold_body(
                (acc_param_name, acc_param_ty, acc_value),
                (elem_param_name, elem_param_ty, elem_value),
                body,
                acc_ty,
            )
        }
    }

    /// Ground (definitional) unfoldings of a `Seq` fold over a concrete length.
    ///
    /// For each `k` in `0..K` assert `source_len == k => result == v_k`, where
    /// `v_k` is the fold closure applied `k` times over the first `k` concrete
    /// element reads `select(receiver, bv#0..k)`:
    ///
    ///   fold_left:  v_0 = init; v_{j+1} = f(v_j, s[j])             (j = 0..k)
    ///   fold_right: v_k = init; v_j     = f(s[j], v_{j+1})         (j = k-1..0)
    ///
    /// This mirrors `assert_last_ground_insts` (#1979): the `forall i < len`
    /// step axiom plus the `result == select(states, bv2int-companion)` index
    /// leave `result` under-determined because ay does not invert `bv2int` to
    /// identify the companion-indexed read with the ground-seeded one (the B2
    /// Int-vs-BitVec bridge gap). These instances pin `result` EXACTLY for every
    /// concrete length `< K` via a pure-LIA `source_len == k` guard, with no
    /// dependence on the `states` array. They are entailed by the fold semantics
    /// in BOTH directions, so a wrong claimed value is refuted (Counterexample /
    /// Unknown), never falsely Verified. For `len >= K` no instance fires and the
    /// quantified axiom remains the (Unknown) fallback.
    #[allow(clippy::too_many_arguments)]
    fn assert_seq_fold_ground_insts(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        source_len: Term,
        init_value: Term,
        result: Term,
        acc_param: (&str, &TrustVcType),
        elem_param: (&str, &TrustVcType),
        body: &TrustVcExpr,
        acc_ty: &TrustVcType,
        fold_right: bool,
    ) -> TrustVcResult<()> {
        const K: i64 = 8;
        for k in 0i64..K {
            let mut acc = init_value;
            if fold_right {
                for j in (0i64..k).rev() {
                    acc = self.seq_fold_apply_concrete_step(
                        receiver,
                        receiver_name,
                        acc,
                        j,
                        acc_param,
                        elem_param,
                        body,
                        acc_ty,
                        true,
                    )?;
                }
            } else {
                for j in 0i64..k {
                    acc = self.seq_fold_apply_concrete_step(
                        receiver,
                        receiver_name,
                        acc,
                        j,
                        acc_param,
                        elem_param,
                        body,
                        acc_ty,
                        false,
                    )?;
                }
            }
            // `source_len == k` is a pure-LIA length guard (the solver discharges
            // it trivially against the assumed/derived length — no encode-time
            // concrete length is required).
            let len_k = self.len_const_like(source_len, k)?;
            let len_eq = self
                .solver
                .try_eq(source_len, len_k)
                .map_err(|e| e.to_string())?;
            let res_eq = self.solver.try_eq(result, acc).map_err(|e| e.to_string())?;
            let inst = self
                .solver
                .try_implies(len_eq, res_eq)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(inst)
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    /// Encode `Seq::fold_left(init, f)` via an accumulator state array.
    ///
    /// Encoding:
    ///   state[0] == init
    ///   forall i < len. state[i + 1] == f(state[i], source[i])
    ///   result == state[len]
    ///
    /// The current slice deliberately rejects collection-valued accumulators:
    /// the state array can carry the raw SMT term, but trust_vc does not yet
    /// propagate collection length/domain metadata through accumulator steps.
    pub(in crate::encoder) fn encode_seq_fold_left(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [init_expr, TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Seq::fold_left expects an initial accumulator plus SpecFn::new(...)"
                    .to_string()
                    .into(),
            );
        };
        let [(acc_param_name, acc_param_ty), (elem_param_name, elem_param_ty)] = params.as_slice()
        else {
            return Err(
                "Seq::fold_left requires a 2-parameter SpecFn (accumulator, element)"
                    .to_string()
                    .into(),
            );
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::fold_left requires a SpecFn argument"
                .to_string()
                .into());
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
                "Seq::fold_left currently supports non-collection accumulator/result types only"
                    .to_string()
                    .into(),
            );
        }
        let pw = crate::ir::pointer_width();

        let source_len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Seq '{}' in fold_left()", rname))?;
        // BV view of the (Int) length for BV-indexed select / range guards (#2779).
        // Precondition-guarded: a length-DECREASING source view (`skip(n>len)`,
        // `subrange(i>j)`, `drop_first`/`drop_last` on empty) registers a NEGATIVE
        // Int length; the unconditional `len_index_companion` bridge
        // `bv2int(companion) == -k` is UNSAT and would POISON the context into a
        // vacuous proof, masking the violated source precondition (#soundness
        // skip/subrange/drop — fold_left consumer site).
        let source_len_bv = self.len_index_companion_maybe_negative(source_len)?;
        let state_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: sort_for_type(acc_ty),
        }));
        let states = self.solver.fresh_var("__seq_fold_left_state", state_sort);
        let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;

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

        let bound_i = self.solver.fresh_var("__seq_fold_left_i", Sort::bitvec(pw));
        let state_i_raw = self
            .solver
            .try_select(states, bound_i)
            .map_err(|e| e.to_string())?;
        let acc_value = self.coerce_term_for_declared_type_in_int_mode(state_i_raw, acc_ty)?;
        let source_elem = self
            .solver
            .try_select(receiver, bound_i)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let elem_value = self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;
        let step_value = self.bind_seq_fold_body(
            (acc_param_name, acc_param_ty, acc_value),
            (elem_param_name, elem_param_ty, elem_value),
            body,
            acc_ty,
        )?;

        let next_i = self
            .solver
            .try_bvadd(bound_i, one)
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
        let i_in_range = self
            .solver
            .try_bvult(bound_i, source_len_bv)
            .map_err(|e| e.to_string())?;
        let step_eq = self
            .solver
            .try_implies(i_in_range, step_eq)
            .map_err(|e| e.to_string())?;
        let step_axiom = self
            .solver
            .try_forall_with_triggers(&[bound_i], step_eq, &[&[state_next_raw]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(step_axiom)
            .map_err(|e| e.to_string())?;

        for i in 0i64..4 {
            let i_const = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            let state_i_raw = self
                .solver
                .try_select(states, i_const)
                .map_err(|e| e.to_string())?;
            let acc_value = self.coerce_term_for_declared_type_in_int_mode(state_i_raw, acc_ty)?;
            let source_elem = self
                .solver
                .try_select(receiver, i_const)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let elem_value =
                self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;
            let step_value = self.bind_seq_fold_body(
                (acc_param_name, acc_param_ty, acc_value),
                (elem_param_name, elem_param_ty, elem_value),
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
            let i_in_range = self
                .solver
                .try_bvult(i_const, source_len_bv)
                .map_err(|e| e.to_string())?;
            let step_eq = self
                .solver
                .try_implies(i_in_range, step_eq)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(step_eq)
                .map_err(|e| e.to_string())?;
        }

        let result = self
            .solver
            .try_select(states, source_len_bv)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(result, acc_ty);

        // Definitional ground unfoldings: pin `result` exactly for every
        // concrete length `< K`, recovering the per-length correctness the
        // `bv2int`-companion index hides from ay (mirrors `assert_last_ground_insts`).
        self.assert_seq_fold_ground_insts(
            receiver,
            receiver_name,
            source_len,
            init_value,
            result,
            (acc_param_name, acc_param_ty),
            (elem_param_name, elem_param_ty),
            body,
            acc_ty,
            false,
        )?;
        Ok(result)
    }

    /// Encode `Seq::fold_right(init, f)` via a suffix accumulator state array.
    ///
    /// Encoding:
    ///   state[len] == init
    ///   forall i < len. state[i] == f(source[i], state[i + 1])
    ///   result == state[0]
    pub(in crate::encoder) fn encode_seq_fold_right(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [init_expr, TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Seq::fold_right expects an initial accumulator plus SpecFn::new(...)"
                    .to_string()
                    .into(),
            );
        };
        let [(elem_param_name, elem_param_ty), (acc_param_name, acc_param_ty)] = params.as_slice()
        else {
            return Err(
                "Seq::fold_right requires a 2-parameter SpecFn (element, accumulator)"
                    .to_string()
                    .into(),
            );
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::fold_right requires a SpecFn argument"
                .to_string()
                .into());
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
                "Seq::fold_right currently supports non-collection accumulator/result types only"
                    .to_string()
                    .into(),
            );
        }
        let pw = crate::ir::pointer_width();

        let source_len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Seq '{}' in fold_right()", rname))?;
        // BV view of the (Int) length for BV-indexed select / range guards (#2779).
        // Precondition-guarded so a NEGATIVE length-decreasing source view leaves
        // the bridge inert instead of UNSAT-poisoning the context (#soundness
        // skip/subrange/drop — fold_right consumer site; see `encode_seq_fold_left`).
        let source_len_bv = self.len_index_companion_maybe_negative(source_len)?;
        let state_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: sort_for_type(acc_ty),
        }));
        let states = self.solver.fresh_var("__seq_fold_right_state", state_sort);
        let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;

        let init_value = self.encode_subexpr(init_expr)?;
        let init_value = self.coerce_value_for_seq_elem_ty(init_value, acc_ty)?;
        let state_end = self
            .solver
            .try_select(states, source_len_bv)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(state_end, acc_ty);
        let init_eq = self
            .solver
            .try_eq(state_end, init_value)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(init_eq)
            .map_err(|e| e.to_string())?;

        let bound_i = self
            .solver
            .fresh_var("__seq_fold_right_i", Sort::bitvec(pw));
        let next_i = self
            .solver
            .try_bvadd(bound_i, one)
            .map_err(|e| e.to_string())?;
        let state_next_raw = self
            .solver
            .try_select(states, next_i)
            .map_err(|e| e.to_string())?;
        let acc_value = self.coerce_term_for_declared_type_in_int_mode(state_next_raw, acc_ty)?;
        let source_elem = self
            .solver
            .try_select(receiver, bound_i)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let elem_value = self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;
        let step_value = self.bind_seq_fold_body(
            (elem_param_name, elem_param_ty, elem_value),
            (acc_param_name, acc_param_ty, acc_value),
            body,
            acc_ty,
        )?;

        let state_i_raw = self
            .solver
            .try_select(states, bound_i)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(state_i_raw, acc_ty);
        let step_eq = self
            .solver
            .try_eq(state_i_raw, step_value)
            .map_err(|e| e.to_string())?;
        let i_in_range = self
            .solver
            .try_bvult(bound_i, source_len_bv)
            .map_err(|e| e.to_string())?;
        let step_eq = self
            .solver
            .try_implies(i_in_range, step_eq)
            .map_err(|e| e.to_string())?;
        let step_axiom = self
            .solver
            .try_forall_with_triggers(&[bound_i], step_eq, &[&[state_i_raw]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(step_axiom)
            .map_err(|e| e.to_string())?;

        for i in 0i64..4 {
            let i_const = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            let next_i = self
                .solver
                .try_bvadd(i_const, one)
                .map_err(|e| e.to_string())?;
            let state_next_raw = self
                .solver
                .try_select(states, next_i)
                .map_err(|e| e.to_string())?;
            let acc_value =
                self.coerce_term_for_declared_type_in_int_mode(state_next_raw, acc_ty)?;
            let source_elem = self
                .solver
                .try_select(receiver, i_const)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let elem_value =
                self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;
            let step_value = self.bind_seq_fold_body(
                (elem_param_name, elem_param_ty, elem_value),
                (acc_param_name, acc_param_ty, acc_value),
                body,
                acc_ty,
            )?;
            let state_i_raw = self
                .solver
                .try_select(states, i_const)
                .map_err(|e| e.to_string())?;
            self.register_term_width_for_declared_type(state_i_raw, acc_ty);
            let step_eq = self
                .solver
                .try_eq(state_i_raw, step_value)
                .map_err(|e| e.to_string())?;
            let i_in_range = self
                .solver
                .try_bvult(i_const, source_len_bv)
                .map_err(|e| e.to_string())?;
            let step_eq = self
                .solver
                .try_implies(i_in_range, step_eq)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(step_eq)
                .map_err(|e| e.to_string())?;
        }

        let result = self
            .solver
            .try_select(states, zero)
            .map_err(|e| e.to_string())?;
        self.register_term_width_for_declared_type(result, acc_ty);

        // Definitional ground unfoldings (suffix direction): pin `result`
        // exactly for every concrete length `< K`.
        self.assert_seq_fold_ground_insts(
            receiver,
            receiver_name,
            source_len,
            init_value,
            result,
            (acc_param_name, acc_param_ty),
            (elem_param_name, elem_param_ty),
            body,
            acc_ty,
            true,
        )?;
        Ok(result)
    }
}
