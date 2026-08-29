//! Native Seq higher-order operations: map, filter, fold, flat_map, to_set, count.
//!
//! These operations encode higher-order collection ops using quantified axioms
//! over `seq.nth` with Int-sorted indices, adapting the array-based encoding
//! patterns for ay's native Seq theory.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{ArraySort, Sort, Term};

use super::super::parser_state::{CollectionKind, CollectionMeta};
use super::super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};

/// Maximum number of ground instances to seed for E-matching completeness.
const GROUND_SEED_COUNT: i64 = 4;
const FROM_FN_LITERAL_GROUND_SEED_LIMIT: i64 = 16;

impl<'a> AstExpressionParser<'a> {
    pub(super) fn native_seq_unsupported_op(&mut self, op: CollectionOp) -> TrustVcResult<Term> {
        Err(format!(
            "Seq operation {:?} is not yet supported with native-seq encoding. \
             Disable the native-seq feature or use the array encoding.",
            op
        )
        .into())
    }

    /// Encode `Seq::from_fn(len, f)` under native-seq.
    ///
    /// Creates a fresh native sequence and asserts:
    ///   seq.len(result) == len
    ///   forall i. 0 <= i < len => nth(result, i) == f(i)
    pub(in crate::encoder) fn native_seq_from_fn(
        &mut self,
        args: &[TrustVcExpr],
        return_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let [len_expr, TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Seq::from_fn expects a length plus SpecFn::new(...)"
                .to_string()
                .into());
        };
        let [(idx_param_name, idx_param_ty)] = params.as_slice() else {
            return Err("Seq::from_fn requires a unary SpecFn<usize, T>"
                .to_string()
                .into());
        };
        let TrustVcType::Seq(elem_ty) = return_ty else {
            return Err("Seq::from_fn builtin must return Seq<T>".to_string().into());
        };
        if idx_param_ty
            != &(TrustVcType::Uint {
                width: crate::ir::pointer_width(),
            })
        {
            return Err(format!(
                "Seq::from_fn requires SpecFn<usize, T>, got SpecFn<{}, _>",
                idx_param_ty.to_type_string()
            )
            .into());
        }
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::from_fn requires a SpecFn argument".to_string().into());
        };
        if ret_ty.as_ref() != elem_ty.as_ref() {
            return Err(format!(
                "Seq::from_fn closure returns '{}', but result element type is '{}'",
                ret_ty.to_type_string(),
                elem_ty.to_type_string()
            )
            .into());
        }

        let len = self.native_seq_coerce_to_int_index(len_expr)?;
        let zero = self.solver.int_const(0);
        let len_nonnegative = self
            .solver
            .try_ge(len, zero)
            .map_err(|e| format!("native Seq::from_fn len nonnegative: {e}"))?;
        self.overflow_checks.push((
            "Seq::from_fn(len) requires len >= 0".into(),
            len_nonnegative,
        ));

        let result = self
            .solver
            .fresh_var("__native_seq_from_fn", Sort::seq(sort_for_type(elem_ty)));
        let result_len = self.solver.fresh_var("__native_seq_from_fn_len", Sort::Int);
        self.register_native_seq_len_with_elem_ty(
            result,
            result_len,
            Some(elem_ty.as_ref().clone()),
        );
        let raw_result_len = self
            .solver
            .try_seq_len(result)
            .map_err(|e| format!("native Seq::from_fn result len: {e}"))?;
        self.assert_eq_axiom(result_len, raw_result_len, "native Seq::from_fn len alias")?;
        self.assert_eq_axiom(result_len, len, "native Seq::from_fn len eq")?;

        let bound_i = self.solver.fresh_var("__native_seq_from_fn_i", Sort::Int);
        let result_elem = self
            .solver
            .try_seq_nth(result, bound_i)
            .map_err(|e| format!("native Seq::from_fn result nth: {e}"))?;
        let idx_bv = self
            .solver
            .try_int2bv(bound_i, crate::ir::pointer_width())
            .map_err(|e| format!("native Seq::from_fn index int2bv: {e}"))?;
        self.term_widths
            .insert(idx_bv, (crate::ir::pointer_width(), false));
        let mapped_body = {
            let old_depth = self.quantifier_depth;
            let old_bv_depth = self.bv_quantifier_depth;
            self.quantifier_depth += 1;
            self.bv_quantifier_depth += 1;
            let result = self.with_local_bindings(
                [(idx_param_name.clone(), idx_bv, idx_param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            );
            self.quantifier_depth = old_depth;
            self.bv_quantifier_depth = old_bv_depth;
            result?
        };
        let mapped_body = self.coerce_value_for_seq_elem_ty(mapped_body, elem_ty)?;
        let elem_eq = self
            .solver
            .try_eq(result_elem, mapped_body)
            .map_err(|e| format!("native Seq::from_fn elem eq: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            result_len,
            elem_eq,
            &[&[result_elem]],
            "native Seq::from_fn",
        )?;

        let ground_seed_count = seq_from_fn_ground_seed_count(len_expr);
        for i in 0..ground_seed_count {
            let i_const = self.solver.int_const(i);
            let i_bv = self
                .solver
                .try_bv_const(i, crate::ir::pointer_width())
                .map_err(|e| format!("native Seq::from_fn ground idx: {e}"))?;
            self.term_widths
                .insert(i_bv, (crate::ir::pointer_width(), false));
            let mapped_i = {
                let old_depth = self.quantifier_depth;
                let old_bv_depth = self.bv_quantifier_depth;
                self.quantifier_depth += 1;
                self.bv_quantifier_depth += 1;
                let result = self.with_local_bindings(
                    [(idx_param_name.clone(), i_bv, idx_param_ty.clone())],
                    |s| s.encode_trust_vc_expr(body),
                );
                self.quantifier_depth = old_depth;
                self.bv_quantifier_depth = old_bv_depth;
                result?
            };
            let mapped_i = self.coerce_value_for_seq_elem_ty(mapped_i, elem_ty)?;
            let result_elem_i = self
                .solver
                .try_seq_nth(result, i_const)
                .map_err(|e| format!("native Seq::from_fn ground result nth: {e}"))?;
            let elem_eq_i = self
                .solver
                .try_eq(result_elem_i, mapped_i)
                .map_err(|e| format!("native Seq::from_fn ground eq: {e}"))?;
            self.assert_guarded_ground(
                i_const,
                result_len,
                elem_eq_i,
                "native Seq::from_fn ground",
            )?;
        }

        Ok(result)
    }

    // -----------------------------------------------------------------------
    // map_values: forall i. 0 <= i < len => nth(result, i) == f(nth(source, i))
    // -----------------------------------------------------------------------

    /// Encode `Seq::map_values(f)` under native-seq.
    ///
    /// Creates a fresh Seq variable and asserts a quantified pointwise axiom:
    ///   len(result) == len(source)
    ///   forall i. 0 <= i < len => nth(result, i) == f(nth(source, i))
    ///
    /// Ground seeds at indices 0..GROUND_SEED_COUNT for E-matching completeness.
    pub(super) fn native_seq_map_values(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Seq::map_values expects exactly one SpecFn::new(...) argument"
                    .to_string()
                    .into(),
            );
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err(
                "Seq::map_values currently supports unary SpecFn closures only"
                    .to_string()
                    .into(),
            );
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::map_values requires a SpecFn argument"
                .to_string()
                .into());
        };

        let source_len = self.native_seq_len(receiver, receiver_name)?;
        let result_sort = Sort::seq(sort_for_type(ret_ty));
        let result = self
            .solver
            .fresh_var("__native_seq_map_values", result_sort);

        // len(result) == len(source)
        let result_len = self
            .solver
            .fresh_var("__native_seq_map_values_len", Sort::Int);
        self.register_native_seq_len_with_elem_ty(
            result,
            result_len,
            Some(ret_ty.as_ref().clone()),
        );
        let raw_result_len = self
            .solver
            .try_seq_len(result)
            .map_err(|e| format!("native seq map_values result len: {e}"))?;
        self.assert_eq_axiom(
            result_len,
            raw_result_len,
            "native seq map_values len alias",
        )?;
        self.assert_eq_axiom(result_len, source_len, "native seq map_values len eq")?;

        // Quantified axiom: forall i. 0 <= i < len => nth(result, i) == f(nth(source, i))
        let bound_i = self
            .solver
            .fresh_var("__native_seq_map_values_i", Sort::Int);
        let source_elem = self
            .solver
            .try_seq_nth(receiver, bound_i)
            .map_err(|e| format!("native seq map_values source nth: {e}"))?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let mapped_body = self.with_closure_body_bindings(
            [(param_name.clone(), source_elem, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;
        let result_elem = self
            .solver
            .try_seq_nth(result, bound_i)
            .map_err(|e| format!("native seq map_values result nth: {e}"))?;
        let elem_eq = self
            .solver
            .try_eq(result_elem, mapped_body)
            .map_err(|e| format!("native seq map_values elem eq: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            source_len,
            elem_eq,
            &[&[result_elem]],
            "native seq map_values",
        )?;

        // Ground seeding
        self.native_seq_ground_seed_map(
            receiver,
            receiver_name,
            result,
            source_len,
            param_name,
            param_ty,
            body,
        )?;

        Ok(result)
    }

    // -----------------------------------------------------------------------
    // map: forall i. 0 <= i < len => nth(result, i) == f(i, nth(source, i))
    // -----------------------------------------------------------------------

    /// Encode `Seq::map(f)` under native-seq (2-param: index + element).
    pub(super) fn native_seq_map(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Seq::map expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        let [(idx_param_name, _), (val_param_name, val_param_ty)] = params.as_slice() else {
            return Err("Seq::map requires a 2-parameter SpecFn (index, element)"
                .to_string()
                .into());
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::map requires a SpecFn argument".to_string().into());
        };

        let source_len = self.native_seq_len(receiver, receiver_name)?;
        let result_sort = Sort::seq(sort_for_type(ret_ty));
        let result = self.solver.fresh_var("__native_seq_map", result_sort);

        // len(result) == len(source)
        let result_len = self.solver.fresh_var("__native_seq_map_len", Sort::Int);
        self.register_native_seq_len_with_elem_ty(
            result,
            result_len,
            Some(ret_ty.as_ref().clone()),
        );
        let raw_result_len = self
            .solver
            .try_seq_len(result)
            .map_err(|e| format!("native seq map result len: {e}"))?;
        self.assert_eq_axiom(result_len, raw_result_len, "native seq map len alias")?;
        self.assert_eq_axiom(result_len, source_len, "native seq map len eq")?;

        // Quantified axiom
        let bound_i = self.solver.fresh_var("__native_seq_map_i", Sort::Int);
        let source_elem = self
            .solver
            .try_seq_nth(receiver, bound_i)
            .map_err(|e| format!("native seq map source nth: {e}"))?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let mapped_body = self.with_closure_body_bindings(
            [
                (idx_param_name.clone(), bound_i, TrustVcType::MathInt),
                (val_param_name.clone(), source_elem, val_param_ty.clone()),
            ],
            |s| s.encode_trust_vc_expr(body),
        )?;
        let result_elem = self
            .solver
            .try_seq_nth(result, bound_i)
            .map_err(|e| format!("native seq map result nth: {e}"))?;
        let elem_eq = self
            .solver
            .try_eq(result_elem, mapped_body)
            .map_err(|e| format!("native seq map elem eq: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            source_len,
            elem_eq,
            &[&[result_elem]],
            "native seq map",
        )?;

        // Ground seeding (2-param variant with index binding)
        for i in 0..GROUND_SEED_COUNT {
            let i_const = self.solver.int_const(i);
            let source_elem_i = self
                .solver
                .try_seq_nth(receiver, i_const)
                .map_err(|e| format!("native seq map ground source nth: {e}"))?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem_i, info);
            }
            let mapped_i = self.with_closure_body_bindings(
                [
                    (idx_param_name.clone(), i_const, TrustVcType::MathInt),
                    (val_param_name.clone(), source_elem_i, val_param_ty.clone()),
                ],
                |s| s.encode_trust_vc_expr(body),
            )?;
            let result_elem_i = self
                .solver
                .try_seq_nth(result, i_const)
                .map_err(|e| format!("native seq map ground result nth: {e}"))?;
            let elem_eq_i = self
                .solver
                .try_eq(result_elem_i, mapped_i)
                .map_err(|e| format!("native seq map ground eq: {e}"))?;
            self.assert_guarded_ground(i_const, source_len, elem_eq_i, "native seq map ground")?;
        }

        Ok(result)
    }

    // -----------------------------------------------------------------------
    // filter: 2-axiom encoding with Int-indexed Skolemized witness
    // -----------------------------------------------------------------------

    /// Encode `Seq::filter(pred)` under native-seq.
    ///
    /// Encoding:
    ///   result_len <= source_len
    ///   forall j. 0 <= j < result_len => pred(nth(result, j))
    ///   forall i. 0 <= i < source_len && pred(nth(source, i))
    ///     => witness[i] < result_len && nth(result, witness[i]) == nth(source, i)
    pub(super) fn native_seq_filter(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [TrustVcExpr::SpecClosure { params, body, .. }] = args else {
            return Err("Seq::filter expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err("Seq::filter requires a unary SpecFn predicate"
                .to_string()
                .into());
        };

        let source_len = self.native_seq_len(receiver, receiver_name)?;
        let elem_sort = self.seq_element_sort(receiver, receiver_name)?;
        let result_sort = Sort::seq(elem_sort);
        let result = self.solver.fresh_var("__native_seq_filter", result_sort);
        let result_len = self.solver.fresh_var("__native_seq_filter_len", Sort::Int);

        // Register metadata
        let elem_ty = self.resolve_source_elem_ty(receiver, receiver_name);
        self.register_native_seq_len_with_elem_ty(result, result_len, elem_ty);

        let raw_result_len = self
            .solver
            .try_seq_len(result)
            .map_err(|e| format!("native seq filter result len: {e}"))?;
        let len_alias = self
            .solver
            .try_eq(result_len, raw_result_len)
            .map_err(|e| format!("native seq filter len alias: {e}"))?;
        self.solver
            .try_assert_term(len_alias)
            .map_err(|e| format!("native seq filter assert len alias: {e}"))?;

        // result_len >= 0
        let zero = self.solver.int_const(0);
        let result_len_nonneg = self
            .solver
            .try_ge(result_len, zero)
            .map_err(|e| format!("native seq filter result len nonneg: {e}"))?;
        self.solver
            .try_assert_term(result_len_nonneg)
            .map_err(|e| format!("native seq filter assert result len nonneg: {e}"))?;

        // result_len <= source_len
        let len_bound = self
            .solver
            .try_le(result_len, source_len)
            .map_err(|e| format!("native seq filter len bound: {e}"))?;
        self.solver
            .try_assert_term(len_bound)
            .map_err(|e| format!("native seq filter assert len bound: {e}"))?;

        // Axiom 1: all result elements satisfy predicate
        {
            let bound_j = self.solver.fresh_var("__native_seq_filter_j", Sort::Int);
            let result_elem = self
                .solver
                .try_seq_nth(result, bound_j)
                .map_err(|e| format!("native seq filter result nth: {e}"))?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(result_elem, info);
            }
            let pred_body = self.with_closure_body_bindings(
                [(param_name.clone(), result_elem, param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            )?;
            self.assert_guarded_forall(
                bound_j,
                result_len,
                pred_body,
                &[&[result_elem]],
                "native seq filter axiom1",
            )?;
        }

        // Axiom 2: Skolemized witness — every matching source element appears in result
        let witness_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        }));
        let witness = self
            .solver
            .fresh_var("__native_seq_filter_witness", witness_sort);
        {
            let bound_i = self.solver.fresh_var("__native_seq_filter_i", Sort::Int);
            let source_elem = self
                .solver
                .try_seq_nth(receiver, bound_i)
                .map_err(|e| format!("native seq filter source nth: {e}"))?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let pred_body = self.with_closure_body_bindings(
                [(param_name.clone(), source_elem, param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            )?;
            let i_in_range = self.int_range_guard(bound_i, source_len, "native seq filter i")?;
            let antecedent = self
                .solver
                .try_and(i_in_range, pred_body)
                .map_err(|e| format!("native seq filter antecedent: {e}"))?;

            let witness_idx = self
                .solver
                .try_select(witness, bound_i)
                .map_err(|e| format!("native seq filter witness select: {e}"))?;
            let witness_nonneg = self
                .solver
                .try_ge(witness_idx, zero)
                .map_err(|e| format!("native seq filter witness nonneg: {e}"))?;
            let witness_in_range = self
                .solver
                .try_lt(witness_idx, result_len)
                .map_err(|e| format!("native seq filter witness in range: {e}"))?;
            let result_at_witness = self
                .solver
                .try_seq_nth(result, witness_idx)
                .map_err(|e| format!("native seq filter result at witness: {e}"))?;
            let elem_match = self
                .solver
                .try_eq(result_at_witness, source_elem)
                .map_err(|e| format!("native seq filter elem match: {e}"))?;
            let consequent = self
                .solver
                .try_and(witness_nonneg, witness_in_range)
                .map_err(|e| format!("native seq filter consequent1: {e}"))?;
            let consequent = self
                .solver
                .try_and(consequent, elem_match)
                .map_err(|e| format!("native seq filter consequent2: {e}"))?;

            let implication = self
                .solver
                .try_implies(antecedent, consequent)
                .map_err(|e| format!("native seq filter axiom2 implies: {e}"))?;
            let axiom2 = self
                .solver
                .try_forall_with_triggers(&[bound_i], implication, &[&[source_elem]])
                .map_err(|e| format!("native seq filter axiom2 forall: {e}"))?;
            self.solver
                .try_assert_term(axiom2)
                .map_err(|e| format!("native seq filter assert axiom2: {e}"))?;
        }

        Ok(result)
    }

    // -----------------------------------------------------------------------
    // fold_left: state Array(Int, AccSort) with quantified step axiom
    // -----------------------------------------------------------------------

    /// Encode `Seq::fold_left(init, f)` under native-seq.
    ///
    /// Encoding:
    ///   state[0] == init
    ///   forall i. 0 <= i < len => state[i + 1] == f(state[i], nth(source, i))
    ///   result == state[len]
    pub(super) fn native_seq_fold_left(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
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

        let source_len = self.native_seq_len(receiver, receiver_name)?;
        // State array: Array(Int, AccSort)
        let state_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: sort_for_type(acc_ty),
        }));
        let states = self
            .solver
            .fresh_var("__native_seq_fold_left_state", state_sort);
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);

        // state[0] == init
        let init_value = self.encode_subexpr(init_expr)?;
        let state_zero = self
            .solver
            .try_select(states, zero)
            .map_err(|e| format!("native seq fold_left state[0]: {e}"))?;
        self.assert_eq_axiom(state_zero, init_value, "native seq fold_left init")?;

        // Quantified step: forall i. 0 <= i < len => state[i+1] == f(state[i], nth(source, i))
        let bound_i = self.solver.fresh_var("__native_seq_fold_left_i", Sort::Int);
        let state_i = self
            .solver
            .try_select(states, bound_i)
            .map_err(|e| format!("native seq fold_left state[i]: {e}"))?;
        let source_elem = self
            .solver
            .try_seq_nth(receiver, bound_i)
            .map_err(|e| format!("native seq fold_left source nth: {e}"))?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let step_value = self.bind_seq_fold_body(
            (acc_param_name, acc_param_ty, state_i),
            (elem_param_name, elem_param_ty, source_elem),
            body,
            acc_ty,
        )?;
        let next_i = self
            .solver
            .try_add(bound_i, one)
            .map_err(|e| format!("native seq fold_left i+1: {e}"))?;
        let state_next = self
            .solver
            .try_select(states, next_i)
            .map_err(|e| format!("native seq fold_left state[i+1]: {e}"))?;
        let step_eq = self
            .solver
            .try_eq(state_next, step_value)
            .map_err(|e| format!("native seq fold_left step eq: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            source_len,
            step_eq,
            &[&[state_next]],
            "native seq fold_left",
        )?;

        // Ground seeding
        for i in 0..GROUND_SEED_COUNT {
            let i_const = self.solver.int_const(i);
            let state_i = self
                .solver
                .try_select(states, i_const)
                .map_err(|e| format!("native seq fold_left ground state[{i}]: {e}"))?;
            let source_elem = self
                .solver
                .try_seq_nth(receiver, i_const)
                .map_err(|e| format!("native seq fold_left ground source nth: {e}"))?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let step_value = self.bind_seq_fold_body(
                (acc_param_name, acc_param_ty, state_i),
                (elem_param_name, elem_param_ty, source_elem),
                body,
                acc_ty,
            )?;
            let next_i = self
                .solver
                .try_add(i_const, one)
                .map_err(|e| format!("native seq fold_left ground i+1: {e}"))?;
            let state_next = self
                .solver
                .try_select(states, next_i)
                .map_err(|e| format!("native seq fold_left ground state[i+1]: {e}"))?;
            let step_eq = self
                .solver
                .try_eq(state_next, step_value)
                .map_err(|e| format!("native seq fold_left ground step eq: {e}"))?;
            self.assert_guarded_ground(
                i_const,
                source_len,
                step_eq,
                "native seq fold_left ground",
            )?;
        }

        // result == state[len]
        let result = self
            .solver
            .try_select(states, source_len)
            .map_err(|e| format!("native seq fold_left result: {e}"))?;
        Ok(result)
    }

    // -----------------------------------------------------------------------
    // fold_right: suffix state array
    // -----------------------------------------------------------------------

    /// Encode `Seq::fold_right(init, f)` under native-seq.
    ///
    /// Encoding:
    ///   state[len] == init
    ///   forall i. 0 <= i < len => state[i] == f(nth(source, i), state[i + 1])
    ///   result == state[0]
    pub(super) fn native_seq_fold_right(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
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

        let source_len = self.native_seq_len(receiver, receiver_name)?;
        let state_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: sort_for_type(acc_ty),
        }));
        let states = self
            .solver
            .fresh_var("__native_seq_fold_right_state", state_sort);
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);

        // state[len] == init
        let init_value = self.encode_subexpr(init_expr)?;
        let state_end = self
            .solver
            .try_select(states, source_len)
            .map_err(|e| format!("native seq fold_right state[len]: {e}"))?;
        self.assert_eq_axiom(state_end, init_value, "native seq fold_right init")?;

        // Quantified step: forall i. 0 <= i < len => state[i] == f(nth(source, i), state[i+1])
        let bound_i = self
            .solver
            .fresh_var("__native_seq_fold_right_i", Sort::Int);
        let next_i = self
            .solver
            .try_add(bound_i, one)
            .map_err(|e| format!("native seq fold_right i+1: {e}"))?;
        let state_next = self
            .solver
            .try_select(states, next_i)
            .map_err(|e| format!("native seq fold_right state[i+1]: {e}"))?;
        let source_elem = self
            .solver
            .try_seq_nth(receiver, bound_i)
            .map_err(|e| format!("native seq fold_right source nth: {e}"))?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let step_value = self.bind_seq_fold_body(
            (elem_param_name, elem_param_ty, source_elem),
            (acc_param_name, acc_param_ty, state_next),
            body,
            acc_ty,
        )?;
        let state_i = self
            .solver
            .try_select(states, bound_i)
            .map_err(|e| format!("native seq fold_right state[i]: {e}"))?;
        let step_eq = self
            .solver
            .try_eq(state_i, step_value)
            .map_err(|e| format!("native seq fold_right step eq: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            source_len,
            step_eq,
            &[&[state_i]],
            "native seq fold_right",
        )?;

        // Ground seeding
        for i in 0..GROUND_SEED_COUNT {
            let i_const = self.solver.int_const(i);
            let next_i = self
                .solver
                .try_add(i_const, one)
                .map_err(|e| format!("native seq fold_right ground i+1: {e}"))?;
            let state_next = self
                .solver
                .try_select(states, next_i)
                .map_err(|e| format!("native seq fold_right ground state[i+1]: {e}"))?;
            let source_elem = self
                .solver
                .try_seq_nth(receiver, i_const)
                .map_err(|e| format!("native seq fold_right ground source nth: {e}"))?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let step_value = self.bind_seq_fold_body(
                (elem_param_name, elem_param_ty, source_elem),
                (acc_param_name, acc_param_ty, state_next),
                body,
                acc_ty,
            )?;
            let state_i = self
                .solver
                .try_select(states, i_const)
                .map_err(|e| format!("native seq fold_right ground state[i]: {e}"))?;
            let step_eq = self
                .solver
                .try_eq(state_i, step_value)
                .map_err(|e| format!("native seq fold_right ground step eq: {e}"))?;
            self.assert_guarded_ground(
                i_const,
                source_len,
                step_eq,
                "native seq fold_right ground",
            )?;
        }

        // result == state[0]
        let result = self
            .solver
            .try_select(states, zero)
            .map_err(|e| format!("native seq fold_right result: {e}"))?;
        Ok(result)
    }

    // -----------------------------------------------------------------------
    // to_set: membership axiom + inverse witness
    // -----------------------------------------------------------------------

    /// Encode `Seq::to_set()` under native-seq.
    ///
    /// Creates a fresh Set (Array(ElemSort, Bool)) and asserts:
    ///   forall e. select(result, e) <==>
    ///     exists i. 0 <= i < len && nth(source, i) == e
    ///
    /// The existential is Skolemized via an inverse witness Array(ElemSort, Int).
    pub(super) fn native_seq_to_set(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let source_len = self.native_seq_len(receiver, receiver_name)?;
        let elem_sort = self.seq_element_sort(receiver, receiver_name)?;

        // Result is Array(ElemSort, Bool)
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort.clone(),
            element_sort: Sort::Bool,
        }));
        let result = self.solver.fresh_var("__native_seq_to_set", result_sort);

        // Register as a Set
        let elem_ty = self.resolve_source_elem_ty(receiver, receiver_name);
        self.collection_meta_by_term.insert(
            result,
            CollectionMeta {
                kind: CollectionKind::Set,
                len_term: None,
                len_guard: None,
                elem_ty,
                key_ty: None,
                dom_term: None,
            },
        );
        // A set drops duplicates: `|seq.to_set()| <= |seq|`, not `== |seq|`.
        // Mirror of the non-native `encode_seq_to_set` decline.
        self.decline_collection_len(result);

        // Native Seq already has membership for singleton subsequences. Tie
        // the Set projection directly to that operation so assumptions and
        // assertions can move between `s.contains(e)` and
        // `s.to_set().contains(e)` without relying on witness quantifier search.
        let bound_equiv_e = self
            .solver
            .fresh_var("__native_seq_to_set_equiv_e", elem_sort.clone());
        let membership_equiv = self
            .solver
            .try_select(result, bound_equiv_e)
            .map_err(|e| format!("native seq to_set equivalence select: {e}"))?;
        let unit_equiv = self
            .solver
            .try_seq_unit(bound_equiv_e)
            .map_err(|e| format!("native seq to_set equivalence unit: {e}"))?;
        let contains_equiv = self
            .solver
            .try_seq_contains(receiver, unit_equiv)
            .map_err(|e| format!("native seq to_set equivalence contains: {e}"))?;
        let equiv_body = self
            .solver
            .try_eq(membership_equiv, contains_equiv)
            .map_err(|e| format!("native seq to_set equivalence eq: {e}"))?;
        let equiv_axiom = self
            .solver
            .try_forall_with_triggers(
                &[bound_equiv_e],
                equiv_body,
                &[&[membership_equiv], &[contains_equiv]],
            )
            .map_err(|e| format!("native seq to_set equivalence forall: {e}"))?;
        self.solver
            .try_assert_term(equiv_axiom)
            .map_err(|e| format!("native seq to_set assert equivalence: {e}"))?;

        // Forward: forall i. 0 <= i < len => select(result, nth(source, i))
        let bound_i = self.solver.fresh_var("__native_seq_to_set_i", Sort::Int);
        let source_elem = self
            .solver
            .try_seq_nth(receiver, bound_i)
            .map_err(|e| format!("native seq to_set source nth: {e}"))?;
        let membership = self
            .solver
            .try_select(result, source_elem)
            .map_err(|e| format!("native seq to_set select: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            source_len,
            membership,
            &[&[source_elem]],
            "native seq to_set forward",
        )?;

        // Backward: inverse witness Array(ElemSort, Int)
        // forall e. select(result, e) => 0 <= witness[e] < len && nth(source, witness[e]) == e
        let witness_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort.clone(),
            element_sort: Sort::Int,
        }));
        let witness = self
            .solver
            .fresh_var("__native_seq_to_set_witness", witness_sort);
        let bound_e = self.solver.fresh_var("__native_seq_to_set_e", elem_sort);
        let membership_e = self
            .solver
            .try_select(result, bound_e)
            .map_err(|e| format!("native seq to_set backward select: {e}"))?;
        let witness_idx = self
            .solver
            .try_select(witness, bound_e)
            .map_err(|e| format!("native seq to_set witness select: {e}"))?;
        let w_in_range =
            self.int_range_guard(witness_idx, source_len, "native seq to_set witness")?;
        let source_at_witness = self
            .solver
            .try_seq_nth(receiver, witness_idx)
            .map_err(|e| format!("native seq to_set source at witness: {e}"))?;
        let elem_match = self
            .solver
            .try_eq(source_at_witness, bound_e)
            .map_err(|e| format!("native seq to_set elem match: {e}"))?;
        let consequent = self
            .solver
            .try_and(w_in_range, elem_match)
            .map_err(|e| format!("native seq to_set consequent: {e}"))?;
        let backward = self
            .solver
            .try_implies(membership_e, consequent)
            .map_err(|e| format!("native seq to_set backward implies: {e}"))?;
        let backward_axiom = self
            .solver
            .try_forall_with_triggers(&[bound_e], backward, &[&[membership_e]])
            .map_err(|e| format!("native seq to_set backward forall: {e}"))?;
        self.solver
            .try_assert_term(backward_axiom)
            .map_err(|e| format!("native seq to_set assert backward: {e}"))?;

        Ok(result)
    }

    // -----------------------------------------------------------------------
    // count: fold-like state array counting with ITE increment
    // -----------------------------------------------------------------------

    /// Encode `Seq::count(elem)` under native-seq.
    ///
    /// Encoding via accumulator state array:
    ///   state[0] == 0
    ///   forall i. 0 <= i < len =>
    ///     state[i+1] == state[i] + ite(nth(source, i) == elem, 1, 0)
    ///   result == state[len]
    pub(super) fn native_seq_count(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("Seq::count expects 1 argument, got {}", args.len()).into());
        }
        let target = self.encode_subexpr(&args[0])?;
        let source_len = self.native_seq_len(receiver, receiver_name)?;

        // State array: Array(Int, Int) tracking running count
        let state_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        }));
        let states = self
            .solver
            .fresh_var("__native_seq_count_state", state_sort);
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);

        // state[0] == 0
        let state_zero = self
            .solver
            .try_select(states, zero)
            .map_err(|e| format!("native seq count state[0]: {e}"))?;
        self.assert_eq_axiom(state_zero, zero, "native seq count init")?;

        // Quantified step
        let bound_i = self.solver.fresh_var("__native_seq_count_i", Sort::Int);
        let state_i = self
            .solver
            .try_select(states, bound_i)
            .map_err(|e| format!("native seq count state[i]: {e}"))?;
        let source_elem = self
            .solver
            .try_seq_nth(receiver, bound_i)
            .map_err(|e| format!("native seq count source nth: {e}"))?;
        let matches_target = self
            .solver
            .try_eq(source_elem, target)
            .map_err(|e| format!("native seq count eq: {e}"))?;
        let increment = self
            .solver
            .try_ite(matches_target, one, zero)
            .map_err(|e| format!("native seq count ite: {e}"))?;
        let next_count = self
            .solver
            .try_add(state_i, increment)
            .map_err(|e| format!("native seq count add: {e}"))?;
        let next_i = self
            .solver
            .try_add(bound_i, one)
            .map_err(|e| format!("native seq count i+1: {e}"))?;
        let state_next = self
            .solver
            .try_select(states, next_i)
            .map_err(|e| format!("native seq count state[i+1]: {e}"))?;
        let step_eq = self
            .solver
            .try_eq(state_next, next_count)
            .map_err(|e| format!("native seq count step eq: {e}"))?;
        self.assert_guarded_forall(
            bound_i,
            source_len,
            step_eq,
            &[&[state_next]],
            "native seq count",
        )?;

        // Ground seeding
        for i in 0..GROUND_SEED_COUNT {
            let i_const = self.solver.int_const(i);
            let state_i = self
                .solver
                .try_select(states, i_const)
                .map_err(|e| format!("native seq count ground state[{i}]: {e}"))?;
            let source_elem = self
                .solver
                .try_seq_nth(receiver, i_const)
                .map_err(|e| format!("native seq count ground source nth: {e}"))?;
            let matches_target = self
                .solver
                .try_eq(source_elem, target)
                .map_err(|e| format!("native seq count ground eq: {e}"))?;
            let increment = self
                .solver
                .try_ite(matches_target, one, zero)
                .map_err(|e| format!("native seq count ground ite: {e}"))?;
            let next_count = self
                .solver
                .try_add(state_i, increment)
                .map_err(|e| format!("native seq count ground add: {e}"))?;
            let next_i = self
                .solver
                .try_add(i_const, one)
                .map_err(|e| format!("native seq count ground i+1: {e}"))?;
            let state_next = self
                .solver
                .try_select(states, next_i)
                .map_err(|e| format!("native seq count ground state[i+1]: {e}"))?;
            let step_eq = self
                .solver
                .try_eq(state_next, next_count)
                .map_err(|e| format!("native seq count ground step eq: {e}"))?;
            self.assert_guarded_ground(i_const, source_len, step_eq, "native seq count ground")?;
        }

        // result == state[len] (Int-sorted)
        let result = self
            .solver
            .try_select(states, source_len)
            .map_err(|e| format!("native seq count result: {e}"))?;
        Ok(result)
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /// Register native seq len metadata with an explicit element type
    /// (used when the result element type differs from the source).
    fn register_native_seq_len_with_elem_ty(
        &mut self,
        term: Term,
        len_term: Term,
        elem_ty: Option<TrustVcType>,
    ) {
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

    /// Ground seed map-like operations at concrete indices for E-matching.
    fn native_seq_ground_seed_map(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        result: Term,
        source_len: Term,
        param_name: &str,
        param_ty: &TrustVcType,
        body: &TrustVcExpr,
    ) -> TrustVcResult<()> {
        for i in 0..GROUND_SEED_COUNT {
            let i_const = self.solver.int_const(i);
            let source_elem = self
                .solver
                .try_seq_nth(receiver, i_const)
                .map_err(|e| format!("native seq map ground source nth: {e}"))?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(source_elem, info);
            }
            let mapped_body = self.with_closure_body_bindings(
                [(param_name.to_string(), source_elem, param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            )?;
            let result_elem = self
                .solver
                .try_seq_nth(result, i_const)
                .map_err(|e| format!("native seq map ground result nth: {e}"))?;
            let elem_eq = self
                .solver
                .try_eq(result_elem, mapped_body)
                .map_err(|e| format!("native seq map ground eq: {e}"))?;
            self.assert_guarded_ground(i_const, source_len, elem_eq, "native seq map ground")?;
        }
        Ok(())
    }
}

fn seq_from_fn_ground_seed_count(len_expr: &TrustVcExpr) -> i64 {
    let literal_len = match len_expr {
        TrustVcExpr::IntLit { value, .. } => i64::try_from(*value).ok(),
        _ => None,
    };
    literal_len
        .filter(|len| *len > GROUND_SEED_COUNT)
        .map(|len| len.min(FROM_FN_LITERAL_GROUND_SEED_LIMIT))
        .unwrap_or(GROUND_SEED_COUNT)
}
