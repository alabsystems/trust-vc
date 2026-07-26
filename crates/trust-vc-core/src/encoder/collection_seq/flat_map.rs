//! Seq flat_map encoder.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use super::{super::AstExpressionParser, seq_expr_receiver_name};
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::expr_references_any_name;
use ay_dpll::api::{ArraySort, Sort, Term};

enum FlatMapSeqSummary {
    Encoded {
        term: Term,
        receiver_name: Option<String>,
        len_term: Term,
    },
    Push {
        base: Box<Self>,
        pushed_value: Term,
        len_term: Term,
    },
    Concat {
        lhs: Box<Self>,
        rhs: Box<Self>,
        len_term: Term,
    },
}

impl FlatMapSeqSummary {
    fn len_term(&self) -> Term {
        match self {
            Self::Encoded { len_term, .. }
            | Self::Push { len_term, .. }
            | Self::Concat { len_term, .. } => *len_term,
        }
    }
}

impl<'a> AstExpressionParser<'a> {
    fn emit_seq_flat_map_quantified_axioms() -> bool {
        crate::encoder::seq_flat_map_quantifiers_enabled()
    }

    fn build_seq_flat_map_summary(
        &mut self,
        expr: &TrustVcExpr,
        bound_names: &HashSet<&str>,
        result_elem_ty: &TrustVcType,
    ) -> TrustVcResult<FlatMapSeqSummary> {
        match expr {
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Push,
                receiver,
                args,
                ..
            } => {
                let [pushed_arg] = args.as_slice() else {
                    return Err(
                        "Seq::flat_map requires Seq::push bodies to have exactly one argument"
                            .to_string()
                            .into(),
                    );
                };
                let base =
                    self.build_seq_flat_map_summary(receiver, bound_names, result_elem_ty)?;
                let pushed_value = self.encode_subexpr(pushed_arg)?;
                let pushed_value =
                    self.coerce_value_for_seq_elem_ty(pushed_value, result_elem_ty)?;
                let one = self
                    .solver
                    .try_bv_const(1, crate::ir::pointer_width())
                    .map_err(|e| e.to_string())?;
                let len_term = self
                    .solver
                    .try_bvadd(base.len_term(), one)
                    .map_err(|e| e.to_string())?;
                Ok(FlatMapSeqSummary::Push {
                    base: Box::new(base),
                    pushed_value,
                    len_term,
                })
            }
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Concat | CollectionOp::Add,
                receiver,
                args,
                ..
            } => {
                let [rhs_arg] = args.as_slice() else {
                    return Err("Seq::flat_map requires Seq::add/concat bodies to have exactly one rhs argument"
                        .to_string()
                        .into());
                };
                let lhs = self.build_seq_flat_map_summary(receiver, bound_names, result_elem_ty)?;
                let rhs = self.build_seq_flat_map_summary(rhs_arg, bound_names, result_elem_ty)?;
                let len_term = self
                    .solver
                    .try_bvadd(lhs.len_term(), rhs.len_term())
                    .map_err(|e| e.to_string())?;
                Ok(FlatMapSeqSummary::Concat {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    len_term,
                })
            }
            _ => {
                if expr_references_any_name(expr, bound_names) {
                    return Err("Seq::flat_map currently supports binder-dependent bodies built from Seq::push and Seq::add/concat over binder-free sequence expressions"
                        .to_string()
                        .into());
                }

                let term = self.encode_subexpr(expr)?;
                let receiver_name = seq_expr_receiver_name(expr).map(str::to_string);
                let len_term = self
                    .lookup_collection_len(term, receiver_name.as_deref())
                    .ok_or_else(|| {
                        "Seq::flat_map body must produce a sequence with tracked length metadata"
                            .to_string()
                    })?;
                // flat_map's internal summary lengths are used as BV array
                // indices throughout (prefix sums, ITE element selection), so
                // keep them BV. Bridge the (Int, Route A #2779) collection
                // length to a BV view here. The carrier-level no-overflow is a
                // bounded-width artifact only on this internal arithmetic; the
                // externally-visible result length is Int (see encode path).
                let len_term = self.len_as_index_bv(len_term)?;
                Ok(FlatMapSeqSummary::Encoded {
                    term,
                    receiver_name,
                    len_term,
                })
            }
        }
    }

    fn seq_flat_map_summary_elem(
        &mut self,
        summary: &FlatMapSeqSummary,
        idx: Term,
    ) -> TrustVcResult<Term> {
        match summary {
            FlatMapSeqSummary::Encoded {
                term,
                receiver_name,
                ..
            } => {
                let elem = self
                    .solver
                    .try_select(*term, idx)
                    .map_err(|e| e.to_string())?;
                if let Some(info) = self.element_width_info(*term, receiver_name.as_deref()) {
                    self.term_widths.insert(elem, info);
                }
                Ok(elem)
            }
            FlatMapSeqSummary::Push {
                base, pushed_value, ..
            } => {
                let base_len = base.len_term();
                let base_elem = self.seq_flat_map_summary_elem(base, idx)?;
                let at_end = self
                    .solver
                    .try_eq(idx, base_len)
                    .map_err(|e| e.to_string())?;
                let (base_elem, pushed_value) = self.coerce_bv_widths(base_elem, *pushed_value)?;
                self.solver
                    .try_ite(at_end, pushed_value, base_elem)
                    .map_err(|e| e.to_string().into())
            }
            FlatMapSeqSummary::Concat { lhs, rhs, .. } => {
                let lhs_len = lhs.len_term();
                let lhs_elem = self.seq_flat_map_summary_elem(lhs, idx)?;
                let rhs_idx = self
                    .solver
                    .try_bvsub(idx, lhs_len)
                    .map_err(|e| e.to_string())?;
                let rhs_elem = self.seq_flat_map_summary_elem(rhs, rhs_idx)?;
                let in_lhs = self
                    .solver
                    .try_bvult(idx, lhs_len)
                    .map_err(|e| e.to_string())?;
                let (lhs_elem, rhs_elem) = self.coerce_bv_widths(lhs_elem, rhs_elem)?;
                self.solver
                    .try_ite(in_lhs, lhs_elem, rhs_elem)
                    .map_err(|e| e.to_string().into())
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_seq_flat_map_summary(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        source_idx: Term,
        param_name: &str,
        param_ty: &TrustVcType,
        body: &TrustVcExpr,
        result_elem_ty: &TrustVcType,
    ) -> TrustVcResult<FlatMapSeqSummary> {
        let source_elem = self
            .solver
            .try_select(receiver, source_idx)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(source_elem, info);
        }
        let bound_value = self.coerce_element_for_int_mode(source_elem, receiver, receiver_name)?;
        let bound_names = HashSet::from([param_name]);
        self.with_closure_body_bindings(
            [(param_name.to_string(), bound_value, param_ty.clone())],
            |s| s.build_seq_flat_map_summary(body, &bound_names, result_elem_ty),
        )
    }

    /// Encode `Seq::flat_map(f)` as a fresh sequence built from prefix-summed segments.
    ///
    /// This slice deliberately supports binder-dependent closure bodies only
    /// when they can be summarized without invoking the normal side-effecting
    /// sequence encoder under the outer binder. Supported structural forms are:
    /// `Seq::push`, `Seq::add`, and `Seq::concat` over binder-free sequence
    /// expressions. Everything else fails closed instead of leaking the binder
    /// through top-level helper assertions.
    pub(in crate::encoder) fn encode_seq_flat_map(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Seq::flat_map expects exactly one SpecFn::new(...) argument"
                    .to_string()
                    .into(),
            );
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err(
                "Seq::flat_map currently supports unary SpecFn closures only"
                    .to_string()
                    .into(),
            );
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Seq::flat_map requires a SpecFn argument"
                .to_string()
                .into());
        };
        let TrustVcType::Seq(result_elem_ty) = ret_ty.as_ref() else {
            return Err("Seq::flat_map requires SpecFn<T, Seq<U>>"
                .to_string()
                .into());
        };
        let pw = crate::ir::pointer_width();

        let source_len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| format!("No length tracked for Seq '{}' in flat_map()", rname))?;
        // BV view of the (Int) source length for BV-indexed prefix select /
        // range guards; the prefix-sum machinery is BV internally (#2779).
        let source_len_bv = self.len_as_index_bv(source_len)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: sort_for_type(result_elem_ty),
        }));
        let result = self.solver.fresh_var("__seq_flat_map", result_sort);
        // Externally-visible result length is Int (Route A #2779), bridged to
        // the BV prefix-sum total below.
        let result_len = self.solver.fresh_var("__seq_flat_map_len", Sort::Int);
        let result_len_zero = self.solver.int_const(0);
        let result_len_nonneg = self
            .solver
            .try_ge(result_len, result_len_zero)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(result_len_nonneg)
            .map_err(|e| e.to_string())?;
        let prefix_sort = Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pw),
            element_sort: Sort::bitvec(pw),
        }));
        let prefix = self.solver.fresh_var("__seq_flat_map_prefix", prefix_sort);

        self.register_collection_meta(
            result,
            super::super::parser_state::CollectionMeta {
                kind: super::super::parser_state::CollectionKind::Seq,
                len_term: Some(result_len),
                len_guard: None,
                elem_ty: Some(result_elem_ty.as_ref().clone()),
                key_ty: None,
                dom_term: None,
            },
        );

        let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
        let one = self.solver.try_bv_const(1, pw).map_err(|e| e.to_string())?;
        let prefix_zero = self
            .solver
            .try_select(prefix, zero)
            .map_err(|e| e.to_string())?;
        let prefix_zero_eq = self
            .solver
            .try_eq(prefix_zero, zero)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(prefix_zero_eq)
            .map_err(|e| e.to_string())?;

        if Self::emit_seq_flat_map_quantified_axioms() {
            let bound_i = self.solver.fresh_var("__seq_flat_map_i", Sort::bitvec(pw));
            let summary = self.bind_seq_flat_map_summary(
                receiver,
                receiver_name,
                bound_i,
                param_name,
                param_ty,
                body,
                result_elem_ty,
            )?;
            let mapped_len = summary.len_term();
            let i_in_range = self
                .solver
                .try_bvult(bound_i, source_len_bv)
                .map_err(|e| e.to_string())?;
            let prefix_i = self
                .solver
                .try_select(prefix, bound_i)
                .map_err(|e| e.to_string())?;
            let next_i = self
                .solver
                .try_bvadd(bound_i, one)
                .map_err(|e| e.to_string())?;
            let prefix_next = self
                .solver
                .try_select(prefix, next_i)
                .map_err(|e| e.to_string())?;
            let expected_next = self
                .solver
                .try_bvadd(prefix_i, mapped_len)
                .map_err(|e| e.to_string())?;
            let prefix_step = self
                .solver
                .try_eq(prefix_next, expected_next)
                .map_err(|e| e.to_string())?;
            let prefix_step = self
                .solver
                .try_implies(i_in_range, prefix_step)
                .map_err(|e| e.to_string())?;
            let prefix_axiom = self
                .solver
                .try_forall_with_triggers(&[bound_i], prefix_step, &[&[prefix_next]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(prefix_axiom)
                .map_err(|e| e.to_string())?;

            let prefix_no_overflow = self
                .solver
                .try_bvuge(expected_next, prefix_i)
                .map_err(|e| e.to_string())?;
            let prefix_no_overflow = self
                .solver
                .try_implies(i_in_range, prefix_no_overflow)
                .map_err(|e| e.to_string())?;
            let prefix_no_overflow = self
                .solver
                .try_forall_with_triggers(&[bound_i], prefix_no_overflow, &[&[prefix_next]])
                .map_err(|e| e.to_string())?;
            self.overflow_checks.push((
                "Seq::flat_map prefix length no overflow".into(),
                prefix_no_overflow,
            ));

            let bound_k = self.solver.fresh_var("__seq_flat_map_k", Sort::bitvec(pw));
            let mapped_elem = self.seq_flat_map_summary_elem(&summary, bound_k)?;
            let k_in_range = self
                .solver
                .try_bvult(bound_k, mapped_len)
                .map_err(|e| e.to_string())?;
            let idx_in_segment = self
                .solver
                .try_and(i_in_range, k_in_range)
                .map_err(|e| e.to_string())?;
            let result_idx = self
                .solver
                .try_bvadd(prefix_i, bound_k)
                .map_err(|e| e.to_string())?;
            let result_elem = self
                .solver
                .try_select(result, result_idx)
                .map_err(|e| e.to_string())?;
            let (result_elem, mapped_elem) = self.coerce_bv_widths(result_elem, mapped_elem)?;
            let elem_eq = self
                .solver
                .try_eq(result_elem, mapped_elem)
                .map_err(|e| e.to_string())?;
            let elem_eq = self
                .solver
                .try_implies(idx_in_segment, elem_eq)
                .map_err(|e| e.to_string())?;
            let elem_axiom = self
                .solver
                .try_forall_with_triggers(&[bound_i, bound_k], elem_eq, &[&[result_elem]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(elem_axiom)
                .map_err(|e| e.to_string())?;
        }

        let final_prefix = self
            .solver
            .try_select(prefix, source_len_bv)
            .map_err(|e| e.to_string())?;
        // result_len (Int) == final prefix total (BV) — bridge via bv2int.
        let final_prefix_int = self.len_match_sort(result_len, final_prefix)?;
        let result_len_eq = self
            .solver
            .try_eq(result_len, final_prefix_int)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(result_len_eq)
            .map_err(|e| e.to_string())?;

        for i in 0i64..4 {
            let i_const = self.solver.try_bv_const(i, pw).map_err(|e| e.to_string())?;
            let summary = self.bind_seq_flat_map_summary(
                receiver,
                receiver_name,
                i_const,
                param_name,
                param_ty,
                body,
                result_elem_ty,
            )?;
            let mapped_len = summary.len_term();
            let i_in_range = self
                .solver
                .try_bvult(i_const, source_len_bv)
                .map_err(|e| e.to_string())?;
            let prefix_i = self
                .solver
                .try_select(prefix, i_const)
                .map_err(|e| e.to_string())?;
            let next_i = self
                .solver
                .try_bvadd(i_const, one)
                .map_err(|e| e.to_string())?;
            let prefix_next = self
                .solver
                .try_select(prefix, next_i)
                .map_err(|e| e.to_string())?;
            let expected_next = self
                .solver
                .try_bvadd(prefix_i, mapped_len)
                .map_err(|e| e.to_string())?;
            let prefix_step = self
                .solver
                .try_eq(prefix_next, expected_next)
                .map_err(|e| e.to_string())?;
            let prefix_step = self
                .solver
                .try_implies(i_in_range, prefix_step)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(prefix_step)
                .map_err(|e| e.to_string())?;

            let prefix_no_overflow = self
                .solver
                .try_bvuge(expected_next, prefix_i)
                .map_err(|e| e.to_string())?;
            let prefix_no_overflow = self
                .solver
                .try_implies(i_in_range, prefix_no_overflow)
                .map_err(|e| e.to_string())?;
            self.overflow_checks.push((
                format!("Seq::flat_map prefix length no overflow at source index {i}").into(),
                prefix_no_overflow,
            ));

            for k in 0i64..4 {
                let k_const = self.solver.try_bv_const(k, pw).map_err(|e| e.to_string())?;
                let mapped_elem = self.seq_flat_map_summary_elem(&summary, k_const)?;
                let k_in_range = self
                    .solver
                    .try_bvult(k_const, mapped_len)
                    .map_err(|e| e.to_string())?;
                let in_segment = self
                    .solver
                    .try_and(i_in_range, k_in_range)
                    .map_err(|e| e.to_string())?;
                let result_idx = self
                    .solver
                    .try_bvadd(prefix_i, k_const)
                    .map_err(|e| e.to_string())?;
                let result_elem = self
                    .solver
                    .try_select(result, result_idx)
                    .map_err(|e| e.to_string())?;
                let (result_elem, mapped_elem) = self.coerce_bv_widths(result_elem, mapped_elem)?;
                let elem_eq = self
                    .solver
                    .try_eq(result_elem, mapped_elem)
                    .map_err(|e| e.to_string())?;
                let elem_eq = self
                    .solver
                    .try_implies(in_segment, elem_eq)
                    .map_err(|e| e.to_string())?;
                self.solver
                    .try_assert_term(elem_eq)
                    .map_err(|e| e.to_string())?;
            }
        }

        Ok(result)
    }
}
