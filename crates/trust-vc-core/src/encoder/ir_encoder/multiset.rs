//! Multiset-specific collection encoding — insert, remove, count, union, intersect.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `Multiset<T>` is encoded as Array(T_sort, Int) where values are Nat counts.
//! Part of #2421 Slice 2.

use std::borrow::Cow;

use ay_dpll::api::{ArraySort, Sort, Term};

use crate::encoder::parser_state::{
    CollectionKind, CollectionMeta, DerivedSeqView, DerivedSeqViewKind,
};
use crate::encoder::types::sort_for_type;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;

type MultisetNamedTerm = (Cow<'static, str>, Term);
type MultisetAccessInfo = Option<(Term, MultisetNamedTerm)>;

impl<'a> AstExpressionParser<'a> {
    /// Encode `Seq::to_multiset()` as an opaque projection-view carrier (#2600).
    pub(super) fn encode_seq_to_multiset(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        // `|seq.to_multiset()| == |seq|` EXACTLY — `Multiset::len` is the total
        // multiplicity, so every sequence position contributes one. Bind the
        // source length into the result's metadata rather than leaving
        // `len_term: None` and letting `lookup_collection_len`'s name fallback
        // re-derive it: the fallback resolves the BASE receiver's name, which is
        // only accidentally right here and is outright wrong one link further
        // down a chain (`s.to_multiset().insert(x)`).
        let source_len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in to_multiset()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let elem_ty = self
            .resolve_source_elem_ty(receiver_term, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No element type tracking for Seq '{}' in to_multiset()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let elem_sort = sort_for_type(&elem_ty);
        let multiset_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort,
            element_sort: Sort::Int,
        }));
        let result = self.solver.fresh_var("__seq_to_multiset", multiset_sort);
        self.register_collection_meta(
            result,
            CollectionMeta {
                kind: CollectionKind::Multiset,
                len_term: Some(source_len),
                len_guard: None,
                elem_ty: Some(elem_ty.clone()),
                key_ty: None,
                dom_term: None,
            },
        );
        self.register_derived_seq_view(
            result,
            DerivedSeqView {
                kind: DerivedSeqViewKind::MultisetView,
                source_term: receiver_term,
                source_name: receiver_name.map(str::to_owned),
            },
        );
        Ok(result)
    }

    #[allow(clippy::only_used_in_recursion)]
    fn guard_multiset_receiver_access(
        &mut self,
        receiver_term: Term,
        elem: Term,
    ) -> TrustVcResult<()> {
        if let Some((lhs, rhs)) = self.multiset_union_sources.get(&receiver_term).copied() {
            self.guard_multiset_receiver_access(lhs, elem)?;
            self.guard_multiset_receiver_access(rhs, elem)?;
        }
        Ok(())
    }

    fn multiset_add_back_sources(
        &self,
        lhs: Term,
        rhs: Term,
        _rhs_name: Option<&str>,
    ) -> Option<(Term, Term)> {
        if let Some((minuend, subtrahend, subtrahend_name)) =
            self.multiset_difference_sources.get(&lhs)
        {
            let _ = subtrahend_name;
            if *subtrahend == rhs {
                return Some((*minuend, *subtrahend));
            }
        }
        self.multiset_difference_sources
            .get(&rhs)
            .and_then(|(minuend, subtrahend, _)| {
                if *subtrahend == lhs {
                    Some((*minuend, *subtrahend))
                } else {
                    None
                }
            })
    }

    fn assert_multiset_add_back_axiom(
        &mut self,
        result: Term,
        minuend: Term,
        subtrahend: Term,
        elem_ty: &crate::ir::TrustVcType,
    ) -> TrustVcResult<()> {
        let (quant_var, elem_term) = self.safe_element_quantifier("__ms_add_back_elem", elem_ty)?;
        let minuend_count = self
            .solver
            .try_select(minuend, elem_term)
            .map_err(|e| e.to_string())?;
        let subtrahend_count = self
            .solver
            .try_select(subtrahend, elem_term)
            .map_err(|e| e.to_string())?;
        let result_count = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let minuend_ge_subtrahend = self
            .solver
            .try_ge(minuend_count, subtrahend_count)
            .map_err(|e| e.to_string())?;
        let restored_count = self
            .solver
            .try_ite(minuend_ge_subtrahend, minuend_count, subtrahend_count)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_count, restored_count)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(elem_ty, quant_var, body)?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[quant_var], guarded, &[&[result_count]])
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    fn assert_ground_multiset_count_nonnegative(&mut self, count: Term) -> TrustVcResult<()> {
        // The Nat invariant `count >= 0` is sound to assert as a ground fact
        // whenever the element index is fixed — at top level OR at a refutation
        // Skolem witness (a ground constant). The gate is therefore the *symbolic*
        // quantifier depth, NOT `quantifier_depth`: the latter is also bumped by
        // `encode_forall_refutation`, whose witness is ground, so keying off it
        // would drop the Nat fact exactly where a refuted `=~=` over a saturating
        // `sub`/`intersect` needs it (e.g. `a.add(b).sub(b) =~= a`). Inside a
        // genuine `forall`/`exists` the index is symbolic, so a ground assertion
        // would be unsound — the pointwise axioms carry the Nat guard there. #2779.
        if self.symbolic_quantifier_depth != 0 || !matches!(self.solver.term_sort(count), Sort::Int)
        {
            return Ok(());
        }
        let zero = self.solver.int_const(0);
        let nonnegative = self
            .solver
            .try_ge(count, zero)
            .map_err(|e| format!("Multiset count Nat guard: {e}"))?;
        self.solver
            .try_assert_term(nonnegative)
            .map_err(|e| format!("Multiset count Nat guard: {e}").into())
    }

    fn with_multiset_count_nat_guards(
        &mut self,
        body: Term,
        counts: &[Term],
    ) -> TrustVcResult<Term> {
        let zero = self.solver.int_const(0);
        counts.iter().copied().try_fold(body, |acc, count| {
            let nonnegative = self
                .solver
                .try_ge(count, zero)
                .map_err(|e| format!("Multiset quantified count Nat guard: {e}"))?;
            self.solver
                .try_and(nonnegative, acc)
                .map_err(|e| format!("Multiset quantified count Nat guard: {e}").into())
        })
    }

    fn assert_multiset_insert_axioms(
        &mut self,
        source: Term,
        elem: Term,
        new_count: Term,
        result: Term,
        elem_ty: &crate::ir::TrustVcType,
    ) -> TrustVcResult<()> {
        let inserted_count = self
            .solver
            .try_select(result, elem)
            .map_err(|e| format!("Multiset insert axiom: select inserted element: {e}"))?;
        let inserted_eq = self
            .solver
            .try_eq(inserted_count, new_count)
            .map_err(|e| format!("Multiset insert axiom: inserted count equality: {e}"))?;
        self.solver
            .try_assert_term(inserted_eq)
            .map_err(|e| format!("Multiset insert axiom: assert inserted count equality: {e}"))?;

        if self.quantifier_scopes.is_empty() {
            return Ok(());
        }

        let (quant_var, quant_elem) = self.safe_element_quantifier("__ms_insert_elem", elem_ty)?;
        let source_count_at_insert = self
            .solver
            .try_select(source, elem)
            .map_err(|e| format!("Multiset insert axiom: source inserted count: {e}"))?;
        let source_count_at_quant = self
            .solver
            .try_select(source, quant_elem)
            .map_err(|e| format!("Multiset insert axiom: source quantified count: {e}"))?;
        let result_count = self
            .solver
            .try_select(result, quant_elem)
            .map_err(|e| format!("Multiset insert axiom: result quantified count: {e}"))?;
        let one = self.solver.int_const(1);
        let incremented = self
            .solver
            .try_add(source_count_at_insert, one)
            .map_err(|e| format!("Multiset insert axiom: increment count: {e}"))?;
        let is_inserted_elem = self
            .solver
            .try_eq(quant_elem, elem)
            .map_err(|e| format!("Multiset insert axiom: element equality: {e}"))?;
        let expected = self
            .solver
            .try_ite(is_inserted_elem, incremented, source_count_at_quant)
            .map_err(|e| format!("Multiset insert axiom: pointwise count: {e}"))?;
        let body = self
            .solver
            .try_eq(result_count, expected)
            .map_err(|e| format!("Multiset insert axiom: pointwise equality: {e}"))?;
        let body = self.with_multiset_count_nat_guards(
            body,
            &[source_count_at_insert, source_count_at_quant, result_count],
        )?;
        let guarded = self.guard_element_quantifier(elem_ty, quant_var, body)?;
        let axiom = self
            .solver
            .try_forall_with_triggers(&[quant_var], guarded, &[&[result_count]])
            .map_err(|e| format!("Multiset insert axiom: quantified pointwise axiom: {e}"))?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| format!("Multiset insert axiom: assert pointwise axiom: {e}").into())
    }

    fn multiset_len_nonempty_predicate(&mut self, len: Term, context: &str) -> TrustVcResult<Term> {
        match self.solver.term_sort(len) {
            Sort::BitVec(bv_sort) => {
                let zero = self
                    .solver
                    .try_bv_const(0, bv_sort.width)
                    .map_err(|e| format!("{context}: failed to create length zero: {e}"))?;
                let is_zero = self
                    .solver
                    .try_eq(len, zero)
                    .map_err(|e| format!("{context}: failed to build len == 0: {e}"))?;
                self.solver
                    .try_not(is_zero)
                    .map_err(|e| format!("{context}: failed to build len != 0: {e}").into())
            }
            Sort::Int => {
                let zero = self.solver.int_const(0);
                self.solver
                    .try_gt(len, zero)
                    .map_err(|e| format!("{context}: failed to build len > 0: {e}").into())
            }
            other => Err(
                format!("{context} requires numeric length metadata, got sort {other:?}").into(),
            ),
        }
    }

    pub(super) fn assert_multiset_nonempty_count_witness(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<()> {
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        let Some(len) = self.exact_multiset_len(receiver_term, receiver_name)? else {
            return Ok(());
        };

        let receiver_sort = self.solver.term_sort(receiver_term);
        let return_sort = sort_for_type(&elem_ty);
        let key = format!("multiset_choose::{}", elem_ty.to_type_string());

        let Some(registry) = self.choose_registry.as_mut() else {
            return Ok(());
        };
        let choose_decl = if let Some(existing) = registry.get(&key).cloned() {
            existing
        } else {
            let decl_name = format!("__trust_vc_multiset_choose_{}", registry.len());
            let decl = self
                .solver
                .try_declare_fun(
                    &decl_name,
                    std::slice::from_ref(&receiver_sort),
                    return_sort,
                )
                .map_err(|e| format!("Multiset nonempty witness: failed to declare UF: {e}"))?;
            registry.insert(key, decl.clone());
            decl
        };

        let chosen = self
            .solver
            .try_apply(&choose_decl, &[receiver_term])
            .map_err(|e| format!("Multiset nonempty witness: failed to apply UF: {e}"))?;

        let len_nonempty =
            self.multiset_len_nonempty_predicate(len, "Multiset nonempty witness")?;
        let count = self
            .solver
            .try_select(receiver_term, chosen)
            .map_err(|e| format!("Multiset nonempty witness: failed to select count: {e}"))?;
        let zero_count = self.solver.int_const(0);
        let count_positive = self
            .solver
            .try_gt(count, zero_count)
            .map_err(|e| format!("Multiset nonempty witness: failed to build count > 0: {e}"))?;
        let axiom = self
            .solver
            .try_implies(len_nonempty, count_positive)
            .map_err(|e| format!("Multiset nonempty witness: failed to build axiom: {e}"))?;
        self.solver.try_assert_term(axiom).map_err(|e| {
            format!("Multiset nonempty witness: failed to assert nonempty axiom: {e}").into()
        })
    }

    #[allow(clippy::only_used_in_recursion)]
    fn multiset_access_well_formed(
        &mut self,
        receiver_term: Term,
        elem: Term,
    ) -> TrustVcResult<Term> {
        let mut wf = self.solver.bool_const(true);
        if let Some(sources) = self.multiset_operand_sources.get(&receiver_term).cloned() {
            for source in sources {
                let source_wf = self.multiset_access_well_formed(source, elem)?;
                wf = self
                    .solver
                    .try_and(wf, source_wf)
                    .map_err(|e| e.to_string())?;
            }
        }
        if let Some((lhs, rhs)) = self.multiset_union_sources.get(&receiver_term).copied() {
            let lhs_wf = self.multiset_access_well_formed(lhs, elem)?;
            let rhs_wf = self.multiset_access_well_formed(rhs, elem)?;
            let union_wf = self
                .solver
                .try_and(lhs_wf, rhs_wf)
                .map_err(|e| e.to_string())?;
            wf = self
                .solver
                .try_and(wf, union_wf)
                .map_err(|e| e.to_string())?;
        }
        Ok(wf)
    }

    /// `ms.count(v)` → `select(ms, v)` (returns Nat/Int count)
    pub(super) fn encode_multiset_count(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!("count() expects 1 argument, got {}", args.len()).into());
        };
        if let Some(view) = self.lookup_derived_seq_view(receiver_term) {
            if view.kind == DerivedSeqViewKind::MultisetView {
                let needle = self.encode_multiset_key_arg(arg, receiver_term, receiver_name)?;
                return self.encode_seq_occurrence_count(
                    view.source_term,
                    view.source_name.as_deref(),
                    needle,
                );
            }
        }
        let elem = self.encode_multiset_key_arg(arg, receiver_term, receiver_name)?;
        self.guard_multiset_receiver_access(receiver_term, elem)?;
        self.multiset_count_at(receiver_term, elem)
    }

    /// Compute `count(receiver, elem)` compositionally as a quantifier-free
    /// arithmetic term over the operand counts, recursing through the registered
    /// union / difference / intersect provenance and bottoming out at a leaf
    /// `select(leaf, elem)` (which is also ground for `insert`/`remove`, since
    /// those are array `store`s decided by the array theory).
    ///
    /// This is the witness-extraction enabler for #2779: with a ground count term
    /// the extensional-equality refutation's body `count(lhs, w) != count(rhs, w)`
    /// is quantifier-free, so a genuinely false `=~=` yields a concrete differing
    /// model (Counterexample) instead of being blocked by the MBQI-unsafe
    /// array-indexing pointwise `forall` axioms. The compositional identities are
    /// exactly the pointwise multiset semantics, so this is sound, and the Nat
    /// guard on each leaf keeps saturating `sub`/`intersect` correct.
    fn multiset_count_at(&mut self, receiver: Term, elem: Term) -> TrustVcResult<Term> {
        // union(lhs, rhs): count = count(lhs) + count(rhs). This also subsumes the
        // "add-back" identity `union(diff(a,b), b)` — summing the saturating
        // difference with the subtrahend reproduces `max(a, b)` pointwise.
        if let Some((lhs, rhs)) = self.multiset_union_sources.get(&receiver).copied() {
            let lhs_count = self.multiset_count_at(lhs, elem)?;
            let rhs_count = self.multiset_count_at(rhs, elem)?;
            let sum = self
                .solver
                .try_add(lhs_count, rhs_count)
                .map_err(|e| e.to_string())?;
            self.assert_ground_multiset_count_nonnegative(sum)?;
            return Ok(sum);
        }
        // difference(minuend, subtrahend): saturating subtraction
        // `ite(min > sub, min - sub, 0)`.
        if let Some((minuend, subtrahend, _)) =
            self.multiset_difference_sources.get(&receiver).cloned()
        {
            let min_count = self.multiset_count_at(minuend, elem)?;
            let sub_count = self.multiset_count_at(subtrahend, elem)?;
            let gt = self
                .solver
                .try_gt(min_count, sub_count)
                .map_err(|e| e.to_string())?;
            let diff = self
                .solver
                .try_sub(min_count, sub_count)
                .map_err(|e| e.to_string())?;
            let zero = self.solver.int_const(0);
            let saturated = self
                .solver
                .try_ite(gt, diff, zero)
                .map_err(|e| e.to_string())?;
            self.assert_ground_multiset_count_nonnegative(saturated)?;
            return Ok(saturated);
        }
        // intersect(lhs, rhs): pointwise minimum `ite(lhs < rhs, lhs, rhs)`.
        if let Some((lhs, rhs)) = self.multiset_intersect_sources.get(&receiver).copied() {
            let lhs_count = self.multiset_count_at(lhs, elem)?;
            let rhs_count = self.multiset_count_at(rhs, elem)?;
            let lt = self
                .solver
                .try_lt(lhs_count, rhs_count)
                .map_err(|e| e.to_string())?;
            let min_val = self
                .solver
                .try_ite(lt, lhs_count, rhs_count)
                .map_err(|e| e.to_string())?;
            self.assert_ground_multiset_count_nonnegative(min_val)?;
            return Ok(min_val);
        }
        // Leaf multiset (variable, empty, singleton) or an `insert`/`remove`
        // store: a direct array select. For stores the array theory rewrites the
        // select to a ground `ite`, so no pointwise `forall` is needed.
        let count = self
            .solver
            .try_select(receiver, elem)
            .map_err(|e| e.to_string())?;
        self.assert_ground_multiset_count_nonnegative(count)?;
        Ok(count)
    }

    /// `ms.choose()` → deterministic witness term with guarded membership.
    ///
    /// Verus only exposes a membership fact for non-empty multisets. Encoding
    /// this as an unguarded `choose!(|x| ms.contains(x))` would be unsound for
    /// empty multisets, so this UF is constrained only by:
    ///
    /// `ms.len() != 0 ==> ms.count(ms.choose()) > 0`.
    pub(super) fn encode_multiset_choose(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if !args.is_empty() {
            return Err(
                format!("Multiset::choose() expects 0 arguments, got {}", args.len()).into(),
            );
        }

        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        let len = self
            .exact_multiset_len(receiver_term, receiver_name)?
            .ok_or_else(|| {
                format!(
                    "Multiset::choose() requires exact length metadata for '{}'",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        self.emit_collection_len_guard(receiver_term);

        let receiver_sort = self.solver.term_sort(receiver_term);
        let return_sort = sort_for_type(&elem_ty);
        let key = format!("multiset_choose::{}", elem_ty.to_type_string());

        let existing = self
            .choose_registry
            .as_ref()
            .and_then(|registry| registry.get(&key).cloned());
        let choose_decl = if let Some(existing) = existing {
            existing
        } else {
            let decl_name = {
                let registry = self.choose_registry.as_ref().ok_or_else(|| {
                    "Multiset::choose(): no choose_registry available (internal error)".to_string()
                })?;
                format!("__trust_vc_multiset_choose_{}", registry.len())
            };
            let decl = self
                .solver
                .try_declare_fun(
                    &decl_name,
                    std::slice::from_ref(&receiver_sort),
                    return_sort,
                )
                .map_err(|e| format!("Multiset::choose(): failed to declare UF: {e}"))?;
            let registry = self.choose_registry.as_mut().ok_or_else(|| {
                "Multiset::choose(): no choose_registry available (internal error)".to_string()
            })?;
            registry.insert(key, decl.clone());
            decl
        };

        let chosen = self
            .solver
            .try_apply(&choose_decl, &[receiver_term])
            .map_err(|e| format!("Multiset::choose(): failed to apply UF: {e}"))?;

        let len_nonempty = self.multiset_len_nonempty_predicate(len, "Multiset::choose()")?;
        let count = self
            .solver
            .try_select(receiver_term, chosen)
            .map_err(|e| format!("Multiset::choose(): failed to select chosen count: {e}"))?;
        let zero_count = self.solver.int_const(0);
        let count_positive = self
            .solver
            .try_gt(count, zero_count)
            .map_err(|e| format!("Multiset::choose(): failed to build count > 0: {e}"))?;
        let axiom = self
            .solver
            .try_implies(len_nonempty, count_positive)
            .map_err(|e| format!("Multiset::choose(): failed to build membership axiom: {e}"))?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| format!("Multiset::choose(): failed to assert membership axiom: {e}"))?;

        if let Some(width) = elem_ty.bit_width() {
            if width > 0 {
                let signed = matches!(elem_ty, crate::ir::TrustVcType::Int { .. });
                self.term_widths.insert(chosen, (width, signed));
            }
        }

        Ok(chosen)
    }

    /// `ms.insert(v)` → `store(ms, v, select(ms, v) + 1)`
    pub(super) fn encode_multiset_insert(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(
                format!("Multiset::insert() expects 1 argument, got {}", args.len()).into(),
            );
        };
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        let elem = self.encode_multiset_key_arg(arg, receiver_term, receiver_name)?;
        self.guard_multiset_receiver_access(receiver_term, elem)?;
        let old_count = self
            .solver
            .try_select(receiver_term, elem)
            .map_err(|e| e.to_string())?;
        let one = self.solver.int_const(1);
        let new_count = self
            .solver
            .try_add(old_count, one)
            .map_err(|e| e.to_string())?;
        let result = self
            .solver
            .try_store(receiver_term, elem, new_count)
            .map_err(|e| e.to_string())?;
        self.assert_multiset_insert_axioms(receiver_term, elem, new_count, result, &elem_ty)?;
        let len_meta = self.multiset_insert_len_metadata(receiver_term, receiver_name)?;
        self.register_multiset_meta(result, receiver_term, receiver_name, len_meta);
        self.register_multiset_operand_sources(result, &[receiver_term]);
        Ok(result)
    }

    /// `ms.remove(v)` → `store(ms, v, ite(count > 0, count - 1, 0))`
    pub(super) fn encode_multiset_remove(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(
                format!("Multiset::remove() expects 1 argument, got {}", args.len()).into(),
            );
        };
        let elem = self.encode_multiset_key_arg(arg, receiver_term, receiver_name)?;
        self.guard_multiset_receiver_access(receiver_term, elem)?;
        let old_count = self
            .solver
            .try_select(receiver_term, elem)
            .map_err(|e| e.to_string())?;
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        let decremented = self
            .solver
            .try_sub(old_count, one)
            .map_err(|e| e.to_string())?;
        let is_positive = self
            .solver
            .try_gt(old_count, zero)
            .map_err(|e| e.to_string())?;
        let new_count = self
            .solver
            .try_ite(is_positive, decremented, zero)
            .map_err(|e| e.to_string())?;
        let result = self
            .solver
            .try_store(receiver_term, elem, new_count)
            .map_err(|e| e.to_string())?;
        // `|ms.remove(v)| == |ms| - ite(count(ms, v) > 0, 1, 0)`. That IS
        // computable, but it is a capability add rather than the soundness fix;
        // DECLINE keeps it fail-closed. (Before this, the name fallback answered
        // `a.remove(x).len()` with `a.len()` — false whenever `x` is present.)
        self.register_multiset_meta(result, receiver_term, receiver_name, None);
        self.register_multiset_operand_sources(result, &[receiver_term]);
        Ok(result)
    }

    /// `ms.union(other)` → pointwise addition:
    /// `forall k. select(result, k) == select(ms, k) + select(other, k)`
    pub(super) fn encode_multiset_union(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
        _receiver_expr: Option<&TrustVcExpr>,
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!(
                "Multiset::union() requires exactly 1 argument, got {}",
                args.len()
            )
            .into());
        };
        let other = self.encode_subexpr(arg)?;
        let other_name = multiset_argument_name(arg);
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        self.ensure_matching_multiset_operand(other, other_name, &elem_ty, "Multiset::union()")?;
        let elem_sort = sort_for_type(&elem_ty);

        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort,
            element_sort: Sort::Int,
        }));
        let result = self.solver.fresh_var("__multiset_union", result_sort);

        // Safe quantification: native-sorted bound var (#2531)
        let (quant_var, elem_term) = self.safe_element_quantifier("__ms_elem", &elem_ty)?;

        let self_count = self
            .solver
            .try_select(receiver_term, elem_term)
            .map_err(|e| e.to_string())?;
        let other_count = self
            .solver
            .try_select(other, elem_term)
            .map_err(|e| e.to_string())?;
        let result_count = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let sum = self
            .solver
            .try_add(self_count, other_count)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_count, sum)
            .map_err(|e| e.to_string())?;
        let body =
            self.with_multiset_count_nat_guards(body, &[self_count, other_count, result_count])?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body)?;
        // Register provenance unconditionally so `count` reads decompose
        // compositionally (#2779). The pointwise `forall` axiom indexes an array
        // at its binder, so ay treats it as MBQI-unsafe and degrades to `Unknown`
        // ANY SAT it is in scope for — which would block a false `=~=`'s concrete
        // counterexample. Emit it ONLY in assumption context, where a downstream
        // proof step may read `select(result, k)` symbolically (e.g. a composite
        // `subset_of`) and the ground compositional identity does not apply. For a
        // GOAL — including the positive overflow-prediction pass that shares the
        // refutation's solver scope, and the negated-goal refutation itself —
        // compositional `count` fully determines every read, so suppressing the
        // axiom lets ay exhibit a genuine differing-count witness.
        self.multiset_union_sources
            .insert(result, (receiver_term, other));
        if self.in_assumption_context {
            // Trigger on `select(result, k)` (mirrors insert / add_back).
            let axiom = self
                .solver
                .try_forall_with_triggers(&[quant_var], guarded, &[&[result_count]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| e.to_string())?;
            if let Some((minuend, subtrahend)) =
                self.multiset_add_back_sources(receiver_term, other, other_name)
            {
                self.assert_multiset_add_back_axiom(result, minuend, subtrahend, &elem_ty)?;
            }
        }

        // EXACT cardinality: `|a.union(b)| == |a| + |b|` (total multiplicity,
        // pointwise sum). `None` when either operand's own length is unknown,
        // and `register_multiset_meta` then DECLINES — without that decline the
        // name fallback answers `a.union(b).len()` with `a.len()` (FV-3's
        // Multiset arm).
        let len_meta =
            self.multiset_union_len_metadata(receiver_term, receiver_name, other, other_name)?;
        self.register_multiset_meta(result, receiver_term, receiver_name, len_meta);
        self.register_multiset_operand_sources(result, &[receiver_term, other]);
        Ok(result)
    }

    /// `ms.intersect(other)` → pointwise minimum:
    /// `forall k. select(result, k) == ite(self_k < other_k, self_k, other_k)`
    pub(super) fn encode_multiset_intersect(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!(
                "Multiset::intersect() requires exactly 1 argument, got {}",
                args.len()
            )
            .into());
        };
        let other = self.encode_subexpr(arg)?;
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        self.ensure_matching_multiset_operand(
            other,
            multiset_argument_name(arg),
            &elem_ty,
            "Multiset::intersect()",
        )?;
        let elem_sort = sort_for_type(&elem_ty);

        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort,
            element_sort: Sort::Int,
        }));
        let result = self.solver.fresh_var("__multiset_intersect", result_sort);

        // Safe quantification: native-sorted bound var (#2531)
        let (quant_var, elem_term) = self.safe_element_quantifier("__ms_elem", &elem_ty)?;

        let self_count = self
            .solver
            .try_select(receiver_term, elem_term)
            .map_err(|e| e.to_string())?;
        let other_count = self
            .solver
            .try_select(other, elem_term)
            .map_err(|e| e.to_string())?;
        let result_count = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let self_lt_other = self
            .solver
            .try_lt(self_count, other_count)
            .map_err(|e| e.to_string())?;
        let min_val = self
            .solver
            .try_ite(self_lt_other, self_count, other_count)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_count, min_val)
            .map_err(|e| e.to_string())?;
        let body =
            self.with_multiset_count_nat_guards(body, &[self_count, other_count, result_count])?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body)?;
        // Register provenance unconditionally for compositional `count`; emit the
        // MBQI-unsafe pointwise `forall` only in assumption context (see union).
        self.multiset_intersect_sources
            .insert(result, (receiver_term, other));
        if self.in_assumption_context {
            // Trigger on `select(result, k)` (see union for rationale).
            let axiom = self
                .solver
                .try_forall_with_triggers(&[quant_var], guarded, &[&[result_count]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| e.to_string())?;
        }

        // Pointwise MIN: the total is the sum of `min(a_k, b_k)`, which is not
        // a function of `|a|` and `|b|` — DECLINE (via `register_multiset_meta`)
        // rather than approximate. Unconstrained is sound; the false
        // `a.intersect(b).len() == a.len()` stops verifying.
        self.register_multiset_meta(result, receiver_term, receiver_name, None);
        self.register_multiset_operand_sources(result, &[receiver_term, other]);
        Ok(result)
    }

    /// `ms.difference(other)` / `ms.sub(other)` → pointwise saturating subtraction:
    /// `forall k. select(result, k) == ite(self_k > other_k, self_k - other_k, 0)`
    ///
    /// Fixes #2604: Multiset difference was routing to the Set handler, which
    /// uses boolean difference semantics (`A(x) && !B(x)`). Multiset difference
    /// uses saturating count subtraction: `max(0, count_A(x) - count_B(x))`.
    pub(super) fn encode_multiset_difference(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!(
                "Multiset::difference() requires exactly 1 argument, got {}",
                args.len()
            )
            .into());
        };
        let other = self.encode_subexpr(arg)?;
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        self.ensure_matching_multiset_operand(
            other,
            multiset_argument_name(arg),
            &elem_ty,
            "Multiset::difference()",
        )?;
        let elem_sort = sort_for_type(&elem_ty);

        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort,
            element_sort: Sort::Int,
        }));
        let result = self.solver.fresh_var("__multiset_difference", result_sort);

        // Safe quantification: native-sorted bound var (#2531)
        let (quant_var, elem_term) = self.safe_element_quantifier("__ms_elem", &elem_ty)?;

        let self_count = self
            .solver
            .try_select(receiver_term, elem_term)
            .map_err(|e| e.to_string())?;
        let other_count = self
            .solver
            .try_select(other, elem_term)
            .map_err(|e| e.to_string())?;
        let result_count = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let zero = self.solver.int_const(0);
        let self_gt_other = self
            .solver
            .try_gt(self_count, other_count)
            .map_err(|e| e.to_string())?;
        let subtracted = self
            .solver
            .try_sub(self_count, other_count)
            .map_err(|e| e.to_string())?;
        // max(0, self - other): if self > other then self - other else 0
        let saturated = self
            .solver
            .try_ite(self_gt_other, subtracted, zero)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_eq(result_count, saturated)
            .map_err(|e| e.to_string())?;
        let body =
            self.with_multiset_count_nat_guards(body, &[self_count, other_count, result_count])?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body)?;
        // Emit the MBQI-unsafe pointwise `forall` only in assumption context;
        // compositional `count` covers the goal/refutation context (#2779).
        // Provenance (registered below) is always recorded.
        if self.in_assumption_context {
            // Trigger on `select(result, k)` (see union for rationale).
            let axiom = self
                .solver
                .try_forall_with_triggers(&[quant_var], guarded, &[&[result_count]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| e.to_string())?;
        }

        self.multiset_difference_sources.insert(
            result,
            (
                receiver_term,
                other,
                multiset_argument_name(arg).map(str::to_owned),
            ),
        );
        // Pointwise SATURATING subtraction: the total is the sum of
        // `max(0, a_k - b_k)`, which is not `|a| - |b|` (it is `>=` it, and
        // clamps per element) — DECLINE.
        self.register_multiset_meta(result, receiver_term, receiver_name, None);
        self.register_multiset_operand_sources(result, &[receiver_term, other]);
        Ok(result)
    }

    /// `ms.subset_of(other)` / `ms.subset(other)` / `ms.is_subset(other)`.
    ///
    /// # Encoding (native multiset theory, sound-or-Unknown)
    ///
    /// In the **assertion (goal)** context the subset obligation is emitted as a
    /// single native `(multiset.subset self other)` Bool atom and handed to ay's
    /// finite-multiset theory (QF_MSLIA). The atom carries the count read-through
    /// `Multiset(T) = Array(T -> Int)` that trust-vc already uses, so ay decides:
    ///
    /// * **reflexivity** — `m.subset_of(m)` is valid; ay refutes its negation
    ///   structurally with **no quantifier instantiation (no MBQI)** — the win
    ///   this flip unlocks.
    /// * **ground-witness refutation** — when a present element `e` has
    ///   `count(self, e) > count(other, e)`, the executor-injected
    ///   `subset => count(self,e) <= count(other,e)` obligation refutes the goal
    ///   over that single ground witness (again no MBQI).
    /// * **unconstrained** subset never decides true (ground witnesses cannot
    ///   certify a universal), so an unconstrained goal fails closed — matching
    ///   the prior quantified encoding's fail-closed behaviour.
    ///
    /// If the surrounding obligation introduces other quantifiers, ay routes to
    /// a quantified logic where `multiset.subset` degrades to an opaque UF; an
    /// opaque-UF *goal* still fails closed (sound — it can never be proven from
    /// nothing), so the native atom is sound there too, just less complete.
    ///
    /// In the **assumption** context we keep the full quantified universal
    /// `forall k. count(self, k) <= count(other, k)`: downstream count
    /// obligations at arbitrary `k` (e.g. `a.sub(b).add(b).count(k)`) need the
    /// universal fact, which the native ground-witness implication — restricted
    /// to elements with count reads already present — is too weak to supply. The
    /// assumption-side universal is asserted positively (sound) and is the
    /// strongest fact a subset hypothesis can license.
    pub(super) fn encode_multiset_subset(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!(
                "Multiset::subset_of() requires exactly 1 argument, got {}",
                args.len()
            )
            .into());
        };
        let other = self.encode_subexpr(arg)?;
        let other_name = match arg {
            TrustVcExpr::Var { name, .. } => Some(name.as_str()),
            _ => None,
        };
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        let other_elem_ty = self.multiset_element_trust_vc_type(other, other_name)?;
        if other_elem_ty != elem_ty {
            return Err(format!(
                "Multiset::subset_of() requires matching element types, got lhs {:?} and rhs {:?}",
                elem_ty, other_elem_ty
            )
            .into());
        }

        let assumption_context = self.in_assumption_context;

        // Assertion (goal) context: native ground-witness / reflexivity atom,
        // decided without MBQI by ay's multiset theory when quantifier-free.
        if !assumption_context {
            return self.encode_native_multiset_subset_atom(receiver_term, other);
        }

        // Assumption context: keep the quantified universal so downstream count
        // obligations at arbitrary elements remain provable. (The assertion
        // branch returned above, so we are always in the assumption case here.)
        let (quant_var, elem_term) = self.safe_element_quantifier("__ms_subset_elem", &elem_ty)?;
        let self_wf = self.multiset_access_well_formed(receiver_term, elem_term)?;
        let other_wf = self.multiset_access_well_formed(other, elem_term)?;
        let self_count = self
            .solver
            .try_select(receiver_term, elem_term)
            .map_err(|e| e.to_string())?;
        let other_count = self
            .solver
            .try_select(other, elem_term)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_le(self_count, other_count)
            .map_err(|e| e.to_string())?;
        let operands_wf = self
            .solver
            .try_and(self_wf, other_wf)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_and(operands_wf, body)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body)?;

        self.solver
            .try_forall_with_triggers(&[quant_var], guarded, &[&[self_count], &[other_count]])
            .map_err(|e| e.to_string().into())
    }

    /// Build a native `(multiset.subset sub sup)` Bool atom over the count
    /// carrier `Multiset(T) = Array(T -> Int)`.
    ///
    /// Declares the polymorphic `multiset.subset` symbol over the carrier sorts
    /// of `sub`/`sup` and applies it. ay's feature detection routes any
    /// quantifier-free formula carrying a `multiset.*` symbol to QF_MSLIA, where
    /// the atom is decided by the native finite-multiset procedure: reflexivity
    /// plus the executor-injected `subset => count(sub,e) <= count(sup,e)`
    /// ground-witness obligations. No quantified count axiom is emitted, so the
    /// goal stays quantifier-free and decides without MBQI.
    ///
    /// Soundness contract (sound-or-Unknown): the native procedure never asserts
    /// a positive subset from ground saturation over the unbounded element
    /// domain, so an unconstrained goal does not verify (fails closed). When the
    /// surrounding obligation forces a quantified logic the atom degrades to an
    /// opaque UF goal, which likewise cannot be proven from nothing (sound,
    /// incomplete).
    fn encode_native_multiset_subset_atom(&mut self, sub: Term, sup: Term) -> TrustVcResult<Term> {
        let sub_sort = self.solver.term_sort(sub);
        let sup_sort = self.solver.term_sort(sup);
        let decl = self
            .solver
            .try_declare_fun("multiset.subset", &[sub_sort, sup_sort], Sort::Bool)
            .map_err(|e| format!("Multiset::subset_of: failed to declare multiset.subset: {e}"))?;
        self.solver.try_apply(&decl, &[sub, sup]).map_err(|e| {
            format!("Multiset::subset_of: failed to apply multiset.subset: {e}").into()
        })
    }

    fn encode_multiset_key_arg(
        &mut self,
        arg: &TrustVcExpr,
        receiver_term: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let elem_ty = self.multiset_element_trust_vc_type(receiver_term, receiver_name)?;
        let elem = self.encode_expr_with_integer_hint(arg, Some(&elem_ty))?;
        self.coerce_key_for_store_in_int_mode(elem, receiver_term, receiver_name)
    }

    /// Resolve the element TrustVcType for a Multiset<T> receiver.
    fn multiset_element_trust_vc_type(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<crate::ir::TrustVcType> {
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if meta.kind != CollectionKind::Multiset {
                return Err(format!(
                    "Expected Multiset<T> operand, got collection kind {:?}",
                    meta.kind
                )
                .into());
            }
            return meta.elem_ty.clone().ok_or_else(|| {
                "Multiset operation requires collection metadata with an element type"
                    .to_string()
                    .into()
            });
        }
        let ty = receiver_name
            .and_then(|name| {
                self.local_var_types
                    .get(name)
                    .or_else(|| self.var_types.get(name))
            })
            .ok_or_else(|| {
                "Multiset operation requires a named receiver with known type".to_string()
            })?;
        match ty {
            crate::ir::TrustVcType::Multiset(elem) => Ok((**elem).clone()),
            _ => Err(format!("Expected Multiset<T> type, got: {:?}", ty).into()),
        }
    }

    /// Exact Multiset length lookup that avoids reusing a source variable's
    /// length for anonymous derived terms.
    fn exact_multiset_len(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Option<Term>> {
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if meta.kind != CollectionKind::Multiset {
                return Err(format!(
                    "Expected Multiset<T> metadata, got collection kind {:?}",
                    meta.kind
                )
                .into());
            }
            if let Some(len) = meta.len_term {
                return Ok(Some(len));
            }
            return Ok(receiver_name
                .filter(|name| self.variables.get(*name).copied() == Some(receiver))
                .and_then(|name| self.collection_lengths.get(name).copied()));
        }
        Ok(receiver_name.and_then(|name| self.collection_lengths.get(name).copied()))
    }

    /// Exact length metadata for `ms.insert(v)`:
    /// `len(ms.insert(v)) == len(ms) + 1`, guarded against usize wrap.
    fn multiset_insert_len_metadata(
        &mut self,
        source: Term,
        source_name: Option<&str>,
    ) -> TrustVcResult<MultisetAccessInfo> {
        let Some(old_len) = self.exact_multiset_len(source, source_name)? else {
            return Ok(None);
        };
        match self.solver.term_sort(old_len) {
            Sort::Int => {
                // Route A (#2779): unbounded Int length. `old + 1` is monotone,
                // so the "Multiset insert length no overflow" obligation is a BV
                // wrap artifact and vanishes (MAX+1 != 0 over Int — the near-MAX
                // vacuity guard therefore stays correctly fail-closed). Return a
                // trivially-true guard for the OverflowCheck plumbing.
                let one = self.solver.int_const(1);
                let new_len = self
                    .solver
                    .try_add(old_len, one)
                    .map_err(|e| format!("Multiset insert length increment: {e}"))?;
                let truth = self.solver.bool_const(true);
                Ok(Some((
                    new_len,
                    ("Multiset insert length no overflow".into(), truth),
                )))
            }
            Sort::BitVec(len_sort) => {
                let one = self
                    .solver
                    .try_bv_const(1, len_sort.width)
                    .map_err(|e| format!("Multiset insert length increment: {e}"))?;
                let new_len = self
                    .solver
                    .try_bvadd(old_len, one)
                    .map_err(|e| format!("Multiset insert length increment: {e}"))?;
                self.term_widths.insert(new_len, (len_sort.width, false));
                let no_overflow = self
                    .solver
                    .try_bvugt(new_len, old_len)
                    .map_err(|e| format!("Multiset insert length overflow guard: {e}"))?;
                Ok(Some((
                    new_len,
                    ("Multiset insert length no overflow".into(), no_overflow),
                )))
            }
            other => Err(format!(
                "Multiset::insert() requires numeric length metadata, got {other:?}"
            )
            .into()),
        }
    }

    /// Exact length metadata for `ms.union(other)` / `ms.add(other)`:
    /// `len(a.union(b)) == len(a) + len(b)`.
    ///
    /// `Multiset::len` is the TOTAL multiplicity (`trust_vc_types::Multiset::len`
    /// — "returns the total element count") and `union` is the pointwise SUM
    /// (see `encode_multiset_union`'s axiom), so additivity is exact, not an
    /// approximation. This is the one derived-Multiset cell whose cardinality is
    /// computable: `intersect` needs a pointwise `min` sum, `difference` a
    /// saturating one, and neither is a function of the two total counts — those
    /// decline.
    ///
    /// Returns `None` (⇒ the caller declines) whenever either operand's own
    /// cardinality is unknown, so a declined source can never be laundered into
    /// a known sum.
    fn multiset_union_len_metadata(
        &mut self,
        lhs: Term,
        lhs_name: Option<&str>,
        rhs: Term,
        rhs_name: Option<&str>,
    ) -> TrustVcResult<MultisetAccessInfo> {
        let Some(lhs_len) = self.exact_multiset_len(lhs, lhs_name)? else {
            return Ok(None);
        };
        let Some(rhs_len) = self.exact_multiset_len(rhs, rhs_name)? else {
            return Ok(None);
        };
        match (
            self.solver.term_sort(lhs_len),
            self.solver.term_sort(rhs_len),
        ) {
            (Sort::Int, Sort::Int) => {
                // Route A (#2779): unbounded Int length; `+` is exact, so the
                // wrap obligation is vacuous (mirrors `insert`).
                let sum = self
                    .solver
                    .try_add(lhs_len, rhs_len)
                    .map_err(|e| format!("Multiset union length sum: {e}"))?;
                let truth = self.solver.bool_const(true);
                Ok(Some((
                    sum,
                    ("Multiset union length no overflow".into(), truth),
                )))
            }
            (Sort::BitVec(l), Sort::BitVec(r)) if l.width == r.width => {
                let sum = self
                    .solver
                    .try_bvadd(lhs_len, rhs_len)
                    .map_err(|e| format!("Multiset union length sum: {e}"))?;
                self.term_widths.insert(sum, (l.width, false));
                let no_overflow = self
                    .solver
                    .try_bvuge(sum, lhs_len)
                    .map_err(|e| format!("Multiset union length overflow guard: {e}"))?;
                Ok(Some((
                    sum,
                    ("Multiset union length no overflow".into(), no_overflow),
                )))
            }
            // Mixed or non-numeric length sorts: decline rather than coerce.
            _ => Ok(None),
        }
    }

    /// Register collection metadata for a Multiset result term.
    ///
    /// Every caller passes a term produced by a Multiset operation — an
    /// ANONYMOUS `fresh_var` (`union`/`intersect`/`difference`) or an array
    /// `store` (`insert`/`remove`) — never a declared variable. So when the
    /// exact cardinality is unavailable (`len_meta == None`) the result must
    /// also be entered in `len_declined_terms`: `lookup_collection_len`'s name
    /// fallback keys on `lowered_receiver_name`, which walks a chained
    /// `CollectionOp` down to its BASE receiver, and would otherwise answer
    /// `a.union(b).len()` with `a.len()` (FV-3's Multiset arm — cardinal, fully
    /// inverted: `a.len() == 2 /\ b.len() == 3 |- a.union(b).len() == 2`
    /// verified, and the true `== 5` did not).
    ///
    /// This is the single funnel for the whole Multiset arm: `insert`, `remove`,
    /// `union`/`add`, `intersect` and `difference`/`sub` all pass through here.
    fn register_multiset_meta(
        &mut self,
        result: Term,
        source: Term,
        source_name: Option<&str>,
        len_meta: Option<(Term, (Cow<'static, str>, Term))>,
    ) {
        let elem_ty = self.resolve_source_elem_ty(source, source_name);
        let (len_term, len_guard) = match len_meta {
            Some((len, guard)) => (Some(len), Some(guard)),
            None => (None, None),
        };
        self.register_collection_meta(
            result,
            CollectionMeta {
                kind: CollectionKind::Multiset,
                len_term,
                len_guard,
                elem_ty,
                key_ty: None,
                dom_term: None,
            },
        );
        if len_term.is_none() {
            self.decline_collection_len(result);
        }
    }

    fn ensure_matching_multiset_operand(
        &self,
        operand: Term,
        operand_name: Option<&str>,
        expected_elem_ty: &crate::ir::TrustVcType,
        operation: &str,
    ) -> TrustVcResult<()> {
        let operand_elem_ty = self.multiset_element_trust_vc_type(operand, operand_name)?;
        if operand_elem_ty == *expected_elem_ty {
            return Ok(());
        }
        Err(format!(
            "{operation} requires matching Multiset element types, got lhs {:?} and rhs {:?}",
            expected_elem_ty, operand_elem_ty
        )
        .into())
    }

    fn register_multiset_operand_sources(&mut self, result: Term, sources: &[Term]) {
        self.multiset_operand_sources
            .insert(result, sources.to_vec());
    }
}

fn multiset_argument_name(arg: &TrustVcExpr) -> Option<&str> {
    match arg {
        TrustVcExpr::Var { name, .. } => Some(name.as_str()),
        _ => None,
    }
}
