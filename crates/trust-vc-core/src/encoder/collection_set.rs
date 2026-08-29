//! Set-specific collection encoding (subset, superset, union, intersect, difference).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Higher-order operations (mk_map, fold) are in `collection_set_higher.rs` (#2621).

use ay_dpll::api::{ArraySort, Sort, Term};

use super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;

impl<'a> AstExpressionParser<'a> {
    /// Encode `Set::finite()`.
    ///
    /// Assertions over unbounded element domains still fail closed because the
    /// backend does not encode a true finite-cardinality relation. Assumptions
    /// may mention `finite()` as a precondition without gaining extra facts;
    /// this is sound and lets proofs proceed when they rely on other evidence
    /// such as tracked `len() > 0` metadata.
    pub(super) fn encode_set_finite(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if !args.is_empty() {
            return Err(format!("Set::finite() expects 0 arguments, got {}", args.len()).into());
        }
        if let Some(view) = self.lookup_derived_seq_view(receiver) {
            if view.kind == super::parser_state::DerivedSeqViewKind::SetView {
                let source_name = view.source_name.as_deref();
                self.lookup_collection_len(view.source_term, source_name)
                    .ok_or_else(|| {
                        format!(
                            "No length tracking for Seq '{}' in derived Set finite()",
                            source_name.unwrap_or("<anonymous>")
                        )
                    })?;
                return Ok(self.solver.bool_const(true));
            }
        }
        let elem_ty = self.set_element_trust_vc_type(receiver, receiver_name)?;
        if !set_element_has_finite_backend_domain(&elem_ty) {
            if self.in_assumption_context {
                return Ok(self.solver.bool_const(true));
            }
            return Err(format!(
                "Set::finite() is unsupported for Set<{}>: TrustVc does not encode finite cardinality for unbounded element domains",
                elem_ty.to_type_string()
            )
            .into());
        }
        Ok(self.solver.bool_const(true))
    }

    /// Encode `Seq::to_set()` as a lightweight derived set term (#2600).
    pub(super) fn encode_seq_to_set(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        self.lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in to_set()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let elem_ty = self
            .resolve_source_elem_ty(receiver, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No element type tracking for Seq '{}' in to_set()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let elem_sort = self.seq_element_sort(receiver, receiver_name)?;
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort.clone(),
            element_sort: Sort::Bool,
        }));
        let result = self.solver.fresh_var("__seq_to_set", result_sort.clone());
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Set,
                len_term: None,
                len_guard: None,
                elem_ty: Some(elem_ty.clone()),
                key_ty: None,
                dom_term: None,
            },
        );
        // A set drops duplicates, so `|seq.to_set()| <= |seq|`, NOT `== |seq|`.
        // Without this the name fallback would answer `.len()` with the source
        // SEQUENCE's length.
        self.decline_collection_len(result);
        self.register_derived_seq_view(
            result,
            super::parser_state::DerivedSeqView {
                kind: super::parser_state::DerivedSeqViewKind::SetView,
                source_term: receiver,
                source_name: receiver_name.map(str::to_owned),
            },
        );
        // Keep the derived Set term lightweight and answer supported queries
        // (`contains`) through the source-sequence provenance fast path in
        // `collection_methods.rs`. Unsupported chained Set operations on this
        // derived term fail closed in `encode_collection_op`.
        Ok(result)
    }

    /// Encode `Set::subset(other)` / `Set::superset(other)` as a native
    /// `set.subset` atom decided by ay's finite-set theory (QF_SETLIA).
    ///
    /// Encoding:
    ///   subset:   `(set.subset self other)`
    ///   superset: `(set.subset other self)`  (superset is subset reversed)
    ///
    /// ay's `SetSolver` decides this atom by **ground-witness saturation** over
    /// the membership carrier `Set(T) = Array(T -> Bool)`: trust-vc already emits
    /// membership as `select(set, elem)`, which ay registers as a `set.member`
    /// atom whenever the array operand is a Set carrier. When an asserted-true
    /// `set.subset(s, t)` meets a ground witness `e` with `select(s, e)` true and
    /// `select(t, e)` false, the formula is refuted with **no quantifier
    /// instantiation (no MBQI)** — the win this flip unlocks (Phase 1 routing
    /// already steers `set.*` to QF_SETLIA).
    ///
    /// Soundness contract (sound-or-Unknown):
    /// * The native procedure never *asserts* a positive subset from saturation
    ///   over the unbounded element domain (ground witnesses cannot certify a
    ///   universal). An unconstrained `s.subset(t)` goal therefore does not
    ///   verify (fail-closed), matching the prior quantified encoding.
    /// * Out-of-fragment combinators that reach the set solver yield `Unknown`,
    ///   which trust-vc forwards rather than guessing a verdict.
    ///
    /// The membership carrier itself (`Array(BV n -> Bool)`) and BV/Int element
    /// constants are decided by the array + EUF layers embedded in
    /// `UfSetLiaSolver`; the subset rule is sort-agnostic over the element sort
    /// because it matches on ground term identity.
    pub(crate) fn encode_set_subset_superset(
        &mut self,
        receiver: Term,
        other: Term,
        receiver_name: Option<&str>,
        method: &str,
    ) -> TrustVcResult<Term> {
        // Validate the receiver is a typed Set<T> (preserves prior diagnostics
        // for malformed receivers) before building the native atom.
        let _elem_ty = self.set_element_trust_vc_type(receiver, receiver_name)?;

        let (sub, sup) = if method == "subset" {
            (receiver, other)
        } else {
            // superset(other) == other.subset(self)
            (other, receiver)
        };

        self.encode_native_set_subset_atom(sub, sup)
    }

    /// Build a native `(set.subset sub sup)` Bool atom.
    ///
    /// Declares the polymorphic `set.subset` symbol over the carrier sorts of
    /// `sub`/`sup` and applies it. ay's feature detection routes any formula
    /// containing a `set.*` symbol to QF_SETLIA, where the atom is decided by the
    /// native finite-set procedure.
    pub(super) fn encode_native_set_subset_atom(
        &mut self,
        sub: Term,
        sup: Term,
    ) -> TrustVcResult<Term> {
        let sub_sort = self.solver.term_sort(sub);
        let sup_sort = self.solver.term_sort(sup);
        let decl = self
            .solver
            .try_declare_fun("set.subset", &[sub_sort, sup_sort], Sort::Bool)
            .map_err(|e| format!("Set::subset: failed to declare set.subset: {e}"))?;
        self.solver
            .try_apply(&decl, &[sub, sup])
            .map_err(|e| format!("Set::subset: failed to apply set.subset: {e}").into())
    }

    /// Extract the element TrustVcType for a Set<T> type.
    ///
    /// Resolves from term-keyed `CollectionMeta.elem_ty` first (#2067),
    /// falling back to name-keyed `var_types` for declared variables.
    pub(super) fn set_element_trust_vc_type(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<crate::ir::TrustVcType> {
        // Term-first: covers anonymous/chained results (#2067)
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let Some(ref elem) = meta.elem_ty {
                return Ok(elem.clone());
            }
        }
        // Name fallback
        let ty = receiver_name
            .and_then(|name| self.var_types.get(name))
            .ok_or_else(|| "Set operation requires a named receiver with known type".to_string())?;
        match ty {
            crate::ir::TrustVcType::Set(elem) => Ok((**elem).clone()),
            _ => Err(format!("Expected Set<T> type, got: {:?}", ty).into()),
        }
    }

    /// Encode `Set::filter(pred)` as a fresh set with membership equivalence.
    ///
    /// Encoding:
    ///   forall x. result[x] <-> (self[x] && pred(x))
    #[allow(clippy::indexing_slicing)] // invariant: `params[0]` is only used after matching one closure arg and `params.len() == 1`
    pub(super) fn encode_set_filter(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [crate::ir::TrustVcExpr::SpecClosure { params, body, .. }] = args else {
            return Err("Set::filter expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        if params.len() != 1 {
            return Err("Set::filter requires a unary SpecFn predicate"
                .to_string()
                .into());
        }
        let (param_name, param_ty) = &params[0];

        let elem_ty = self.set_element_trust_vc_type(receiver, receiver_name)?;
        let elem_sort = self.set_element_sort(receiver, receiver_name)?;
        let result_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
            index_sort: elem_sort.clone(),
            element_sort: Sort::Bool,
        }));
        let result = self.solver.fresh_var("__set_filter", result_sort);
        // No len metadata for filtered sets (design: fail-closed on cardinality).
        // `decline_collection_len` is what makes that design actually hold: the
        // result is anonymous, so `lookup_collection_len`'s name fallback would
        // otherwise resolve the SOURCE set's length and let `f.len() == s.len()`
        // verify for a filter that removed elements. Computing the true value
        // needs counting, and even `<= s.len()` needs `s.finite()`, which the
        // Set model does not track — so decline rather than approximate.
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Set,
                len_term: None,
                len_guard: None,
                elem_ty: Some(elem_ty.clone()),
                key_ty: None,
                dom_term: None,
            },
        );
        self.decline_collection_len(result);

        // Safe quantification via helper — native-sorted bound var (#2531)
        let (quant_var, elem_term) = self.safe_element_quantifier("__set_filter_x", &elem_ty)?;
        let self_has = self
            .solver
            .try_select(receiver, elem_term)
            .map_err(|e| e.to_string())?;

        // Bind the closure parameter to the quantifier-bound element term
        let pred_result = self.with_closure_body_bindings(
            [(param_name.clone(), elem_term, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_has = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let self_and_pred = self
            .solver
            .try_and(self_has, pred_result)
            .map_err(|e| e.to_string())?;
        let body_eq = self
            .solver
            .try_eq(result_has, self_and_pred)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body_eq)?;
        let axiom = self
            .solver
            .try_forall(&[quant_var], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Encode the set-comprehension constructor `Set::new(|x| pred)` as a fresh
    /// set whose membership is *exactly* the predicate.
    ///
    /// Encoding (mirrors `Seq::from_fn`'s pointwise definition):
    ///   forall x. result.contains(x) <-> pred(x)
    ///
    /// Soundness: this is the defining axiom of the comprehension and adds no
    /// finiteness/cardinality claim — `result` carries no length metadata, so any
    /// `len()`/`finite()` query over it fails closed exactly as for filter/map.
    /// The membership equivalence is the only fact asserted, and it is the true
    /// semantics of `Set::new`, so no false `Verified` can arise from it.
    #[allow(clippy::indexing_slicing)] // invariant: `params[0]` is only used after matching one closure arg and `params.len() == 1`
    pub(in crate::encoder) fn encode_set_new(
        &mut self,
        args: &[crate::ir::TrustVcExpr],
        return_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let TrustVcType::Set(elem_ty_box) = return_ty else {
            return Err(format!(
                "Set::new builtin must return Set<T>, got '{}'",
                return_ty.to_type_string()
            )
            .into());
        };
        let elem_ty = elem_ty_box.as_ref().clone();

        let [crate::ir::TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Set::new expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        if params.len() != 1 {
            return Err("Set::new requires a unary SpecFn predicate"
                .to_string()
                .into());
        }
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Set::new requires a SpecFn argument".to_string().into());
        };
        if ret_ty.as_ref() != &TrustVcType::Bool {
            return Err(format!(
                "Set::new predicate must return bool, got '{}'",
                ret_ty.to_type_string()
            )
            .into());
        }
        let (param_name, param_ty) = &params[0];
        if param_ty != &elem_ty {
            return Err(format!(
                "Set::new closure parameter type '{}' does not match Set element type '{}'",
                param_ty.to_type_string(),
                elem_ty.to_type_string()
            )
            .into());
        }

        let elem_sort = sort_for_type(&elem_ty);
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort,
            element_sort: Sort::Bool,
        }));
        let result = self.solver.fresh_var("__set_new", result_sort);
        // No len metadata for comprehension sets (design: fail-closed on
        // cardinality, identical to filter/map).
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Set,
                len_term: None,
                len_guard: None,
                elem_ty: Some(elem_ty.clone()),
                key_ty: None,
                dom_term: None,
            },
        );
        self.decline_collection_len(result);

        // Safe quantification via helper — native-sorted bound var (#2531)
        let (quant_var, elem_term) = self.safe_element_quantifier("__set_new_x", &elem_ty)?;

        // Bind the closure parameter to the quantifier-bound element term
        let pred_result = self.with_closure_body_bindings(
            [(param_name.clone(), elem_term, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_has = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;
        let body_eq = self
            .solver
            .try_eq(result_has, pred_result)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body_eq)?;
        let axiom = self
            .solver
            .try_forall(&[quant_var], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Encode `Set::map(f)` as a fresh set whose members are exactly the image
    /// of `self` under `f`.
    ///
    /// Encoding (both directions — image exactness):
    ///   forward: forall x. self[x] => result[f(x)]
    ///   reverse: forall y. result[y] => exists x. self[x] && f(x) == y
    ///
    /// The reverse (exactness) direction is Skolemized with a fresh inverse
    /// array `inv : ret -> elem`, so the existential becomes
    ///   forall y. result[y] => (self[inv[y]] && f(inv[y]) == y)
    /// with trigger `select(result, y)`. `inv` is fresh and otherwise
    /// unconstrained, so this is a sound Skolemization of the existential and
    /// pins `result` to exactly the image of `self` (mirrors the surjection
    /// Skolem in `encode_set_fold`). The reverse axiom is only emitted when the
    /// return type is quantifiable; otherwise the forward-only (sound but
    /// incomplete) encoding is retained.
    #[allow(clippy::indexing_slicing)] // invariant: `params[0]` is only used after matching one closure arg and `params.len() == 1`
    pub(super) fn encode_set_map(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [crate::ir::TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err("Set::map expects exactly one SpecFn::new(...) argument"
                .to_string()
                .into());
        };
        if params.len() != 1 {
            return Err("Set::map requires a unary SpecFn".to_string().into());
        }
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Set::map requires a SpecFn argument".to_string().into());
        };
        let (param_name, param_ty) = &params[0];

        let ret_sort = sort_for_type(ret_ty);
        let result_sort = Sort::Array(Box::new(ay_dpll::api::ArraySort {
            index_sort: ret_sort,
            element_sort: Sort::Bool,
        }));
        let result = self.solver.fresh_var("__set_map", result_sort);
        // No len metadata for mapped sets (design: fail-closed on cardinality).
        // `|s.map(f)| == |s|` needs `f` injective on `s`, which is not checked,
        // so the length is declined rather than inherited from the source.
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Set,
                len_term: None,
                len_guard: None,
                elem_ty: Some(ret_ty.as_ref().clone()),
                key_ty: None,
                dom_term: None,
            },
        );
        self.decline_collection_len(result);

        // Forward: forall x. self[x] => result[f(x)]
        // Safe quantification via helper — native-sorted bound var (#2531)
        let elem_ty_resolved = self.set_element_trust_vc_type(receiver, receiver_name)?;
        let (quant_var, elem_term) =
            self.safe_element_quantifier("__set_map_x", &elem_ty_resolved)?;
        let self_has = self
            .solver
            .try_select(receiver, elem_term)
            .map_err(|e| e.to_string())?;

        // Bind closure parameter to the quantifier-bound element term
        let mapped = self.with_closure_body_bindings(
            [(param_name.clone(), elem_term, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_has_mapped = self
            .solver
            .try_select(result, mapped)
            .map_err(|e| e.to_string())?;
        let forward = self
            .solver
            .try_implies(self_has, result_has_mapped)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&elem_ty_resolved, quant_var, forward)?;
        let axiom = self
            .solver
            .try_forall(&[quant_var], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        // Reverse (image exactness): forall y. result[y] => exists x. self[x] && f(x) == y.
        // Skolemized with a fresh inverse array inv : ret -> elem, giving
        //   forall y. result[y] => (self[inv[y]] && f(inv[y]) == y).
        // Only emitted when the return type is quantifiable (Bool / MathInt /
        // poly / fixed-width integer); otherwise forward-only is retained, which
        // is still sound. `inv` is fresh and unconstrained, so this is a sound
        // Skolemization that pins `result` to exactly the image of `self`.
        if let Ok((quant_y, y_term)) = self.safe_element_quantifier("__set_map_y", ret_ty) {
            let inv_sort = Sort::Array(Box::new(ArraySort {
                index_sort: sort_for_type(ret_ty),
                element_sort: sort_for_type(&elem_ty_resolved),
            }));
            let inv = self.solver.fresh_var("__set_map_inv", inv_sort);
            let result_has_y = self
                .solver
                .try_select(result, y_term)
                .map_err(|e| e.to_string())?;
            let inv_y = self
                .solver
                .try_select(inv, y_term)
                .map_err(|e| e.to_string())?;
            // Width metadata for the preimage element so arithmetic in the
            // closure body is correctly bounded (mirrors `ord_elem` in fold).
            if let Some(width) = elem_ty_resolved.bit_width() {
                if width > 0 {
                    self.term_widths
                        .insert(inv_y, (width, !elem_ty_resolved.is_unsigned()));
                }
            }
            let self_has_inv = self
                .solver
                .try_select(receiver, inv_y)
                .map_err(|e| e.to_string())?;
            // f(inv[y]): re-encode the closure body with the parameter bound to
            // the Skolem preimage element.
            let mapped_inv = self.with_closure_body_bindings(
                [(param_name.clone(), inv_y, param_ty.clone())],
                |s| s.encode_trust_vc_expr(body),
            )?;
            let mapped_eq_y = self
                .solver
                .try_eq(mapped_inv, y_term)
                .map_err(|e| e.to_string())?;
            let consequent = self
                .solver
                .try_and(self_has_inv, mapped_eq_y)
                .map_err(|e| e.to_string())?;
            let reverse = self
                .solver
                .try_implies(result_has_y, consequent)
                .map_err(|e| e.to_string())?;
            let guarded_rev = self.guard_element_quantifier(ret_ty, quant_y, reverse)?;
            let reverse_axiom = self
                .solver
                .try_forall_with_triggers(&[quant_y], guarded_rev, &[&[result_has_y]])
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(reverse_axiom)
                .map_err(|e| e.to_string())?;
        }

        Ok(result)
    }

    /// Extract the element sort for a Set<T> type.
    ///
    /// Resolves from term-keyed `CollectionMeta.elem_ty` first (#2067),
    /// falling back to name-keyed `var_types` for declared variables.
    pub(super) fn set_element_sort(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Sort> {
        // Term-first: covers anonymous/chained results (#2067)
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let Some(ref elem) = meta.elem_ty {
                return Ok(sort_for_type(elem));
            }
        }
        // Name fallback
        let ty = receiver_name
            .and_then(|name| self.var_types.get(name))
            .ok_or_else(|| "Set operation requires a named receiver with known type".to_string())?;
        match ty {
            crate::ir::TrustVcType::Set(elem) => Ok(sort_for_type(elem)),
            _ => Err(format!("Expected Set<T> type, got: {:?}", ty).into()),
        }
    }

    /// Encode `Set::choose()` as a deterministic witness with guarded membership.
    ///
    /// The membership fact is available when either a concrete member witness is
    /// known or the tracked set length is nonzero:
    ///
    /// `forall x. s.contains(x) ==> s.contains(s.choose())`
    /// `s.len() > 0 ==> s.contains(s.choose())`.
    pub(super) fn encode_set_choose(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if !args.is_empty() {
            return Err(format!("Set::choose() expects 0 arguments, got {}", args.len()).into());
        }

        let elem_ty = self.set_element_trust_vc_type(receiver_term, receiver_name)?;
        let len = self.lookup_collection_len(receiver_term, receiver_name);
        if len.is_some() {
            self.emit_collection_len_guard(receiver_term);
        }

        let receiver_sort = self.solver.term_sort(receiver_term);
        let return_sort = sort_for_type(&elem_ty);
        let key = format!("set_choose::{}", elem_ty.to_type_string());

        let existing = self
            .choose_registry
            .as_ref()
            .and_then(|registry| registry.get(&key).cloned());
        let choose_decl = if let Some(existing) = existing {
            existing
        } else {
            let decl_name = {
                let registry = self.choose_registry.as_ref().ok_or_else(|| {
                    "Set::choose(): no choose_registry available (internal error)".to_string()
                })?;
                format!("__trust_vc_set_choose_{}", registry.len())
            };
            let decl = self
                .solver
                .try_declare_fun(
                    &decl_name,
                    std::slice::from_ref(&receiver_sort),
                    return_sort,
                )
                .map_err(|e| format!("Set::choose(): failed to declare UF: {e}"))?;
            let registry = self.choose_registry.as_mut().ok_or_else(|| {
                "Set::choose(): no choose_registry available (internal error)".to_string()
            })?;
            registry.insert(key, decl.clone());
            decl
        };

        let chosen = self
            .solver
            .try_apply(&choose_decl, &[receiver_term])
            .map_err(|e| format!("Set::choose(): failed to apply UF: {e}"))?;

        let membership = self
            .solver
            .try_select(receiver_term, chosen)
            .map_err(|e| format!("Set::choose(): failed to select chosen membership: {e}"))?;

        if let Some(len) = len {
            let len_nonempty = match self.solver.term_sort(len) {
                Sort::BitVec(bv_sort) => {
                    let zero = self
                        .solver
                        .try_bv_const(0, bv_sort.width)
                        .map_err(|e| format!("Set::choose(): failed to create length zero: {e}"))?;
                    self.solver
                        .try_bvugt(len, zero)
                        .map_err(|e| format!("Set::choose(): failed to build len > 0: {e}"))?
                }
                Sort::Int => {
                    let zero = self.solver.int_const(0);
                    self.solver
                        .try_gt(len, zero)
                        .map_err(|e| format!("Set::choose(): failed to build len > 0: {e}"))?
                }
                other => {
                    return Err(format!(
                        "Set::choose() requires numeric length metadata, got sort {other:?}"
                    )
                    .into());
                }
            };
            let axiom = self
                .solver
                .try_implies(len_nonempty, membership)
                .map_err(|e| format!("Set::choose(): failed to build length axiom: {e}"))?;
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| format!("Set::choose(): failed to assert length axiom: {e}"))?;
        }

        let witness_var = self
            .solver
            .fresh_var("__set_choose_witness", sort_for_type(&elem_ty));
        if let Some(width) = elem_ty.bit_width() {
            if width > 0 {
                let signed = matches!(elem_ty, crate::ir::TrustVcType::Int { .. });
                self.term_widths.insert(witness_var, (width, signed));
            }
        }
        let witness_membership = self
            .solver
            .try_select(receiver_term, witness_var)
            .map_err(|e| format!("Set::choose(): failed to select witness membership: {e}"))?;
        let witness_axiom = self
            .solver
            .try_implies(witness_membership, membership)
            .map_err(|e| format!("Set::choose(): failed to build witness axiom: {e}"))?;
        let witness_axiom = self.guard_element_quantifier(&elem_ty, witness_var, witness_axiom)?;
        let witness_axiom = self
            .solver
            .try_forall_with_triggers(&[witness_var], witness_axiom, &[&[witness_membership]])
            .map_err(|e| format!("Set::choose(): failed to quantify witness axiom: {e}"))?;
        self.solver
            .try_assert_term(witness_axiom)
            .map_err(|e| format!("Set::choose(): failed to assert witness axiom: {e}"))?;

        if let Some(width) = elem_ty.bit_width() {
            if width > 0 {
                let signed = matches!(elem_ty, crate::ir::TrustVcType::Int { .. });
                self.term_widths.insert(chosen, (width, signed));
            }
        }

        Ok(chosen)
    }
}

fn set_element_has_finite_backend_domain(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Unit
            | TrustVcType::Bool
            | TrustVcType::Char
            | TrustVcType::Int { .. }
            | TrustVcType::Uint { .. }
            | TrustVcType::Float { .. }
    )
}
