//! Map-specific higher-order collection encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{ArraySort, Sort, Term};

use super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MapInsertChainBase {
    Empty,
    Other,
}

#[derive(Debug, Clone, Copy)]
struct MapInsertEntry<'a> {
    key: &'a TrustVcExpr,
    value: &'a TrustVcExpr,
}

impl<'a> AstExpressionParser<'a> {
    /// Try to encode `Map::contains_value` without quantifiers for finite insert
    /// chains. The exact finite form is:
    ///
    ///   exists visible insert i. value_i == needle && key_i not overwritten later
    ///
    /// For chains over an arbitrary base map, this returns that visible-insert
    /// witness disjoined with the general existential fallback so it remains a
    /// sound over-the-base encoding while still proving obvious inserted values.
    pub(super) fn try_encode_map_contains_value_finite(
        &mut self,
        receiver: &TrustVcExpr,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Option<Term>> {
        let [value_arg] = args else {
            return Err(format!(
                "Map::contains_value() expects 1 argument, got {}",
                args.len()
            )
            .into());
        };

        let mut entries = Vec::new();
        let Some(base) = collect_map_insert_chain(receiver, &mut entries) else {
            return Ok(None);
        };
        if entries.is_empty() && base != MapInsertChainBase::Empty {
            return Ok(None);
        }

        let mut needle = self.encode_subexpr(value_arg)?;
        needle = self.coerce_value_for_store_in_int_mode(needle, receiver_term, receiver_name)?;

        let mut encoded_entries = Vec::with_capacity(entries.len());
        for entry in entries {
            let key = self.encode_subexpr(entry.key)?;
            let key = self.coerce_key_for_store_in_int_mode(key, receiver_term, receiver_name)?;

            let value = self.encode_subexpr(entry.value)?;
            let value =
                self.coerce_value_for_store_in_int_mode(value, receiver_term, receiver_name)?;
            encoded_entries.push((key, value));
        }

        let mut visible_value = self.solver.bool_const(false);
        let mut newer_keys = Vec::new();
        for (key, value) in encoded_entries.iter().rev() {
            let (value, coerced_needle) = self.coerce_bv_widths(*value, needle)?;
            needle = coerced_needle;
            let mut contribution = self
                .solver
                .try_eq(value, needle)
                .map_err(|e| e.to_string())?;

            for newer_key in &newer_keys {
                let (key, newer_key) = self.coerce_bv_widths(*key, *newer_key)?;
                let same_key = self
                    .solver
                    .try_eq(key, newer_key)
                    .map_err(|e| e.to_string())?;
                let different_key = self.solver.try_not(same_key).map_err(|e| e.to_string())?;
                contribution = self
                    .solver
                    .try_and(contribution, different_key)
                    .map_err(|e| e.to_string())?;
            }

            visible_value = self
                .solver
                .try_or(visible_value, contribution)
                .map_err(|e| e.to_string())?;
            newer_keys.push(*key);
        }

        if base == MapInsertChainBase::Empty {
            return Ok(Some(visible_value));
        }

        let fallback = self.encode_map_contains_value(receiver_term, receiver_name, args)?;
        self.solver
            .try_or(visible_value, fallback)
            .map(Some)
            .map_err(|e| e.to_string().into())
    }

    /// Encode `Map::contains_value(v)` as an existential over tracked domain keys.
    ///
    /// Encoding:
    ///   exists k. dom[k] && map[k] == v
    ///
    /// The key witness uses the same Int-sorted assertion-side shape as
    /// `Seq::contains` for BV key types, keeping existential witnesses in the
    /// solver fragment that already backs collection membership.
    pub(super) fn encode_map_contains_value(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [value_arg] = args else {
            return Err(format!(
                "Map::contains_value() expects 1 argument, got {}",
                args.len()
            )
            .into());
        };

        let rname = receiver_name.unwrap_or("<anonymous>");
        let dom = self
            .lookup_collection_dom(receiver, receiver_name)
            .ok_or_else(|| {
                format!("Map::contains_value requires domain tracking for receiver '{rname}'")
            })?;
        let (key_ty, _value_ty) = self.map_key_value_types(receiver, receiver_name)?;

        let value = self.encode_subexpr(value_arg)?;
        let value = self.coerce_value_for_store_in_int_mode(value, receiver, receiver_name)?;

        let (quant_key, key_term) =
            self.assertion_element_quantifier("__map_contains_value_key", &key_ty)?;
        let in_dom = self
            .solver
            .try_select(dom, key_term)
            .map_err(|e| e.to_string())?;
        let map_value = self
            .solver
            .try_select(receiver, key_term)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(map_value, info);
        }

        let (map_value, value) = self.coerce_bv_widths(map_value, value)?;
        let value_eq = self
            .solver
            .try_eq(map_value, value)
            .map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_and(in_dom, value_eq)
            .map_err(|e| e.to_string())?;
        let guarded =
            self.add_integer_range_guards(&[(String::new(), key_ty, quant_key)], body, false)?;

        self.solver
            .try_exists(&[quant_key], guarded)
            .map_err(|e| e.to_string().into())
    }

    /// Encode `Map::map_values(f)` as a fresh map with preserved domain.
    ///
    /// Encoding:
    ///   result.dom == source.dom  (same domain membership array)
    ///   result.len == source.len  (preserved length)
    ///   forall k. dom[k] => result[k] == f(source[k])
    pub(super) fn encode_map_map_values(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let _rname = receiver_name.unwrap_or("<anonymous>");
        let [crate::ir::TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Map::map_values expects exactly one SpecFn::new(...) argument"
                    .to_string()
                    .into(),
            );
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err("Map::map_values requires a unary SpecFn".to_string().into());
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Map::map_values requires a SpecFn argument"
                .to_string()
                .into());
        };

        // Resolve key/value types from receiver
        let (key_ty, _val_ty) = self.map_key_value_types(receiver, receiver_name)?;
        let key_sort = sort_for_type(&key_ty);
        let val_sort = sort_for_type(ret_ty);

        // Fresh result map array
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: key_sort.clone(),
            element_sort: val_sort,
        }));
        let result = self.solver.fresh_var("__map_map_values", result_sort);

        // Preserve domain and length from source
        let dom = self.lookup_collection_dom(receiver, receiver_name);
        let len = self.lookup_collection_len(receiver, receiver_name);
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Map,
                len_term: len,
                len_guard: None,
                elem_ty: Some(ret_ty.as_ref().clone()),
                key_ty: Some(key_ty.clone()),
                dom_term: dom,
            },
        );
        if len.is_none() {
            // `map_values` preserves the key domain, so inheriting the source's
            // length is correct — but only when the source HAS one. If the
            // source declined (e.g. `m.filter_keys(p)`), the decline must
            // propagate, or the name fallback re-acquires the ORIGINAL map's
            // length through the chained receiver name.
            self.decline_collection_len(result);
        }

        // forall k. dom[k] => result[k] == f(source[k])
        // Safe quantification: native-sorted bound var (#2531)
        let (quant_key, key_term) = self.safe_element_quantifier("__map_mv_k", &key_ty)?;

        // Get the source value at this key
        let source_val = self
            .solver
            .try_select(receiver, key_term)
            .map_err(|e| e.to_string())?;

        // Bind closure parameter to source value
        let mapped = self.with_closure_body_bindings(
            [(param_name.clone(), source_val, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_val = self
            .solver
            .try_select(result, key_term)
            .map_err(|e| e.to_string())?;
        let val_eq = self
            .solver
            .try_eq(result_val, mapped)
            .map_err(|e| e.to_string())?;

        // Guard with domain membership (required for correct Map semantics)
        let dom_term = dom.ok_or_else(|| {
            format!(
                "Map::map_values requires domain tracking for receiver '{}'",
                _rname,
            )
        })?;
        let in_dom = self
            .solver
            .try_select(dom_term, key_term)
            .map_err(|e| e.to_string())?;
        let mv_body = self
            .solver
            .try_implies(in_dom, val_eq)
            .map_err(|e| e.to_string())?;

        let guarded = self.guard_element_quantifier(&key_ty, quant_key, mv_body)?;
        let axiom = self
            .solver
            .try_forall(&[quant_key], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Encode `Map::map_entries(f)` as a fresh map with preserved domain.
    ///
    /// Encoding:
    ///   result.dom == source.dom  (same domain membership array)
    ///   result.len == source.len  (preserved length)
    ///   forall k. dom[k] => result[k] == f(k, source[k])
    pub(super) fn encode_map_map_entries(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [crate::ir::TrustVcExpr::SpecClosure { params, body, ty }] = args else {
            return Err(
                "Map::map_entries expects exactly one SpecFn::new(...) argument"
                    .to_string()
                    .into(),
            );
        };
        let [(key_param_name, key_param_ty), (value_param_name, value_param_ty)] =
            params.as_slice()
        else {
            return Err(
                "Map::map_entries requires a 2-parameter SpecFn (key, value)"
                    .to_string()
                    .into(),
            );
        };
        let TrustVcType::SpecFn(_, ret_ty) = ty else {
            return Err("Map::map_entries requires a SpecFn argument"
                .to_string()
                .into());
        };

        let (key_ty, _value_ty) = self.map_key_value_types(receiver, receiver_name)?;
        let key_sort = sort_for_type(&key_ty);
        let val_sort = sort_for_type(ret_ty);
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: key_sort.clone(),
            element_sort: val_sort,
        }));
        let result = self.solver.fresh_var("__map_map_entries", result_sort);

        let dom = self.lookup_collection_dom(receiver, receiver_name);
        let len = self.lookup_collection_len(receiver, receiver_name);
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Map,
                len_term: len,
                len_guard: None,
                elem_ty: Some(ret_ty.as_ref().clone()),
                key_ty: Some(key_ty.clone()),
                dom_term: dom,
            },
        );
        if len.is_none() {
            // See `map_values`: a declined source cardinality must not be
            // re-acquired through the chained receiver name.
            self.decline_collection_len(result);
        }

        // Safe quantification: native-sorted bound var (#2531)
        let (quant_key, key_term) = self.safe_element_quantifier("__map_me_k", &key_ty)?;
        let source_val = self
            .solver
            .try_select(receiver, key_term)
            .map_err(|e| e.to_string())?;

        // Bind key and value closure parameters to quantifier-bound terms
        let mapped = self.with_closure_body_bindings(
            [
                (key_param_name.clone(), key_term, key_param_ty.clone()),
                (value_param_name.clone(), source_val, value_param_ty.clone()),
            ],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_val = self
            .solver
            .try_select(result, key_term)
            .map_err(|e| e.to_string())?;
        let val_eq = self
            .solver
            .try_eq(result_val, mapped)
            .map_err(|e| e.to_string())?;
        let dom_term = dom.ok_or_else(|| {
            format!(
                "Map::map_entries requires domain tracking for receiver '{}'",
                rname,
            )
        })?;
        let in_dom = self
            .solver
            .try_select(dom_term, key_term)
            .map_err(|e| e.to_string())?;
        let me_body = self
            .solver
            .try_implies(in_dom, val_eq)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&key_ty, quant_key, me_body)?;
        let axiom = self
            .solver
            .try_forall(&[quant_key], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Encode `Map::filter_keys(pred)` as a fresh map with filtered domain.
    ///
    /// Encoding:
    ///   result_dom[k] <-> (source_dom[k] && pred(k))
    ///   forall k. result_dom[k] => result[k] == source[k]
    ///   No exact length metadata (design: fail-closed on cardinality)
    pub(super) fn encode_map_filter_keys(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        args: &[crate::ir::TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let rname = receiver_name.unwrap_or("<anonymous>");
        let [crate::ir::TrustVcExpr::SpecClosure { params, body, .. }] = args else {
            return Err(
                "Map::filter_keys expects exactly one SpecFn::new(...) argument"
                    .to_string()
                    .into(),
            );
        };
        let [(param_name, param_ty)] = params.as_slice() else {
            return Err("Map::filter_keys requires a unary SpecFn predicate"
                .to_string()
                .into());
        };

        let (key_ty, val_ty) = self.map_key_value_types(receiver, receiver_name)?;
        let key_sort = sort_for_type(&key_ty);
        let val_sort = sort_for_type(&val_ty);

        // Fresh result map and domain arrays
        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: key_sort.clone(),
            element_sort: val_sort,
        }));
        let result = self.solver.fresh_var("__map_filter_keys", result_sort);
        let dom_sort = Sort::Array(Box::new(ArraySort {
            index_sort: key_sort.clone(),
            element_sort: Sort::Bool,
        }));
        let result_dom = self.solver.fresh_var("__map_fk_dom", dom_sort);

        // No len metadata for filtered maps (fail-closed on cardinality).
        // Same shape as `Set::filter`: the result is anonymous, so the name
        // fallback would otherwise hand back the SOURCE map's length.
        self.register_collection_meta(
            result,
            super::parser_state::CollectionMeta {
                kind: super::parser_state::CollectionKind::Map,
                len_term: None,
                len_guard: None,
                elem_ty: Some(val_ty),
                key_ty: Some(key_ty.clone()),
                dom_term: Some(result_dom),
            },
        );
        self.decline_collection_len(result);

        // Safe quantification: native-sorted bound var (#2531)
        let (quant_key, key_term) = self.safe_element_quantifier("__map_fk_k", &key_ty)?;

        // Domain membership axiom: result_dom[k] <-> (source_dom[k] && pred(k))
        let source_dom = self.lookup_collection_dom(receiver, receiver_name);
        let source_in_dom = if let Some(dom_term) = source_dom {
            self.solver
                .try_select(dom_term, key_term)
                .map_err(|e| e.to_string())?
        } else {
            return Err(format!(
                "Map::filter_keys requires domain tracking for '{}', but none found",
                rname
            )
            .into());
        };

        // Bind closure parameter to the quantifier-bound key term
        let pred_result = self.with_closure_body_bindings(
            [(param_name.clone(), key_term, param_ty.clone())],
            |s| s.encode_trust_vc_expr(body),
        )?;

        let result_in_dom = self
            .solver
            .try_select(result_dom, key_term)
            .map_err(|e| e.to_string())?;
        let source_and_pred = self
            .solver
            .try_and(source_in_dom, pred_result)
            .map_err(|e| e.to_string())?;
        let dom_eq = self
            .solver
            .try_eq(result_in_dom, source_and_pred)
            .map_err(|e| e.to_string())?;
        let dom_guarded = self.guard_element_quantifier(&key_ty, quant_key, dom_eq)?;
        let dom_axiom = self
            .solver
            .try_forall(&[quant_key], dom_guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(dom_axiom)
            .map_err(|e| e.to_string())?;

        // Value preservation: forall k. result_dom[k] => result[k] == source[k]
        // Safe quantification: native-sorted bound var (#2531)
        let (quant_key2, key_term2) = self.safe_element_quantifier("__map_fk_k2", &key_ty)?;
        let r_in_dom = self
            .solver
            .try_select(result_dom, key_term2)
            .map_err(|e| e.to_string())?;
        let source_val = self
            .solver
            .try_select(receiver, key_term2)
            .map_err(|e| e.to_string())?;
        let result_val = self
            .solver
            .try_select(result, key_term2)
            .map_err(|e| e.to_string())?;
        let val_eq = self
            .solver
            .try_eq(result_val, source_val)
            .map_err(|e| e.to_string())?;
        let dom_guarded2 = self
            .solver
            .try_implies(r_in_dom, val_eq)
            .map_err(|e| e.to_string())?;
        let range_guarded = self.guard_element_quantifier(&key_ty, quant_key2, dom_guarded2)?;
        let val_axiom = self
            .solver
            .try_forall(&[quant_key2], range_guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(val_axiom)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Extract key and value TrustVcTypes for a Map<K, V> receiver.
    ///
    /// Resolves from term-keyed metadata first (covers anonymous/chained results),
    /// then falls back to name-keyed `var_types`. Part of #2507.
    fn map_key_value_types(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<(TrustVcType, TrustVcType)> {
        // Term-first: covers anonymous/chained results (#2507)
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let (Some(ref key), Some(ref val)) = (&meta.key_ty, &meta.elem_ty) {
                return Ok((key.clone(), val.clone()));
            }
            // Partial metadata: have elem_ty but not key_ty — try name fallback for key
            if let Some(ref elem) = meta.elem_ty {
                if let Some(name) = receiver_name {
                    if let Some(TrustVcType::Map(k, _)) = self.var_types.get(name) {
                        return Ok((k.as_ref().clone(), elem.clone()));
                    }
                }
            }
        }
        // Name fallback
        let ty = receiver_name
            .and_then(|name| self.var_types.get(name))
            .ok_or_else(|| "Map operation requires a named receiver with known type".to_string())?;
        match ty {
            TrustVcType::Map(k, v) => Ok((k.as_ref().clone(), v.as_ref().clone())),
            _ => Err(format!("Expected Map<K, V> type, got: {:?}", ty).into()),
        }
    }

    /// Build (and memoize) the native `(map.dom m)` domain projection for a Map
    /// value carrier `map_term`, bridged once to `map_term`'s tracked domain
    /// array by equality.
    ///
    /// `contains_key` reads membership through `(select (map.dom m) k)` so ay's
    /// finite-map theory can discover the ground subset↔key witnesses and decide
    /// `map.subset` with no MBQI. The bridge `(map.dom m) == tracked_dom` ties
    /// the projection to the array that trust-vc's insert/remove logic actually
    /// updates — it is the *same* array (sound, verdict-neutral); only the
    /// syntactic shape of the membership read changes.
    ///
    /// Returns `None` when no tracked domain array exists for the receiver, in
    /// which case `contains_key` keeps its prior (separate-array) read.
    pub(super) fn map_dom_projection(
        &mut self,
        map_term: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Option<Term>> {
        if let Some(&proj) = self.map_dom_bridges.get(&map_term) {
            return Ok(Some(proj));
        }
        let Some(tracked_dom) = self.lookup_collection_dom(map_term, receiver_name) else {
            return Ok(None);
        };
        let map_sort = self.solver.term_sort(map_term);
        let dom_sort = self.solver.term_sort(tracked_dom);
        // (map.dom m): declared over the Map value-carrier sort -> dom array sort.
        let decl = self
            .solver
            .try_declare_fun("map.dom", &[map_sort], dom_sort)
            .map_err(|e| format!("Map::dom: failed to declare map.dom: {e}"))?;
        let proj = self
            .solver
            .try_apply(&decl, &[map_term])
            .map_err(|e| format!("Map::dom: failed to apply map.dom: {e}"))?;
        // Bridge: (map.dom m) == tracked_dom (the array insert/remove update).
        let bridge = self
            .solver
            .try_eq(proj, tracked_dom)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(bridge)
            .map_err(|e| e.to_string())?;
        self.map_dom_bridges.insert(map_term, proj);
        Ok(Some(proj))
    }

    /// Encode `Map::subset_of(other)` / `Map::submap_of(other)` as a native
    /// `(map.subset self other)` Bool atom decided by ay's finite-map theory
    /// (QF_MAPLIA).
    ///
    /// # Encoding (native map theory, sound-or-Unknown)
    ///
    /// The atom is handed to ay's map solver, which decides submap obligations by
    /// **ground-witness saturation** over the value carrier `Map(K, V) =
    /// Array(K -> V)` and the domain carrier `(map.dom m)`:
    ///
    /// * **reflexivity** — `m.subset_of(m)` is valid; ay refutes its negation
    ///   structurally with **no quantifier instantiation (no MBQI)**.
    /// * **domain-witness propagation** — for a present key `e` with
    ///   `contains_key(self, e)`, the executor-injected
    ///   `subset => (contains_key(self,e) => contains_key(other,e))` obligation
    ///   forces membership into `other` (no MBQI) — the win this flip unlocks.
    /// * **value-witness propagation** — when both operands have value reads at a
    ///   present key, `subset => (contains_key(self,e) => get(self,e)=get(other,e))`
    ///   forces value agreement (Verus submap semantics).
    /// * **unconstrained** subset never decides true (ground witnesses cannot
    ///   certify a universal over the unbounded key domain), so an unconstrained
    ///   goal fails closed — matching the prior encoding.
    ///
    /// Membership reads must reach ay as `(select (map.dom m) k)` for the
    /// ground-witness discovery to match, so each operand's domain projection is
    /// established (and bridged to its tracked array) here.
    ///
    /// If the surrounding obligation introduces other quantifiers, ay routes to a
    /// quantified logic where `map.subset`/`map.dom` degrade to opaque UF. An
    /// opaque-UF *goal* still fails closed (sound — never provable from nothing),
    /// so the native atom is sound there too, just less complete.
    pub(super) fn encode_map_subset(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        other: Term,
        other_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        // Validate the receiver is a typed Map<K, V> (preserves prior
        // diagnostics) before building the native atom.
        let _ = self.map_key_value_types(receiver_term, receiver_name)?;
        // Once a subset atom is in play, contains_key reads switch to the native
        // `(map.dom m)` projection (gated on this flag) so ay can discover the
        // ground subset↔key witnesses. Non-subset Map queries keep the plain
        // tracked-array reads and stay on the array/BV path (no regression).
        self.map_subset_seen = true;
        // Establish the domain projections + bridges so contains_key witnesses
        // already in the obligation connect to ay's subset↔key discovery.
        let _ = self.map_dom_projection(receiver_term, receiver_name)?;
        let _ = self.map_dom_projection(other, other_name)?;
        self.encode_native_map_subset_atom(receiver_term, other)
    }

    /// Build a native `(map.subset sub sup)` Bool atom over the Map value
    /// carriers.
    ///
    /// Declares the polymorphic `map.subset` symbol over the carrier sorts of
    /// `sub`/`sup` and applies it. ay's feature detection routes any
    /// quantifier-free formula carrying a `map.*` symbol to QF_MAPLIA, where the
    /// atom is decided by the native finite-map procedure (reflexivity plus the
    /// executor-injected ground subset↔key obligations). No quantified domain or
    /// value axiom is emitted, so the goal stays quantifier-free and decides
    /// without MBQI.
    ///
    /// Soundness contract (sound-or-Unknown): the procedure never asserts a
    /// positive subset from ground saturation over the unbounded key domain, so
    /// an unconstrained goal does not verify (fails closed). When a surrounding
    /// quantifier forces a quantified logic, the atom degrades to an opaque UF
    /// goal, which likewise cannot be proven from nothing (sound, incomplete).
    fn encode_native_map_subset_atom(&mut self, sub: Term, sup: Term) -> TrustVcResult<Term> {
        let sub_sort = self.solver.term_sort(sub);
        let sup_sort = self.solver.term_sort(sup);
        let decl = self
            .solver
            .try_declare_fun("map.subset", &[sub_sort, sup_sort], Sort::Bool)
            .map_err(|e| format!("Map::subset_of: failed to declare map.subset: {e}"))?;
        self.solver
            .try_apply(&decl, &[sub, sup])
            .map_err(|e| format!("Map::subset_of: failed to apply map.subset: {e}").into())
    }
}

fn collect_map_insert_chain<'expr>(
    expr: &'expr TrustVcExpr,
    entries: &mut Vec<MapInsertEntry<'expr>>,
) -> Option<MapInsertChainBase> {
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ty: TrustVcType::Map(_, _),
            ..
        } => {
            let [key, value] = args.as_slice() else {
                return None;
            };
            let base = collect_map_insert_chain(receiver, entries)?;
            entries.push(MapInsertEntry { key, value });
            Some(base)
        }
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if args.is_empty()
            && matches!(return_ty, TrustVcType::Map(_, _))
            && is_empty_map_constructor(name) =>
        {
            Some(MapInsertChainBase::Empty)
        }
        _ if matches!(
            crate::ir_lowering::infer_expr_type(expr),
            TrustVcType::Map(_, _)
        ) =>
        {
            Some(MapInsertChainBase::Other)
        }
        _ => None,
    }
}

fn is_empty_map_constructor(name: &str) -> bool {
    name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX) && name.ends_with("_empty")
}
