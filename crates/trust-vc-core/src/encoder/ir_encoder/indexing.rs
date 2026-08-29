//! Array indexing, insert/remove helpers, and Set binary operations for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from collections.rs to stay under 500 LOC.

use ay_dpll::api::{ArraySort, Sort, Term};

use crate::ir::{TrustVcExpr, TrustVcType};

use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
use crate::encoder::types::sort_for_type;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    // =================================================================
    // Insert helper
    // =================================================================

    /// Encode insert — handles both Map (2-arg) and Set (1-arg) variants.
    ///
    /// Updates cardinality: old_len <= new_len <= old_len + 1
    /// (parity: methods.rs:497-566).
    pub(super) fn encode_trust_vc_insert(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        // Save encoded key for Map domain update after the match (#1966).
        let mut map_key_for_dom: Option<Term> = None;
        // Save encoded elem for Set cardinality axiom (#1800 Slice 3).
        let mut set_elem_for_cardinality: Option<Term> = None;
        let result = match args {
            [key_arg, value_arg] => {
                // Map insert(key, value)
                let key = self.encode_subexpr(key_arg)?;
                let key = self.coerce_key_for_store_in_int_mode(key, receiver_term, Some(rname))?;
                map_key_for_dom = Some(key);
                let value = self.encode_subexpr(value_arg)?;
                let value =
                    self.coerce_value_for_store_in_int_mode(value, receiver_term, Some(rname))?;
                self.solver
                    .try_store(receiver_term, key, value)
                    .map_err(|e| e.to_string())?
            }
            [elem_arg] => {
                // Set insert(elem)
                let elem = self.encode_subexpr(elem_arg)?;
                let elem =
                    self.coerce_key_for_store_in_int_mode(elem, receiver_term, Some(rname))?;
                set_elem_for_cardinality = Some(elem);
                let true_val = self.solver.bool_const(true);
                self.solver
                    .try_store(receiver_term, elem, true_val)
                    .map_err(|e| e.to_string())?
            }
            _ => {
                return Err(format!("insert() expects 1 or 2 arguments, got {}", args.len()).into())
            }
        };
        // Update cardinality using term-keyed lookup for chained operations (#1749).
        // Fail-closed: return error if no length tracked (was silently skipped). Fixes #2142.
        let old_len = self
            .lookup_collection_len(receiver_term, Some(rname))
            .ok_or_else(|| format!("No length tracked for collection '{}' in insert", rname))?;
        {
            let (label, kind) = if args.len() == 2 {
                ("__map_len_insert", CollectionKind::Map)
            } else {
                ("__set_len_insert", CollectionKind::Set)
            };
            // Route A (#2779): length is an unbounded Int; match the source
            // length's sort so legacy/test BV lengths stay consistent.
            let new_len = self.solver.fresh_var(label, self.solver.term_sort(old_len));
            let len_guard = if let Some(elem) = set_elem_for_cardinality {
                // Set insert: exact conditional cardinality plus a guarded
                // no-wrap overflow predicate (#1800 Slice 3).
                // new_len == old_len + ite(select(set, elem), 0, 1)
                Some(self.assert_set_insert_cardinality(new_len, old_len, receiver_term, elem)?)
            } else {
                // Map insert: over-approximate bounds (domain membership tracked separately).
                // old_len <= new_len <= old_len + 1. Int arithmetic is monotone,
                // so the "insert length no overflow" / non-negativity obligations
                // (BV wrap artifacts) DISAPPEAR over the integers.
                let one = self.len_const_like(old_len, 1)?;
                let old_plus_one = self.len_add(old_len, one)?;
                let ge = self.len_ge(new_len, old_len)?;
                self.solver.try_assert_term(ge).map_err(|e| e.to_string())?;
                let le = self.len_le(new_len, old_plus_one)?;
                self.solver.try_assert_term(le).map_err(|e| e.to_string())?;
                if !self.len_is_int(new_len) {
                    // Legacy BV-length path keeps the bounded-width guards.
                    let no_overflow = self
                        .solver
                        .try_bvuge(old_plus_one, old_len)
                        .map_err(|e| format!("insert length overflow: {}", e))?;
                    self.overflow_checks
                        .push(("insert length no overflow".into(), no_overflow));
                    let zero = self.len_const_like(old_len, 0)?;
                    let nonneg = self.len_ge(new_len, zero)?;
                    self.overflow_checks
                        .push(("insert length non-negative".into(), nonneg));
                }
                None
            };
            self.collection_lengths.insert(rname.to_string(), new_len);
            // Register term-keyed metadata for chained operations (#1749).
            let elem_ty = self.resolve_source_elem_ty(receiver_term, Some(rname));
            // For Map insert, update the domain array: store(dom, key, true) (#1966).
            // Reads initial domain from variables, writes update to domain_terms.
            let dom_term = if let Some(key) = map_key_for_dom {
                let dom_name = format!("{}_dom", rname);
                let current_dom = self
                    .domain_terms
                    .get(&dom_name)
                    .or_else(|| self.variables.get(&dom_name))
                    .copied();
                if let Some(dom) = current_dom {
                    let true_val = self.solver.bool_const(true);
                    let new_dom = self
                        .solver
                        .try_store(dom, key, true_val)
                        .map_err(|e| format!("Map insert domain update: {}", e))?;
                    self.domain_terms.insert(dom_name, new_dom);
                    Some(new_dom)
                } else {
                    None
                }
            } else {
                None
            };
            let key_ty = self
                .collection_meta_by_term
                .get(&receiver_term)
                .and_then(|m| m.key_ty.clone());
            self.register_collection_meta(
                result,
                CollectionMeta {
                    kind,
                    len_term: Some(new_len),
                    len_guard,
                    elem_ty,
                    key_ty,
                    dom_term,
                },
            );
        }
        Ok(result)
    }

    // =================================================================
    // Map remove helper (#1966)
    // =================================================================

    /// Encode Map::remove(key) — stores false in the domain array (#1966).
    ///
    /// The data array is unchanged (removed key's value is unspecified in Verus).
    /// Cardinality: old_len - 1 <= new_len <= old_len (same as Set::remove).
    pub(super) fn encode_map_remove(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!("Map::remove() expects 1 argument, got {}", args.len()).into());
        };
        let rname = receiver_name.unwrap_or("_anon");
        let key = self.encode_subexpr(arg)?;
        let key = self.coerce_key_for_store_in_int_mode(key, receiver_term, receiver_name)?;
        let old_value = self
            .solver
            .try_select(receiver_term, key)
            .map_err(|e| format!("Map remove value select: {}", e))?;
        let identity_term = self
            .solver
            .try_store(receiver_term, key, old_value)
            .map_err(|e| format!("Map remove result store: {}", e))?;
        // The solver canonicalizes `store(a, k, select(a, k))` back to `a`, so
        // materialize a fresh array term and tie it to the identity store with
        // an equality assertion. This preserves semantics while giving
        // term-keyed collection metadata a distinct result handle.
        let result_term = self
            .solver
            .fresh_var("__map_remove_result", self.solver.term_sort(receiver_term));
        let result_eq = self
            .solver
            .try_eq(result_term, identity_term)
            .map_err(|e| format!("Map remove result equality: {}", e))?;
        self.solver
            .try_assert_term(result_eq)
            .map_err(|e| format!("Map remove result assertion: {}", e))?;
        let dom_term = self
            .lookup_collection_dom(receiver_term, receiver_name)
            .ok_or_else(|| format!("No domain tracked for Map '{}' in remove", rname))?;
        let false_val = self.solver.bool_const(false);
        let new_dom = self
            .solver
            .try_store(dom_term, key, false_val)
            .map_err(|e| format!("Map remove domain update: {}", e))?;
        if let Some(name) = receiver_name {
            self.domain_terms.insert(format!("{}_dom", name), new_dom);
        }
        let old_len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| format!("No length tracked for Map '{}' in remove", rname))?;
        // Route A (#2779): Map length is an unbounded Int. Cardinality bounds
        // `old-1 <= new <= old` are Int constraints; the non-negativity is
        // implied by `new >= old-1 >= 0` under the present-element guard, so
        // the bounded-width wrap obligation disappears. Match the source
        // length's sort so legacy/test BV lengths stay consistent.
        let new_len = self
            .solver
            .fresh_var("__map_len_remove", self.solver.term_sort(old_len));
        let one = self.len_const_like(old_len, 1)?;
        let old_minus_one = self.len_sub(old_len, one)?;
        let zero = self.len_const_like(old_len, 0)?;
        let ge_zero = self.len_ge(new_len, zero)?;
        self.solver
            .try_assert_term(ge_zero)
            .map_err(|e| e.to_string())?;
        let old_pos = self.len_gt(old_len, zero)?;
        let ge_minus = self.len_ge(new_len, old_minus_one)?;
        let guarded = self
            .solver
            .try_implies(old_pos, ge_minus)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(guarded)
            .map_err(|e| e.to_string())?;
        let le = self.len_le(new_len, old_len)?;
        self.solver.try_assert_term(le).map_err(|e| e.to_string())?;
        if let Some(name) = receiver_name {
            self.collection_lengths.insert(name.to_string(), new_len);
        }
        // new_len is Int (Route A #2779); register_collection_meta skips BV-width
        // registration for Int lengths, so no term_widths insert is needed.
        let elem_ty = self.resolve_source_elem_ty(receiver_term, receiver_name);
        let key_ty = self
            .collection_meta_by_term
            .get(&receiver_term)
            .and_then(|m| m.key_ty.clone());
        self.register_collection_meta(
            result_term,
            CollectionMeta {
                kind: CollectionKind::Map,
                len_term: Some(new_len),
                len_guard: None,
                elem_ty,
                key_ty,
                dom_term: Some(new_dom),
            },
        );
        Ok(result_term)
    }

    // =================================================================
    // Set binary operations
    // =================================================================

    /// Encode Set::union, Set::intersect, or Set::difference from TrustVcExpr args.
    ///
    /// Creates a fresh array variable for the result and asserts a universally
    /// quantified axiom defining its contents.
    pub(super) fn encode_trust_vc_set_binary_op(
        &mut self,
        receiver_term: Term,
        args: &[TrustVcExpr],
        receiver_name: Option<&str>,
        method: &str,
    ) -> TrustVcResult<Term> {
        let [arg] = args else {
            return Err(format!(
                "Set::{}() requires exactly 1 argument, got {}",
                method,
                args.len()
            )
            .into());
        };
        let other = self.encode_subexpr(arg)?;
        let elem_ty = self.set_element_trust_vc_type(receiver_term, receiver_name)?;
        let elem_sort = sort_for_type(&elem_ty);

        let result_sort = Sort::Array(Box::new(ArraySort {
            index_sort: elem_sort,
            element_sort: Sort::Bool,
        }));
        let result = self.solver.fresh_var("__set_result", result_sort);

        // Safe quantification via helper — native-sorted bound var (#2531)
        let (quant_var, elem_term) = self.safe_element_quantifier("__set_elem", &elem_ty)?;

        let self_has = self
            .solver
            .try_select(receiver_term, elem_term)
            .map_err(|e| e.to_string())?;
        let other_has = self
            .solver
            .try_select(other, elem_term)
            .map_err(|e| e.to_string())?;
        let result_has = self
            .solver
            .try_select(result, elem_term)
            .map_err(|e| e.to_string())?;

        let combined = match method {
            "union" => self
                .solver
                .try_or(self_has, other_has)
                .map_err(|e| e.to_string())?,
            "intersect" => self
                .solver
                .try_and(self_has, other_has)
                .map_err(|e| e.to_string())?,
            "difference" => {
                let not_other = self.solver.try_not(other_has).map_err(|e| e.to_string())?;
                self.solver
                    .try_and(self_has, not_other)
                    .map_err(|e| e.to_string())?
            }
            _ => {
                return Err(format!(
                    "unknown set operation `{method}` — supported Set operations are: \
                 contains, insert, remove, union, intersect, difference, is_subset, \
                 len, is_empty, filter, map, fold"
                )
                .into())
            }
        };

        let body = self
            .solver
            .try_eq(result_has, combined)
            .map_err(|e| e.to_string())?;
        let guarded = self.guard_element_quantifier(&elem_ty, quant_var, body)?;
        let axiom = self
            .solver
            .try_forall(&[quant_var], guarded)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(axiom)
            .map_err(|e| e.to_string())?;

        // Register term metadata so downstream chained operations (e.g.,
        // `s.union(t).contains(v)`) can resolve the collection kind (#2067).
        let elem_ty = self.resolve_source_elem_ty(receiver_term, receiver_name);
        self.register_collection_meta(
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
        // Cardinality of a union/intersection/difference is not either operand's
        // (inclusion-exclusion needs the overlap). The result is anonymous, so
        // without this the name fallback would answer `.len()` with the LEFT
        // operand's length — `s.union(t).len() == s.len()` verified for disjoint
        // non-empty `t`.
        self.decline_collection_len(result);

        Ok(result)
    }

    // =================================================================
    // Array indexing
    // =================================================================

    /// Encode array/Seq indexing: receiver[index].
    ///
    /// Adds bounds checking for Seq types (parity: methods.rs:32-37) and
    /// element width registration (parity: methods.rs:43-45).
    pub(super) fn encode_index(
        &mut self,
        receiver: &TrustVcExpr,
        index: &TrustVcExpr,
        receiver_name: Option<&str>,
        elem_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        // Under native-seq (#2680 Slice 2), Seq indexing uses seq.nth.
        #[cfg(feature = "native-seq")]
        {
            let is_seq = match receiver {
                TrustVcExpr::Var { ty, .. } => {
                    matches!(ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _))
                }
                TrustVcExpr::CollectionOp { ty, .. } => {
                    matches!(ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _))
                }
                TrustVcExpr::FnCall { return_ty, .. } => {
                    matches!(return_ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _))
                }
                _ => false,
            };
            if is_seq {
                return self.encode_native_seq_index(receiver, index);
            }
        }

        if let Some(result) = self.try_encode_seq_concat_index(receiver, index)? {
            return Ok(result);
        }

        let receiver_term = self.encode_subexpr(receiver)?;
        let index_term = self.encode_subexpr(index)?;
        let rname = receiver_name.unwrap_or("_anon");

        if !self.collection_meta_by_term.contains_key(&receiver_term) {
            if let Some(meta) = self.typed_collection_meta_with_static_array_len(
                receiver,
                receiver_term,
                receiver_name,
            )? {
                self.register_collection_meta(receiver_term, meta);
            }
        }

        let is_map = self.receiver_is_map(receiver_term, Some(rname));
        // Same-index `Seq::push` read-back (see
        // `try_encode_push_same_index_readback`): reuse the store's own carrier
        // index so the just-pushed cell reads back exactly, with no spurious
        // representability obligation. Skipped for nested-array elements, whose
        // element-metadata registration below the select must still run.
        if !is_map && !matches!(elem_ty, TrustVcType::Array(_, _)) {
            if let Some(result) =
                self.try_encode_push_same_index_readback(receiver_term, index_term, Some(rname))?
            {
                return Ok(result);
            }
        }
        let idx = if is_map {
            self.coerce_key_for_store_in_int_mode(index_term, receiver_term, Some(rname))?
        } else {
            self.coerce_seq_index(receiver_term, Some(rname), index_term)?
        };

        // Verus precondition: Map indexing requires key membership; Seq
        // indexing requires 0 <= idx < len.
        if is_map {
            self.add_map_index_domain_check(receiver_term, Some(rname), idx, "index")?;
        } else {
            self.add_seq_index_bounds_check(receiver_term, Some(rname), idx, "index")?;
        }

        let result = self
            .solver
            .try_select(receiver_term, idx)
            .map_err(|e| e.to_string())?;

        // Register element width for downstream coercion (parity: methods.rs:43-45)
        if let Some(info) = self.element_width_info(receiver_term, Some(rname)) {
            self.term_widths.insert(result, info);
        }
        if let TrustVcType::Array(inner, len) = elem_ty {
            let len = i64::try_from(*len)
                .map_err(|_| format!("array length {len} exceeds solver literal range"))?;
            let len_term = self
                .solver
                .try_bv_const(len, crate::ir::pointer_width())
                .map_err(|e| e.to_string())?;
            self.register_collection_meta(
                result,
                CollectionMeta {
                    kind: CollectionKind::Seq,
                    len_term: Some(len_term),
                    len_guard: None,
                    elem_ty: Some(*inner.clone()),
                    key_ty: None,
                    dom_term: None,
                },
            );
        }
        // In int_mode, convert BV element to Int (parity: methods.rs:47)
        let result = self.coerce_element_for_int_mode(result, receiver_term, Some(rname))?;
        Ok(result)
    }

    pub(in crate::encoder::ir_encoder) fn add_map_index_domain_check(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        key: Term,
        method: &str,
    ) -> TrustVcResult<()> {
        // Map extensional equality guards the select explicitly with
        // contains_key; do not leak Map::get's public precondition here.
        if receiver_name == Some(crate::extensional_eq::MAP_EXTENSIONAL_SELECT_RECEIVER) {
            return Ok(());
        }
        let rname = receiver_name.unwrap_or("<anonymous>");
        let dom = self
            .lookup_collection_dom(receiver_term, receiver_name)
            .ok_or_else(|| format!("Map::{method} requires domain tracking for '{rname}'"))?;
        let in_domain = self
            .solver
            .try_select(dom, key)
            .map_err(|e| format!("Map::{method} domain membership check: {e}"))?;
        self.overflow_checks.push((
            format!("Map::{method}(k) requires contains_key(k)").into(),
            in_domain,
        ));
        Ok(())
    }
}
