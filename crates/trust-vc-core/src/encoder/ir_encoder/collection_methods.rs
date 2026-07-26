//! Collection metadata and helper methods — contains, remove, push, subrange.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from collections.rs to stay under 500 LOC (#2249).

use ay_dpll::api::{Sort, Term};

use crate::encoder::parser_state::{
    CollectionKind, CollectionMeta, DerivedSeqViewKind, PushReadback,
};
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    pub(super) fn typed_collection_meta(receiver: &TrustVcExpr) -> Option<CollectionMeta> {
        match crate::ir_lowering::infer_expr_type(receiver) {
            TrustVcType::Seq(elem_ty) | TrustVcType::Array(elem_ty, _) => Some(CollectionMeta {
                kind: CollectionKind::Seq,
                len_term: None,
                len_guard: None,
                elem_ty: Some(*elem_ty),
                key_ty: None,
                dom_term: None,
            }),
            TrustVcType::Set(elem_ty) => Some(CollectionMeta {
                kind: CollectionKind::Set,
                len_term: None,
                len_guard: None,
                elem_ty: Some(*elem_ty),
                key_ty: None,
                dom_term: None,
            }),
            TrustVcType::Multiset(elem_ty) => Some(CollectionMeta {
                kind: CollectionKind::Multiset,
                len_term: None,
                len_guard: None,
                elem_ty: Some(*elem_ty),
                key_ty: None,
                dom_term: None,
            }),
            TrustVcType::Map(key_ty, value_ty) => Some(CollectionMeta {
                kind: CollectionKind::Map,
                len_term: None,
                len_guard: None,
                elem_ty: Some(*value_ty),
                key_ty: Some(*key_ty),
                dom_term: None,
            }),
            _ => None,
        }
    }

    pub(super) fn typed_collection_meta_with_static_array_len(
        &mut self,
        receiver: &TrustVcExpr,
        receiver_term: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Option<CollectionMeta>> {
        let Some(mut meta) = Self::typed_collection_meta(receiver) else {
            return Ok(None);
        };
        meta.len_term = self.lookup_collection_len(receiver_term, receiver_name);
        meta.dom_term = self.lookup_collection_dom(receiver_term, receiver_name);
        if meta.len_term.is_none() {
            if let TrustVcType::Array(_, len) = crate::ir_lowering::infer_expr_type(receiver) {
                let len = i64::try_from(len)
                    .map_err(|_| format!("array length {len} exceeds solver literal range"))?;
                meta.len_term = Some(
                    self.solver
                        .try_bv_const(len, crate::ir::pointer_width())
                        .map_err(|e| e.to_string())?,
                );
            }
        }
        Ok(Some(meta))
    }

    /// Resolve the collection kind for a receiver, checking term metadata
    /// first, then falling back to typed IR inference.
    pub(super) fn resolve_receiver_kind(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        receiver: &TrustVcExpr,
    ) -> Option<CollectionKind> {
        if let Some(kind) = self.lookup_collection_kind(receiver_term, receiver_name) {
            Some(kind)
        } else if let Some(meta) = Self::typed_collection_meta(receiver) {
            let kind = meta.kind;
            self.register_collection_meta(receiver_term, meta);
            Some(kind)
        } else {
            None
        }
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 in each supported branch
    pub(super) fn encode_contains(
        &mut self,
        receiver_term: Term,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("contains() expects 1 argument, got {}", args.len()).into());
        }
        // Discriminate by collection type, using term-keyed metadata first (#1749),
        // then falling back to the typed IR receiver when the receiver is
        // anonymous (for example `mk_set().contains(5)`). Register the
        // inferred collection metadata so downstream width coercion can still
        // recover Set/Seq element types without a name binding.
        let kind = if let Some(kind) = self.lookup_collection_kind(receiver_term, receiver_name) {
            Some(kind)
        } else if let Some(meta) = Self::typed_collection_meta(receiver) {
            let kind = meta.kind;
            self.register_collection_meta(receiver_term, meta);
            Some(kind)
        } else {
            None
        };
        let derived_view = self.lookup_derived_seq_view(receiver_term);
        match kind {
            Some(CollectionKind::Seq) => {
                let value = self.encode_subexpr(&args[0])?;
                let finite_len_hint = Self::finite_seq_literal_len(receiver);
                self.encode_seq_contains(receiver_term, receiver_name, value, finite_len_hint)
            }
            Some(CollectionKind::Multiset) => {
                let count = self.encode_multiset_count(receiver_term, receiver_name, args)?;
                let zero = self.solver.int_const(0);
                self.solver
                    .try_gt(count, zero)
                    .map_err(|e| e.to_string().into())
            }
            Some(CollectionKind::Map) => {
                Err("Map::contains() does not exist — use Map::contains_key(k) \
                 for key membership testing."
                    .to_string()
                    .into())
            }
            Some(CollectionKind::Set) => {
                if let Some(view) = derived_view.as_ref() {
                    if view.kind == DerivedSeqViewKind::SetView {
                        let source_seq = view.source_term;
                        let source_name = view.source_name.as_deref();
                        let source_len = self
                            .lookup_collection_len(source_seq, source_name)
                            .ok_or_else(|| {
                                format!(
                                    "No length tracking for Seq '{}' in derived Set contains()",
                                    source_name.unwrap_or("<anonymous>")
                                )
                            })?;
                        let value = self.encode_subexpr(&args[0])?;

                        // A COMPOSED source view (`subrange()`, a `push`-chain
                        // literal, `add()`) has a STATIC element count that is not a
                        // bare literal length term, so both the declared-only
                        // delegation below and the bespoke `0..5` enumeration leave
                        // e.g. `seq![..].subrange(1,4).to_set().contains(x)` at
                        // Unknown — even though the direct `.subrange(1,4).contains(x)`
                        // decides it (refuting an absent member, verifying a present
                        // one). Recover that exact length from the `.to_set()`
                        // receiver's SOURCE expression and delegate to the general
                        // `encode_seq_contains` with it as a finite-length hint, which
                        // grounds the concrete-index membership through the
                        // fixed-array path. Sound: `seq_static_len` returns `Some`
                        // only for a fully-determined finite length (the EXACT
                        // element count of `source_seq`, whose elements fold via the
                        // view's ground seeds), and this is the same encoding used by
                        // a direct `seq.contains(x)`.
                        if let TrustVcExpr::CollectionOp {
                            op: CollectionOp::ToSet,
                            receiver: source_expr,
                            ..
                        } = receiver
                        {
                            if let Some(hint) = crate::extensional_eq::seq_static_len(source_expr) {
                                return self.encode_seq_contains(
                                    source_seq,
                                    source_name,
                                    value,
                                    Some(hint),
                                );
                            }
                        }

                        let declared_source =
                            source_name.is_some_and(|name| self.var_types.contains_key(name));
                        let finite_push_chain = self
                            .solver
                            .format_term(source_len)
                            .contains("__seq_len_push");
                        if declared_source && !finite_push_chain {
                            return self.encode_seq_contains(source_seq, source_name, value, None);
                        }

                        let pw = crate::ir::pointer_width();
                        let mut value = self.coerce_value_for_store_in_int_mode(
                            value,
                            source_seq,
                            source_name,
                        )?;
                        // `len <= 5` is a length comparison (Int under Route A
                        // #2779); the per-index `idx < len` guards use a BV view.
                        let five_len = self.len_const_like(source_len, 5)?;
                        let small_len = self.len_le(source_len, five_len)?;
                        self.overflow_checks.push((
                            "Seq-derived contains() currently requires len <= 5".into(),
                            small_len,
                        ));
                        let source_len_bv = self.len_as_index_bv(source_len)?;
                        let mut grounded = self.solver.bool_const(false);
                        for idx_value in 0i64..5 {
                            let idx = self
                                .solver
                                .try_bv_const(idx_value, pw)
                                .map_err(|e| e.to_string())?;
                            let in_range = self
                                .solver
                                .try_bvult(idx, source_len_bv)
                                .map_err(|e| e.to_string())?;
                            let candidate = self
                                .solver
                                .try_select(source_seq, idx)
                                .map_err(|e| e.to_string())?;
                            if let Some(info) = self.element_width_info(source_seq, source_name) {
                                self.term_widths.insert(candidate, info);
                                self.term_widths.entry(value).or_insert(info);
                            }
                            let (candidate, coerced_value) =
                                self.coerce_bv_widths(candidate, value)?;
                            value = coerced_value;
                            let matches = self
                                .solver
                                .try_eq(candidate, value)
                                .map_err(|e| e.to_string())?;
                            let witness = self
                                .solver
                                .try_and(in_range, matches)
                                .map_err(|e| e.to_string())?;
                            grounded = self
                                .solver
                                .try_or(grounded, witness)
                                .map_err(|e| e.to_string())?;
                        }
                        return Ok(grounded);
                    }
                }
                let elem = self.encode_subexpr(&args[0])?;
                let elem =
                    self.coerce_key_for_store_in_int_mode(elem, receiver_term, receiver_name)?;
                self.solver
                    .try_select(receiver_term, elem)
                    .map_err(|e| e.to_string().into())
            }
            None => Err("contains() requires a receiver with known collection type \
                 (Set<T>, Multiset<T>, or Seq<T>). If the receiver is an anonymous chained \
                 expression, ensure the producing operation registers term metadata."
                .to_string()
                .into()),
        }
    }

    pub(in crate::encoder) fn finite_seq_literal_len(expr: &TrustVcExpr) -> Option<usize> {
        match expr {
            TrustVcExpr::Var {
                ty: TrustVcType::Array(_, len),
                ..
            } => Some(*len),
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } if args.is_empty()
                && Self::is_empty_collection_constructor_name(name)
                && name.contains("Seq_")
                && matches!(return_ty, TrustVcType::Seq(_)) =>
            {
                Some(0)
            }
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Push,
                receiver,
                args,
                ty,
                ..
            } if args.len() == 1 && matches!(ty, TrustVcType::Seq(_)) => {
                Self::finite_seq_literal_len(receiver)?.checked_add(1)
            }
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Add | CollectionOp::Concat,
                receiver,
                args,
                ty,
                ..
            } if args.len() == 1 && matches!(ty, TrustVcType::Seq(_)) => {
                Self::finite_seq_literal_len(receiver)?
                    .checked_add(Self::finite_seq_literal_len(&args[0])?)
            }
            TrustVcExpr::CollectionOp {
                op: CollectionOp::View,
                receiver,
                ..
            } => Self::finite_seq_literal_len(receiver),
            TrustVcExpr::Cast {
                expr,
                to_ty: TrustVcType::Seq(_),
                ..
            } => Self::finite_seq_literal_len(expr),
            _ => None,
        }
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(super) fn encode_remove(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("remove() expects 1 argument, got {}", args.len()).into());
        }
        let elem = self.encode_subexpr(&args[0])?;
        let elem = self.coerce_key_for_store_in_int_mode(elem, receiver_term, Some(rname))?;
        let false_val = self.solver.bool_const(false);
        let result = self
            .solver
            .try_store(receiver_term, elem, false_val)
            .map_err(|e| e.to_string())?;
        // Exact cardinality for Set::remove (#1800 Slice 3).
        // new_len == old_len - ite(select(set, elem), 1, 0)
        // Uses term-keyed lookup (#1749).
        // Fail-closed: return error if no length tracked. Fixes #2142.
        let old_len = self
            .lookup_collection_len(receiver_term, Some(rname))
            .ok_or_else(|| format!("No length tracked for collection '{}' in remove", rname))?;
        {
            // Route A (#2779): Set cardinality is an unbounded Int. Match the
            // source length's sort so legacy/test BV lengths stay consistent.
            let new_len_sort = self.solver.term_sort(old_len);
            let new_len = self.solver.fresh_var("__set_len_remove", new_len_sort);
            // Exact conditional cardinality plus a guarded no-wrap underflow
            // predicate (#1800 Slice 3). select(set, elem) is checked on the
            // ORIGINAL set (receiver_term), not the result (which already has
            // elem removed).
            let len_guard =
                self.assert_set_remove_cardinality(new_len, old_len, receiver_term, elem)?;
            self.collection_lengths.insert(rname.to_string(), new_len);
            // new_len is Int; register_collection_meta skips BV-width registration.
            // Register term metadata for chained operations (e.g.,
            // `s.remove(5).contains(3)`) so downstream can resolve kind (#2067).
            let elem_ty = self.resolve_source_elem_ty(receiver_term, Some(rname));
            self.register_collection_meta(
                result,
                CollectionMeta {
                    kind: CollectionKind::Set,
                    len_term: Some(new_len),
                    len_guard: Some(len_guard),
                    elem_ty,
                    key_ty: None,
                    dom_term: None,
                },
            );
        }
        Ok(result)
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(super) fn encode_push(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
        finite_len_hint: Option<usize>,
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("push expects 1 argument, got {}", args.len()).into());
        }
        let val = self.encode_subexpr(&args[0])?;
        let val = self.coerce_value_for_store_in_int_mode(val, receiver_term, Some(rname))?;
        // Resolve length via term-keyed metadata first, then name fallback (#1749).
        let pw = crate::ir::pointer_width();
        let len_term = self
            .lookup_collection_len(receiver_term, Some(rname))
            .ok_or_else(|| format!("No length tracked for collection '{}'", rname))?;
        // The append position is the old length used as an array INDEX, so it
        // must be BV(pw); the LENGTH stays Int (Route A #2779). With a literal
        // length hint the index is the concrete BV constant.
        let append_idx_bv = if let Some(len) = finite_len_hint {
            let len = i64::try_from(len)
                .map_err(|_| format!("collection literal length {len} exceeds solver range"))?;
            self.solver
                .try_bv_const(len, pw)
                .map_err(|e| e.to_string())?
        } else {
            self.len_as_index_bv(len_term)?
        };
        let result = self
            .solver
            .try_store(receiver_term, append_idx_bv, val)
            .map_err(|e| e.to_string())?;
        // Record same-index read-back provenance (see `PushReadback`): a later
        // `db.index(db.len() - 1)` reduces to a select at the SAME `append_idx_bv`,
        // which read-over-write discharges to `val` regardless of int2bv carrier
        // representability. `store_index_int` is the Int `old_len` ONLY when the
        // store index crossed via a wrapping `int2bv` (the case that queued the
        // representability obligation the recognizer retracts); a finite/literal
        // push writes a representable BV constant, so there is nothing to retract.
        let store_index_int = if finite_len_hint.is_none() && self.len_is_int(len_term) {
            Some(len_term)
        } else {
            None
        };
        self.push_readback_by_term.insert(
            result,
            PushReadback {
                store_index: append_idx_bv,
                store_index_int,
            },
        );
        let appended = self
            .solver
            .try_select(result, append_idx_bv)
            .map_err(|e| e.to_string())?;
        let appended_eq = self
            .solver
            .try_eq(appended, val)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(appended_eq)
            .map_err(|e| e.to_string())?;
        let constructor_backed = Self::is_empty_collection_constructor_name(rname);
        if !constructor_backed {
            // Explicit element-preservation axiom (#1979).
            self.assert_store_preservation(result, receiver_term, append_idx_bv, "push")?;
        }
        // Update length: new_len = old_len + 1 — Int addition, monotone, no
        // wrap. The bounded-width "push length no overflow" / non-negativity
        // obligations are artifacts of the old BV length model and are absent
        // over the integers (MAX+1 != 0), so they DISAPPEAR on the Int path.
        let new_len = if let Some(len) = finite_len_hint {
            let new_len = len
                .checked_add(1)
                .ok_or_else(|| "collection literal length overflow in push".to_string())?;
            let new_len = i64::try_from(new_len)
                .map_err(|_| format!("collection literal length {new_len} exceeds solver range"))?;
            self.solver.int_const(new_len)
        } else if constructor_backed {
            // Finite push-chain length witness (detected by name downstream).
            self.solver.fresh_var("__seq_len_push", Sort::Int)
        } else {
            let one_len = self.len_const_like(len_term, 1)?;
            self.len_add(len_term, one_len)?
        };
        if !self.len_is_int(new_len) {
            // Legacy BV-length path retains the bounded-width guards.
            let zero = self.solver.try_bv_const(0, pw).map_err(|e| e.to_string())?;
            let nonneg = self
                .solver
                .try_bvuge(new_len, zero)
                .map_err(|e| format!("push length non-negativity: {}", e))?;
            self.overflow_checks
                .push(("push length non-negative".into(), nonneg));
            let no_overflow = self
                .solver
                .try_bvuge(new_len, len_term)
                .map_err(|e| format!("push length overflow: {}", e))?;
            self.overflow_checks
                .push(("push length no overflow".into(), no_overflow));
        }
        if constructor_backed {
            // Constructor-backed push-chain witnesses are fresh and unbounded;
            // anchor non-negativity so chained .len() reasoning stays sound.
            let zero = self.solver.int_const(0);
            let nonneg = self
                .solver
                .try_ge(new_len, zero)
                .map_err(|e| format!("push length non-negativity: {}", e))?;
            self.solver
                .try_assert_term(nonneg)
                .map_err(|e| e.to_string())?;
        } else {
            self.collection_lengths.insert(rname.to_string(), new_len);
        }
        // Register term-keyed metadata so chained operations (e.g., s.push(v).len())
        // can resolve this result's length without a variable name (#1749).
        self.register_seq_len(result, new_len, receiver_term, Some(rname));
        // Explicit length axiom for cross-function reasoning (#1800).
        self.assert_push_length_axiom(new_len, len_term)?;
        Ok(result)
    }

    #[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() == 2 above
    pub(super) fn encode_subrange(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 2 {
            return Err(format!("subrange() expects 2 arguments, got {}", args.len()).into());
        }
        let len = self
            .lookup_collection_len(receiver_term, Some(rname))
            .ok_or_else(|| format!("No length tracked for collection '{}'", rname))?;
        let start = self.encode_subexpr(&args[0])?;
        let end = self.encode_subexpr(&args[1])?;
        let start_pw = self.coerce_to_len_width(start)?;
        let end_pw = self.coerce_to_len_width(end)?;
        // `start <= end` across possibly-mixed BV/Int sorts: a length-derived
        // bound (`(v).len()`, `(v).len() - 1`) stays Sort::Int under Route A
        // (#2779) and `coerce_to_len_width` passes it through outside
        // quantifier bodies, so a raw `bvule` here was ill-sorted (BV64 vs
        // Int). `index_bound_le` compares in Int with an EXACT `bv2int` lift
        // of any BV side — never a wrapping `int2bv` in an obligation.
        let start_le_end = self
            .index_bound_le(start_pw, end_pw)
            .map_err(|e| format!("Failed to create subrange bounds check: {}", e))?;
        self.overflow_checks.push((
            "Seq::subrange(start, end) requires start <= end".into(),
            start_le_end,
        ));
        // An Int-sorted `start` is not `>= 0` by sort (the unsigned BV path
        // was); keep the Verus `0 <= start` precondition genuinely enforced.
        self.push_int_bound_nonneg_check(
            start_pw,
            "Seq::subrange(start, end) requires 0 <= start",
        )?;
        // Discharge `end <= len`: a BV `end` keeps the incumbent BV-domain
        // discharge (peer BV bounds live there) against a BV view of the
        // (Int) length — avoids an incompletely-handled bv2int bridge in the
        // obligation. An Int `end` compares in the length's own Int domain
        // instead (exact; lowering it via a wrapping `int2bv` could discharge
        // a genuinely-violated `end <= len` for a negative/huge bound).
        let end_le_len = if self.len_is_int(end_pw) {
            self.index_bound_le(end_pw, len)
                .map_err(|e| format!("Failed to create subrange bounds check: {}", e))?
        } else {
            let len_bv = self.len_as_index_bv(len)?;
            self.solver
                .try_bvule(end_pw, len_bv)
                .map_err(|e| format!("Failed to create subrange bounds check: {}", e))?
        };
        self.overflow_checks.push((
            "Seq::subrange(start, end) requires end <= len".into(),
            end_le_len,
        ));
        // new_len = end - start is a LENGTH (Int). The shift offset into the
        // carrier remains a BV index.
        let end_len = self.len_match_sort(len, end_pw)?;
        let start_len = self.len_match_sort(len, start_pw)?;
        let new_len = self.len_sub(end_len, start_len)?;

        // The carrier shift offset must be a BitVec(pw) index. An Int start
        // (e.g. `subrange((v).len(), (v).len())` from the Vec::append model)
        // is bridged via the total `len_as_index_bv`; exact within the
        // BV(pw)-indexed carrier once the pushed `0 <= start <= end <= len`
        // obligations hold. A BV start is already pointer_width (#1745).
        let start_idx = if self.len_is_int(start_pw) {
            self.len_as_index_bv(start_pw)?
        } else {
            start_pw
        };
        let receiver_name = Some(rname);
        self.encode_index_shifted_seq(receiver_term, receiver_name, start_idx, new_len)
    }
}
