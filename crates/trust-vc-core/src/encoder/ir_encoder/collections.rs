//! Collection operation dispatch for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Metadata/query helpers live in `collection_methods.rs`; extracted inline
//! Seq and Set/Map dispatch helpers live in `collection_seq_inline.rs` and
//! `collection_set_map_inline.rs`; mutation helpers, Set binary ops, and index
//! encoding are in `indexing.rs`.

use ay_dpll::api::Term;

use crate::encoder::parser_state::{CollectionKind, DerivedSeqViewKind};
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};

/// Check if a TrustVcExpr receiver represents a Seq-typed collection.
///
/// Used under `native-seq` to dispatch Seq operations to the native ay
/// Seq theory encoder instead of the array-based encoder.
#[cfg(feature = "native-seq")]
fn receiver_expr_is_seq(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::Var { ty, .. } => matches!(ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _)),
        // CollectionOp.ty is the result type. If Seq, the receiver chain is Seq.
        TrustVcExpr::CollectionOp { ty, .. } => {
            matches!(ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _))
        }
        TrustVcExpr::FnCall { return_ty, .. } => {
            matches!(return_ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _))
        }
        TrustVcExpr::Cast { expr, .. } => receiver_expr_is_seq(expr),
        _ => false,
    }
}

/// Bind the arguments of `receiver.op(args)` that stand for an element, a key
/// or a value of the receiver at that type (`ir_lowering::bind_call_argument`,
/// §5b rule 6): a value of the element type as is, a literal the element type
/// holds at it, a fixed-width value whose every value it holds widened by the
/// value's OWN sign (`Seq<i64>::contains(x_i32)` sign-extends `x`), anything
/// else refused. Every other argument (an index, a count, a closure) passes
/// unchanged.
///
/// The widening used to happen on TERMS, by the value term's `term_widths`
/// entry — which for a hash-consed constant answers for whichever occurrence
/// registered last — after `contains`/`index_of` had registered the value
/// with the ELEMENT's sign when it had no entry of its own; and a value wider
/// than the element was truncated to it.
fn bind_element_arguments(
    op: CollectionOp,
    receiver: &TrustVcExpr,
    args: &[TrustVcExpr],
) -> TrustVcResult<Vec<TrustVcExpr>> {
    let receiver_ty = crate::ir_lowering::infer_expr_type(receiver);
    let slots: Vec<(usize, TrustVcType)> = match (&receiver_ty, op) {
        (
            TrustVcType::Seq(elem) | TrustVcType::Array(elem, _),
            CollectionOp::Contains | CollectionOp::Count | CollectionOp::Push,
        ) => vec![(0, *elem.clone())],
        (TrustVcType::Seq(elem) | TrustVcType::Array(elem, _), CollectionOp::Update) => {
            vec![(1, *elem.clone())]
        }
        (
            TrustVcType::Set(elem) | TrustVcType::Multiset(elem),
            CollectionOp::Contains
            | CollectionOp::Count
            | CollectionOp::Insert
            | CollectionOp::Remove,
        ) => vec![(0, *elem.clone())],
        (
            TrustVcType::Map(key, _),
            CollectionOp::ContainsKey | CollectionOp::Get | CollectionOp::Remove,
        ) => vec![(0, *key.clone())],
        (TrustVcType::Map(_, value), CollectionOp::ContainsValue) => vec![(0, *value.clone())],
        (TrustVcType::Map(key, value), CollectionOp::Insert) => {
            vec![(0, *key.clone()), (1, *value.clone())]
        }
        _ => Vec::new(),
    };
    let mut bound = args.to_vec();
    for (index, elem_ty) in slots {
        let Some(arg) = args.get(index) else { continue };
        let bound_arg =
            crate::ir_lowering::bind_call_argument(arg, &elem_ty).map_err(|arg_ty| {
                format!(
                    "`{op:?}` on a `{}` is passed a value of type `{}`, which its element type \
                 cannot hold",
                    receiver_ty.to_type_string(),
                    arg_ty.to_type_string()
                )
            })?;
        if let Some(slot) = bound.get_mut(index) {
            *slot = bound_arg;
        }
    }
    Ok(bound)
}

impl<'a> AstExpressionParser<'a> {
    // =================================================================
    // Collections (Seq/Set/Multiset/Map)
    // =================================================================

    /// Encode a collection operation (Seq/Set/Map method call).
    ///
    /// This dispatches by `CollectionOp` enum instead of method name string.
    #[allow(clippy::indexing_slicing)] // args[0]/args[1] guarded by args.len() checks in each arm
    pub(super) fn encode_collection_op(
        &mut self,
        op: CollectionOp,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
        _ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        // An argument that stands for an ELEMENT (or key, or value) of the
        // receiver is bound at that type here, where its own expression is
        // still known — widened by ITS OWN sign where the element type holds
        // it, refused otherwise (`bind_element_arguments`). The term-level
        // encoders below neither widen nor narrow a value.
        let bound_args = bind_element_arguments(op, receiver, args)?;
        let args = bound_args.as_slice();
        #[cfg(feature = "native-strings")]
        if matches!(
            crate::ir_lowering::infer_expr_type(receiver),
            TrustVcType::String | TrustVcType::StrSlice
        ) {
            return self.encode_native_string_op(op, receiver, receiver_name, args);
        }

        // Under native-seq (#2680 Slice 2), Seq operations use ay's native
        // Sort::Seq encoding. Dispatch before encoding the receiver because
        // the native module handles receiver encoding internally.
        #[cfg(feature = "native-seq")]
        if receiver_expr_is_seq(receiver) {
            return self.encode_native_seq_op(op, receiver, receiver_name, args);
        }

        if matches!(op, CollectionOp::Get) {
            if let [index] = args {
                if let Some(result) = self.try_encode_seq_concat_index(receiver, index)? {
                    return Ok(result);
                }
            }
        }

        let receiver_term = self.encode_subexpr(receiver)?;
        if matches!(op, CollectionOp::Get)
            && receiver_name == Some(crate::extensional_eq::MAP_EXTENSIONAL_SELECT_RECEIVER)
            && !self.collection_meta_by_term.contains_key(&receiver_term)
        {
            if let Some(meta) =
                self.typed_collection_meta_with_static_array_len(receiver, receiver_term, None)?
            {
                self.register_collection_meta(receiver_term, meta);
            }
        }
        if !self.collection_meta_by_term.contains_key(&receiver_term) {
            if let Some(meta) = self.typed_collection_meta_with_static_array_len(
                receiver,
                receiver_term,
                receiver_name,
            )? {
                self.register_collection_meta(receiver_term, meta);
            }
        }
        let rname = receiver_name.unwrap_or("_anon");
        if let Some(view) = self.lookup_derived_seq_view(receiver_term) {
            match view.kind {
                DerivedSeqViewKind::SetView
                    if !matches!(op, CollectionOp::Contains | CollectionOp::Finite) =>
                {
                    return Err(
                        "Seq::to_set() projection views currently support contains() and finite() only"
                            .to_string()
                            .into(),
                    );
                }
                DerivedSeqViewKind::MultisetView
                    if !matches!(op, CollectionOp::Contains | CollectionOp::Count) =>
                {
                    return Err(
                        "Seq::to_multiset() projection views currently support contains() and count() only"
                            .to_string()
                            .into(),
                    );
                }
                _ => {}
            }
        }

        match op {
            CollectionOp::Len => {
                let len = self.encode_seq_len(receiver_term, receiver_name, rname)?;
                if self.lookup_collection_kind(receiver_term, receiver_name)
                    == Some(CollectionKind::Multiset)
                {
                    self.assert_multiset_nonempty_count_witness(receiver_term, receiver_name)?;
                }
                Ok(len)
            }
            CollectionOp::IsEmpty => {
                let is_empty = self.encode_seq_is_empty(receiver_term, receiver_name, rname)?;
                if self.lookup_collection_kind(receiver_term, receiver_name)
                    == Some(CollectionKind::Multiset)
                {
                    self.assert_multiset_nonempty_count_witness(receiver_term, receiver_name)?;
                }
                Ok(is_empty)
            }
            CollectionOp::Get => self.encode_seq_get(receiver_term, rname, args),
            CollectionOp::Contains => {
                self.encode_contains(receiver_term, receiver, receiver_name, args)
            }
            CollectionOp::ContainsKey => {
                self.encode_contains_key(receiver_term, receiver_name, rname, args)
            }
            CollectionOp::ContainsValue => {
                if let Some(result) = self.try_encode_map_contains_value_finite(
                    receiver,
                    receiver_term,
                    receiver_name,
                    args,
                )? {
                    Ok(result)
                } else {
                    self.encode_map_contains_value(receiver_term, receiver_name, args)
                }
            }
            CollectionOp::Count => {
                // `count(e)` is overloaded. `Multiset::count(e)` is the native
                // pointwise multiplicity; `Seq::count(e)` is the number of
                // occurrences of `e` in the sequence. The Multiset count encoder
                // rejects a Seq operand (`multiset_element_trust_vc_type` →
                // "Expected Multiset<T> operand, got collection kind Seq"), so a
                // Seq receiver must be routed to the bounded array-based
                // occurrence count `encode_seq_occurrence_count` instead. This
                // is exactly the path already used for `to_multiset().count()`;
                // it is sound-or-fail-closed (the emitted `len < 5` guard must be
                // discharged before the count is relied upon).
                //
                // A `to_multiset()` view term is registered with
                // `CollectionKind::Multiset` (see `encode_seq_to_multiset`), so
                // it stays on the Multiset path and flows through
                // `encode_multiset_count`'s MultisetView handling — unchanged.
                //
                // Under `native-seq` a genuine Seq receiver is dispatched to
                // `native_seq_count` by the early `receiver_expr_is_seq` return
                // at the top of this function, so this arm only ever sees a
                // Multiset there; the redirect is gated off to avoid sending a
                // native `Sort::Seq` term to the array-`select` encoding.
                #[cfg(not(feature = "native-seq"))]
                if self.resolve_receiver_kind(receiver_term, receiver_name, receiver)
                    == Some(CollectionKind::Seq)
                {
                    if args.len() != 1 {
                        return Err(
                            format!("count() expects 1 argument, got {}", args.len()).into()
                        );
                    }
                    let needle = self.encode_subexpr(&args[0])?;
                    return self.encode_seq_occurrence_count(receiver_term, receiver_name, needle);
                }
                self.encode_multiset_count(receiver_term, receiver_name, args)
            }
            CollectionOp::Choose => {
                let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
                match kind {
                    Some(CollectionKind::Set) => {
                        self.encode_set_choose(receiver_term, receiver_name, args)
                    }
                    Some(CollectionKind::Multiset) => {
                        self.encode_multiset_choose(receiver_term, receiver_name, args)
                    }
                    _ => Err("choose() is only supported for Set and Multiset receivers"
                        .to_string()
                        .into()),
                }
            }
            CollectionOp::Insert => {
                let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
                match kind {
                    Some(CollectionKind::Multiset) => {
                        self.encode_multiset_insert(receiver_term, receiver_name, args)
                    }
                    _ => self.encode_trust_vc_insert(receiver_term, rname, args),
                }
            }
            CollectionOp::Remove => {
                let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
                match kind {
                    Some(CollectionKind::Multiset) => {
                        self.encode_multiset_remove(receiver_term, receiver_name, args)
                    }
                    Some(CollectionKind::Set) => self.encode_remove(receiver_term, rname, args),
                    Some(CollectionKind::Map) => {
                        self.encode_map_remove(receiver_term, receiver_name, args)
                    }
                    _ => Err("remove() is not supported for this type — \
                         only Set, Multiset, and Map support remove."
                        .to_string()
                        .into()),
                }
            }
            CollectionOp::Push => self.encode_push(
                receiver_term,
                rname,
                args,
                Self::finite_seq_literal_len(receiver),
            ),
            CollectionOp::Update => self.encode_seq_update(receiver, receiver_term, rname, args),
            CollectionOp::First => self.encode_seq_first(receiver_term, receiver_name, rname),
            CollectionOp::Last => self.encode_seq_last(receiver_term, receiver_name, rname),
            CollectionOp::DropLast => {
                self.encode_seq_drop_last(receiver_term, receiver_name, rname)
            }
            CollectionOp::DropFirst => {
                self.encode_seq_drop_first(receiver_term, receiver_name, rname)
            }
            CollectionOp::Take => self.encode_seq_take(receiver_term, receiver_name, rname, args),
            CollectionOp::Skip => self.encode_seq_skip(receiver_term, receiver_name, rname, args),
            CollectionOp::Subrange => self.encode_subrange(receiver_term, rname, args),
            CollectionOp::Concat | CollectionOp::Add => {
                if args.len() != 1 {
                    return Err(format!("concat() expects 1 argument, got {}", args.len()).into());
                }
                let other = self.encode_subexpr(&args[0])?;
                let rhs_name = match &args[0] {
                    TrustVcExpr::Var { name, .. } => Some(name.as_str()),
                    _ => None,
                };
                self.encode_seq_concat(receiver_term, other, rname, rhs_name)
            }
            CollectionOp::SeqMapValues => {
                self.encode_seq_map_values(receiver_term, receiver_name, args)
            }
            CollectionOp::SeqMap => self.encode_seq_map(receiver_term, receiver_name, args),
            CollectionOp::SeqFilter => self.encode_seq_filter(receiver_term, receiver_name, args),
            CollectionOp::SeqFlatMap => {
                self.encode_seq_flat_map(receiver_term, receiver_name, args)
            }
            CollectionOp::SeqFoldLeft => {
                self.encode_seq_fold_left(receiver_term, receiver_name, args)
            }
            CollectionOp::SeqFoldRight => {
                self.encode_seq_fold_right(receiver_term, receiver_name, args)
            }
            CollectionOp::Reverse => self.encode_seq_reverse(receiver_term, receiver_name),
            CollectionOp::NoDuplicates => {
                self.encode_seq_no_duplicates(receiver_term, receiver_name)
            }
            CollectionOp::ToSet => self.encode_seq_to_set(receiver_term, receiver_name),
            CollectionOp::ToMultiset => self.encode_seq_to_multiset(receiver_term, receiver_name),
            CollectionOp::SetFilter => {
                // Memoize closed `set.filter(|x| pred)` over a shared source-set
                // term so duplicate occurrences collapse to one image set. #2778.
                let skip_memo = self.refs_transient_local_binding(&args.iter().collect::<Vec<_>>());
                let key = format!("set_filter::{:?}::{:?}", receiver_term, args);
                self.memoized_pure_collection(skip_memo, key, |s| {
                    s.encode_set_filter(receiver_term, receiver_name, args)
                })
            }
            CollectionOp::SetMap => {
                // Memoize closed `set.map(|x| f)` over a shared source-set term so
                // every occurrence shares one image set + forward/reverse axioms,
                // letting the image axioms fire on the source set's membership
                // facts established elsewhere in the query (GAP3). #2778.
                let skip_memo = self.refs_transient_local_binding(&args.iter().collect::<Vec<_>>());
                let key = format!("set_map::{:?}::{:?}", receiver_term, args);
                self.memoized_pure_collection(skip_memo, key, |s| {
                    s.encode_set_map(receiver_term, receiver_name, args)
                })
            }
            CollectionOp::SetMkMap => self.encode_set_mk_map(receiver_term, receiver_name, args),
            CollectionOp::SetFold => self.encode_set_fold(receiver_term, receiver_name, args),
            CollectionOp::MapMapValues => {
                self.encode_map_map_values(receiver_term, receiver_name, args)
            }
            CollectionOp::MapMapEntries => {
                self.encode_map_map_entries(receiver_term, receiver_name, args)
            }
            CollectionOp::MapFilterKeys => {
                self.encode_map_filter_keys(receiver_term, receiver_name, args)
            }
            CollectionOp::View => self.encode_view(receiver_term, receiver, receiver_name, rname),
            CollectionOp::Union => self.encode_union(receiver_term, receiver, receiver_name, args),
            CollectionOp::Intersect => {
                self.encode_intersect(receiver_term, receiver, receiver_name, args)
            }
            CollectionOp::Difference => {
                self.encode_difference(receiver_term, receiver, receiver_name, args)
            }
            CollectionOp::Subset | CollectionOp::Superset => {
                self.encode_subset_or_superset(receiver_term, rname, args, op)
            }
            CollectionOp::Finite => {
                let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
                match kind {
                    Some(CollectionKind::Set) => {
                        self.encode_set_finite(receiver_term, receiver_name, args)
                    }
                    _ => Err("finite() is only supported for Set receivers"
                        .to_string()
                        .into()),
                }
            }
            CollectionOp::Dom => self.encode_dom(receiver_term, receiver_name, rname),
        }
    }

    #[cfg(feature = "native-strings")]
    fn encode_native_string_op(
        &mut self,
        op: CollectionOp,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let receiver_term = self.encode_subexpr(receiver)?;
        match op {
            CollectionOp::View => {
                self.ensure_native_string_view_shadow(receiver_term, receiver_name)
            }
            CollectionOp::Len => self.native_string_len_term(receiver_term, receiver_name),
            CollectionOp::Contains => {
                if args.len() != 1 {
                    return Err(format!("contains() expects 1 argument, got {}", args.len()).into());
                }
                let needle = self.encode_subexpr(&args[0])?;
                self.solver
                    .try_str_contains(receiver_term, needle)
                    .map_err(|e| e.to_string().into())
            }
            _ => Err(format!(
                "String operation {:?} is not supported in the native-string encoder",
                op
            )
            .into()),
        }
    }
}
