//! Collection metadata helpers for `AstExpressionParser`.
//!
//! Extracted from `parser_state.rs` to isolate the collection metadata
//! lookup and registration surface. These methods operate on term-keyed
//! `CollectionMeta` and the legacy name-keyed fallback maps. Part of #2436.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{ArraySort, Sort, Term};

#[cfg(feature = "native-seq")]
use super::parser_state::NativeSeqShadow;
#[cfg(feature = "native-strings")]
use super::parser_state::NativeStringViewShadow;
use super::parser_state::{AstExpressionParser, CollectionKind, CollectionMeta, DerivedSeqView};
use super::types::sort_for_type;
#[cfg(feature = "native-seq")]
use crate::error::TrustVcError;
use crate::error::TrustVcResult;
use crate::ir::TrustVcType;

impl<'a> AstExpressionParser<'a> {
    /// True for synthetic zero-arity collection constructors such as
    /// `Seq::<T>::empty()`.
    pub(super) fn is_empty_collection_constructor_name(name: &str) -> bool {
        name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
            && (name.ends_with("_empty") || name.ends_with("_new"))
    }

    /// Look up the length term for a collection, resolving term-keyed metadata
    /// first, then falling back to the name-keyed `collection_lengths` map.
    ///
    /// This is the migration entry point for #1749: callers that previously used
    /// `self.collection_lengths.get(name)` should switch to this method so that
    /// anonymous (chained) collection results are resolved correctly.
    pub(super) fn lookup_collection_len(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> Option<Term> {
        // Term-first: covers anonymous results from chained operations.
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let Some(len) = meta.len_term {
                return Some(len);
            }
        }
        // Derived collections that explicitly DECLINED a cardinality must not
        // reach the name fallback. `s.filter(p)` / `s.map(f)` / `s.union(t)` are
        // anonymous results, so `receiver_name` is the *source* collection's
        // name (`lowered_receiver_name` walks a chained `CollectionOp` down to
        // its base receiver). Falling back would answer `s.filter(p).len()` with
        // `s.len()` — the source's cardinality, which is not the derived one's.
        if self.len_declined_terms.contains(&receiver) {
            return None;
        }
        // Name fallback: covers declared variables during migration.
        receiver_name.and_then(|name| self.collection_lengths.get(name).copied())
    }

    /// Mark `term` as a derived collection with no known cardinality.
    ///
    /// Pairs with every `register_collection_meta` call that passes
    /// `len_term: None` because the length genuinely cannot be computed (as
    /// opposed to "not filled in yet"). Sound by construction: it only ever
    /// removes a length answer, so `.len()`/`.is_empty()` fail closed instead of
    /// silently reading the source collection's length.
    pub(super) fn decline_collection_len(&mut self, term: Term) {
        self.len_declined_terms.insert(term);
    }

    /// Register term-keyed metadata for a collection value.
    ///
    /// Called when a collection method produces a new term (e.g., `push` returns
    /// an updated array term with a new length). Also registers the length term
    /// in `term_widths` as pointer-width unsigned so width coercion works.
    pub(super) fn register_collection_meta(&mut self, term: Term, meta: CollectionMeta) {
        if let Some(len) = meta.len_term {
            if !matches!(self.solver.term_sort(len), Sort::Int) {
                self.term_widths
                    .insert(len, (crate::ir::pointer_width(), false));
            }
        }
        self.collection_meta_by_term.insert(term, meta);
    }

    /// Register collection metadata for a quantifier-bound collection value.
    ///
    /// Array-backed collections carry companion length/domain terms in TrustVc's
    /// encoding, so bound collection variables need those companions bound in
    /// the same solver quantifier. The returned terms must be appended to the
    /// quantifier's bound term list.
    pub(super) fn register_bound_collection_meta(
        &mut self,
        name: &str,
        ty: &TrustVcType,
        term: Term,
    ) -> TrustVcResult<Vec<Term>> {
        let kind = match ty {
            TrustVcType::Seq(_) | TrustVcType::Array(_, _) => CollectionKind::Seq,
            TrustVcType::Set(_) => CollectionKind::Set,
            TrustVcType::Multiset(_) => CollectionKind::Multiset,
            TrustVcType::Map(_, _) => CollectionKind::Map,
            _ => return Ok(Vec::new()),
        };

        let mut extra_bound_terms = Vec::new();
        let len_term = self.bound_collection_len_term(name, ty, term)?;
        if let Some(len) = len_term {
            if !matches!(self.solver.term_sort(len), Sort::Int) {
                extra_bound_terms.push(len);
            }
        }

        let dom_term = if let TrustVcType::Map(key_ty, _) = ty {
            let dom_sort = Sort::Array(Box::new(ArraySort {
                index_sort: sort_for_type(key_ty),
                element_sort: Sort::Bool,
            }));
            let dom = self
                .solver
                .fresh_var(&format!("__trust_vc_bound_dom_{name}"), dom_sort);
            extra_bound_terms.push(dom);
            Some(dom)
        } else {
            None
        };

        let key_ty = match ty {
            TrustVcType::Map(key, _) => Some(key.as_ref().clone()),
            _ => None,
        };

        self.register_collection_meta(
            term,
            CollectionMeta {
                kind,
                len_term,
                len_guard: None,
                elem_ty: ty.collection_elem(),
                key_ty,
                dom_term,
            },
        );

        Ok(extra_bound_terms)
    }

    fn bound_collection_len_term(
        &mut self,
        name: &str,
        ty: &TrustVcType,
        _term: Term,
    ) -> TrustVcResult<Option<Term>> {
        #[cfg(not(feature = "native-seq"))]
        let _ = ty;

        #[cfg(feature = "native-seq")]
        if matches!(ty, TrustVcType::Seq(_) | TrustVcType::Array(_, _)) {
            return self
                .solver
                .try_seq_len(_term)
                .map(Some)
                .map_err(|e| TrustVcError::Encoding {
                    context: "quantifier bound collection metadata",
                    detail: format!("Failed to compute seq.len for bound '{name}': {e}"),
                });
        }

        let len = self.solver.fresh_var(
            &format!("__trust_vc_bound_len_{name}"),
            Sort::bitvec(crate::ir::pointer_width()),
        );
        Ok(Some(len))
    }

    /// Register projection-view provenance for an opaque Seq-derived carrier.
    pub(super) fn register_derived_seq_view(&mut self, term: Term, view: DerivedSeqView) {
        self.derived_seq_views.insert(term, view);
    }

    /// Look up projection-view provenance for an opaque Seq-derived carrier.
    pub(super) fn lookup_derived_seq_view(&self, term: Term) -> Option<DerivedSeqView> {
        self.derived_seq_views.get(&term).cloned()
    }

    /// Register native Seq shadow provenance for a source carrier term.
    #[cfg(feature = "native-seq")]
    #[allow(dead_code)]
    pub(super) fn register_native_seq_shadow(&mut self, term: Term, shadow: NativeSeqShadow) {
        self.native_seq_shadows.insert(term, shadow);
    }

    /// Look up the native Seq shadow for a source carrier term.
    #[cfg(feature = "native-seq")]
    #[allow(dead_code)]
    pub(super) fn lookup_native_seq_shadow(&self, term: Term) -> Option<NativeSeqShadow> {
        self.native_seq_shadows.get(&term).cloned()
    }

    /// Register a cached String/str -> Seq<char> view shadow.
    #[cfg(feature = "native-strings")]
    pub(super) fn register_native_string_view_shadow(
        &mut self,
        term: Term,
        shadow: NativeStringViewShadow,
    ) {
        self.native_string_view_shadows.insert(term, shadow);
    }

    /// Look up the cached String/str -> Seq<char> view shadow.
    #[cfg(feature = "native-strings")]
    pub(super) fn lookup_native_string_view_shadow(
        &self,
        term: Term,
    ) -> Option<NativeStringViewShadow> {
        self.native_string_view_shadows.get(&term).cloned()
    }

    /// Register a Seq term with its length (convenience for the common pattern).
    ///
    /// Propagates elem_ty from the source receiver's metadata or var_types (#2067).
    pub(super) fn register_seq_len(
        &mut self,
        term: Term,
        len_term: Term,
        source: Term,
        source_name: Option<&str>,
    ) {
        let elem_ty = self.resolve_source_elem_ty(source, source_name);
        self.register_collection_meta(
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

    /// Queue any path-sensitive guard attached to the receiver's length term.
    ///
    /// Derived collection results such as `s.insert(x)` can have a valid length
    /// term only under an additional finite-cardinality condition. Emit that
    /// guard only when `.len()` / `.is_empty()` is actually consumed.
    pub(super) fn emit_collection_len_guard(&mut self, receiver: Term) {
        let guard = self
            .collection_meta_by_term
            .get(&receiver)
            .and_then(|meta| {
                meta.len_guard
                    .as_ref()
                    .map(|(label, term)| (label.clone(), *term))
            });
        if let Some(guard) = guard {
            self.overflow_checks.push(guard);
        }
    }

    /// Resolve the element type from a source collection's metadata or var_types.
    ///
    /// Used to propagate `elem_ty` to derived collection terms (push, concat,
    /// update, insert, remove) so that downstream chained operations can resolve
    /// element type from term-keyed metadata without a variable name (#2067).
    pub(super) fn resolve_source_elem_ty(
        &self,
        source: Term,
        source_name: Option<&str>,
    ) -> Option<crate::ir::TrustVcType> {
        // Term-first: source may be an anonymous derived term with metadata
        if let Some(meta) = self.collection_meta_by_term.get(&source) {
            if let Some(ref elem) = meta.elem_ty {
                return Some(elem.clone());
            }
        }
        // Name fallback: source is a declared variable
        source_name
            .and_then(|name| self.var_types.get(name))
            .and_then(|ty| ty.collection_elem())
    }

    /// Look up the `CollectionKind` for a receiver, resolving term-keyed
    /// metadata first, then inferring from `var_types`.
    pub(super) fn lookup_collection_kind(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> Option<CollectionKind> {
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            return Some(meta.kind);
        }
        receiver_name
            .and_then(|name| self.var_types.get(name))
            .and_then(|ty| match ty {
                crate::ir::TrustVcType::Seq(_) | crate::ir::TrustVcType::Array(_, _) => {
                    Some(CollectionKind::Seq)
                }
                crate::ir::TrustVcType::Set(_) => Some(CollectionKind::Set),
                crate::ir::TrustVcType::Multiset(_) => Some(CollectionKind::Multiset),
                crate::ir::TrustVcType::Map(_, _) => Some(CollectionKind::Map),
                _ => None,
            })
    }

    /// Look up the domain-membership term for a Map, resolving term-keyed
    /// metadata first and then falling back to the legacy `{name}_dom` maps.
    pub(super) fn lookup_collection_dom(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> Option<Term> {
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let Some(dom) = meta.dom_term {
                return Some(dom);
            }
        }
        receiver_name.and_then(|name| {
            let dom_name = format!("{}_dom", name);
            self.domain_terms
                .get(&dom_name)
                .or_else(|| self.variables.get(&dom_name))
                .copied()
        })
    }
}
