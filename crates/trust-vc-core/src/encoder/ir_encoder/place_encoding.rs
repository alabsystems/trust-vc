//! ay encoding for `ReadPlace` and `PlaceDisjoint` expressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `ReadPlace` walks the projection chain directly, applying datatype selectors
//! through ay's native datatype API and index projections via existing
//! `TrustVcExpr::Index` encoding. `PlaceDisjoint` delegates to
//! `place_disjoint()` which returns a TrustVcExpr directly.
//!
//! Part of #2515 Slice 4.

use ay_dpll::api::{ArraySort, Sort, Term};

use crate::encoder::datatype::{datatype_sort_for, field_sort_for, selector_symbol_name};
use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
use crate::encoder::types::sort_for_type;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_place::{PlaceProjection, TrustVcPlace};

impl<'a> AstExpressionParser<'a> {
    /// Encode a `ReadPlace` by walking the projection chain directly.
    ///
    /// - Field projections → native datatype selector application.
    /// - Index projections → encoded as `TrustVcExpr::Index` through existing paths.
    ///
    pub(super) fn encode_read_place(
        &mut self,
        place: &TrustVcPlace,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        // Start with the root variable
        let root_expr = TrustVcExpr::Var {
            name: place.root_name.clone(),
            ty: place.root_ty.clone(),
        };
        let mut term = self.encode_subexpr(&root_expr)?;
        let mut current_ty = place.root_ty.clone();

        for proj in &place.projections {
            match proj {
                PlaceProjection::Field {
                    field_name,
                    field_ty,
                } => {
                    if let TrustVcType::Datatype { name, variants } = &current_ty {
                        self.solver
                            .try_declare_datatype(&datatype_sort_for(name, variants))
                            .map_err(|e| e.to_string())?;
                    }
                    let selector_name = resolve_selector_name(&current_ty, field_name)?;
                    let selector_sort = match &current_ty {
                        TrustVcType::Datatype { name, .. } => field_sort_for(name, field_ty),
                        _ => sort_for_type(field_ty),
                    };
                    // Protect use_int_arithmetic across field projection — BV-typed
                    // selector results flip the flag, matching match_encode.rs.
                    // Uses with_flag_unwind_safe! for restore-on-exit safety (same
                    // class as #2643). Fixes #2534 acceptance criterion 2.
                    term = crate::encoder::with_flag_unwind_safe!(self.use_int_arithmetic, {
                        let field_term = self
                            .solver
                            .try_datatype_selector(&selector_name, term, selector_sort)
                            .map_err(|e| e.to_string())?;
                        if let Some(width) = field_ty.bit_width() {
                            if width > 0 {
                                let signed = !field_ty.is_unsigned();
                                self.term_widths.insert(field_term, (width, signed));
                                self.use_int_arithmetic = false;
                            }
                        }
                        self.ensure_projected_collection_meta(field_term, field_ty);
                        Ok::<_, crate::error::TrustVcError>(field_term)
                    })?;
                    current_ty = field_ty.clone();
                }
                PlaceProjection::Index { index, elem_ty } => {
                    self.ensure_projected_collection_meta(term, &current_ty);
                    term = self.encode_place_index_projection(term, index, elem_ty)?;
                    self.ensure_projected_collection_meta(term, elem_ty);
                    current_ty = elem_ty.clone();
                }
            }
        }

        if matches!(ty, TrustVcType::Unit) {
            super::super::unit::assert_unit_term(
                self.solver,
                term,
                "encode place read",
                &place.root_name,
            )?;
        }

        Ok(term)
    }

    /// Encode `PlaceDisjoint` by computing the static disjointness expression.
    ///
    /// `place_disjoint()` returns a `TrustVcExpr`:
    /// - `BoolLit(true)` for statically disjoint places
    /// - `BoolLit(false)` for identical/prefix places
    /// - `Compare(Ne, i, j)` for index-differing places
    pub(super) fn encode_place_disjoint(
        &mut self,
        left: &TrustVcPlace,
        right: &TrustVcPlace,
    ) -> TrustVcResult<Term> {
        let result = crate::ir_place::place_disjoint(left, right);
        self.encode_subexpr(&result)
    }

    /// Mint fresh, UNCONSTRAINED dom/len metadata for a collection value that
    /// was reached by PROJECTION rather than declared as a variable.
    ///
    /// Also called from `encode_fn_call` (fn_call.rs): a struct FIELD read in a
    /// SPEC expression does not lower to a `ReadPlace` at all — `lower_field_access`
    /// emits `TrustVcExpr::FnCall { name: <selector UF>, .. }` — so the receiver
    /// never travels the place route and would otherwise carry no metadata,
    /// making every `contains_key()` on it fail closed.
    ///
    /// Soundness: the minted `__trust_vc_place_dom` array and
    /// `__trust_vc_place_len` BV are FRESH and carry no axiom tying them to the
    /// collection value, so they answer nothing the query's own assumptions have
    /// not pinned through the very same term. The early return on an
    /// already-registered term is what keeps two occurrences of one place on one
    /// dom (term identity, not re-minting).
    pub(in crate::encoder::ir_encoder) fn ensure_projected_collection_meta(
        &mut self,
        term: Term,
        ty: &TrustVcType,
    ) {
        if self.collection_meta_by_term.contains_key(&term) {
            return;
        }

        // SAME PLACE => SAME TERM => SAME COMPANIONS. `collection_meta_by_term`
        // is rebuilt per `AstExpressionParser`, so a term minted while encoding
        // the assumptions would otherwise get a SECOND, unrelated dom while
        // encoding the goal. `projected_collection_meta` carries the first one
        // across every parser instance of the query.
        if let Some(meta) = self.projected_collection_meta.get(&term).cloned() {
            self.register_collection_meta(term, meta);
            return;
        }

        let kind = match ty {
            TrustVcType::Seq(_) | TrustVcType::Array(_, _) => Some(CollectionKind::Seq),
            TrustVcType::Set(_) => Some(CollectionKind::Set),
            TrustVcType::Multiset(_) => Some(CollectionKind::Multiset),
            TrustVcType::Map(_, _) => Some(CollectionKind::Map),
            _ => None,
        };
        let Some(kind) = kind else {
            return;
        };

        let len_term = if ty.has_collection_length() {
            Some(self.solver.fresh_var(
                "__trust_vc_place_len",
                Sort::bitvec(crate::ir::pointer_width()),
            ))
        } else {
            None
        };
        let key_ty = match ty {
            TrustVcType::Map(key_ty, _) => Some(key_ty.as_ref().clone()),
            _ => None,
        };
        let dom_term = match ty {
            TrustVcType::Map(key_ty, _) => Some(self.solver.fresh_var(
                "__trust_vc_place_dom",
                Sort::Array(Box::new(ArraySort {
                    index_sort: sort_for_type(key_ty),
                    element_sort: Sort::Bool,
                })),
            )),
            _ => None,
        };

        let meta = CollectionMeta {
            kind,
            len_term,
            len_guard: None,
            elem_ty: ty.collection_elem(),
            key_ty,
            dom_term,
        };
        self.projected_collection_meta.insert(term, meta.clone());
        self.register_collection_meta(term, meta);
    }

    fn encode_place_index_projection(
        &mut self,
        receiver_term: Term,
        index: &TrustVcExpr,
        _elem_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let index_term = self.encode_subexpr(index)?;
        let own = self.own_sign(index, None);
        let idx = self.coerce_seq_index(receiver_term, None, index_term, own)?;

        if !self.receiver_is_map(receiver_term, None) {
            self.add_seq_index_bounds_check(receiver_term, None, idx, "index")?;
        }

        let result = self
            .solver
            .try_select(receiver_term, idx)
            .map_err(|e| e.to_string())?;

        if let Some(info) = self.element_width_info(receiver_term, None) {
            self.term_widths.insert(result, info);
        }

        self.coerce_element_for_int_mode(result, receiver_term, None)
    }
}

/// Resolve the selector UF name for a field on a datatype.
fn resolve_selector_name(ty: &TrustVcType, field_name: &str) -> TrustVcResult<String> {
    match ty {
        TrustVcType::Datatype { name, variants } => {
            let variant = variants.first().ok_or_else(|| {
                format!(
                    "datatype '{}' has no variants for field '{}'",
                    name, field_name
                )
            })?;
            let (idx, _) = variant
                .fields
                .iter()
                .enumerate()
                .find(|(_, (n, _))| n == field_name)
                .ok_or_else(|| {
                    format!("field '{}' not found in datatype '{}'", field_name, name)
                })?;
            Ok(selector_symbol_name(name, &variant.name, field_name, idx))
        }
        _ => Err(format!(
            "field projection '{}' requires a datatype type, got '{}'",
            field_name,
            ty.to_type_string()
        )
        .into()),
    }
}
