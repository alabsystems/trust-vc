//! Extracted Set and Map collection dispatch helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;
#[cfg(feature = "native-strings")]
use ay_dpll::api::{FuncDecl, Sort};

use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
use crate::encoder::AstExpressionParser;
#[cfg(feature = "native-strings")]
use crate::error::TrustVcError;
use crate::error::TrustVcResult;
use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    #[cfg(feature = "native-strings")]
    fn build_native_string_view_valid_char_predicate(
        &mut self,
        term: Term,
        context: &'static str,
    ) -> TrustVcResult<Term> {
        let max_scalar =
            self.solver
                .try_bv_const(0x10FFFF_i64, 32)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to create char max bound: {e}"),
                })?;
        let surrogate_start =
            self.solver
                .try_bv_const(0xD800_i64, 32)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to create surrogate start bound: {e}"),
                })?;
        let surrogate_end =
            self.solver
                .try_bv_const(0xDFFF_i64, 32)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to create surrogate end bound: {e}"),
                })?;

        let in_scalar_range =
            self.solver
                .try_bvule(term, max_scalar)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to build scalar upper bound: {e}"),
                })?;
        let below_surrogates =
            self.solver
                .try_bvult(term, surrogate_start)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to build surrogate lower exclusion: {e}"),
                })?;
        let above_surrogates =
            self.solver
                .try_bvugt(term, surrogate_end)
                .map_err(|e| TrustVcError::Encoding {
                    context,
                    detail: format!("Failed to build surrogate upper exclusion: {e}"),
                })?;
        let not_surrogate = self
            .solver
            .try_or(below_surrogates, above_surrogates)
            .map_err(|e| TrustVcError::Encoding {
                context,
                detail: format!("Failed to combine surrogate exclusions: {e}"),
            })?;
        self.solver
            .try_and(in_scalar_range, not_surrogate)
            .map_err(|e| TrustVcError::Encoding {
                context,
                detail: format!("Failed to build Unicode scalar predicate: {e}"),
            })
    }

    #[cfg(all(feature = "native-strings", not(feature = "native-seq")))]
    fn assert_native_string_view_char_sequence(
        &mut self,
        seq_term: Term,
        len_term: Term,
    ) -> TrustVcResult<()> {
        let pw = crate::ir::pointer_width();
        let idx = self
            .solver
            .fresh_var("__trust_vc_char_idx", Sort::bitvec(pw));
        let idx_in_range =
            self.solver
                .try_bvult(idx, len_term)
                .map_err(|e| TrustVcError::Encoding {
                    context: "native string view bridge",
                    detail: format!("Failed to build char-sequence bound: {e}"),
                })?;
        let elem = self
            .solver
            .try_select(seq_term, idx)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to select char-sequence element: {e}"),
            })?;
        let elem_valid =
            self.build_native_string_view_valid_char_predicate(elem, "native string view bridge")?;
        let body = self
            .solver
            .try_implies(idx_in_range, elem_valid)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to build char-sequence implication: {e}"),
            })?;
        let quantified = self
            .solver
            .try_forall_with_triggers(&[idx], body, &[&[elem]])
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to quantify char-sequence invariant: {e}"),
            })?;
        self.solver
            .try_assert_term(quantified)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to assert char-sequence invariant: {e}"),
            })
    }

    #[cfg(all(feature = "native-strings", feature = "native-seq"))]
    fn assert_native_string_view_char_sequence_native_seq(
        &mut self,
        seq_term: Term,
        len_term: Term,
    ) -> TrustVcResult<()> {
        let idx = self.solver.fresh_var("__trust_vc_char_idx", Sort::Int);
        let zero = self.solver.int_const(0);
        let idx_ge_zero = self
            .solver
            .try_ge(idx, zero)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to build char-sequence lower bound: {e}"),
            })?;
        let idx_lt_len = self
            .solver
            .try_lt(idx, len_term)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to build char-sequence upper bound: {e}"),
            })?;
        let idx_in_range =
            self.solver
                .try_and(idx_ge_zero, idx_lt_len)
                .map_err(|e| TrustVcError::Encoding {
                    context: "native string view bridge",
                    detail: format!("Failed to build char-sequence range: {e}"),
                })?;
        let elem = self
            .solver
            .try_seq_nth(seq_term, idx)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to access seq.nth for char validation: {e}"),
            })?;
        let elem_valid =
            self.build_native_string_view_valid_char_predicate(elem, "native string view bridge")?;
        let body = self
            .solver
            .try_implies(idx_in_range, elem_valid)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to build char-sequence implication: {e}"),
            })?;
        let quantified = self
            .solver
            .try_forall_with_triggers(&[idx], body, &[&[elem]])
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to quantify char-sequence invariant: {e}"),
            })?;
        self.solver
            .try_assert_term(quantified)
            .map_err(|e| TrustVcError::Encoding {
                context: "native string view bridge",
                detail: format!("Failed to assert char-sequence invariant: {e}"),
            })
    }

    #[cfg(feature = "native-strings")]
    pub(in crate::encoder::ir_encoder) fn native_string_len_term(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        if let Some(len) = receiver_name.and_then(|name| self.collection_lengths.get(name).copied())
        {
            return Ok(len);
        }
        let raw_len = self
            .solver
            .try_str_len(receiver)
            .map_err(|e| format!("native string len: {e}"))?;
        let alias = self
            .solver
            .fresh_var("__native_string_len_derived", Sort::Int);
        let bridge = self
            .solver
            .try_eq(alias, raw_len)
            .map_err(|e| format!("native string len alias bridge: {e}"))?;
        self.solver
            .try_assert_term(bridge)
            .map_err(|e| format!("native string len alias assert: {e}"))?;
        Ok(alias)
    }

    #[cfg(feature = "native-strings")]
    fn native_string_to_code(&mut self, string_term: Term) -> TrustVcResult<Term> {
        let to_code = FuncDecl::new("str.to_code".into(), vec![Sort::String], Sort::Int);
        self.solver
            .try_apply(&to_code, &[string_term])
            .map_err(|e| format!("native string str.to_code: {e}").into())
    }

    #[cfg(feature = "native-strings")]
    fn build_native_string_view_shadow(
        &mut self,
        source_term: Term,
        source_name: Option<&str>,
    ) -> TrustVcResult<crate::encoder::parser_state::NativeStringViewShadow> {
        let view_sort =
            crate::encoder::types::sort_for_type(&TrustVcType::Seq(Box::new(TrustVcType::Char)));
        let view_term = self
            .solver
            .fresh_var("__native_string_view_shadow", view_sort);
        let source_len = self.native_string_len_term(source_term, source_name)?;

        #[cfg(feature = "native-seq")]
        {
            let raw_view_len = self
                .solver
                .try_seq_len(view_term)
                .map_err(|e| format!("native string view seq.len: {e}"))?;
            let len_eq = self
                .solver
                .try_eq(raw_view_len, source_len)
                .map_err(|e| format!("native string view len bridge: {e}"))?;
            self.solver
                .try_assert_term(len_eq)
                .map_err(|e| format!("native string view len assert: {e}"))?;

            let idx = self.solver.fresh_var("__native_string_view_idx", Sort::Int);
            let zero = self.solver.int_const(0);
            let idx_ge_zero = self
                .solver
                .try_ge(idx, zero)
                .map_err(|e| format!("native string view lower bound: {e}"))?;
            let idx_lt_len = self
                .solver
                .try_lt(idx, source_len)
                .map_err(|e| format!("native string view upper bound: {e}"))?;
            let in_bounds = self
                .solver
                .try_and(idx_ge_zero, idx_lt_len)
                .map_err(|e| format!("native string view in-bounds: {e}"))?;
            let char_string = self
                .solver
                .try_str_at(source_term, idx)
                .map_err(|e| format!("native string view str.at: {e}"))?;
            let char_code = self.native_string_to_code(char_string)?;
            let char_term = self
                .solver
                .try_int2bv(char_code, 32)
                .map_err(|e| format!("native string view codepoint conversion: {e}"))?;
            let view_elem = self
                .solver
                .try_seq_nth(view_term, idx)
                .map_err(|e| format!("native string view seq.nth: {e}"))?;
            let elem_eq = self
                .solver
                .try_eq(view_elem, char_term)
                .map_err(|e| format!("native string view element bridge: {e}"))?;
            let body = self
                .solver
                .try_implies(in_bounds, elem_eq)
                .map_err(|e| format!("native string view implication: {e}"))?;
            let axiom = self
                .solver
                .try_forall_with_triggers(&[idx], body, &[&[view_elem]])
                .map_err(|e| format!("native string view quantifier: {e}"))?;
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| format!("native string view quantifier assert: {e}"))?;
            self.assert_native_string_view_char_sequence_native_seq(view_term, source_len)?;

            return Ok(crate::encoder::parser_state::NativeStringViewShadow {
                view_term,
                len_term: source_len,
            });
        }

        #[cfg(not(feature = "native-seq"))]
        {
            let view_len = self.solver.fresh_var(
                "__native_string_view_len",
                Sort::bitvec(crate::ir::pointer_width()),
            );
            let view_len_int = self
                .solver
                .try_bv2int(view_len)
                .map_err(|e| format!("native string view bv2int: {e}"))?;
            let len_eq = self
                .solver
                .try_eq(view_len_int, source_len)
                .map_err(|e| format!("native string view len bridge: {e}"))?;
            self.solver
                .try_assert_term(len_eq)
                .map_err(|e| format!("native string view len assert: {e}"))?;

            let idx = self.solver.fresh_var(
                "__native_string_view_idx",
                Sort::bitvec(crate::ir::pointer_width()),
            );
            let in_bounds = self
                .solver
                .try_bvult(idx, view_len)
                .map_err(|e| format!("native string view in-bounds: {e}"))?;
            let idx_int = self
                .solver
                .try_bv2int(idx)
                .map_err(|e| format!("native string view index conversion: {e}"))?;
            let char_string = self
                .solver
                .try_str_at(source_term, idx_int)
                .map_err(|e| format!("native string view str.at: {e}"))?;
            let char_code = self.native_string_to_code(char_string)?;
            let char_term = self
                .solver
                .try_int2bv(char_code, 32)
                .map_err(|e| format!("native string view codepoint conversion: {e}"))?;
            let view_elem = self
                .solver
                .try_select(view_term, idx)
                .map_err(|e| format!("native string view select: {e}"))?;
            let elem_eq = self
                .solver
                .try_eq(view_elem, char_term)
                .map_err(|e| format!("native string view element bridge: {e}"))?;
            let body = self
                .solver
                .try_implies(in_bounds, elem_eq)
                .map_err(|e| format!("native string view implication: {e}"))?;
            let axiom = self
                .solver
                .try_forall_with_triggers(&[idx], body, &[&[view_elem]])
                .map_err(|e| format!("native string view quantifier: {e}"))?;
            self.solver
                .try_assert_term(axiom)
                .map_err(|e| format!("native string view quantifier assert: {e}"))?;
            self.assert_native_string_view_char_sequence(view_term, view_len)?;

            Ok(crate::encoder::parser_state::NativeStringViewShadow {
                view_term,
                len_term: view_len,
            })
        }
    }

    #[cfg(feature = "native-strings")]
    pub(in crate::encoder::ir_encoder) fn ensure_native_string_view_shadow(
        &mut self,
        source_term: Term,
        source_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        if let Some(shadow) = self.lookup_native_string_view_shadow(source_term) {
            return Ok(shadow.view_term);
        }

        let shadow = self.build_native_string_view_shadow(source_term, source_name)?;
        let view_term = shadow.view_term;
        let len_term = shadow.len_term;
        self.register_collection_meta(
            view_term,
            CollectionMeta {
                kind: CollectionKind::Seq,
                len_term: Some(len_term),
                len_guard: None,
                elem_ty: Some(TrustVcType::Char),
                key_ty: None,
                dom_term: None,
            },
        );
        self.register_native_string_view_shadow(source_term, shadow);
        Ok(view_term)
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(in crate::encoder::ir_encoder) fn encode_contains_key(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!("contains_key() expects 1 argument, got {}", args.len()).into());
        }
        let key = self.encode_subexpr(&args[0])?;
        let key = self.coerce_key_for_store_in_int_mode(key, receiver_term, Some(rname))?;
        // When a `map.subset` atom is in play this query, read membership through
        // the native `(map.dom m)` projection (bridged to the tracked domain
        // array) so ay's finite-map theory can discover the ground subset↔key
        // witnesses and decide `map.subset` without MBQI. The projection is the
        // same array as the tracked dom (verdict-neutral); the shape change is
        // what lets native subset propagation fire. Otherwise (the common case)
        // read the tracked array directly, keeping non-subset Map queries on the
        // array/BV path so BV-length overflow checks still decide.
        let dom_read_target = if self.map_subset_seen {
            match self.map_dom_projection(receiver_term, receiver_name)? {
                Some(proj) => Some(proj),
                None => self.lookup_collection_dom(receiver_term, receiver_name),
            }
        } else {
            self.lookup_collection_dom(receiver_term, receiver_name)
        };
        if let Some(dom_term) = dom_read_target {
            self.solver
                .try_select(dom_term, key)
                .map_err(|e| e.to_string().into())
        } else {
            Err(format!(
                "contains_key() not supported without dom tracking for '{}'",
                rname
            )
            .into())
        }
    }

    pub(in crate::encoder::ir_encoder) fn encode_view(
        &mut self,
        receiver_term: Term,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        _rname: &str,
    ) -> TrustVcResult<Term> {
        match crate::ir_lowering::infer_expr_type(receiver) {
            #[cfg(feature = "native-strings")]
            TrustVcType::String | TrustVcType::StrSlice => {
                return self.ensure_native_string_view_shadow(receiver_term, receiver_name);
            }
            _ => {
                if !self.collection_meta_by_term.contains_key(&receiver_term) {
                    if let Some(mut meta) = Self::typed_collection_meta(receiver) {
                        meta.len_term = self.lookup_collection_len(receiver_term, receiver_name);
                        meta.dom_term = self.lookup_collection_dom(receiver_term, receiver_name);
                        self.register_collection_meta(receiver_term, meta);
                    }
                }
            }
        }
        Ok(receiver_term)
    }

    pub(in crate::encoder::ir_encoder) fn encode_union(
        &mut self,
        receiver_term: Term,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
        match kind {
            Some(CollectionKind::Multiset) => {
                self.encode_multiset_union(receiver_term, receiver_name, args, Some(receiver))
            }
            _ => self.encode_trust_vc_set_binary_op(receiver_term, args, receiver_name, "union"),
        }
    }

    pub(in crate::encoder::ir_encoder) fn encode_intersect(
        &mut self,
        receiver_term: Term,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
        match kind {
            Some(CollectionKind::Multiset) => {
                self.encode_multiset_intersect(receiver_term, receiver_name, args)
            }
            _ => {
                self.encode_trust_vc_set_binary_op(receiver_term, args, receiver_name, "intersect")
            }
        }
    }

    pub(in crate::encoder::ir_encoder) fn encode_difference(
        &mut self,
        receiver_term: Term,
        receiver: &TrustVcExpr,
        receiver_name: Option<&str>,
        args: &[TrustVcExpr],
    ) -> TrustVcResult<Term> {
        let kind = self.resolve_receiver_kind(receiver_term, receiver_name, receiver);
        match kind {
            Some(CollectionKind::Multiset) => {
                self.encode_multiset_difference(receiver_term, receiver_name, args)
            }
            _ => {
                self.encode_trust_vc_set_binary_op(receiver_term, args, receiver_name, "difference")
            }
        }
    }

    #[allow(clippy::indexing_slicing)] // args[0] guarded by args.len() == 1 above
    pub(in crate::encoder::ir_encoder) fn encode_subset_or_superset(
        &mut self,
        receiver_term: Term,
        rname: &str,
        args: &[TrustVcExpr],
        op: CollectionOp,
    ) -> TrustVcResult<Term> {
        if args.len() != 1 {
            return Err(format!(
                "{}() expects 1 argument, got {}",
                if matches!(op, CollectionOp::Subset) {
                    "subset"
                } else {
                    "superset"
                },
                args.len()
            )
            .into());
        }
        if matches!(op, CollectionOp::Subset) {
            if let Some(meta) = self.collection_meta_by_term.get(&receiver_term) {
                if matches!(meta.kind, CollectionKind::Multiset) {
                    return self.encode_multiset_subset(receiver_term, Some(rname), args);
                }
            }
            if matches!(self.var_types.get(rname), Some(TrustVcType::Multiset(_))) {
                return self.encode_multiset_subset(receiver_term, Some(rname), args);
            }
            // Map::subset_of/submap_of: native (map.subset self other) atom,
            // decided without MBQI by ay's finite-map theory.
            let is_map = self
                .collection_meta_by_term
                .get(&receiver_term)
                .is_some_and(|meta| matches!(meta.kind, CollectionKind::Map))
                || matches!(self.var_types.get(rname), Some(TrustVcType::Map(_, _)));
            if is_map {
                let other_name = match &args[0] {
                    TrustVcExpr::Var { name, .. } => Some(name.as_str()),
                    _ => None,
                };
                let other = self.encode_subexpr(&args[0])?;
                return self.encode_map_subset(receiver_term, Some(rname), other, other_name);
            }
        }
        let other = self.encode_subexpr(&args[0])?;
        let method = if matches!(op, CollectionOp::Subset) {
            "subset"
        } else {
            "superset"
        };
        self.encode_set_subset_superset(receiver_term, other, Some(rname), method)
    }

    pub(in crate::encoder::ir_encoder) fn encode_dom(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        rname: &str,
    ) -> TrustVcResult<Term> {
        let dom = self.lookup_collection_dom(receiver_term, receiver_name);
        if let Some(dom_term) = dom {
            // Register as Set so chained ops (e.g. m.dom().contains(5))
            // dispatch correctly instead of resolving "m" as Map (#1966).
            let key_ty = self
                .collection_meta_by_term
                .get(&receiver_term)
                .and_then(|meta| meta.key_ty.clone())
                .or_else(|| {
                    receiver_name
                        .and_then(|name| self.var_types.get(name))
                        .and_then(|ty| match ty {
                            TrustVcType::Map(k, _) => Some(k.as_ref().clone()),
                            _ => None,
                        })
                });
            let len = self.lookup_collection_len(receiver_term, receiver_name);
            self.register_collection_meta(
                dom_term,
                CollectionMeta {
                    kind: CollectionKind::Set,
                    len_term: len,
                    len_guard: None,
                    elem_ty: key_ty,
                    key_ty: None,
                    dom_term: None,
                },
            );
            if len.is_none() {
                // `|m.dom()| == |m|` is true, but only when `m` HAS a tracked
                // cardinality. If it declined (e.g. `m.filter_keys(p)`), the
                // decline must propagate — otherwise the name fallback answers
                // `.len()` on the domain set with the ORIGINAL map's length.
                self.decline_collection_len(dom_term);
            }
            Ok(dom_term)
        } else {
            Err(format!(
                "Map::dom() not supported without domain tracking for '{}'",
                rname
            )
            .into())
        }
    }
}
