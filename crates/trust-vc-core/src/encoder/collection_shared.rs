//! Shared collection helper encoding for the IR encoder.
//!
//! Type/width introspection and int-mode coercion methods used across
//! Seq, Set, and Map encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::width_coercion::OwnSign;
use ay_dpll::api::{Sort, Term};
use num_bigint::BigInt;

use super::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

impl<'a> AstExpressionParser<'a> {
    /// True when any of `exprs` references a transient binding currently in
    /// scope (`local_vars` — quantifier/closure/let-in-spec variables).
    ///
    /// A pure spec-collection constructor may only be memoized
    /// (`memoized_pure_collection`) when it is closed with respect to such
    /// bindings: the same syntax evaluated under two different bindings of a
    /// transient variable denotes two different values, so sharing one backend
    /// term would be unsound. Free references to *stable* terms (function
    /// parameters / globals in `variables`) are fine — they resolve to the same
    /// term by name at every occurrence, so the structural key already captures
    /// their identity. `SpecClosure`/quantifier/let binders inside `exprs` are
    /// treated as bound (not free) by the scope-aware free-variable walk.
    pub(super) fn refs_transient_local_binding(&self, exprs: &[&TrustVcExpr]) -> bool {
        if self.local_vars.is_empty() {
            return false;
        }
        let empty = std::collections::HashSet::new();
        exprs.iter().any(|expr| {
            crate::ir_expr_traversal::free_root_names_with_initial_bound(expr, &empty)
                .iter()
                .any(|name| self.local_vars.contains_key(name))
        })
    }

    /// Memoize a pure, deterministic spec-collection constructor so that two
    /// syntactically-identical occurrences within one verification query share a
    /// single backend term + axiom set instead of minting a fresh, disconnected
    /// array each time.
    ///
    /// `skip_memo` (typically `refs_transient_local_binding(..)`) forces a fresh
    /// encoding for binding-dependent constructors. Otherwise the `key` (a
    /// canonical structural string) is looked up in `pure_collection_cache`;
    /// on a miss `build` runs and its result is cached.
    ///
    /// Soundness: a constructor that is closed w.r.t. transient bindings denotes
    /// the same value at every occurrence, so returning one shared term only adds
    /// the *true* syntactic identity that the membership-axiom-only encoding
    /// omitted. It can never make a false goal provable — it strictly strengthens
    /// E-matching connectivity (e.g. a mapped set's image axiom can now fire on a
    /// membership fact stated on another occurrence of the same source set).
    pub(super) fn memoized_pure_collection(
        &mut self,
        skip_memo: bool,
        key: String,
        build: impl FnOnce(&mut Self) -> TrustVcResult<Term>,
    ) -> TrustVcResult<Term> {
        if skip_memo {
            return build(self);
        }
        if let Some(&cached) = self.pure_collection_cache.get(&key) {
            return Ok(cached);
        }
        let term = build(self)?;
        self.pure_collection_cache.insert(key, term);
        Ok(term)
    }

    /// Create a correctly-sorted bound variable for quantifying over collection
    /// elements. Returns `(quant_var, elem_term)` where `quant_var` is the
    /// quantifier-bound variable (for `try_forall`) and `elem_term` is the term
    /// to use in axiom bodies (for `select`, `local_vars`).
    ///
    /// For all types, both are the same variable with the native sort:
    /// - Bool → Sort::Bool
    /// - MathInt → Sort::Int
    /// - BV types → Sort::bitvec(width)
    /// - TypeParam/Poly → Sort::Uninterpreted("Poly")
    ///
    /// BV-sorted quantifier variables allow ay-dpll E-matching to match
    /// trigger patterns like `select(array, x)` against ground terms like
    /// `select(array, bv_const(1))`. Current ay-dpll supports int2bv and
    /// multi-round E-matching, but this helper intentionally avoids the older
    /// Int-sorted + int2bv shape because TrustVc's ground terms are already
    /// BV-sorted and trigger matching stays syntactically direct (#2531).
    pub(super) fn safe_element_quantifier(
        &mut self,
        name: &str,
        elem_ty: &TrustVcType,
    ) -> TrustVcResult<(Term, Term)> {
        if matches!(elem_ty, TrustVcType::Bool) {
            let var = self.solver.fresh_var(name, Sort::Bool);
            return Ok((var, var));
        }
        if matches!(elem_ty, TrustVcType::MathInt) {
            let var = self.solver.fresh_var(name, Sort::Int);
            return Ok((var, var));
        }
        if matches!(elem_ty, TrustVcType::TypeParam(_) | TrustVcType::Poly) {
            let var = self
                .solver
                .fresh_var(name, Sort::Uninterpreted("Poly".to_string()));
            return Ok((var, var));
        }
        let width = elem_ty.bit_width().ok_or_else(|| {
            format!(
                "safe_element_quantifier requires integer element type, got {:?}",
                elem_ty
            )
        })?;
        let var = self.solver.fresh_var(name, Sort::bitvec(width));
        Ok((var, var))
    }

    /// Guard companion for `safe_element_quantifier`.
    ///
    /// Since `safe_element_quantifier` returns native-sorted variables
    /// for all types (Bool, Int, BV), no range guard is needed — the sort
    /// itself constrains the domain. Retained as a no-op for API consistency
    /// with callers that pair the two helpers.
    ///
    /// ```ignore
    /// let (qv, et) = self.safe_element_quantifier("x", &elem_ty)?;
    /// // ... build body using et for select/binding ...
    /// let guarded = self.guard_element_quantifier(&elem_ty, qv, body)?;
    /// self.solver.try_forall(&[qv], guarded)?;
    /// ```
    pub(super) fn guard_element_quantifier(
        &mut self,
        _elem_ty: &TrustVcType,
        _quant_var: Term,
        body: Term,
    ) -> TrustVcResult<Term> {
        Ok(body)
    }

    /// Create an Int-sorted bound variable for **assertion-side** quantifiers
    /// (subset, superset) that get negated during refutation.
    /// Returns `(quant_var, elem_term)` where `quant_var` is Int-sorted and
    /// `elem_term` is `int2bv(quant_var, width)` for BV elements.
    ///
    /// This avoids BV-sorted universal quantifiers whose negation (existential)
    /// is incomplete in ay-dpll E-matching (#1757). Only needed for quantifiers
    /// that the solver negates (subset/superset assertions).
    ///
    /// For axiom-side quantifiers (union, intersect, filter, map, etc.) that are
    /// asserted positively, use `safe_element_quantifier` which produces native
    /// BV-sorted vars with live E-matching triggers (#2536).
    pub(super) fn assertion_element_quantifier(
        &mut self,
        name: &str,
        elem_ty: &TrustVcType,
    ) -> TrustVcResult<(Term, Term)> {
        if matches!(elem_ty, TrustVcType::Bool) {
            let var = self.solver.fresh_var(name, Sort::Bool);
            return Ok((var, var));
        }
        if matches!(elem_ty, TrustVcType::MathInt) {
            let var = self.solver.fresh_var(name, Sort::Int);
            return Ok((var, var));
        }
        if matches!(elem_ty, TrustVcType::TypeParam(_) | TrustVcType::Poly) {
            let var = self
                .solver
                .fresh_var(name, Sort::Uninterpreted("Poly".to_string()));
            return Ok((var, var));
        }
        let width = elem_ty.bit_width().ok_or_else(|| {
            format!(
                "assertion_element_quantifier requires integer element type, got {:?}",
                elem_ty
            )
        })?;
        let var = self.solver.fresh_var(name, Sort::Int);
        let bv = self
            .solver
            .try_int2bv(var, width)
            .map_err(|e| e.to_string())?;
        Ok((var, bv))
    }

    /// Wrap an assertion-side quantified body with range guards for the
    /// Int-sorted bound variable from `assertion_element_quantifier`.
    ///
    /// For BV element types: wraps as `range_guard(quant_var, elem_ty) => body`.
    /// For Bool/MathInt/TypeParam/Poly: returns body unchanged.
    ///
    /// Retained as the documented companion of `assertion_element_quantifier`.
    /// Its sole former caller (Multiset::subset_of in the assertion context) now
    /// emits a native `multiset.subset` atom, so this guard is currently unused;
    /// kept available for the next assertion-side count quantifier.
    #[allow(dead_code)]
    pub(super) fn guard_assertion_quantifier(
        &mut self,
        elem_ty: &TrustVcType,
        quant_var: Term,
        body: Term,
    ) -> TrustVcResult<Term> {
        if matches!(
            elem_ty,
            TrustVcType::Bool
                | TrustVcType::MathInt
                | TrustVcType::TypeParam(_)
                | TrustVcType::Poly
        ) {
            return Ok(body);
        }
        self.add_integer_range_guards(
            &[(String::new(), elem_ty.clone(), quant_var)],
            body,
            true, // is_forall
        )
    }

    /// Extract the element type's bit width and signedness from a collection receiver.
    ///
    /// Resolves from term-keyed `CollectionMeta.elem_ty` first (#2067),
    /// falling back to name-keyed `var_types` for declared variables.
    ///
    /// For `Seq<T>` and `Map<K,V>`, returns the element type's `(width, is_signed)`.
    /// For `Set<T>`, the element sort is Bool (select returns membership), so no
    /// BV width tracking is needed — returns `None`.
    /// Returns `None` if the receiver has no known type or the element type is not
    /// a bitvector type (e.g., Bool, Int, Real, or nested collections).
    ///
    /// Used to register `try_select` results in `term_widths` so that downstream
    /// width coercion (e.g., comparing `s.index(0)` with a variable of different
    /// width) works correctly. Fixes #1752.
    pub(super) fn element_width_info(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> Option<(u32, bool)> {
        // Term-first: covers anonymous/chained results (#2067)
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let Some(ref elem) = meta.elem_ty {
                // Set<T> element is T but select returns Bool — no BV width
                if matches!(meta.kind, super::parser_state::CollectionKind::Set) {
                    return None;
                }
                let width = elem.bit_width()?;
                if width == 0 {
                    return None;
                }
                return Some((width, !elem.is_unsigned()));
            }
        }
        // Name fallback
        let ty = receiver_name.and_then(|name| self.var_types.get(name))?;
        let elem = match ty {
            crate::ir::TrustVcType::Seq(elem) | crate::ir::TrustVcType::Array(elem, _) => {
                elem.as_ref()
            }
            crate::ir::TrustVcType::Map(_, val) => val.as_ref(),
            // Set<T> select returns Bool — no BV width to track
            _ => return None,
        };
        let width = elem.bit_width()?;
        if width == 0 {
            return None;
        }
        let is_signed = !elem.is_unsigned();
        Some((width, is_signed))
    }

    /// Returns the bit width and signedness of the key/index sort for a
    /// Map, Set, or Multiset receiver.
    ///
    /// Resolves from term-keyed `CollectionMeta` first (#2067),
    /// falling back to name-keyed `var_types` for declared variables.
    ///
    /// For Map<K,V>, returns K's width. For Set<T> and Multiset<T>,
    /// returns T's width (the array index sort). Returns None for Seq
    /// (which uses BV64 indices handled by coerce_seq_index) and unknown types.
    fn key_width_info(&self, receiver: Term, receiver_name: Option<&str>) -> Option<(u32, bool)> {
        // Term-first: for Set/Multiset, elem_ty IS the key type (#2067)
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if matches!(
                meta.kind,
                super::parser_state::CollectionKind::Set
                    | super::parser_state::CollectionKind::Multiset
            ) {
                if let Some(ref elem) = meta.elem_ty {
                    let width = elem.bit_width()?;
                    if width == 0 {
                        return None;
                    }
                    return Some((width, !elem.is_unsigned()));
                }
            }
            if meta.kind == super::parser_state::CollectionKind::Map {
                if let Some(ref key) = meta.key_ty {
                    let width = key.bit_width()?;
                    if width == 0 {
                        return None;
                    }
                    return Some((width, !key.is_unsigned()));
                }
            }
        }
        // Name fallback
        let ty = receiver_name.and_then(|name| self.var_types.get(name))?;
        let key_ty = match ty {
            crate::ir::TrustVcType::Map(key, _) => key.as_ref(),
            crate::ir::TrustVcType::Set(elem) => elem.as_ref(),
            crate::ir::TrustVcType::Multiset(elem) => elem.as_ref(),
            _ => return None,
        };
        let width = key_ty.bit_width()?;
        if width == 0 {
            return None;
        }
        let is_signed = !key_ty.is_unsigned();
        Some((width, is_signed))
    }

    /// When inside a quantifier body (int_mode), Seq elements have BV sort but
    /// all arithmetic is done in Sort::Int. Convert the element via bv2int so
    /// downstream comparisons (e.g., `s.index(i) >= 0`) don't produce sort
    /// mismatches. Uses signed conversion for signed element types (i8..i128)
    /// and unsigned for u8..u128. Fixes #1932.
    pub(super) fn coerce_element_for_int_mode(
        &mut self,
        element: Term,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        if !self.int_mode() {
            return Ok(element);
        }
        // Only convert if we know the element is a BV type
        let Some((width, is_signed)) = self.element_width_info(receiver, receiver_name) else {
            return Ok(element);
        };
        if width == 0 {
            return Ok(element);
        }
        let converted = if is_signed {
            self.solver
                .try_bv2int_signed(element)
                .map_err(|e| e.to_string())?
        } else {
            self.solver.try_bv2int(element).map_err(|e| e.to_string())?
        };
        // Remove BV width tracking — the term is now Sort::Int
        self.term_widths.remove(&converted);
        Ok(converted)
    }

    /// Reverse of `coerce_element_for_int_mode`: converts a Sort::Int value
    /// back to the BV element sort expected by `try_store` for array writes.
    ///
    /// In int_mode (quantifier bodies), arithmetic produces Sort::Int values,
    /// but Seq/Map arrays have BV element sorts. Without this coercion,
    /// `try_store(array, idx, int_value)` would panic with a sort mismatch.
    /// Fixes #1936.
    pub(super) fn coerce_value_for_store_in_int_mode(
        &mut self,
        value: Term,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let Some((expected_width, expected_signed)) =
            self.element_width_info(receiver, receiver_name)
        else {
            return Ok(value);
        };
        if expected_width == 0 {
            return Ok(value);
        }

        // A bit-vector value must ARRIVE at the element's width: this is where
        // a value meets a collection it was bound to, and nothing here knows
        // the value's own type. It used to be widened by its `term_widths`
        // entry (which answers for whichever occurrence of a hash-consed
        // constant registered last, not for this value) or TRUNCATED to the
        // element width — a value re-read at a type that cannot hold it.
        // Both are refused; the element binding is the IR's (a `seq!`
        // literal, `push`, typed element coercions).
        if let Some(value_width) = self.bv_term_width(value) {
            if value_width == expected_width {
                return Ok(value);
            }
            return Err(format!(
                "a {value_width}-bit value cannot be stored as a {expected_width}-bit collection \
                 element: its own type is not known here, so it is neither widened nor narrowed"
            )
            .into());
        }

        // Sort::Int → BV conversion — only in int_mode (quantifier bodies
        // with Sort::Int bound vars). In BV mode, pass through unchanged.
        if self.int_mode() {
            self.diagnostics
                .record(super::diagnostics::EncodingApproximation::IntBvCoercion);
            let converted = self.solver.try_int2bv(value, expected_width).map_err(|e| {
                format!(
                    "Failed to coerce Int to BV{} for store: {}",
                    expected_width, e
                )
            })?;
            self.term_widths
                .insert(converted, (expected_width, expected_signed));
            return Ok(converted);
        }
        Ok(value)
    }

    /// Coerce a Map/Set key from Sort::Int to the BV key sort in int_mode.
    ///
    /// In int_mode (quantifier bodies), key expressions may be Sort::Int
    /// (from quantifier-bound variables or arithmetic), but Map/Set arrays
    /// have BV key sorts. Without this coercion, `try_store(array, int_key, value)`
    /// panics with a ay sort mismatch. Fixes #1953.
    pub(super) fn coerce_key_for_store_in_int_mode(
        &mut self,
        key: Term,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Term> {
        let Some((expected_width, expected_signed)) = self.key_width_info(receiver, receiver_name)
        else {
            return Ok(key);
        };

        // As for values: a bit-vector key must arrive at the key width (it
        // used to be widened by a `term_widths` sign or truncated).
        if let Some(key_width) = self.bv_term_width(key) {
            if key_width == expected_width {
                return Ok(key);
            }
            return Err(format!(
                "a {key_width}-bit key cannot be used as a {expected_width}-bit collection key: \
                 its own type is not known here, so it is neither widened nor narrowed"
            )
            .into());
        }

        // Sort::Int → BV conversion — only in int_mode.
        if self.int_mode() {
            self.diagnostics
                .record(super::diagnostics::EncodingApproximation::IntBvCoercion);
            let converted = self.solver.try_int2bv(key, expected_width).map_err(|e| {
                format!(
                    "Failed to coerce Int to BV{} for key: {}",
                    expected_width, e
                )
            })?;
            self.term_widths
                .insert(converted, (expected_width, expected_signed));
            return Ok(converted);
        }
        Ok(key)
    }

    /// Coerce a term to pointer-width for use as a length value.
    ///
    /// Handles all BV widths: narrows >target terms via extraction, widens
    /// <target terms via sign/zero extension. In int_mode (Sort::Int terms),
    /// passes through unchanged since Int is compatible with length comparisons.
    ///
    /// Target width is `pointer_width()` (matches collection length encoding).
    /// Fixes #1745: previously targeted 32-bit, causing sort mismatches with
    /// pointer-width collection lengths.
    ///
    /// `own` is the sign of the term's OWN IR type (a length, or an index the
    /// encoder already brought to pointer width, is unsigned by
    /// construction; a `subrange`/`take`/`skip` argument's comes from its
    /// expression). It used to be the term's `term_widths` entry, which for a
    /// hash-consed constant answers for whichever occurrence registered last.
    pub(super) fn coerce_to_len_width(&mut self, term: Term, own: OwnSign) -> TrustVcResult<Term> {
        let pw = crate::ir::pointer_width();
        if let Some(width) = self.bv_term_width(term) {
            if width == pw {
                return Ok(term);
            }
            if width > pw {
                // Narrow: extract lower pw bits
                let result = self
                    .solver
                    .try_bvextract(term, pw - 1, 0)
                    .map_err(|e| e.to_string())?;
                self.term_widths.insert(result, (pw, false));
                return Ok(result);
            }
            // width < pw: widen by the term's own sign
            let result = self.extend_term(term, pw - width, own)?;
            self.term_widths.insert(result, (pw, false));
            return Ok(result);
        }
        // No width info (Sort::Int from quantifier-bound vars).
        // In int_mode, convert Int → BitVec(pw) so bvule comparison
        // against BV-width collection lengths works. Mirrors coerce_seq_index.
        if self.int_mode() {
            if let Ok(converted) = self.solver.try_int2bv(term, pw) {
                // Wrapping Int -> BV(pw) crossing: exact only on
                // [0, 2^pw); guard the GROUND case with the carrier
                // representability obligation (no-op under a binder, where
                // the quantifier's own range guard scopes the bound var —
                // see push_index_representability_check / NC4).
                self.push_index_representability_check(term)?;
                self.diagnostics
                    .record(super::diagnostics::EncodingApproximation::IntBvCoercion);
                self.term_widths.insert(converted, (pw, false));
                return Ok(converted);
            }
        }
        Ok(term)
    }

    /// Returns true if the receiver is a Map type.
    ///
    /// Resolves from term-keyed `CollectionMeta.kind` first (#2067),
    /// falling back to name-keyed `var_types` for declared variables.
    ///
    /// Used to skip Seq-specific bounds checks on Map access (#1916).
    /// Map<K,V> is encoded as Array(K,V), a total function where every key
    /// maps to a value — there is no "out of bounds".
    pub(super) fn receiver_is_map(&self, receiver: Term, receiver_name: Option<&str>) -> bool {
        // Term-first: covers anonymous/chained results (#2067)
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            return meta.kind == super::parser_state::CollectionKind::Map;
        }
        // Name fallback
        receiver_name
            .and_then(|name| self.var_types.get(name))
            .map(|ty| matches!(ty, crate::ir::TrustVcType::Map(_, _)))
            .unwrap_or(false)
    }

    // ----------------------------------------------------------------------
    // Route A (#2779): sort-polymorphic LENGTH arithmetic.
    //
    // Spec-collection lengths are modelled as unbounded non-negative `Int`
    // (declared at `mod.rs` / `function_registration.rs`), so length
    // arithmetic (concat/push/drop/take/skip/subrange/insert/remove
    // cardinality) is monotone Int arithmetic with NO wraparound — the old
    // "... length no overflow" BV obligations are unsound to assume on a
    // bounded width and are simply absent over the integers (MAX+1 != 0).
    //
    // These helpers branch on the operand's solver sort so they stay correct
    // for any legacy/feature path that still produces a BitVec length
    // (the helpers degrade to the previous BV behaviour there). They are the
    // single audited surface for length math; array INDEX arithmetic is left
    // untouched (it stays BV — `select`/`store` are BV-indexed), and the
    // bridge between an Int length and a BV index goes through
    // `len_as_index_bv` / `bridge_len_to_index_width`.
    // ----------------------------------------------------------------------

    /// True when a length term is modelled as an unbounded `Int`.
    pub(super) fn len_is_int(&self, len: Term) -> bool {
        matches!(self.solver.term_sort(len), Sort::Int)
    }

    /// A length-sorted constant matching the sort of `model` (Int or the BV
    /// width of `model`). Used so comparisons/arithmetic against a constant
    /// never cross sorts.
    pub(super) fn len_const_like(&mut self, model: Term, value: i64) -> TrustVcResult<Term> {
        match self.solver.term_sort(model) {
            Sort::Int => Ok(self.solver.int_const(value)),
            Sort::BitVec(bv) => self
                .solver
                .try_bv_const(value, bv.width)
                .map_err(|e| e.to_string().into()),
            other => Err(format!("length constant requires numeric sort, got {other:?}").into()),
        }
    }

    /// Coerce a length operand to match the sort of `model` so they can be
    /// combined. If `model` is Int and `operand` is BV, lift via `bv2int`; if
    /// `model` is BV and `operand` is Int, lower via `int2bv` at `model`'s
    /// width. (In the all-Int default path this is a no-op.)
    pub(super) fn len_match_sort(&mut self, model: Term, operand: Term) -> TrustVcResult<Term> {
        let model_int = self.len_is_int(model);
        let operand_int = self.len_is_int(operand);
        if model_int == operand_int {
            return Ok(operand);
        }
        if model_int {
            // operand is BV -> Int
            self.solver
                .try_bv2int(operand)
                .map_err(|e| e.to_string().into())
        } else if let Sort::BitVec(bv) = self.solver.term_sort(model) {
            self.solver
                .try_int2bv(operand, bv.width)
                .map_err(|e| e.to_string().into())
        } else {
            Ok(operand)
        }
    }

    /// Length addition: `a + b`, monotone over Int (no overflow obligation).
    pub(super) fn len_add(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let b = self.len_match_sort(a, b)?;
        if self.len_is_int(a) {
            self.solver.try_add(a, b).map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bvadd(a, b)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Length subtraction: `a - b`. For Int lengths the caller guards
    /// non-negativity (e.g. nonempty / `n <= len`) just as before.
    pub(super) fn len_sub(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let b = self.len_match_sort(a, b)?;
        if self.len_is_int(a) {
            self.solver.try_sub(a, b).map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bvsub(a, b)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Length `a >= b` (unsigned for BV).
    pub(super) fn len_ge(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let b = self.len_match_sort(a, b)?;
        if self.len_is_int(a) {
            self.solver.try_ge(a, b).map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bvuge(a, b)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Length `a <= b` (unsigned for BV).
    pub(super) fn len_le(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let b = self.len_match_sort(a, b)?;
        if self.len_is_int(a) {
            self.solver.try_le(a, b).map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bvule(a, b)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Length `a > b` (unsigned for BV).
    pub(super) fn len_gt(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let b = self.len_match_sort(a, b)?;
        if self.len_is_int(a) {
            self.solver.try_gt(a, b).map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bvugt(a, b)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Length `a < b` (unsigned for BV).
    pub(super) fn len_lt(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let b = self.len_match_sort(a, b)?;
        if self.len_is_int(a) {
            self.solver.try_lt(a, b).map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bvult(a, b)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Index/length bound `a <= b` across possibly-MIXED BV/Int operands.
    ///
    /// Pure-BV operands keep the incumbent unsigned `bvule`. When EITHER
    /// operand is `Sort::Int` (Route A #2779: a length-derived bound such as
    /// `s.len()` / `s.len() - 1` stays Int even outside quantifier bodies —
    /// `coerce_to_len_width` passes it through), the comparison is taken in
    /// the Int domain with the BV side lifted via `bv2int` (unsigned view —
    /// EXACT and total; ay constant-folds it for BV literals, so concrete
    /// indices yield pure-Int obligations that discharge against the Int
    /// length facts).
    ///
    /// Deliberately NEVER lowers the Int side via `int2bv` here: these terms
    /// become proof OBLIGATIONS (`overflow_checks`), and a wraparound
    /// lowering of a negative or huge Int bound could discharge a
    /// genuinely-violated precondition (wrong-verify). The exact `bv2int`
    /// lift can at worst leave a true obligation `Unknown` (fail-closed).
    pub(super) fn index_bound_le(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let a_int = self.len_is_int(a);
        let b_int = self.len_is_int(b);
        if !a_int && !b_int {
            return self
                .solver
                .try_bvule(a, b)
                .map_err(|e| e.to_string().into());
        }
        let a_lifted = if a_int {
            a
        } else {
            self.solver.try_bv2int(a).map_err(|e| e.to_string())?
        };
        let b_lifted = if b_int {
            b
        } else {
            self.solver.try_bv2int(b).map_err(|e| e.to_string())?
        };
        self.solver
            .try_le(a_lifted, b_lifted)
            .map_err(|e| e.to_string().into())
    }

    /// Push an explicit `0 <= bound` obligation for an Int-sorted index
    /// bound. The unsigned-BV bound path enforces non-negativity BY SORT;
    /// an Int-sorted bound (Route A length expression like `s.len() - 1`)
    /// has no such guarantee, so the precondition must stay genuinely
    /// enforced with an explicit check. No-op for BV-sorted bounds.
    pub(super) fn push_int_bound_nonneg_check(
        &mut self,
        bound: Term,
        label: &str,
    ) -> TrustVcResult<()> {
        if !self.len_is_int(bound) {
            return Ok(());
        }
        let zero = self.solver.int_const(0);
        let nonneg = self.solver.try_le(zero, bound).map_err(|e| e.to_string())?;
        self.overflow_checks
            .push((label.to_string().into(), nonneg));
        Ok(())
    }

    /// The stable label carried by every carrier-index representability
    /// obligation pushed by [`Self::push_index_representability_check`].
    /// Surfaced verbatim in `possible {label} in '...'` counterexamples and
    /// Unknown reasons; tests key on the `"not representable in the BitVec"`
    /// substring.
    pub(super) fn index_representability_label() -> String {
        let pw = crate::ir::pointer_width();
        format!(
            "index/length not representable in the BitVec({pw}) carrier \
             (requires 0 <= value < 2^{pw})"
        )
    }

    /// Push an explicit carrier-REPRESENTABILITY obligation
    /// `0 <= value <= 2^pw - 1` for an Int-sorted length/index that is about
    /// to cross into the `BitVec(pw)` carrier index domain via a WRAPPING
    /// `int2bv` (`len_as_index_bv`, `coerce_seq_index`, the
    /// `coerce_to_len_width` int-mode fallback).
    ///
    /// SOUNDNESS (the NC4 class, aa97668 adversarial-review follow-up): spec
    /// collection lengths are unbounded non-negative `Int` (Route A #2779),
    /// but the carrier is `Array(BitVec(pw), T)` — a length-derived index
    /// `>= 2^pw` (assumable for a spec Seq: `len == 2^64 + 2`) or `< 0` WRAPS
    /// under `int2bv`, aliasing the unconstrained true-semantics cell
    /// `s[2^64]` onto the carrier cell of `s[0]`. Today ay does not
    /// constant-fold `int2bv` over bigints, so such queries fail closed by
    /// LUCK (Unknown); this obligation makes the huge-len regime fail
    /// HONESTLY (the labelled check is refuted) and stays sound if ay ever
    /// learns the fold. For ordinary programs the obligation discharges for
    /// free: exec-derived lengths are usize-bounded and test/spec lengths are
    /// pinned to concrete values; the check can only turn Verified into
    /// not-Verified for the unrepresentable regime, never invent a Verified.
    ///
    /// No-ops: non-Int values (a BV value is representable BY SORT) and
    /// `quantifier_depth > 0` (pushing to `overflow_checks` under a binder is
    /// broken — the bound variables become free at the outer assertion scope,
    /// #2557; quantified element axioms instead constrain lengths via the
    /// `len_index_companion` bridge). Values that are STATICALLY carrier-
    /// representable (see `int_value_statically_carrier_representable`) skip
    /// the obligation entirely — a free discharge for exec-derived / finite
    /// constructor-chain lengths, so ordinary Vec/Seq programs pay nothing
    /// (proven load-bearing: without it the vec_rs insert-view cases burn
    /// minutes of solver time re-deriving `0 <= k <= 2^64-1` for push-chain
    /// witnesses pinned to tiny constants). Identical (label, term) pushes
    /// are deduplicated.
    pub(super) fn push_index_representability_check(&mut self, value: Term) -> TrustVcResult<()> {
        if !self.len_is_int(value) {
            return Ok(());
        }
        if self.quantifier_depth > 0 {
            return Ok(());
        }
        if self.int_value_statically_carrier_representable(value) {
            return Ok(());
        }
        let pw = crate::ir::pointer_width();
        let max = (BigInt::from(1u8) << pw) - 1;
        let max_term = self.solver.int_const_bigint(&max);
        let le_max = self
            .solver
            .try_le(value, max_term)
            .map_err(|e| e.to_string())?;
        let zero = self.solver.int_const(0);
        let nonneg = self.solver.try_le(zero, value).map_err(|e| e.to_string())?;
        let in_range = self
            .solver
            .try_and(nonneg, le_max)
            .map_err(|e| e.to_string())?;
        // Ground values fold at term build (ay folds Int comparisons over
        // numerals): a folded-TRUE check carries no information — skip the
        // wasted solver scope. A folded-FALSE check is a definite violation
        // and is pushed (it refutes immediately).
        if in_range == self.solver.bool_const(true) {
            return Ok(());
        }
        tracing::debug!(
            value = %self.solver.format_term(value),
            "pushing carrier-index representability obligation"
        );
        let label = Self::index_representability_label();
        if self
            .overflow_checks
            .iter()
            .any(|(l, t)| *t == in_range && l.as_ref() == label)
        {
            return Ok(());
        }
        self.overflow_checks.push((label.into(), in_range));
        Ok(())
    }

    /// Same-index `Seq::push` READ-BACK recognizer (the highest-risk NC4
    /// down-payment). Returns `Some(select_result)` iff BOTH:
    ///
    ///   (i) `receiver_term` is a recorded push result — `store(base,
    ///       store_index, v)` with [`PushReadback`] provenance; AND
    ///   (ii) the select carrier index is PROVABLY the store index: the
    ///       int2bv view of `raw_index` (or `raw_index` itself when already
    ///       BV) is STRUCTURALLY IDENTICAL (hash-consed) to the recorded
    ///       `store_index`.
    ///
    /// Under (i)+(ii) the store cell and the read cell are the identical
    /// (possibly int2bv-wrapped) carrier cell, so ay's read-over-write axiom
    /// `select(store(a, i, v), i) = v` yields `v` EXACTLY, with NO dependence
    /// on `int2bv` carrier representability. We therefore reuse the store's own
    /// index term — minting no fresh int2bv and no select-side representability
    /// obligation — and retract the store-side obligation recorded at push time
    /// ([`Self::retract_index_representability_check`]).
    ///
    /// SOUNDNESS BOUNDARY — the gate is index IDENTITY, never a shape heuristic:
    /// * different-index select `j != i`  → `int2bv(j) != store_index` ⇒ no fire.
    /// * plain-Seq `s.index(s.len() - 2)`  → receiver not a push result ⇒ no fire
    ///   (representability obligation stays; NC4 fail-closed preserved).
    /// * push-then-`index(0)` at huge len  → `int2bv(0) != int2bv(old_len)` for a
    ///   symbolic/huge `old_len` ⇒ no fire (the store obligation stays; the read
    ///   of the possibly-clobbered low cell is NOT rescued).
    ///
    /// The genuine `0 <= idx < len` bounds precondition is KEPT (it discharges as
    /// `old_len < old_len + 1`); only the spurious carrier-representability
    /// obligation is suppressed.
    pub(super) fn try_encode_push_same_index_readback(
        &mut self,
        receiver_term: Term,
        raw_index: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Option<Term>> {
        // Gate (i): receiver is a recorded push/store result.
        let Some(readback) = self.push_readback_by_term.get(&receiver_term).copied() else {
            return Ok(None);
        };
        // Gate (ii): the select carrier index is structurally the store index.
        // Build the same int2bv view the ordinary coercion would (Int index) or
        // take the BV index directly — WITHOUT pushing any obligation — and
        // require hash-consed identity with the recorded store index. Anything
        // that is not the identical carrier cell fails closed to the normal path.
        let pw = crate::ir::pointer_width();
        let candidate = match self.solver.term_sort(raw_index) {
            Sort::Int => self.solver.try_int2bv(raw_index, pw).ok(),
            Sort::BitVec(_) => Some(raw_index),
            _ => None,
        };
        if candidate != Some(readback.store_index) {
            return Ok(None);
        }
        // SAME-INDEX READ-BACK. Keep the genuine `idx < len` precondition (it
        // discharges trivially), reuse the store index for the select, and drop
        // the spurious store-side representability obligation.
        self.add_seq_index_bounds_check(
            receiver_term,
            receiver_name,
            readback.store_index,
            "index",
        )?;
        if let Some(old_len_int) = readback.store_index_int {
            self.retract_index_representability_check(old_len_int)?;
        }
        let result = self
            .solver
            .try_select(receiver_term, readback.store_index)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver_term, receiver_name) {
            self.term_widths.insert(result, info);
        }
        let result = self.coerce_element_for_int_mode(result, receiver_term, receiver_name)?;
        Ok(Some(result))
    }

    /// Retract the carrier-representability obligation
    /// [`Self::push_index_representability_check`] queued for `value` — used by
    /// the same-index read-back recognizer to drop the store-side obligation
    /// once the store cell is proven to be read back at the identical carrier
    /// index. Rebuilds the exact `in_range` term (hash-consed identical) and
    /// removes any matching queued obligation. No-op for non-Int values or when
    /// no matching obligation is queued.
    fn retract_index_representability_check(&mut self, value: Term) -> TrustVcResult<()> {
        if !self.len_is_int(value) {
            return Ok(());
        }
        let pw = crate::ir::pointer_width();
        let max = (BigInt::from(1u8) << pw) - 1;
        let max_term = self.solver.int_const_bigint(&max);
        let le_max = self
            .solver
            .try_le(value, max_term)
            .map_err(|e| e.to_string())?;
        let zero = self.solver.int_const(0);
        let nonneg = self.solver.try_le(zero, value).map_err(|e| e.to_string())?;
        let in_range = self
            .solver
            .try_and(nonneg, le_max)
            .map_err(|e| e.to_string())?;
        let label = Self::index_representability_label();
        self.overflow_checks
            .retain(|(l, t)| !(*t == in_range && l.as_ref() == label));
        Ok(())
    }

    /// True when an Int-sorted length/index is representable in the
    /// `BitVec(pw)` carrier BY CONSTRUCTION, so the crossing obligation of
    /// [`Self::push_index_representability_check`] would be dead weight (a
    /// true-but-symbolic query re-solved against the full context — the exact
    /// shape ay's Int/BV bridge is slow/incomplete on).
    ///
    /// Accepted shapes (each argued sound, NOT a heuristic):
    ///
    /// 1. `bv2nat(x)` with `width(x) <= pw` — unsigned lift, range
    ///    `[0, 2^width) ⊆ [0, 2^pw)`. This is the `s.len() == k` assumption
    ///    bind (`assumption.rs`: the length is stored as `bv2nat(k)`).
    /// 2. A term whose LEAVES are all (a) numerals, (b) finite ctor-rooted
    ///    chain-length witnesses (`__seq_len_push*` fresh vars, or the length
    ///    companion of an empty collection constructor
    ///    `__trust_vc_len___trust_vc_collection_ctor_*_{empty,new}`), or
    ///    (c) `bv2nat` leaves per (1), combined ONLY through `+`/`-`/`*` and
    ///    `ite` VALUE branches. Chain witnesses are pinned by
    ///    `assert_push_length_axiom` chains rooted at an empty-ctor length
    ///    `== 0`, i.e. to the SYNTACTIC push depth of the program — the
    ///    `>= 2^64` regime is unreachable through them. Derived combinations
    ///    (e.g. `push_len - 1` as a subrange bound) are additionally gated by
    ///    the Int-EXACT `0 <= value <= len` obligations every crossing site
    ///    pushes alongside (subrange bounds, index bounds, take/skip
    ///    preconditions): a combination that escaped `[0, len]` fails those
    ///    obligations first, so the verdict is already not-Verified before
    ///    the wrapped carrier read could matter.
    ///
    /// Everything else — in particular any value whose support includes a
    /// DECLARED spec-collection length (`__trust_vc_len_{var}`, unbounded
    /// nonneg Int under Route A) — keeps the explicit obligation: that is
    /// exactly the NC4 huge-length regime.
    ///
    /// `use_declared_bounds` adds shape 3: a length term recorded in
    /// [`AstExpressionParser::usize_bounded_lens`] — an EXEC `Vec`/slice/array
    /// length that `assert_len_usize_bounded` already asserted
    /// `<= 2^pw - 1` — is treated as a `[0, 2^pw - 1]` leaf, so DERIVED views
    /// (`end - start`, `len - 1`) of an exec collection inherit boundedness
    /// through the arithmetic arms.
    ///
    /// That shape is DELIBERATELY opt-in rather than always-on, and every
    /// [`Self::push_index_representability_check`] caller passes `false`. Those
    /// callers use this predicate to SUPPRESS an obligation, and while the
    /// suppression would be semantically valid here (the bound really is on the
    /// assertion stack), dropping the obligation measurably changes what ay
    /// proves for `Vec == Vec` — the trivially-valid
    /// `requires(a == b) |- assert!(a == b)` regressed to a counterexample.
    /// This predicate's other use is a soundness GATE that must not be widened
    /// by an unrelated encoding decision, so the two uses are kept separate:
    /// `false` preserves the obligation set byte-for-byte.
    fn int_value_statically_carrier_representable(&mut self, value: Term) -> bool {
        self.int_value_carrier_representable_inner(value, false)
    }

    /// [`Self::int_value_statically_carrier_representable`] with the declared
    /// exec-collection length bounds (`usize_bounded_lens`) admitted as leaves.
    /// Used by soundness GATES that must decide "is this length representable in
    /// the carrier at all", never to suppress an obligation.
    pub(super) fn len_is_carrier_bounded(&mut self, value: Term) -> bool {
        self.int_value_carrier_representable_inner(value, true)
    }

    fn int_value_carrier_representable_inner(
        &mut self,
        value: Term,
        use_declared_bounds: bool,
    ) -> bool {
        // BigInt INTERVAL ARITHMETIC — deliberately not mere leaf
        // classification, which is unsound for this discharge: a `+`/`*` of
        // individually-bounded leaves can exceed the carrier (two
        // `bv2nat(BV64)` sum to up to 2^65 - 2 at an UN-gated crossing such
        // as a concat/prefix-sum length), and a bare `Const` numeral could in
        // principle be huge or negative. The discharge fires only when the
        // computed interval hull is provably within `[0, 2^pw - 1]` — with
        // ONE principled relaxation: a negative LOWER bound is forgiven when
        // a `0 <= value` obligation for this exact term is ALREADY queued in
        // `overflow_checks` (the aa97668 subrange `0 <= start` push), because
        // that Int-exact obligation refutes the negative regime before the
        // wrapped carrier read could matter. This formalizes the doc-comment
        // argument above instead of assuming it holds at every site.
        fn is_finite_chain_len_name(name: &str) -> bool {
            if name.starts_with("__seq_len_push") {
                return true;
            }
            name.strip_prefix("__trust_vc_len_")
                .is_some_and(AstExpressionParser::is_empty_collection_constructor_name)
        }
        /// Static interval for a finite constructor-chain length witness.
        /// A `__seq_len_push*` node is the length AFTER a push: its axiom
        /// pins it to `prev_len + 1` with `prev_len >= 0`, so it is >= 1 —
        /// which is what lets the ubiquitous `push_len - 1` subrange bound
        /// discharge with a nonnegative hull. An empty-ctor length is
        /// exactly 0 (so `empty_len - 1` keeps the obligation: that shape
        /// genuinely wraps). Upper bound: the syntactic push depth, bounded
        /// far below 2^20 in any real program.
        fn chain_interval(name: &str) -> (BigInt, BigInt) {
            if name.starts_with("__seq_len_push") {
                (BigInt::from(1u32), BigInt::from(1u64 << 20))
            } else {
                // Empty-collection constructor length: pinned to 0.
                (BigInt::from(0u32), BigInt::from(0u32))
            }
        }
        /// Parse an SMT-LIB Int numeral rendering, incl. the `(- N)` form.
        fn parse_numeral(text: &str) -> Option<BigInt> {
            let t = text.trim();
            if let Some(inner) = t.strip_prefix("(-").and_then(|s| s.strip_suffix(')')) {
                return inner.trim().parse::<BigInt>().ok().map(|n| -n);
            }
            t.parse::<BigInt>().ok()
        }
        fn interval(
            slf: &AstExpressionParser<'_>,
            t: Term,
            budget: &mut u32,
            use_declared_bounds: bool,
        ) -> Option<(BigInt, BigInt)> {
            if *budget == 0 {
                return None;
            }
            *budget -= 1;
            let pw = crate::ir::pointer_width();
            // Declared EXEC-collection length leaf: `Vec`/slice/array lengths
            // carry an ASSERTED `0 <= len <= 2^pw - 1` from `declare_variable`
            // (`assert_len_usize_bounded`, gated on `VariableDecl::bounded_len`),
            // which is the only emitter of that bound and never fires for a spec
            // `Seq<T>`. Taking the interval from a fact already on the assertion
            // stack — rather than from the term's shape — is what lets DERIVED
            // views inherit it: `end - start`, `len - 1`, `len - n` all reduce
            // through the `+`/`-`/`*` arm below to a hull inside the carrier.
            // Checked BEFORE the shape arms so a bare `__trust_vc_len_v` Var (no
            // recognizable shape) still resolves.
            if use_declared_bounds && slf.usize_bounded_lens.contains(&t) {
                return Some((BigInt::from(0u32), (BigInt::from(1u32) << pw) - 1));
            }
            // Safe bv2nat leaf: range [0, 2^w - 1] by construction.
            if let ay_dpll::api::TermKind::App {
                ref name,
                num_args: 1,
            } = slf.solver.term_kind(t)
            {
                if name == "bv2nat" {
                    return match slf
                        .solver
                        .term_children(t)
                        .first()
                        .map(|&c| slf.solver.term_sort(c))
                    {
                        Some(Sort::BitVec(bv)) if bv.width <= pw => {
                            Some((BigInt::from(0u32), (BigInt::from(1u32) << bv.width) - 1))
                        }
                        _ => None,
                    };
                }
            }
            match slf.solver.term_kind(t) {
                ay_dpll::api::TermKind::Const => {
                    let n = parse_numeral(&slf.solver.format_term(t))?;
                    Some((n.clone(), n))
                }
                ay_dpll::api::TermKind::Var { ref name } => {
                    is_finite_chain_len_name(name).then(|| chain_interval(name))
                }
                ay_dpll::api::TermKind::App { ref name, num_args } => {
                    // Zero-arity symbols are opaque constants: same name rule
                    // as Var. Compound apps: only linear/monomial length
                    // arithmetic; any other head (UF, div/mod, selects, ...)
                    // is opaque — keep the obligation.
                    if num_args == 0 {
                        return is_finite_chain_len_name(name).then(|| chain_interval(name));
                    }
                    if !matches!(name.as_str(), "+" | "-" | "*") {
                        return None;
                    }
                    let children = slf.solver.term_children(t);
                    let mut acc = interval(slf, *children.first()?, budget, use_declared_bounds)?;
                    for &c in &children[1..] {
                        let (clo, chi) = interval(slf, c, budget, use_declared_bounds)?;
                        acc = match name.as_str() {
                            "+" => (acc.0 + clo, acc.1 + chi),
                            "-" => (acc.0 - chi, acc.1 - clo),
                            "*" => {
                                let cands =
                                    [&acc.0 * &clo, &acc.0 * &chi, &acc.1 * &clo, &acc.1 * &chi];
                                let lo = cands.iter().min().cloned()?;
                                let hi = cands.iter().max().cloned()?;
                                (lo, hi)
                            }
                            _ => return None,
                        };
                    }
                    Some(acc)
                }
                ay_dpll::api::TermKind::Ite => {
                    // The ite VALUE is the hull of its branches; the
                    // condition does not contribute to the range.
                    let children = slf.solver.term_children(t);
                    let (a_lo, a_hi) =
                        interval(slf, *children.get(1)?, budget, use_declared_bounds)?;
                    let (b_lo, b_hi) =
                        interval(slf, *children.get(2)?, budget, use_declared_bounds)?;
                    Some((a_lo.min(b_lo), a_hi.max(b_hi)))
                }
                _ => None,
            }
        }
        let pw = crate::ir::pointer_width();
        let mut budget = 512u32;
        let Some((lo, hi)) = interval(self, value, &mut budget, use_declared_bounds) else {
            return false;
        };
        if hi >= (BigInt::from(1u32) << pw) {
            return false;
        }
        if lo >= BigInt::from(0u32) {
            return true;
        }
        // Negative lower bound: forgiven only when an Int-exact `0 <= value`
        // obligation for this exact term is already queued — it refutes the
        // negative regime before the wrapped carrier read can matter.
        let zero = self.solver.int_const(0);
        let Ok(nonneg) = self.solver.try_le(zero, value) else {
            return false;
        };
        self.overflow_checks.iter().any(|(_, t)| *t == nonneg)
    }

    /// Resolve an Int-sorted LENGTH term to its compile-time CONCRETE value —
    /// the POINT-INTERVAL case of the length model (F3, ay-lane 2026-07-18
    /// probe battery: `docs/probes/2026-07-18-ay-lane/dump-smt2/RESULTS.txt`).
    ///
    /// Deliberately DENOTATIONAL, not contextual: only shapes whose value is
    /// fixed in EVERY model resolve — numerals, and `+`/`-`/`*` spines over
    /// numerals (ay's term build already folds those to a single numeral;
    /// the walk covers any residual unfolded spine defensively). No map of
    /// context-derived pins is consulted, so a `Some(n)` answer is a
    /// TAUTOLOGY (`len` literally denotes `n` in every model), never an
    /// assumption — substituting `n` for `len` anywhere is unconditionally
    /// sound. Context-derived pins (a `requires s.len() == 2`, a
    /// `let s = Seq::empty().push(..)` binding) reach this resolver by the
    /// length TERM itself being registered as the Int literal where their
    /// entailment is established: at declaration for pins harvested from this
    /// query's own assumption set (`setup.rs::collect_finite_len_pins` →
    /// `declare_variable`), or at the assumption boundary
    /// (`record_concrete_collection_len_assumption`).
    fn concrete_len_value(&self, len: Term) -> Option<BigInt> {
        fn parse_numeral(text: &str) -> Option<BigInt> {
            let t = text.trim();
            if let Some(inner) = t.strip_prefix("(-").and_then(|s| s.strip_suffix(')')) {
                return inner.trim().parse::<BigInt>().ok().map(|n| -n);
            }
            t.parse::<BigInt>().ok()
        }
        fn value(slf: &AstExpressionParser<'_>, t: Term, budget: &mut u32) -> Option<BigInt> {
            if *budget == 0 {
                return None;
            }
            *budget -= 1;
            match slf.solver.term_kind(t) {
                ay_dpll::api::TermKind::Const => parse_numeral(&slf.solver.format_term(t)),
                ay_dpll::api::TermKind::App { ref name, num_args } if num_args >= 1 => {
                    // Unary "-" is negation; n-ary +/-/* fold left-to-right.
                    let children = slf.solver.term_children(t);
                    if name == "-" && num_args == 1 {
                        return Some(-value(slf, *children.first()?, budget)?);
                    }
                    if !matches!(name.as_str(), "+" | "-" | "*") {
                        return None;
                    }
                    let mut acc = value(slf, *children.first()?, budget)?;
                    for &c in children.get(1..)? {
                        let v = value(slf, c, budget)?;
                        acc = match name.as_str() {
                            "+" => acc + v,
                            "-" => acc - v,
                            "*" => acc * v,
                            _ => return None,
                        };
                    }
                    Some(acc)
                }
                _ => None,
            }
        }
        if !matches!(self.solver.term_sort(len), Sort::Int) {
            return None;
        }
        let mut budget = 64u32;
        value(self, len, &mut budget)
    }

    /// Point-interval fold (F3): the `BitVec(pw)` literal for an Int length
    /// that DENOTES a concrete, carrier-representable value; `None` otherwise
    /// (callers fail closed to the incumbent symbolic bridge).
    ///
    /// Range gate: `0 <= n < min(2^pw, 2^63)` — a negative length (violated
    /// view precondition) and a length at/above the carrier must keep the
    /// symbolic path (the guarded bridge stays inert / the NC4
    /// representability obligation stays pushed). The `i64` ceiling only
    /// exists because `try_bv_const` takes `i64`; concrete program lengths
    /// live far below it, and values beyond simply keep today's behaviour.
    ///
    /// WHY this fold matters (probe-backed): ay cannot decide the mixed
    /// `bv2nat`/`int2bv` length bridge even for PINNED values (probe_B1:
    /// `2 = bv2nat(k) ∧ k != #x02` is unknown-incomplete at every rev, and
    /// probe_M1d shows pinning the companion VALUE is still insufficient),
    /// but the identical query with the lengths as BV literals is UNSAT in
    /// ~20ms (probe_M2). For a point-interval length the bridge is
    /// unnecessary: emit the literal, and every downstream guard
    /// (`bvult i len_bv`, seeds, `bvadd` of companions) constant-folds at
    /// term build into the pure-BV shape ay decides.
    pub(super) fn concrete_len_index_literal(&mut self, len: Term) -> Option<(i64, Term)> {
        let n = self.concrete_len_value(len)?;
        let pw = crate::ir::pointer_width();
        if n < BigInt::from(0u32) || n >= (BigInt::from(1u8) << pw.min(63)) {
            return None;
        }
        let value = i64::try_from(n).ok()?;
        let bv = self.solver.try_bv_const(value, pw).ok()?;
        self.term_widths.insert(bv, (pw, false));
        Some((value, bv))
    }

    /// Companion-position fold for [`Self::len_index_companion`] /
    /// [`Self::len_index_companion_maybe_negative`]: the BV literal plus the
    /// bridge LINK collapsed to a ground Int fact.
    ///
    /// The incumbent companion contract asserts `bv2int(c) == len` for a
    /// fresh `c` (guarded by `len >= 0` in the maybe-negative variant). With
    /// `c := bv(n)` and `len` denoting `n`, that bridge IS the ground fact
    /// `n == len`; asserting it keeps any residual non-literal spelling of
    /// the same length (e.g. an unfolded `+` spine another site referenced)
    /// connected to the concrete value, and is skipped when `len` is already
    /// the interned numeral (the fact would be the tautology `n == n`).
    /// Sound both ways: the fact is denotationally true, so it can neither
    /// prune a real model nor discharge a false goal.
    fn concrete_len_companion_fold(&mut self, len: Term) -> TrustVcResult<Option<Term>> {
        let Some((value, bv)) = self.concrete_len_index_literal(len) else {
            return Ok(None);
        };
        if !matches!(self.solver.term_kind(len), ay_dpll::api::TermKind::Const) {
            let lit = self.solver.int_const(value);
            let link = self.solver.try_eq(lit, len).map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(link)
                .map_err(|e| e.to_string())?;
        }
        Ok(Some(bv))
    }

    /// Bridge a LENGTH term to a BitVec index of `pointer_width`, for use as a
    /// GROUND array `select`/`store` index or in ground BV index arithmetic. A
    /// BV length is width-normalised; an Int length is lowered via `int2bv`
    /// (total/sound) and a carrier-representability obligation
    /// `0 <= len <= 2^pw - 1` is pushed at the crossing
    /// ([`Self::push_index_representability_check`] — the wrapping `int2bv`
    /// is exact only on that range).
    ///
    /// Point-interval lengths (F3) skip the `int2bv` view entirely: a length
    /// denoting a concrete in-carrier value lowers to the BV literal itself
    /// (see [`Self::concrete_len_index_literal`]), for which the
    /// representability obligation is denotationally true and the literal is
    /// exactly `int2bv(len)` evaluated.
    ///
    /// Use this only where the `int2bv` subterm does not gate the query outcome
    /// (concrete ground instances at small indices, symbolic-tail seeds that
    /// merely add equalities). For QUANTIFIED element axioms use
    /// `len_index_companion`, which keeps the index in pure BV so ay-dpll's
    /// model validator can evaluate the quantifier (Route A #2779; see the ay
    /// attack-plan B2 Int-vs-BitVec model-validation asymmetry).
    pub(super) fn len_as_index_bv(&mut self, len: Term) -> TrustVcResult<Term> {
        let pw = crate::ir::pointer_width();
        match self.solver.term_sort(len) {
            Sort::Int => {
                // F3 point-interval fold: a concrete in-carrier length IS its
                // BV literal — no `int2bv` view to gate the query, and the
                // representability obligation is denotationally discharged.
                if let Some((_, bv)) = self.concrete_len_index_literal(len) {
                    return Ok(bv);
                }
                self.push_index_representability_check(len)?;
                let bv = self.solver.try_int2bv(len, pw).map_err(|e| e.to_string())?;
                self.term_widths.insert(bv, (pw, false));
                Ok(bv)
            }
            Sort::BitVec(_) => self.coerce_to_len_width(len, OwnSign::of_constructed(false)),
            other => {
                Err(format!("length->index bridge requires numeric sort, got {other:?}").into())
            }
        }
    }

    /// Bridge an Int length to a BitVec(pw) index *only* when the lowering
    /// constant-folds away the `int2bv` wrapper — i.e. when the length is an
    /// unsigned `bv2nat(k)` (with `k` already pw-wide), for which ay rewrites
    /// `int2bv(pw, bv2nat(k)) == k`. Returns `Some(k)` in that case and `None`
    /// for any opaque Int length whose `int2bv` view would survive (and gate
    /// the query Unknown — see `len_as_index_bv`). This lets ground BV index
    /// bounds (`idx <u len`) discharge in pure BV against a length pinned to a
    /// BV value, exactly as before Route A made lengths `Int` (#2779).
    ///
    /// NC4-class audit note: if ay ever learns to constant-fold `int2bv` over
    /// out-of-range bigints (`int2bv(2^64 + 2) -> 2`), the fold predicate here
    /// would accept the WRAPPED constant. This stays FAIL-CLOSED at the current
    /// (sole) call site, which uses the result only as the RHS of an
    /// `idx <u len_bv` BOUNDS obligation: a wrapped (smaller) length makes the
    /// bound strictly STRICTER, never weaker — it can refuse a true bound
    /// (Unknown/CE) but cannot discharge a false one. Any new call site that
    /// uses the folded value as a carrier SELECT/STORE index (not a bound)
    /// must add `push_index_representability_check` at the crossing.
    pub(super) fn try_folded_len_index_bv(&mut self, len: Term) -> TrustVcResult<Option<Term>> {
        let pw = crate::ir::pointer_width();
        if !matches!(self.solver.term_sort(len), Sort::Int) {
            return Ok(None);
        }
        // F3 point-interval fold: a concrete in-carrier length folds to its
        // BV literal — EXACT (not merely fail-closed-stricter), since the
        // literal is `int2bv(len)` evaluated on its in-range denotation.
        if let Some((_, bv)) = self.concrete_len_index_literal(len) {
            return Ok(Some(bv));
        }
        let bv = match self.solver.try_int2bv(len, pw) {
            Ok(bv) => bv,
            Err(_) => return Ok(None),
        };
        // Folded iff the result is no longer an `int2bv`/`to_bitvec` application.
        // A surviving conversion wrapper means the bound would carry an
        // Unknown-gating `int2bv` subterm; reject it.
        let folded = match self.solver.term_kind(bv) {
            ay_dpll::api::TermKind::App { ref name, .. } => {
                !name.contains("int2bv")
                    && !name.contains("to_bitvec")
                    && !name.contains("int_to_bv")
            }
            _ => true,
        };
        if !folded {
            return Ok(None);
        }
        self.term_widths.insert(bv, (pw, false));
        Ok(Some(bv))
    }

    /// True when a BitVec term is structurally an `int -> bitvec` conversion
    /// application (`int2bv` / `to_bitvec` / `int_to_bv`).
    ///
    /// Such an index arises when a spec `Int` index expression (e.g. `k - 1`
    /// with `k: u64` lowered as `bv2int(k) - 1`) is coerced to the Seq's
    /// `BitVec(pw)` index sort by `coerce_seq_index`. Comparing it against a
    /// BV-folded length in pure BV (`bvult(int2bv(bv2int(k) - 1), k)`) nests an
    /// `int2bv(bv2int(..))` round-trip that ay-dpll cannot bridge (it returns
    /// `Unknown (incomplete)` even though the bound is a trivial `k - 1 < k`).
    /// The equivalent Int-domain bound `bv2int(idx) < len` discharges directly
    /// (the round-trip collapses to the original Int subtraction), so the
    /// index-bounds check routes these indices through the Int path instead of
    /// the folded-BV path (#2680 / symbolic-tail subrange completeness).
    pub(super) fn bv_index_wraps_int2bv(&self, idx: Term) -> bool {
        matches!(
            self.solver.term_kind(idx),
            ay_dpll::api::TermKind::App { ref name, .. }
                if name.contains("int2bv")
                    || name.contains("to_bitvec")
                    || name.contains("int_to_bv")
        )
    }

    /// A fresh BitVec(pw) companion for an Int length, bridged by
    /// `bv2int(companion) == int_len`, for use inside QUANTIFIED element axioms
    /// where the index arithmetic must stay in pure BV so ay-dpll's model
    /// validator can evaluate it (an `int2bv(int_len)` subterm forces Unknown
    /// for the whole query — see `len_as_index_bv`).
    ///
    /// Soundness: `bv2int(companion) == int_len` asserts the length is in
    /// `[0, 2^pw)`. For a length the carrier can index that is no assumption at
    /// all. For an UNBOUNDED spec `Seq<T>` length it is a real one, and a
    /// FALSE-VERIFYING one: `bv2int(companion) <= 2^pw - 1` holds by SORT, so
    /// the bridge entails the standalone fact `len <= 2^pw - 1` in the enclosing
    /// context — exactly what
    /// [`AYEncoder::assert_len_usize_bounded`](crate::encoder) documents as
    /// SOUNDNESS-CRITICAL to emit ONLY for a `bounded_len` exec `Vec`/slice/
    /// array, because it "would make every huge-length guard's context UNSAT and
    /// vacuously verify". Measured through the production CLI: with the bridge
    /// unconditional, `requires(a.add(b).len() == a.len() + b.len())` (and the
    /// `filter`/`map_values`/`fold_left` analogues) made
    /// `assert!(a.len() <= u64::MAX)` VERIFY on `a: Seq<i32>`, while the same
    /// assertion without the operand op was correctly refuted.
    ///
    /// So the bridge is delivered UNCONDITIONALLY only for a length already
    /// established carrier-bounded ([`Self::len_is_carrier_bounded`] — an exec
    /// `Vec`/slice/array length, a concrete or pinned length, or a derived view
    /// of one), where it restates a fact already on the assertion stack. For any
    /// other length it is delivered under the representability ANTECEDENT
    /// `0 <= len <= 2^pw - 1`, which is satisfied — and so propagates the
    /// equality unchanged — in every model where the carrier could index the
    /// sequence at all, and is simply inert in the huge-length regime instead of
    /// ruling it out. The antecedent is not derivable from the consequent, so
    /// nothing bounds `len` any more.
    ///
    /// This is applied to OPERAND lengths only; the result length of a
    /// length-increasing op (concat/push) is kept as a pure Int (NOT bridged to
    /// BV), so e.g. `len(a)+len(b)` is never forced below `2^pw` — that would
    /// reintroduce the unsound route-B no-wrap assumption.
    pub(super) fn len_index_companion(&mut self, len: Term) -> TrustVcResult<Term> {
        self.len_index_companion_inner(len, false)
    }

    /// Like [`len_index_companion`], but for a length that may be NEGATIVE —
    /// i.e. the result LENGTH of a length-DECREASING op (`skip(n)` -> `len - n`,
    /// `subrange(start, end)` -> `end - start`, `drop_first`/`drop_last` ->
    /// `len - 1`). The plain `len_index_companion` asserts the carrier-range
    /// bridge `bv2int(companion) == len` UNCONDITIONALLY; because `bv2int` is
    /// always `>= 0`, that bridge is UNSAT whenever `len` is negative. A
    /// negative `len` arises EXACTLY when the op's Verus precondition is
    /// violated (`n > len`, `start > end`, empty Seq), so the unconditional
    /// bridge silently POISONED the whole solver context into UNSAT, vacuously
    /// discharging BOTH the surrounding assertion AND the pushed precondition
    /// guard (`n <= len` / `start <= end` / `len >= 1`) that should have refuted
    /// — a catastrophic FALSE-VERIFIED soundness hole (#soundness skip/subrange/
    /// drop).
    ///
    /// Guarding the bridge by `len >= 0` fixes it WITHOUT weakening any valid
    /// case: for a satisfied precondition `len >= 0` holds (the source length is
    /// asserted `>= 0` at declaration and the precondition gives `result >= 0`),
    /// so the antecedent is true and the carrier-range equality is delivered
    /// byte-for-byte as before; for a VIOLATED precondition the negative `len`
    /// makes the antecedent false, so the bridge adds NO constraint, the context
    /// is no longer poisoned, and the precondition guard discharges
    /// (SAT/Unknown -> not Verified) against the asserted SOURCE length.
    ///
    /// This is deliberately a SEPARATE method (not a flag on
    /// `len_index_companion`) so the unconditional bridge — load-bearing for
    /// OPERAND lengths where `len >= 0` is not always syntactically derivable
    /// (filter/ext_eq/quantifier-body index carriers) — is left untouched.
    ///
    /// The `len >= 0` antecedent is WIDENED to the full representability range
    /// `0 <= len <= 2^pw - 1` for a length not established carrier-bounded; see
    /// [`Self::len_index_companion`] for why the bare `len >= 0` form leaked
    /// `len <= 2^pw - 1` into the enclosing context and false-verified. The
    /// negative-length behaviour this method exists for is unchanged: `len < 0`
    /// still falsifies the antecedent, leaving the bridge inert.
    pub(super) fn len_index_companion_maybe_negative(&mut self, len: Term) -> TrustVcResult<Term> {
        self.len_index_companion_inner(len, true)
    }

    /// Shared body of the two companion constructors.
    ///
    /// `guard_nonneg` selects the `maybe_negative` variant's `len >= 0`
    /// antecedent. Independently of it, a length that is NOT
    /// [`Self::len_is_carrier_bounded`] gets the representability antecedent
    /// `0 <= len <= 2^pw - 1` — which subsumes `len >= 0`, so the two combine to
    /// a single conjunction rather than nesting.
    fn len_index_companion_inner(&mut self, len: Term, guard_nonneg: bool) -> TrustVcResult<Term> {
        let pw = crate::ir::pointer_width();
        match self.solver.term_sort(len) {
            Sort::BitVec(_) => self.coerce_to_len_width(len, OwnSign::of_constructed(false)),
            Sort::Int => {
                // F3 point-interval fold: a concrete in-carrier length gets the
                // BV LITERAL as its companion (with the bridge collapsed to a
                // ground Int fact) instead of a fresh var bridged via `bv2int` —
                // the mixed bridge is undecidable for ay even at pinned values
                // (probe_B1/M1d), while literal companions make quantifier
                // guards ground BV (probe_M2, ~20ms UNSAT). The fold's range
                // gate only accepts `n >= 0`, so a concrete NEGATIVE length (a
                // violated view precondition) falls through to the guarded
                // bridge below and the inert-bridge refutation path is
                // byte-identical to before.
                if let Some(bv) = self.concrete_len_companion_fold(len)? {
                    return Ok(bv);
                }
                let carrier_bounded = self.len_is_carrier_bounded(len);
                let bv = self
                    .solver
                    .fresh_var("__trust_vc_len_idx", Sort::bitvec(pw));
                self.term_widths.insert(bv, (pw, false));
                let bv_as_int = self.solver.try_bv2int(bv).map_err(|e| e.to_string())?;
                let eq = self
                    .solver
                    .try_eq(bv_as_int, len)
                    .map_err(|e| e.to_string())?;
                let mut antecedent: Option<Term> = None;
                if guard_nonneg || !carrier_bounded {
                    let zero = self.solver.int_const(0);
                    antecedent = Some(self.solver.try_ge(len, zero).map_err(|e| e.to_string())?);
                }
                if !carrier_bounded {
                    let max = (BigInt::from(1u8) << pw) - 1;
                    let max_term = self.solver.int_const_bigint(&max);
                    let le_max = self
                        .solver
                        .try_le(len, max_term)
                        .map_err(|e| e.to_string())?;
                    antecedent = Some(match antecedent {
                        Some(nonneg) => self
                            .solver
                            .try_and(nonneg, le_max)
                            .map_err(|e| e.to_string())?,
                        None => le_max,
                    });
                }
                let bridge = match antecedent {
                    Some(guard) => self
                        .solver
                        .try_implies(guard, eq)
                        .map_err(|e| e.to_string())?,
                    None => eq,
                };
                self.solver
                    .try_assert_term(bridge)
                    .map_err(|e| e.to_string())?;
                Ok(bv)
            }
            other => {
                Err(format!("length index companion requires numeric sort, got {other:?}").into())
            }
        }
    }

    /// Guard a length FACT by `len >= 0` when `len` is an Int that may be
    /// NEGATIVE (a length-DECREASING view result — `skip`/`subrange`/`drop`).
    ///
    /// Several consumer encodings assert a fact `P(len)` that is itself UNSAT
    /// when `len < 0` — e.g. `filter` asserts `result_len <= source_len` while
    /// `result_len >= 0`, which is UNSAT for `source_len == -2` and POISONS the
    /// whole solver context into a vacuous proof (masking the source op's
    /// violated precondition). Returns `len >= 0 ==> fact` for an Int `len` so a
    /// violated precondition (negative `len`) leaves the fact inert, and returns
    /// `fact` unchanged for a BV `len` (unsigned — no negative case). For a valid
    /// non-negative `len` the antecedent holds and the fact is delivered exactly
    /// as before (#soundness skip/subrange/drop — consumer length-fact site).
    pub(super) fn guard_len_fact_nonneg(&mut self, len: Term, fact: Term) -> TrustVcResult<Term> {
        match self.solver.term_sort(len) {
            Sort::Int => {
                let zero = self.solver.int_const(0);
                let nonneg = self.solver.try_ge(len, zero).map_err(|e| e.to_string())?;
                self.solver
                    .try_implies(nonneg, fact)
                    .map_err(|e| e.to_string().into())
            }
            _ => Ok(fact),
        }
    }
}
