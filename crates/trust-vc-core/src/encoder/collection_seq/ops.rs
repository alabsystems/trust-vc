//! Seq element-level operations: contains, occurrence_count, element_sort, bounds, nonempty.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Sequence-level transforms (shift, reverse, no_duplicates, concat) are in
//! `seq_transforms.rs` (#2621).

use crate::encoder::width_coercion::OwnSign;
use ay_dpll::api::{Sort, Term};

use super::super::AstExpressionParser;
use crate::encoder::types::sort_for_type;
use crate::error::TrustVcResult;

const FIXED_ARRAY_CONTAINS_UNROLL_LIMIT: usize = 64;
const FILTER_CONTAINS_UNROLL_LIMIT: usize = 2;

impl<'a> AstExpressionParser<'a> {
    /// Encode Seq::contains(value) with an Int-sorted witness.
    ///
    /// Meaning (for a symbolic length; see `encode_seq_contains_quantified`
    /// for the exact term spelling, which is the negated guarded universal):
    ///   exists i: Int.
    ///     0 <= i < bv2int(len) && select(seq, int2bv(i, pw)) == value
    ///
    /// This avoids BV-sorted quantifiers, which are unsound in ay-dpll E-matching (#1757).
    pub(in crate::encoder) fn encode_seq_contains(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        value: Term,
        finite_len_hint: Option<usize>,
    ) -> TrustVcResult<Term> {
        let fixed_len = finite_len_hint
            .or_else(|| {
                receiver_name.and_then(|name| {
                    self.local_var_types
                        .get(name)
                        .or_else(|| self.var_types.get(name))
                        .and_then(|ty| match ty {
                            crate::ir::TrustVcType::Array(_, len) => Some(*len),
                            _ => None,
                        })
                })
            })
            .or_else(|| self.static_collection_len_hint(receiver, receiver_name));
        if let Some(len) = fixed_len.filter(|len| *len <= FIXED_ARRAY_CONTAINS_UNROLL_LIMIT) {
            return self.encode_fixed_array_contains(receiver, receiver_name, value, len);
        }
        if self.should_bounded_unroll_filter_contains(receiver, receiver_name) {
            return self.encode_bounded_seq_contains_with_limit(
                receiver,
                receiver_name,
                value,
                FILTER_CONTAINS_UNROLL_LIMIT,
                "Seq::filter().contains() currently requires len <= 2",
            );
        }
        if self.should_bounded_unroll_seq_contains(receiver, receiver_name) {
            return self.encode_bounded_seq_contains(receiver, receiver_name, value);
        }
        self.encode_seq_contains_quantified(receiver, receiver_name, value)
    }

    fn static_collection_len_hint(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> Option<usize> {
        let len = self.lookup_collection_len(receiver, receiver_name)?;
        parse_bv_len_literal(&self.solver.format_term(len))
    }

    fn encode_fixed_array_contains(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        value: Term,
        array_len: usize,
    ) -> TrustVcResult<Term> {
        let pw = crate::ir::pointer_width();
        let mut value = self.coerce_value_for_store_in_int_mode(value, receiver, receiver_name)?;
        let mut result = self.solver.bool_const(false);

        for idx_value in 0..array_len {
            let idx = self
                .solver
                .try_bv_const(idx_value as i64, pw)
                .map_err(|e| e.to_string())?;
            self.term_widths.insert(idx, (pw, false));
            let candidate = self
                .solver
                .try_select(receiver, idx)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(candidate, info);
            }
            let (candidate, coerced_value) = self.coerce_bv_widths(candidate, value)?;
            value = coerced_value;
            let matches = self
                .solver
                .try_eq(candidate, value)
                .map_err(|e| e.to_string())?;
            result = self
                .solver
                .try_or(result, matches)
                .map_err(|e| e.to_string())?;
        }

        Ok(result)
    }

    fn should_bounded_unroll_seq_contains(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> bool {
        let Some(name) = receiver_name else {
            return false;
        };
        if self.collection_lengths.contains_key(name) {
            return false;
        }
        let Some(len) = self.lookup_collection_len(receiver, receiver_name) else {
            return false;
        };
        // Array literals lowered through empty-Seq push chains use fresh
        // `__seq_len_push` length witnesses; unroll these bounded finite views
        // to avoid quantified contains returning unknown.
        self.solver.format_term(len).contains("__seq_len_push")
    }

    fn should_bounded_unroll_filter_contains(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> bool {
        let Some(len) = self.lookup_collection_len(receiver, receiver_name) else {
            return false;
        };
        self.solver.format_term(len).contains("__seq_filter_len")
    }

    fn encode_bounded_seq_contains(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        value: Term,
    ) -> TrustVcResult<Term> {
        self.encode_bounded_seq_contains_with_limit(
            receiver,
            receiver_name,
            value,
            FIXED_ARRAY_CONTAINS_UNROLL_LIMIT,
            "Seq::contains() bounded literal view requires len <= 64",
        )
    }

    fn encode_bounded_seq_contains_with_limit(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        value: Term,
        limit_value: usize,
        guard_label: &'static str,
    ) -> TrustVcResult<Term> {
        let len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in contains()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let pw = crate::ir::pointer_width();
        // `len <= limit` is a length comparison (Int under Route A #2779).
        let limit = self.len_const_like(len, limit_value as i64)?;
        let within_limit = self.len_le(len, limit)?;
        self.overflow_checks
            .push((guard_label.into(), within_limit));
        // BV view of the length for the per-index `idx < len` range guards
        // against the BV-indexed carrier.
        let len_bv = self.len_as_index_bv(len)?;

        let mut value = self.coerce_value_for_store_in_int_mode(value, receiver, receiver_name)?;
        let mut result = self.solver.bool_const(false);

        for idx_value in 0..limit_value {
            let idx = self
                .solver
                .try_bv_const(idx_value as i64, pw)
                .map_err(|e| e.to_string())?;
            self.term_widths.insert(idx, (pw, false));
            let in_range = self
                .solver
                .try_bvult(idx, len_bv)
                .map_err(|e| e.to_string())?;
            let candidate = self
                .solver
                .try_select(receiver, idx)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(candidate, info);
            }
            let (candidate, coerced_value) = self.coerce_bv_widths(candidate, value)?;
            value = coerced_value;
            let matches = self
                .solver
                .try_eq(candidate, value)
                .map_err(|e| e.to_string())?;
            let witness = self
                .solver
                .try_and(in_range, matches)
                .map_err(|e| e.to_string())?;
            result = self
                .solver
                .try_or(result, witness)
                .map_err(|e| e.to_string())?;
        }

        Ok(result)
    }

    fn encode_seq_contains_quantified(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        value: Term,
    ) -> TrustVcResult<Term> {
        let len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in contains()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;

        let bound_idx = self.solver.fresh_var("__seq_contains_idx", Sort::Int);
        let zero = self.solver.int_const(0);
        // Route A (#2779): length is already Int; lift only if a legacy BV
        // length is encountered.
        let len_int = if self.len_is_int(len) {
            len
        } else {
            self.solver.try_bv2int(len).map_err(|e| e.to_string())?
        };
        let lower = self
            .solver
            .try_ge(bound_idx, zero)
            .map_err(|e| e.to_string())?;
        let upper = self
            .solver
            .try_lt(bound_idx, len_int)
            .map_err(|e| e.to_string())?;
        let range = self
            .solver
            .try_and(lower, upper)
            .map_err(|e| e.to_string())?;

        let pw = crate::ir::pointer_width();
        let idx_bv64 = self
            .solver
            .try_int2bv(bound_idx, pw)
            .map_err(|e| e.to_string())?;
        self.term_widths.insert(idx_bv64, (pw, false));
        let element = self
            .solver
            .try_select(receiver, idx_bv64)
            .map_err(|e| e.to_string())?;
        if let Some(info) = self.element_width_info(receiver, receiver_name) {
            self.term_widths.insert(element, info);
        }

        let value = self.coerce_value_for_store_in_int_mode(value, receiver, receiver_name)?;
        let (element, value) = self.coerce_bv_widths(element, value)?;
        let eq = self
            .solver
            .try_eq(element, value)
            .map_err(|e| e.to_string())?;
        // SPELLING: `contains` is built as `not (forall i. range => element != value)`,
        // the exact negation-normal dual of `exists i. range && element == value`
        // (the two are logically equivalent: `not forall i. not P  <=>  exists i. P`,
        // and `range => not eq` is `not (range && eq)`). The spelling matters
        // because ay's term constructor eliminates double negation, so EVERY
        // negation site — a `!s.contains(v)` hypothesis, the verifier's negated
        // goal, De Morgan through `&&`/`||` — gets the guarded universal itself,
        // never `(not (exists ..))`. Measured 2026-09-14 against the ay 0.26.0
        // sibling API (64- and 32-bit carriers): `(not (exists i. range && s[i] == 9))`
        // is `unknown (incomplete)` with or without the ground seed and even with
        // `len == 0` asserted, while `(forall i. range => s[i] != 9)` is `sat`
        // (model validated) in both cases; the hypothesis/goal pair
        // `exists` + `not exists` is `unknown (incomplete)` where `not forall` +
        // `forall` is `unsat`. The positive occurrence `not (forall ..)` behaves
        // as the existential did (skolemized: `sat` without the seed,
        // `unknown (incomplete)` next to it, `unsat` against its dual).
        //
        // SCOPE of that "EVERY": it is a claim about the TERM ay receives, not
        // about what ay can decide. Reaching the solver as the guarded universal
        // is necessary but NOT sufficient — measured 2026-09-16, De Morgan
        // through `&&`, a negated occurrence under a branch, and a `u32`
        // boundary element still come back
        // `unknown ((incomplete quantifier-unhandled))`, and
        // `seq_contains_hypothesis_goal_identity_capability` pins two of that
        // class fail-closed. This spelling removed a class of `(not (exists ..))`
        // blindness; it did not make quantified `contains` decidable.
        let not_eq = self.solver.try_not(eq).map_err(|e| e.to_string())?;
        let body = self
            .solver
            .try_implies(range, not_eq)
            .map_err(|e| e.to_string())?;

        // One term per alpha-equivalence class of the COERCED body (see
        // `SeqContainsQuantifiedMemo`): the key is built only now, after every
        // width coercion, so a value whose extension differs (`sext` vs `zext`
        // of the same interned BV constant) gets a different key.
        let placeholder = match self.seq_contains_memo_mut().placeholder {
            Some(placeholder) => placeholder,
            None => {
                let placeholder = self
                    .solver
                    .fresh_var("__seq_contains_memo_key_idx", Sort::Int);
                self.seq_contains_memo_mut().placeholder = Some(placeholder);
                placeholder
            }
        };
        let renamed_body = self.solver.substitute(body, &[bound_idx], &[placeholder]);
        if let Some(&memo) = self
            .seq_contains_memo_mut()
            .by_renamed_body
            .get(&renamed_body)
        {
            return Ok(memo);
        }
        let absent = self
            .solver
            .try_forall(&[bound_idx], body)
            .map_err(|e| e.to_string())?;
        let contains = self.solver.try_not(absent).map_err(|e| e.to_string())?;
        self.seq_contains_memo_mut()
            .by_renamed_body
            .insert(renamed_body, contains);
        Ok(contains)
    }

    /// The encoder-owned `Seq::contains` memo when one is threaded in, else
    /// this parser's local one.
    fn seq_contains_memo_mut(
        &mut self,
    ) -> &mut super::super::parser_state::SeqContainsQuantifiedMemo {
        match self.seq_contains_quantified_memo.as_deref_mut() {
            Some(memo) => memo,
            None => &mut self.seq_contains_quantified_memo_local,
        }
    }

    /// Encode the exact occurrence count of `needle` for bounded Seq lengths.
    ///
    /// The result is constrained only for `len < 5`; callers must discharge
    /// the emitted guard before relying on the returned count.
    pub(in crate::encoder) fn encode_seq_occurrence_count(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        needle: Term,
    ) -> TrustVcResult<Term> {
        let len = self
            .lookup_collection_len(receiver, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracking for Seq '{}' in count()",
                    receiver_name.unwrap_or("<anonymous>")
                )
            })?;
        let pw = crate::ir::pointer_width();
        let mut needle =
            self.coerce_value_for_store_in_int_mode(needle, receiver, receiver_name)?;
        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        // `len < 5` is a length comparison (Int under Route A #2779).
        let five = self.len_const_like(len, 5)?;
        let len_lt_five = self.len_lt(len, five)?;
        self.overflow_checks.push((
            "Seq::to_multiset().count() currently requires len < 5".into(),
            len_lt_five,
        ));

        let count_sort = Sort::Int;
        let result = self
            .solver
            .fresh_var("__seq_occurrence_count", count_sort.clone());
        let step0 = self
            .solver
            .fresh_var("__seq_occurrence_count_0", count_sort.clone());
        let step0_eq = self.solver.try_eq(step0, zero).map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(step0_eq)
            .map_err(|e| e.to_string())?;

        let mut steps = vec![step0];
        for idx_value in 0i64..4 {
            let idx = self
                .solver
                .try_bv_const(idx_value, pw)
                .map_err(|e| e.to_string())?;
            let candidate = self
                .solver
                .try_select(receiver, idx)
                .map_err(|e| e.to_string())?;
            if let Some(info) = self.element_width_info(receiver, receiver_name) {
                self.term_widths.insert(candidate, info);
            }
            let (candidate, coerced_needle) = self.coerce_bv_widths(candidate, needle)?;
            needle = coerced_needle;
            let matches = self
                .solver
                .try_eq(candidate, needle)
                .map_err(|e| e.to_string())?;
            let prev = steps[idx_value as usize];
            let incremented = self.solver.try_add(prev, one).map_err(|e| e.to_string())?;
            let next_value = self
                .solver
                .try_ite(matches, incremented, prev)
                .map_err(|e| e.to_string())?;
            let step_name = format!("__seq_occurrence_count_{}", idx_value + 1);
            let next = self
                .solver
                .fresh_var(step_name.as_str(), count_sort.clone());
            let next_eq = self
                .solver
                .try_eq(next, next_value)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(next_eq)
                .map_err(|e| e.to_string())?;
            steps.push(next);
        }

        for len_case in 0i64..5 {
            // `len == len_case` is a length comparison (Int under Route A #2779).
            let len_const = self.len_const_like(len, len_case)?;
            let len_eq = self
                .solver
                .try_eq(len, len_const)
                .map_err(|e| e.to_string())?;
            let result_eq = self
                .solver
                .try_eq(result, steps[len_case as usize])
                .map_err(|e| e.to_string())?;
            let implication = self
                .solver
                .try_implies(len_eq, result_eq)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_assert_term(implication)
                .map_err(|e| e.to_string())?;
        }

        Ok(result)
    }

    /// Extract the element sort for a Seq<T> type.
    ///
    /// Resolves from term-keyed `CollectionMeta.elem_ty` first (#2067),
    /// falling back to name-keyed `var_types` for declared variables.
    pub(in crate::encoder) fn seq_element_sort(
        &self,
        receiver: Term,
        receiver_name: Option<&str>,
    ) -> TrustVcResult<Sort> {
        if let Some(meta) = self.collection_meta_by_term.get(&receiver) {
            if let Some(ref elem) = meta.elem_ty {
                return Ok(sort_for_type(elem));
            }
        }
        let ty = receiver_name
            .and_then(|name| self.var_types.get(name))
            .ok_or_else(|| "Seq operation requires a named receiver with known type".to_string())?;
        match ty {
            crate::ir::TrustVcType::Seq(elem) | crate::ir::TrustVcType::Array(elem, _) => {
                Ok(sort_for_type(elem))
            }
            _ => Err(format!("Expected Seq<T> type, got: {:?}", ty).into()),
        }
    }

    /// Add a Verus-compatible index bounds check: 0 <= idx < len (#1805).
    ///
    /// Always-on (not gated by `check_overflow`). In Verus, out-of-bounds Seq
    /// access is a verification error, not an optional overflow check. Length
    /// is now pointer_width (same as Seq index sort), so no extension needed.
    /// Returns the bound it pushed (`None` for a quantifier-bound index, whose
    /// bound is skipped): a read where that obligation is dropped is
    /// unspecified outside it (`read_within_carrier`).
    pub(in crate::encoder) fn add_seq_index_bounds_check(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        idx: Term,
        method: &str,
    ) -> TrustVcResult<Option<Term>> {
        if self.is_quantifier_bound_term(idx) {
            self.diagnostics
                .record(super::super::diagnostics::EncodingApproximation::BoundsCheckSkipped);
            return Ok(None);
        }
        let in_bounds = self.seq_index_bound(receiver_term, receiver_name, idx, method)?;
        self.overflow_checks.push((
            format!(
                "Seq::{}({}, i) requires i < len",
                method,
                receiver_name.unwrap_or("<anonymous>")
            )
            .into(),
            in_bounds,
        ));
        Ok(Some(in_bounds))
    }

    /// The index bound `0 <= idx < len` of a read of `receiver_term` (see
    /// [`Self::add_seq_index_bounds_check`], which pushes it as an obligation).
    fn seq_index_bound(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        idx: Term,
        method: &str,
    ) -> TrustVcResult<Term> {
        let len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracked for collection '{}' in Seq::{} bounds check",
                    receiver_name.unwrap_or("<anonymous>"),
                    method
                )
            })?;
        // When the Int length is pinned to an unsigned BV value (`bv2nat(k)`,
        // e.g. from an assumption `s.len() == k`), `len_as_index_bv` constant-
        // folds `int2bv(pw, bv2nat(k)) == k` and yields a clean BV with no
        // residual `int2bv` subterm. For a BV array index, discharge the bound
        // in pure BV against that companion — `idx <u k` stays tied to the
        // caller's BV facts about `k`, which `bv2int(idx) < bv2int(k)` severs
        // (ay is incomplete across that boundary). Falls through to the Int
        // path for opaque Int lengths (where the fold would leave an
        // Unknown-gating `int2bv`). See `len_as_index_bv` / Route A #2779.
        //
        // An `int2bv`-wrapped index must NOT take this path: `bvult(int2bv(..),
        // k)` would nest an `int2bv(bv2int(..))` round-trip that ay leaves
        // `Unknown`; it falls through to the Int path where the round-trip
        // collapses. The bound itself is built by `seq_index_bound_bv`, which
        // additionally reshapes a `len - c` index (`bvsub(k, c)`) away from the
        // `bvult(bvsub(k, c), k)` form ay cannot decide once `bv2nat(k)` is an
        // asserted hypothesis (the `s.len() == k` bridge) — see that helper.
        let idx_is_bv = matches!(self.solver.term_sort(idx), Sort::BitVec(_));
        // Fixed-size array fast path (#77). When the receiver is a named variable
        // of a statically-sized array type `[T; N]` whose tracked length is
        // exactly the symbolic length companion `len` we were handed, discharge
        // the index bound in PURE BV against the known constant `N`:
        //   idx <u bv(N)
        // rather than the Int form `bv2int(idx) < len`. ay lifts a non-literal BV
        // index to Int via `bv2nat` (e.g. a *dependent* index `ar[ar[0]]` encodes
        // as `bv2nat(bvadd(select(ar,0),1))`), and cannot relate that `bv2nat`
        // back to the BV facts that pin the index (`ar[0] == c`), so the Int bound
        // is left `Unknown` even though `c < N` plainly. Because the engine
        // already asserted `len == N` (`assert_fixed_array_int_length`) and the
        // index is a `BitVec(pointer_width())`, `idx <u bv(N)` is logically
        // EQUIVALENT to `bv2nat(idx) < len` — it NEVER weakens the check: a genuine
        // out-of-bounds index (`idx >= N`, or unbounded) still makes the bound
        // false and fails closed (Counterexample/Unknown), never Verified. We gate
        // on `collection_lengths[name] == len` so a derived/inner array length
        // (a 2D array's inner `[T; M]`, tracked under a different term) can never
        // be discharged against the outer `[_; N]` static length. An `int2bv`-
        // wrapped index keeps the Int route (the BV form would nest an
        // `int2bv(bv2int(..))` round-trip ay cannot bridge — see
        // `bv_index_wraps_int2bv`).
        if idx_is_bv && !self.bv_index_wraps_int2bv(idx) {
            if let Some(len_bv) = self.fixed_array_static_len_bv(receiver_name, len)? {
                let idx_bv = self.coerce_to_len_width(idx, OwnSign::of_constructed(false))?;
                let in_bounds = self
                    .seq_index_bound_bv(idx_bv, len_bv)
                    .map_err(|e| format!("Failed to create Seq::{} bounds check: {}", method, e))?;
                return Ok(in_bounds);
            }
        }
        if self.len_is_int(len) && idx_is_bv && !self.bv_index_wraps_int2bv(idx) {
            if let Some(len_bv) = self.try_folded_len_index_bv(len)? {
                let idx_bv = self.coerce_to_len_width(idx, OwnSign::of_constructed(false))?;
                let in_bounds = self
                    .seq_index_bound_bv(idx_bv, len_bv)
                    .map_err(|e| format!("Failed to create Seq::{} bounds check: {}", method, e))?;
                return Ok(in_bounds);
            }
        }
        // `len` is Int under Route A (#2779): compare `0 <= idx < len` in the
        // Int domain (idx is a BV array index, lifted via bv2int). Legacy
        // BV-length / pure-BV mode keeps the bvult form.
        let in_bounds = if self.len_is_int(len) || self.int_mode() {
            let len_int = if self.len_is_int(len) {
                len
            } else {
                self.solver
                    .try_bv2int(len)
                    .map_err(|e| format!("Failed bv2int for Seq::{} bounds check: {}", method, e))?
            };
            let idx_int = self.solver.try_bv2int(idx).unwrap_or(idx);
            let zero = self.solver.int_const(0);
            let idx_nonneg = self
                .solver
                .try_ge(idx_int, zero)
                .map_err(|e| e.to_string())?;
            let idx_lt_len = self
                .solver
                .try_lt(idx_int, len_int)
                .map_err(|e| e.to_string())?;
            self.solver
                .try_and(idx_nonneg, idx_lt_len)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bvult(idx, len)
                .map_err(|e| format!("Failed to create Seq::{} bounds check: {}", method, e))?
        };
        Ok(in_bounds)
    }

    /// For a named receiver of a statically-sized array type `[T; N]`, return the
    /// `BitVec(pointer_width())` constant `N` to use as the index bound — but only
    /// when the receiver's tracked length companion is *exactly* `len` (the term
    /// handed to the bounds check). See `add_seq_index_bounds_check` (#77).
    ///
    /// Soundness: the engine already asserted `len == N`
    /// (`assert_fixed_array_int_length`), so `bv(N)` is a value `len` is pinned to
    /// — materializing it as the bound adds no assumption. The
    /// `collection_lengths[name] == len` gate is the key guard: it ties the static
    /// `N` from the *declared* type to the *specific* length term being checked,
    /// so a derived/inner array length (e.g. a 2D array's inner `[T; M]`, tracked
    /// under a distinct term) can never be discharged against the outer `N`.
    /// Returns `None` (fall through to the Int/BV-fold paths) when the receiver is
    /// anonymous, not a fixed array, its tracked length is not `len`, or `N` does
    /// not fit the pointer width.
    fn fixed_array_static_len_bv(
        &mut self,
        receiver_name: Option<&str>,
        len: Term,
    ) -> TrustVcResult<Option<Term>> {
        let Some(name) = receiver_name else {
            return Ok(None);
        };
        // The length term under check must be the one tracked for this named
        // variable — otherwise the declared `[T; N]` length may not describe it.
        if self.collection_lengths.get(name) != Some(&len) {
            return Ok(None);
        }
        // Locals shadow parameters; prefer the local type when present.
        let ty = self
            .local_var_types
            .get(name)
            .or_else(|| self.var_types.get(name));
        let Some(crate::ir::TrustVcType::Array(_, array_len)) = ty else {
            return Ok(None);
        };
        let pw = crate::ir::pointer_width();
        // `N` must be representable as an unsigned `pointer_width` index. A length
        // at or above `2^pw` cannot occur for a real array and would not fit the
        // index sort; fall through rather than truncate.
        let array_len = *array_len;
        if (pw < 64 && array_len >= (1usize << pw)) || i64::try_from(array_len).is_err() {
            return Ok(None);
        }
        let len_bv = self
            .solver
            .try_bv_const(array_len as i64, pw)
            .map_err(|e| e.to_string())?;
        self.term_widths.insert(len_bv, (pw, false));
        Ok(Some(len_bv))
    }

    /// Build the BitVec form of the Seq index bound `idx <u len`, reshaping a
    /// `len - c` index so ay-dpll can decide it.
    ///
    /// The folded-BV bounds path produces `bvult(idx, len)` against a length
    /// companion `len` (a BV variable, e.g. `k` from `s.len() == k`). For a
    /// plain BV index (a const or a variable) this discharges directly. But when
    /// the index is `len - c` it is encoded as `bvsub(len, c)`, and the literal
    /// bound `bvult(bvsub(len, c), len)` is left `Unknown` by ay once the
    /// `s.len() == k` hypothesis has put `bv2nat(k)` (= the Int length bridge)
    /// on the assertion stack: the `bvsub` inside the unsigned-less-than
    /// interacts badly with the asserted `bv2nat`, even though the same bound
    /// with a non-`bvsub` index (`bvult(2, k)`) is decided fine.
    ///
    /// `bvult(bvsub(a, b), a)` is logically EQUIVALENT to
    /// `bvuge(a, b) && bvugt(b, 0)`:
    /// * `b == 0`            => `bvsub(a, 0) == a`, so `a <u a` is false, and
    ///   `bvugt(0, 0)` is false — both reject. (A genuine OOB: `idx == len`.)
    /// * `1 <= b <= a`       => `a - b` lies in `[0, a)`, true; `bvuge(a, b)` and
    ///   `bvugt(b, 0)` both true.
    /// * `b > a`             => `bvsub` wraps to `a - b + 2^w >= a`, false; and
    ///   `bvuge(a, b)` is false — both reject. (A genuine underflow-wrap OOB.)
    ///
    /// So the reshaped bound is equisatisfiable with the original — it NEVER
    /// weakens the check (a real OOB still fails closed) — but it removes the
    /// `bvsub` from inside the comparison, which ay decides directly. Only fires
    /// when the `bvsub` minuend is *exactly* the length companion `len`; any
    /// other index keeps the literal `bvult` form.
    fn seq_index_bound_bv(&mut self, idx: Term, len: Term) -> TrustVcResult<Term> {
        if let ay_dpll::api::TermKind::App { name, num_args: 2 } = self.solver.term_kind(idx) {
            if name == "bvsub" {
                let children = self.solver.term_children(idx);
                if let [minuend, subtrahend] = children.as_slice() {
                    if *minuend == len {
                        if let Sort::BitVec(bv) = self.solver.term_sort(len) {
                            let zero = self
                                .solver
                                .try_bv_const(0, bv.width)
                                .map_err(|e| e.to_string())?;
                            let in_range = self
                                .solver
                                .try_bvuge(len, *subtrahend)
                                .map_err(|e| e.to_string())?;
                            let nonzero = self
                                .solver
                                .try_bvugt(*subtrahend, zero)
                                .map_err(|e| e.to_string())?;
                            return self
                                .solver
                                .try_and(in_range, nonzero)
                                .map_err(|e| e.to_string().into());
                        }
                    }
                }
            }
        }
        self.solver
            .try_bvult(idx, len)
            .map_err(|e| e.to_string().into())
    }

    /// Add a Verus-compatible non-empty check: len >= 1 (#1805).
    ///
    /// Always-on — including inside quantifier bodies (#2231 Finding 2).
    /// Unlike bounds checks (which skip for bound-variable indices because the
    /// user guards with `!(i < len) || ...`), nonempty checks are about the
    /// receiver sequence itself, not the bound variable. Accessing `first()`
    /// on an empty Seq is always a verification error regardless of quantifier
    /// context. In Verus, first/last/drop_first/drop_last on an empty Seq
    /// is a verification error.
    pub(in crate::encoder) fn add_seq_nonempty_check(
        &mut self,
        receiver_term: Term,
        receiver_name: Option<&str>,
        method: &str,
    ) -> TrustVcResult<()> {
        let len = self
            .lookup_collection_len(receiver_term, receiver_name)
            .ok_or_else(|| {
                format!(
                    "No length tracked for collection '{}' in Seq::{} non-empty check",
                    receiver_name.unwrap_or("<anonymous>"),
                    method
                )
            })?;
        // `len > 0` matches the (Int under Route A #2779) length sort.
        let zero = self.len_const_like(len, 0)?;
        let nonempty = self.len_gt(len, zero)?;
        self.overflow_checks.push((
            format!("Seq::{}() requires len >= 1", method).into(),
            nonempty,
        ));
        Ok(())
    }
}

fn parse_bv_len_literal(text: &str) -> Option<usize> {
    let text = text.trim();
    if let Some(hex) = text.strip_prefix("#x") {
        return usize::from_str_radix(hex, 16).ok();
    }
    if let Some(indexed) = text.strip_prefix("(_ bv").and_then(|s| s.strip_suffix(')')) {
        return indexed.split_whitespace().next()?.parse().ok();
    }
    // Route A (#2779): spec-collection lengths are Int, so a literal length is
    // a plain decimal Int constant (e.g. `5`). Accept it for the unroll hint.
    text.parse().ok()
}
