//! Background axiom helpers for collection types (#1800).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Emits explicit ay assertions that make collection operation semantics
//! visible to the solver for cross-function reasoning. The inline axioms
//! in `array_axioms.rs` and `collection_seq.rs` handle within-function
//! element-wise reasoning; this module handles length and equality axioms
//! that must persist across function boundaries.
//!
//! Design: `designs/2026-03-19-1800-collection-axiom-encoding.md`

use ay_dpll::api::Term;

use super::parser_state::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    /// Assert an explicit length equality: `len(result) == expected_len`.
    ///
    /// While the length relationship is already implicit in the term graph
    /// (e.g., `new_len = bvadd(old_len, 1)`), asserting it as a ay constraint
    /// makes it available for reasoning paths that don't follow the construction
    /// chain — including cross-function postconditions and quantifier bodies.
    ///
    /// This is safe to call even when the equality is tautological from ay's
    /// perspective — it just makes the fact explicit.
    pub(super) fn assert_length_axiom(
        &mut self,
        result_len: Term,
        expected_len: Term,
        label: &str,
    ) -> TrustVcResult<()> {
        // Bridge a mixed Int/BV pair (Route A #2779 length vs a legacy/test BV
        // companion) to a common sort before the equality.
        let expected_len = self.len_match_sort(result_len, expected_len)?;
        let eq = self
            .solver
            .try_eq(result_len, expected_len)
            .map_err(|e| format!("length axiom ({label}): {e}"))?;
        self.solver
            .try_assert_term(eq)
            .map_err(|e| format!("assert length axiom ({label}): {e}"))?;
        Ok(())
    }

    /// Assert that a push result's length equals source length + 1.
    ///
    /// `len(result) == len(source) + 1`
    pub(super) fn assert_push_length_axiom(
        &mut self,
        new_len: Term,
        old_len: Term,
    ) -> TrustVcResult<()> {
        // `old_len + 1` in the length sort (Int under Route A #2779).
        let one = self.len_const_like(old_len, 1)?;
        let expected = self.len_add(old_len, one)?;
        self.assert_length_axiom(new_len, expected, "push")
    }

    /// Assert that a concat result's length equals the sum of both operands.
    ///
    /// `len(result) == len(lhs) + len(rhs)`
    pub(super) fn assert_concat_length_axiom(
        &mut self,
        result_len: Term,
        lhs_len: Term,
        rhs_len: Term,
    ) -> TrustVcResult<()> {
        // Int addition (Route A #2779): monotone, no wraparound.
        let expected = self.len_add(lhs_len, rhs_len)?;
        self.assert_length_axiom(result_len, expected, "concat")
    }

    /// Assert exact cardinality for Set::insert(elem).
    ///
    /// `new_len == old_len + ite(select(set, elem), 0, 1)`
    ///
    /// If the element was already in the set, length is unchanged.
    /// If the element was not in the set, length increases by 1.
    ///
    /// Also emits a conditional no-wrap overflow check for the "absent before
    /// insert" path. Without that guard, the solver can satisfy
    /// `old_len == u64::MAX` and `!contains(elem)`, then wrap the bitvector sum
    /// to `0`, which is not a valid finite-set cardinality.
    pub(super) fn assert_set_insert_cardinality(
        &mut self,
        new_len: Term,
        old_len: Term,
        set_term: Term,
        elem_term: Term,
    ) -> TrustVcResult<super::parser_state::OverflowCheck> {
        // Length sort is Int under Route A (#2779); constants/arithmetic match.
        let zero = self.len_const_like(old_len, 0)?;
        let one = self.len_const_like(old_len, 1)?;
        // select(set, elem) — true if element was already present
        let already_present = self
            .solver
            .try_select(set_term, elem_term)
            .map_err(|e| format!("set insert cardinality select: {e}"))?;
        // ite(already_present, 0, 1)
        let increment = self
            .solver
            .try_ite(already_present, zero, one)
            .map_err(|e| format!("set insert cardinality ite: {e}"))?;
        // old_len + increment — Int addition, monotone, no wraparound.
        let expected = self.len_add(old_len, increment)?;
        self.assert_length_axiom(new_len, expected, "set_insert")?;
        // Over Int there is no representable MAX to wrap past, so the
        // "absent => old+1 >= old" overflow obligation is vacuously true and
        // is intentionally NOT an assumed axiom (that was the unsound route B
        // — it would make a near-MAX-length context inconsistent). Build a
        // trivially-true guard so the caller's OverflowCheck plumbing is
        // satisfied without constraining the model. On a legacy BV-length path
        // the real bounded-width no-wrap guard is reconstructed instead.
        if self.len_is_int(old_len) {
            let truth = self.solver.bool_const(true);
            Ok(("set insert length no overflow".into(), truth))
        } else {
            let old_plus_one = self
                .solver
                .try_bvadd(old_len, one)
                .map_err(|e| format!("set insert cardinality add: {e}"))?;
            let no_wrap = self
                .solver
                .try_bvuge(old_plus_one, old_len)
                .map_err(|e| format!("set insert cardinality overflow guard: {e}"))?;
            let absent_before = self
                .solver
                .try_not(already_present)
                .map_err(|e| format!("set insert cardinality negate: {e}"))?;
            let guarded_no_wrap = self
                .solver
                .try_implies(absent_before, no_wrap)
                .map_err(|e| format!("set insert cardinality imply: {e}"))?;
            Ok(("set insert length no overflow".into(), guarded_no_wrap))
        }
    }

    /// Assert exact cardinality for Set::remove(elem).
    ///
    /// `new_len == old_len - ite(select(set, elem), 1, 0)`
    ///
    /// If the element was in the set, length decreases by 1.
    /// If the element was not in the set, length is unchanged.
    ///
    /// Also emits a conditional no-wrap underflow check for the "present before
    /// remove" path. Without that guard, the solver can satisfy
    /// `old_len == 0` and `contains(elem)`, then wrap the bitvector subtraction
    /// to `u64::MAX`, which is not a valid finite-set cardinality.
    pub(super) fn assert_set_remove_cardinality(
        &mut self,
        new_len: Term,
        old_len: Term,
        set_term: Term,
        elem_term: Term,
    ) -> TrustVcResult<super::parser_state::OverflowCheck> {
        // Length sort is Int under Route A (#2779); constants/arithmetic match.
        let zero = self.len_const_like(old_len, 0)?;
        let one = self.len_const_like(old_len, 1)?;
        // select(set, elem) — true if element was present before removal
        let was_present = self
            .solver
            .try_select(set_term, elem_term)
            .map_err(|e| format!("set remove cardinality select: {e}"))?;
        // Real precondition (preserved over Int): removing a present element
        // requires a non-empty set, else `old_len - 1` would be negative — not
        // a valid finite-set cardinality. This is NOT a wraparound artifact.
        let old_gt_zero = self.len_gt(old_len, zero)?;
        let guarded_no_wrap = self
            .solver
            .try_implies(was_present, old_gt_zero)
            .map_err(|e| format!("set remove cardinality imply: {e}"))?;
        // ite(was_present, 1, 0)
        let decrement = self
            .solver
            .try_ite(was_present, one, zero)
            .map_err(|e| format!("set remove cardinality ite: {e}"))?;
        // old_len - decrement
        let expected = self.len_sub(old_len, decrement)?;
        self.assert_length_axiom(new_len, expected, "set_remove")?;
        Ok(("set remove length no underflow".into(), guarded_no_wrap))
    }
}
