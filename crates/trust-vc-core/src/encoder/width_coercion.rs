//! Width inference and bitvector coercion helpers for `AstExpressionParser`.
//!
//! Extracted from `parser_state.rs` to isolate the integer-width inference
//! and BV width-coercion surface. These methods normalize width behavior for
//! integer literals, mixed-width operations, and seq indices. Part of #2436.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use crate::error::TrustVcResult;

use super::parser_state::{AstExpressionParser, CollectionKind};
use super::types::infer_int_width_from_types;

impl<'a> AstExpressionParser<'a> {
    /// Infer the bit width for integer literals from the variable context.
    ///
    /// Uses a deterministic strategy: pick the most common integer width among
    /// variables (including quantifier-bound locals). Falls back to 32.
    pub(super) fn infer_int_width(&self) -> u32 {
        infer_int_width_from_types(self.var_types.values().chain(self.local_var_types.values()))
    }

    /// Coerce two bitvector terms to the same width, using sign-extension for
    /// signed types and zero-extension for unsigned types.
    ///
    /// Uses the `term_widths` tracker to determine widths and signedness without
    /// accessing ay private API. When binary operations involve bitvectors of
    /// different widths (e.g., i32 + i64, or u8 compared with u32), this extends
    /// the narrower operand to match the wider one. Terms not in `term_widths`
    /// are returned unchanged.
    pub(super) fn coerce_bv_widths(&mut self, a: Term, b: Term) -> TrustVcResult<(Term, Term)> {
        let a_info = self.term_widths.get(&a).copied();
        let b_info = self.term_widths.get(&b).copied();
        match (a_info, b_info) {
            (Some((aw, a_signed)), Some((bw, _b_signed))) if aw < bw => {
                let extended = self.extend_term(a, bw - aw, a_signed)?;
                self.term_widths.insert(extended, (bw, a_signed));
                Ok((extended, b))
            }
            (Some((aw, _a_signed)), Some((bw, b_signed))) if aw > bw => {
                let extended = self.extend_term(b, aw - bw, b_signed)?;
                self.term_widths.insert(extended, (aw, b_signed));
                Ok((a, extended))
            }
            _ => Ok((a, b)),
        }
    }

    /// Extend a bitvector term: sign-extend if signed, zero-extend if unsigned.
    pub(super) fn extend_term(
        &mut self,
        term: Term,
        extra_bits: u32,
        signed: bool,
    ) -> TrustVcResult<Term> {
        if signed {
            self.solver.try_bvsignext(term, extra_bits)
        } else {
            self.solver.try_bvzeroext(term, extra_bits)
        }
        .map_err(|e| e.to_string().into())
    }

    /// Coerce an index term to match a Seq's expected BitVec(pointer_width) index sort.
    ///
    /// Seq indices are BitVec(pointer_width) (usize), but most integer
    /// variables/literals are 32-bit. This extends the index when needed.
    ///
    /// When inside quantifier bodies (int_mode), bound variables have Sort::Int
    /// but Seq arrays still use BitVec(pointer_width) index sort. In this case,
    /// convert the Int-typed index to BitVec(pointer_width) via int2bv (#1888).
    ///
    /// The `receiver` Term is used to resolve collection kind via term-keyed
    /// metadata (#1749), which handles anonymous/chained collection results
    /// where `receiver_name` lookup in `var_types` would fail (#2067).
    pub(super) fn coerce_seq_index(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        idx: Term,
    ) -> TrustVcResult<Term> {
        // Only coerce for Seq types (which have BitVec(64) index sort).
        // Use lookup_collection_kind which checks term-keyed metadata first,
        // then falls back to var_types. This resolves the sort mismatch for
        // anonymous/chained collection results (#2067).
        let is_seq = self
            .lookup_collection_kind(receiver, receiver_name)
            .map(|k| k == CollectionKind::Seq)
            .unwrap_or(false);
        if !is_seq {
            return Ok(idx);
        }
        // Seq index sort is BitVec(pointer_width). If idx is narrower, zero-extend
        // it (indices are unsigned — usize semantics).
        let pw = crate::ir::pointer_width();
        if let Some(&(idx_w, _signed)) = self.term_widths.get(&idx) {
            if idx_w < pw {
                // Always zero-extend for indices (usize is unsigned)
                let extended = self
                    .solver
                    .try_bvzeroext(idx, pw - idx_w)
                    .map_err(|e| e.to_string())?;
                self.term_widths.insert(extended, (pw, false));
                return Ok(extended);
            }
        } else if matches!(self.solver.term_sort(idx), ay_dpll::api::Sort::Int) {
            // Quantifier-bound variables and int-mode constants can use Sort::Int
            // while Seq arrays have BitVec(pointer_width) index sort. Convert
            // Int -> BitVec(pw) before select/bounds encoding (#1888, #2223).
            // try_int2bv expects Sort::Int; if idx is already BitVec, it
            // returns Err and we fall through to return idx unchanged.
            if let Ok(converted) = self.solver.try_int2bv(idx, pw) {
                // Wrapping Int -> BV(pw) carrier-index crossing (NC4b): a
                // GROUND length-derived index (`s.len() - 2` with an assumed
                // huge len) is exact only on [0, 2^pw); push the carrier
                // representability obligation. Quantifier-bound indices are
                // skipped both here and inside the helper (#2557) — their
                // range is scoped by the quantifier's own `0 <= i < len`
                // guard and the `len_index_companion` length bridge.
                if !self.is_quantifier_bound_term(idx) {
                    self.push_index_representability_check(idx)?;
                }
                self.diagnostics
                    .record(super::diagnostics::EncodingApproximation::IntBvCoercion);
                self.term_widths.insert(converted, (pw, false));
                if self.is_quantifier_bound_term(idx) {
                    if let Some(scope) = self.quantifier_scopes.last_mut() {
                        scope.add_bound_term(converted);
                    }
                }
                return Ok(converted);
            }
        }
        Ok(idx)
    }
}
