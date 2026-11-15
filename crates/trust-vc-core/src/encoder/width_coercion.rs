//! Width inference and bitvector coercion helpers for `AstExpressionParser`.
//!
//! Extracted from `parser_state.rs` to isolate the integer-width inference
//! and BV width-coercion surface. These methods normalize width behavior for
//! integer literals, mixed-width operations, and seq indices. Part of #2436.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term};

use crate::error::TrustVcResult;
use crate::ir::{CompareOp, TrustVcType};

use super::parser_state::{AstExpressionParser, CollectionKind};
use super::types::infer_int_width_from_types;

/// The signedness a bit-vector operand of IR type `ty` DENOTES: `Int` signed,
/// `Uint` and `char` unsigned, and `None` for every type that fixes none.
///
/// This — the operand's type at its use site — is the ONLY sound source of a
/// BV operand's signedness. The term alone cannot say: ay hash-conses
/// constants, so `u64::MAX` and `-1i64` are one term, and a term-keyed table
/// answers for whichever occurrence registered last (see `term_widths.rs`).
///
/// It answers for a TYPE; what reads a sign to WIDEN or LIFT a term takes an
/// [`OwnSign`], which only the term's own subexpression can produce.
pub(super) fn ir_type_signedness(ty: &TrustVcType) -> Option<bool> {
    ty.bit_width().map(|_| !ty.is_unsigned())
}

/// The signedness of ONE subterm, read from that subterm's OWN IR type — the
/// only sign a widening or a lift to `Int` may use.
///
/// Every value that is widened ([`AstExpressionParser::coerce_bv_widths_signed`],
/// [`AstExpressionParser::extend_term`]) or lifted to the integer it denotes
/// ([`AstExpressionParser::lift_bv_operand_to_int`]) takes one of these. It
/// has no constructor from a caller-chosen type and no `or`:
/// [`AstExpressionParser::own_sign`] derives it from the subexpression that
/// produced the term (and [`OwnSign::of_constructed`] states the
/// representation of a term the encoder itself assembled). So a PARENT's sign — a node's, a
/// match's, a conditional's, a peer's — cannot be handed to a widening at
/// all. That is the defect this type closes, and it kept recurring while the
/// sign was an `Option<bool>` every caller assembled with `.or(..)`
/// fallbacks: `match s { 0 => y_i16, _ => x_u8 }` widened the accumulated
/// later arms by the MATCH's sign, so `x == 200` read -56 (`== -56`
/// Verified, the true `== 200` refuted).
///
/// A subterm whose own type fixes no sign carries `None`, and every widening
/// or lift of a bit-vector with `None` is refused (fail closed) — never
/// guessed from its neighbours.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct OwnSign(Option<bool>);

impl OwnSign {
    /// The sign a term the encoder BUILT in a known representation carries:
    /// a two's-complement bit pattern it assembled itself (the mixed-type
    /// bitwise result, read signed at its widened width). Private to this
    /// module's callers that construct such terms; never a subterm's.
    pub(super) const fn of_constructed(signed: bool) -> Self {
        Self(Some(signed))
    }

    /// The sign, when the subterm's own type fixes one.
    pub(super) const fn get(self) -> Option<bool> {
        self.0
    }
}

/// Error for an operand that must be widened, lifted or ordered while its IR
/// type fixes no signedness. Fail closed: guessing a sign is how a negative
/// value reads as a huge positive one.
fn undetermined_signedness(what: &str) -> crate::error::TrustVcError {
    format!(
        "cannot {what}: the operand is a bit-vector whose IR type fixes no signedness \
         (signedness is taken from the operand's type, never from the hash-consed term)"
    )
    .into()
}

impl<'a> AstExpressionParser<'a> {
    /// The [`OwnSign`] of the term `expr` produced: the sign of `expr`'s OWN
    /// value type at this use site (`literal_hint` types an UNTYPED literal
    /// by the peer it meets, §5b rule 2 — it is consulted for nothing else,
    /// and never changes a literal's value, so it cannot change its sign).
    pub(super) fn own_sign(
        &self,
        expr: &crate::ir::TrustVcExpr,
        literal_hint: Option<&TrustVcType>,
    ) -> OwnSign {
        OwnSign(ir_type_signedness(
            &self.infer_operand_value_type(expr, literal_hint),
        ))
    }

    /// The width of a bit-vector-sorted term, read from its SORT; `None` for
    /// any other sort.
    pub(super) fn bv_term_width(&self, term: Term) -> Option<u32> {
        match self.solver.term_sort(term) {
            Sort::BitVec(bv) => Some(bv.width),
            _ => None,
        }
    }

    /// Lift `term` to the unbounded integer it denotes, with the signedness of
    /// its OPERAND (`signed`, from [`ir_type_signedness`]). Non-BV terms are
    /// returned unchanged; a BV term whose signedness is not fixed is refused.
    pub(super) fn lift_bv_operand_to_int(
        &mut self,
        term: Term,
        signed: OwnSign,
    ) -> TrustVcResult<Term> {
        if self.bv_term_width(term).is_none() {
            return Ok(term);
        }
        let signed = signed
            .get()
            .ok_or_else(|| undetermined_signedness("lift it to Int"))?;
        let converted = if signed {
            self.solver
                .try_bv2int_signed(term)
                .map_err(|e| e.to_string())?
        } else {
            self.solver.try_bv2int(term).map_err(|e| e.to_string())?
        };
        self.term_widths.remove(&converted);
        Ok(converted)
    }

    /// Coerce two terms to one BV width, extending the narrower one by the
    /// signedness of ITS OWN operand type (`a_signed` / `b_signed`).
    ///
    /// Widths come from the term sorts; a pair that is not two bit-vectors of
    /// different widths is returned unchanged. The typed counterpart of
    /// [`Self::coerce_bv_widths`], which reads the sign from `term_widths`.
    pub(super) fn coerce_bv_widths_signed(
        &mut self,
        (a, a_signed): (Term, OwnSign),
        (b, b_signed): (Term, OwnSign),
    ) -> TrustVcResult<(Term, Term)> {
        let (Some(aw), Some(bw)) = (self.bv_term_width(a), self.bv_term_width(b)) else {
            return Ok((a, b));
        };
        if aw < bw {
            return Ok((self.widen_bv_to(a, bw, a_signed)?, b));
        }
        if bw < aw {
            return Ok((a, self.widen_bv_to(b, aw, b_signed)?));
        }
        Ok((a, b))
    }

    /// Widen the bit-vector `term` to `width` bits by ITS OWN sign. A term
    /// already `width` wide is returned unchanged; a WIDER one is refused —
    /// narrowing would change its value — and so is one whose own type fixes
    /// no sign.
    pub(super) fn widen_bv_to(
        &mut self,
        term: Term,
        width: u32,
        own: OwnSign,
    ) -> TrustVcResult<Term> {
        let Some(term_width) = self.bv_term_width(term) else {
            return Ok(term);
        };
        if term_width == width {
            return Ok(term);
        }
        if term_width > width {
            return Err(format!(
                "cannot widen a {term_width}-bit value to {width} bits: it is wider, and \
                 narrowing it would change its value"
            )
            .into());
        }
        let signed = own
            .get()
            .ok_or_else(|| undetermined_signedness("widen it"))?;
        let extended = self.extend_term(term, width - term_width, own)?;
        self.term_widths.insert(extended, (width, signed));
        Ok(extended)
    }

    /// Compare two bit-vector operands as the INTEGERS they denote.
    ///
    /// Each operand carries the signedness of its own IR type; one whose type
    /// fixes none takes its peer's (Rust compares operands of one type).
    /// * same signedness — the narrower is extended by it and the comparison
    ///   uses it (`bvult`/`bvslt`, …), exactly the previous encoding;
    /// * MIXED signedness — both are extended to `max(width) + 1` bits by their
    ///   own signedness, where every value of both is representable as a signed
    ///   number, and compared signed. At equal widths the old encoding compared
    ///   the bits signed (`200u8 < 100i8` read `200` as `-56`), or equal
    ///   (`255u8 == -1i8`).
    /// * neither signedness known — only a same-width `==`/`!=` is decided (bit
    ///   equality is integer equality within one type); anything else is refused.
    ///
    /// `None` when a term is not a bit-vector, so the caller keeps its path.
    pub(super) fn try_encode_bv_compare_signed(
        &mut self,
        op: CompareOp,
        (left, left_signed): (Term, OwnSign),
        (right, right_signed): (Term, OwnSign),
    ) -> TrustVcResult<Option<Term>> {
        let (Some(lw), Some(rw)) = (self.bv_term_width(left), self.bv_term_width(right)) else {
            return Ok(None);
        };
        let (left, right, signed) = match (left_signed.get(), right_signed.get()) {
            (Some(ls), Some(rs)) if ls == rs => {
                let (left, right) =
                    self.coerce_bv_widths_signed((left, left_signed), (right, right_signed))?;
                (left, right, ls)
            }
            (Some(_), Some(_)) => {
                let width = lw.max(rw) + 1;
                let left = self.extend_term(left, width - lw, left_signed)?;
                let right = self.extend_term(right, width - rw, right_signed)?;
                (left, right, true)
            }
            // Bit equality is integer equality within ONE width, whatever the
            // sign; an ordering, or operands of two widths, needs each one's
            // own sign — a peer's is not borrowed (it used to be: an operand
            // whose type fixed none took the other's).
            _ if lw == rw && matches!(op, CompareOp::Eq | CompareOp::Ne) => (left, right, false),
            _ => return Err(undetermined_signedness("compare it")),
        };
        let solver = &mut *self.solver;
        let term = match op {
            CompareOp::Eq => solver.try_eq(left, right),
            CompareOp::Ne => solver.try_eq(left, right).and_then(|eq| solver.try_not(eq)),
            CompareOp::Lt if signed => solver.try_bvslt(left, right),
            CompareOp::Lt => solver.try_bvult(left, right),
            CompareOp::Le if signed => solver.try_bvsle(left, right),
            CompareOp::Le => solver.try_bvule(left, right),
            CompareOp::Gt if signed => solver.try_bvsgt(left, right),
            CompareOp::Gt => solver.try_bvugt(left, right),
            CompareOp::Ge if signed => solver.try_bvsge(left, right),
            CompareOp::Ge => solver.try_bvuge(left, right),
        }
        .map_err(|e| e.to_string())?;
        Ok(Some(term))
    }

    /// Infer the bit width for integer literals from the variable context.
    ///
    /// Uses a deterministic strategy: pick the most common integer width among
    /// variables (including quantifier-bound locals). Falls back to 32.
    pub(super) fn infer_int_width(&self) -> u32 {
        infer_int_width_from_types(self.var_types.values().chain(self.local_var_types.values()))
    }

    /// Require two terms that meet UNTYPED (a collection element and the value
    /// compared or stored against it, two map keys) to have one width.
    ///
    /// Neither side's own IR type is known here, so nothing may be widened:
    /// this used to extend the narrower term by its `term_widths` entry, and
    /// that table answers for whichever occurrence of a hash-consed constant
    /// registered last (`term_widths.rs`) — a sign that was never the value's.
    /// Two bit-vectors of different widths are refused (fail closed); a value
    /// is bound at the element type where its own type is known (the `seq!`
    /// literal, `push`, the typed element coercions), before it gets here.
    pub(super) fn coerce_bv_widths(&mut self, a: Term, b: Term) -> TrustVcResult<(Term, Term)> {
        match (self.bv_term_width(a), self.bv_term_width(b)) {
            (Some(aw), Some(bw)) if aw != bw => Err(format!(
                "cannot compare or store a {aw}-bit value against a {bw}-bit one: neither \
                 side's own type is known here, so neither may be widened"
            )
            .into()),
            _ => Ok((a, b)),
        }
    }

    /// Extend a bitvector term by `extra_bits`, by the term's OWN sign
    /// (sign-extend a signed value, zero-extend an unsigned one); refused when
    /// its own type fixes no sign.
    pub(super) fn extend_term(
        &mut self,
        term: Term,
        extra_bits: u32,
        own: OwnSign,
    ) -> TrustVcResult<Term> {
        let signed = own
            .get()
            .ok_or_else(|| undetermined_signedness("widen it"))?;
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
    ///
    /// `own` is the sign of the INDEX's own IR type. A narrower index is
    /// widened by it: a signed negative index stays negative (so it is out of
    /// bounds as the huge unsigned it reads as), where zero-extension made
    /// `-1i8` the in-range index 255 of a 300-element sequence.
    pub(super) fn coerce_seq_index(
        &mut self,
        receiver: Term,
        receiver_name: Option<&str>,
        idx: Term,
        own: OwnSign,
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
        // Seq index sort is BitVec(pointer_width). A narrower index is widened
        // by its own sign (see above).
        let pw = crate::ir::pointer_width();
        if let Some(idx_w) = self.bv_term_width(idx) {
            if idx_w < pw {
                let extended = self.extend_term(idx, pw - idx_w, own)?;
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
