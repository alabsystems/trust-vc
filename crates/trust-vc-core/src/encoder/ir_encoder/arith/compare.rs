//! Comparison encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;

use crate::error::TrustVcResult;
use crate::ir::{CompareOp, TrustVcExpr, TrustVcType};
use crate::ir_expr::CollectionOp;

use super::super::is_trust_vc_literal_zero;
use crate::encoder::width_coercion::OwnSign;
use crate::encoder::AstExpressionParser;

fn seq_like_elem_type(ty: &TrustVcType) -> Option<&TrustVcType> {
    match ty {
        TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => Some(elem.as_ref()),
        _ => None,
    }
}

impl<'a> AstExpressionParser<'a> {
    /// Encode a comparison operation.
    ///
    /// Signedness is determined from the TrustVcExpr operand types, not from
    /// `term_widths`: ay hash-conses constants, so `u64::MAX` and `-1i64` are
    /// ONE term and a term-keyed table answers for whichever occurrence was
    /// encoded last. Every BV operand here is lifted, widened and ordered with
    /// the signedness of its own IR type at this use site
    /// ([`crate::encoder::width_coercion::OwnSign`] of
    /// [`Self::infer_operand_value_type`]).
    ///
    /// Unsigned comparison is selected only when both operands are unsigned
    /// (AND semantics, #1769). Unsuffixed literal cases like `u32 >= 0` are
    /// handled by lowering-time literal coercion in `ir_lowering::operators`.
    /// Fixes #2068 without regressing mixed-sign comparisons.
    pub(in crate::encoder::ir_encoder) fn encode_compare(
        &mut self,
        op: CompareOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
    ) -> TrustVcResult<Term> {
        // Determine signedness from the effective operand IR types BEFORE
        // encoding to ay Terms. Direct IR can still carry a default `Int{32}`
        // literal, so apply the same peer-type hint used during term encoding
        // before deciding whether `<`, `<=`, `>`, `>=` should be unsigned.
        let left_hint_ty = self.infer_effective_expr_type(right, None);
        let right_hint_ty = self.infer_effective_expr_type(left, None);
        let left_ty = self.infer_effective_expr_type(left, Some(&left_hint_ty));
        let right_ty = self.infer_effective_expr_type(right, Some(&right_hint_ty));
        // The signedness each operand DENOTES, from its own type at this use
        // site — never from `term_widths`, whose entry for a hash-consed
        // constant may have been written by a different operand.
        let left_signed = self.own_sign(left, Some(&left_hint_ty));
        let right_signed = self.own_sign(right, Some(&right_hint_ty));
        if matches!(op, CompareOp::Eq | CompareOp::Ne)
            && seq_like_elem_type(&left_ty)
                .zip(seq_like_elem_type(&right_ty))
                .is_some_and(|(left_elem, right_elem)| left_elem == right_elem)
        {
            if let Some(finite_eq) = self.encode_finite_seq_literal_eq(op, left, right)? {
                return Ok(finite_eq);
            }

            // Under native-seq, ay's Seq theory provides built-in extensional
            // equality — just use try_eq on the Seq-sorted terms directly.
            // The array encoding needs the manual extensional equality axiom
            // (forall i. i < len => a[i] == b[i]) because array select/store
            // doesn't guarantee structural equality.
            #[cfg(feature = "native-seq")]
            let seq_eq = {
                let left_term = self.encode_subexpr(left)?;
                let right_term = self.encode_subexpr(right)?;
                self.solver
                    .try_eq(left_term, right_term)
                    .map_err(|e| -> crate::error::TrustVcError { e.to_string().into() })?
            };
            // Non-native (array-backed) Seq: two structurally-distinct but
            // pointwise-equal CONCRETE seqs (`Seq::new(5, |i| 10*i)` vs a
            // `push`-chain / `seq!` literal) are provably `==`, but the symbolic
            // BV-companion `encode_seq_extensional_eq` form does not unroll them,
            // leaving `assert(a === b)` stuck at `unknown` (the exact gap behind
            // upstream `seqs.rs::test1`'s `assert(s1 === s2)` after `=~=`). When
            // BOTH operands have a static length within the finite-unroll cap,
            // route through the SAME `build_ext_eq_expr` finite form that
            // `assert_seqs_equal!` (`ext_eq!`) already uses — it emits the decided
            // conjunction `a[0]==b[0] && … && a[n-1]==b[n-1]` (or a concrete
            // `len_eq` refutation on a length mismatch), so a valid equality is
            // proven and a wrong element/length still refutes. SYMBOLIC-length
            // operands keep `encode_seq_extensional_eq` unchanged — no regression
            // to the quantifier / counterexample-model paths it was tuned for.
            #[cfg(not(feature = "native-seq"))]
            let seq_eq = if crate::extensional_eq::seq_pair_is_finite_unrollable(left, right) {
                let ext_eq = crate::extensional_eq::build_ext_eq_expr(left.clone(), right.clone());
                self.encode_subexpr(&ext_eq)?
            } else {
                self.encode_seq_extensional_eq(left, right)?
            };
            return match op {
                CompareOp::Eq => Ok(seq_eq),
                CompareOp::Ne => self
                    .solver
                    .try_not(seq_eq)
                    .map_err(|e| e.to_string().into()),
                _ => unreachable!("guarded above"),
            };
        }
        if left_ty == right_ty
            && matches!(
                left_ty,
                TrustVcType::Set(_) | TrustVcType::Map(_, _) | TrustVcType::Multiset(_)
            )
            && matches!(op, CompareOp::Eq | CompareOp::Ne)
        {
            let extensional_expr = if matches!(op, CompareOp::Eq) {
                crate::extensional_eq::build_ext_eq_expr(left.clone(), right.clone())
            } else {
                crate::extensional_eq::build_ext_ne_expr(left.clone(), right.clone())
            };
            return self.encode_subexpr(&extensional_expr);
        }
        let both_explicit_bv = left_ty.bit_width().is_some() && right_ty.bit_width().is_some();
        let unsigned = both_explicit_bv && left_ty.is_unsigned() && right_ty.is_unsigned();

        // When both operand types are explicit BV but the session-level
        // use_int_arithmetic is active (not quantifier-depth int_mode), temporarily
        // disable it so both terms encode as BV. Without this, a match result
        // is BV64 but the peer literal encodes as Int, causing a sort mismatch.
        // Only applies when quantifier_depth == 0 — inside quantifiers, int_mode
        // stays true and both sides encode as Int (no mismatch). Part of #2557.
        let use_bv_compare = both_explicit_bv
            && self.use_int_arithmetic
            && self.quantifier_depth == 0
            // Measure-mode setup can promote integer variables to MathInt/Nat in
            // the encoder context while the lowered IR still carries concrete
            // widths. Keep int-mode active for those comparisons so `encode_var`
            // accepts the promoted context instead of forcing the #2557 BV path.
            && !self.expr_references_promoted_int_var(left)
            && !self.expr_references_promoted_int_var(right)
            // After equality-assumption substitution, expressions may be fully
            // constant (all Vars replaced by IntLit). Without any solver-declared
            // variables in the expression, there is no sort-mismatch risk — the
            // BV-compare path would silently apply modular wrapping to constants
            // that must be compared with Int semantics. Part of #2668.
            && !(left.is_definitely_var_free_for_bv_compare()
                && right.is_definitely_var_free_for_bv_compare());
        let original_use_int_arithmetic = self.use_int_arithmetic;
        let (left_term, right_term) = crate::encoder::with_flag_unwind_safe!(
            self.use_int_arithmetic,
            original_use_int_arithmetic,
            {
                if use_bv_compare {
                    self.use_int_arithmetic = false;
                }
                let left_term = self.encode_expr_with_integer_hint(left, Some(&left_hint_ty))?;
                let right_term = self.encode_expr_with_integer_hint(right, Some(&right_hint_ty))?;
                Ok::<_, crate::error::TrustVcError>((left_term, right_term))
            }
        )?;

        if self
            .classify_float_compare_operands(&left_ty, &right_ty)?
            .is_some()
        {
            return self.encode_float_compare(op, left_term, right_term);
        }

        // Real comparisons: try_lt/try_le/try_gt/try_ge work for Sort::Real (#2517).
        if matches!(left_ty, TrustVcType::Real) || matches!(right_ty, TrustVcType::Real) {
            return self.encode_int_compare(op, left_term, right_term);
        }

        // When both operands are explicit BV types and we disabled int_mode
        // above, use the BV comparison path. The terms were encoded as BV —
        // EXCEPT a spec-collection length, which is an Int term whatever its IR
        // type says (Route A #2779; see `try_encode_int_sorted_compare`), so an
        // Int-sorted operand takes the integer comparison instead of reaching
        // `bvslt` with an Int argument. Part of #2557 Slice 2.
        if use_bv_compare {
            if let Some(int_compare) = self.try_encode_int_sorted_compare(
                op,
                (left_term, left_signed),
                (right_term, right_signed),
            )? {
                return Ok(int_compare);
            }
            if let Some(bv_compare) = self.try_encode_bv_compare_signed(
                op,
                (left_term, left_signed),
                (right_term, right_signed),
            )? {
                return Ok(bv_compare);
            }
            let (left_term, right_term) = self.coerce_bv_widths(left_term, right_term)?;
            return match op {
                CompareOp::Eq => self
                    .solver
                    .try_eq(left_term, right_term)
                    .map_err(|e| e.to_string().into()),
                CompareOp::Ne => {
                    let eq = self
                        .solver
                        .try_eq(left_term, right_term)
                        .map_err(|e| e.to_string())?;
                    self.solver.try_not(eq).map_err(|e| e.to_string().into())
                }
                CompareOp::Lt => if unsigned {
                    self.solver.try_bvult(left_term, right_term)
                } else {
                    self.solver.try_bvslt(left_term, right_term)
                }
                .map_err(|e| e.to_string().into()),
                CompareOp::Le => if unsigned {
                    self.solver.try_bvule(left_term, right_term)
                } else {
                    self.solver.try_bvsle(left_term, right_term)
                }
                .map_err(|e| e.to_string().into()),
                CompareOp::Gt => if unsigned {
                    self.solver.try_bvugt(left_term, right_term)
                } else {
                    self.solver.try_bvsgt(left_term, right_term)
                }
                .map_err(|e| e.to_string().into()),
                CompareOp::Ge => if unsigned {
                    self.solver.try_bvuge(left_term, right_term)
                } else {
                    self.solver.try_bvsge(left_term, right_term)
                }
                .map_err(|e| e.to_string().into()),
            };
        }

        if self.int_mode() {
            // In int_mode, unsigned wrapping (mod 2^w) always produces values
            // in [0, 2^w). Comparisons against literal 0 involving only unsigned
            // operands can be simplified to avoid modular arithmetic that ay-dpll's
            // CEGQI cannot handle in quantified formulas (#2062).
            if unsigned {
                if let Some(tautology) = Self::simplify_unsigned_zero_compare(op, left, right) {
                    return Ok(self.solver.bool_const(tautology));
                }
            }
            return self.encode_int_compare(op, left_term, right_term);
        }

        // Under native-seq, comparisons involving Int-sorted terms (e.g.,
        // seq.len which returns Sort::Int) must use Int comparison even
        // outside int_mode. When one operand is MathInt and the other is
        // BV (e.g., `s.len() == k` where k: u64), convert the BV operand
        // to Int via bv2int so both sides share Sort::Int. Check actual
        // term sort, not IR type, because arithmetic on MathInt operands
        // can return Int-sorted terms even when the Arith node's IR type
        // is Uint{64}. #2680.
        if !both_explicit_bv
            && (matches!(left_ty, TrustVcType::MathInt | TrustVcType::Nat)
                || matches!(right_ty, TrustVcType::MathInt | TrustVcType::Nat))
        {
            let left_term = self.lift_bv_operand_to_int(left_term, left_signed)?;
            let right_term = self.lift_bv_operand_to_int(right_term, right_signed)?;
            return self.encode_int_compare(op, left_term, right_term);
        }

        // Route A (#2779): spec-collection `.len()` is Int while a peer integer
        // literal/usize value encodes as BV — and TWO lengths are both Int.
        // Either way the comparison is over the integers; see
        // `try_encode_int_sorted_compare`.
        if let Some(int_compare) = self.try_encode_int_sorted_compare(
            op,
            (left_term, left_signed),
            (right_term, right_signed),
        )? {
            return Ok(int_compare);
        }

        // Two bit-vectors: compared as the integers they denote, each with its
        // own operand's signedness (a mixed pair used to be compared as bits).
        if let Some(bv_compare) = self.try_encode_bv_compare_signed(
            op,
            (left_term, left_signed),
            (right_term, right_signed),
        )? {
            return Ok(bv_compare);
        }

        // Not a bit-vector pair (datatypes, arrays, booleans under `==`): the
        // previous path, unchanged.
        let (left_term, right_term) = self.coerce_bv_widths(left_term, right_term)?;

        match op {
            CompareOp::Eq => self
                .solver
                .try_eq(left_term, right_term)
                .map_err(|e| e.to_string().into()),
            CompareOp::Ne => {
                let eq = self
                    .solver
                    .try_eq(left_term, right_term)
                    .map_err(|e| e.to_string())?;
                self.solver.try_not(eq).map_err(|e| e.to_string().into())
            }
            CompareOp::Lt => if unsigned {
                self.solver.try_bvult(left_term, right_term)
            } else {
                self.solver.try_bvslt(left_term, right_term)
            }
            .map_err(|e| e.to_string().into()),
            CompareOp::Le => if unsigned {
                self.solver.try_bvule(left_term, right_term)
            } else {
                self.solver.try_bvsle(left_term, right_term)
            }
            .map_err(|e| e.to_string().into()),
            CompareOp::Gt => if unsigned {
                self.solver.try_bvugt(left_term, right_term)
            } else {
                self.solver.try_bvsgt(left_term, right_term)
            }
            .map_err(|e| e.to_string().into()),
            CompareOp::Ge => if unsigned {
                self.solver.try_bvuge(left_term, right_term)
            } else {
                self.solver.try_bvsge(left_term, right_term)
            }
            .map_err(|e| e.to_string().into()),
        }
    }

    /// Route A (#2779) at the comparison boundary: when at least one operand
    /// TERM is `Int`-sorted, compare over the integers.
    ///
    /// A spec-collection length is modelled as an unbounded non-negative
    /// `Int` (`encoder/mod.rs`, `collection_shared.rs`), whatever the IR type
    /// of the `.len()` node says — the driver's string-length view types it
    /// `Int { width: 64 }`, which made `both_explicit_bv` true and sent
    /// `a.len() < b.len()` (Int, Int) to `bvslt`: "sort mismatch in bvslt:
    /// expected BitVec(w), BitVec(w), got Int, Int", an `Unknown` for a true
    /// fact. So the sort of the TERM, not the IR type, decides:
    ///
    /// * `(Int, Int)` — compared as integers, which is exactly what the two
    ///   terms are;
    /// * `(Int, BV)` / `(BV, Int)` — the BV operand is lifted to the integer
    ///   it DENOTES, with the signedness of ITS OWN operand type (`*_signed`,
    ///   an [`OwnSign`]; an operand whose type fixes none is refused — it
    ///   used to take its peer's). The lift used to
    ///   be unsigned unconditionally ("lengths/usize are non-negative"), which
    ///   read a negative signed peer as a huge positive number (`a.len() == 2`
    ///   entailed `a.len() < -1i64`); d4e06963 then took the sign from
    ///   `term_widths`, whose entry for a hash-consed constant belongs to
    ///   whichever operand encoded it last: `u64::MAX < a.len() + (-1i64)`
    ///   read `u64::MAX` as `-1` and came back `Verified`
    ///   (`tests/operand_signedness_soundness.rs`).
    ///
    /// `None` when neither term is `Int`, or when a term is neither `Int` nor
    /// BV (floats and reals are routed before this is reached), so every
    /// other comparison keeps its path.
    fn try_encode_int_sorted_compare(
        &mut self,
        op: CompareOp,
        (left_term, left_signed): (Term, OwnSign),
        (right_term, right_signed): (Term, OwnSign),
    ) -> TrustVcResult<Option<Term>> {
        use ay_dpll::api::Sort;
        let left_sort = self.solver.term_sort(left_term);
        let right_sort = self.solver.term_sort(right_term);
        let left_int = matches!(left_sort, Sort::Int);
        let right_int = matches!(right_sort, Sort::Int);
        let numeric = |int: bool, sort: &Sort| int || matches!(sort, Sort::BitVec(_));
        if !(left_int || right_int)
            || !numeric(left_int, &left_sort)
            || !numeric(right_int, &right_sort)
        {
            return Ok(None);
        }
        // An Int term is returned unchanged; a BV term is lifted with the
        // signedness of ITS OWN operand only — a peer's is never borrowed, and
        // an operand whose own type fixes none is refused.
        let left_int_term = self.lift_bv_operand_to_int(left_term, left_signed)?;
        let right_int_term = self.lift_bv_operand_to_int(right_term, right_signed)?;
        self.encode_int_compare(op, left_int_term, right_int_term)
            .map(Some)
    }

    fn encode_finite_seq_literal_eq(
        &mut self,
        op: CompareOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
    ) -> TrustVcResult<Option<Term>> {
        let Some(left_elements) = finite_seq_literal_elements(left) else {
            return Ok(None);
        };
        let Some(right_elements) = finite_seq_literal_elements(right) else {
            return Ok(None);
        };

        let mut eq = if left_elements.len() == right_elements.len() {
            self.solver.bool_const(true)
        } else {
            self.solver.bool_const(false)
        };
        if left_elements.len() == right_elements.len() {
            for (left_element, right_element) in left_elements.iter().zip(right_elements.iter()) {
                let left_hint_ty = self.infer_effective_expr_type(right_element, None);
                let right_hint_ty = self.infer_effective_expr_type(left_element, None);
                let left_term =
                    self.encode_expr_with_integer_hint(left_element, Some(&left_hint_ty))?;
                let right_term =
                    self.encode_expr_with_integer_hint(right_element, Some(&right_hint_ty))?;
                let element_eq = self
                    .solver
                    .try_eq(left_term, right_term)
                    .map_err(|e| e.to_string())?;
                eq = self
                    .solver
                    .try_and(eq, element_eq)
                    .map_err(|e| e.to_string())?;
            }
        }

        let result = match op {
            CompareOp::Eq => eq,
            CompareOp::Ne => self.solver.try_not(eq).map_err(|e| e.to_string())?,
            _ => unreachable!("guarded by caller"),
        };
        Ok(Some(result))
    }

    fn encode_float_compare(
        &mut self,
        op: CompareOp,
        left: Term,
        right: Term,
    ) -> TrustVcResult<Term> {
        match op {
            CompareOp::Eq => self
                .solver
                .try_fp_eq(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Ne => {
                let eq = self
                    .solver
                    .try_fp_eq(left, right)
                    .map_err(|e| e.to_string())?;
                self.solver.try_not(eq).map_err(|e| e.to_string().into())
            }
            CompareOp::Lt => self
                .solver
                .try_fp_lt(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Le => self
                .solver
                .try_fp_le(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Gt => self
                .solver
                .try_fp_gt(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Ge => self
                .solver
                .try_fp_ge(left, right)
                .map_err(|e| e.to_string().into()),
        }
    }

    /// Encode comparison in Int arithmetic mode.
    fn encode_int_compare(
        &mut self,
        op: CompareOp,
        left: Term,
        right: Term,
    ) -> TrustVcResult<Term> {
        match op {
            CompareOp::Eq => self
                .solver
                .try_eq(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Ne => {
                let eq = self.solver.try_eq(left, right).map_err(|e| e.to_string())?;
                self.solver.try_not(eq).map_err(|e| e.to_string().into())
            }
            CompareOp::Lt => self
                .solver
                .try_lt(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Le => self
                .solver
                .try_le(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Gt => self
                .solver
                .try_gt(left, right)
                .map_err(|e| e.to_string().into()),
            CompareOp::Ge => self
                .solver
                .try_ge(left, right)
                .map_err(|e| e.to_string().into()),
        }
    }

    /// Simplify unsigned comparisons against literal 0 in int_mode (#2062).
    ///
    /// - `unsigned_expr >= 0` → always true
    /// - `0 <= unsigned_expr` → always true
    /// - `unsigned_expr < 0`  → always false
    /// - `0 > unsigned_expr`  → always false
    ///
    /// Returns `Some(true)` for tautologies, `Some(false)` for contradictions,
    /// `None` when no simplification applies.
    ///
    /// # Why the operand must be subtraction-free
    ///
    /// The original justification was *"in int_mode, unsigned arithmetic results
    /// are wrapped via `mod 2^w`, which always produces values in `[0, 2^w)`"*.
    /// That premise DIED when quantifier bodies moved to faithful mathematical
    /// arithmetic: `encode_int_arith` no longer wraps under a binder, so
    /// `i - 1` for `i: u64` is now the honest `int` value `-1` at `i == 0`,
    /// exactly as Verus types it (`u64 - u64 : int`, not `u64`).
    ///
    /// Left unrestricted the fold would be a false verify in BOTH polarities:
    /// `forall|i: u64| i - 1 >= 0` folds to `true` (refuted by `i == 0`), and
    /// `forall|i: u64| !(i - 1 < 0)` folds the inner compare to `false` and so
    /// verifies (also refuted by `i == 0`).
    ///
    /// Restricting to operands with no `-` and no unary negation anywhere
    /// restores the invariant the fold actually needs — every remaining leaf is
    /// a genuinely unsigned-typed value (`>= 0` by Rust/Verus typing) and
    /// `+`/`*`/`/`/`%` are monotone on non-negatives, so the whole expression is
    /// non-negative. The #2062 motivating shape `forall(|j: u32| j + 1 >= 0)`
    /// is subtraction-free and keeps folding.
    fn simplify_unsigned_zero_compare(
        op: CompareOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
    ) -> Option<bool> {
        let right_is_zero = is_trust_vc_literal_zero(right);
        let left_is_zero = is_trust_vc_literal_zero(left);

        match op {
            // unsigned_expr >= 0 → true
            CompareOp::Ge if right_is_zero && expr_is_subtraction_free(left) => Some(true),
            // 0 <= unsigned_expr → true
            CompareOp::Le if left_is_zero && expr_is_subtraction_free(right) => Some(true),
            // unsigned_expr < 0 → false
            CompareOp::Lt if right_is_zero && expr_is_subtraction_free(left) => Some(false),
            // 0 > unsigned_expr → false
            CompareOp::Gt if left_is_zero && expr_is_subtraction_free(right) => Some(false),
            _ => None,
        }
    }
}

/// Whether `expr` contains no subtraction and no unary negation anywhere.
///
/// Narrowness pin for `simplify_unsigned_zero_compare`: `-` (and unary `-`) is
/// the ONLY way an expression built from unsigned-typed leaves can take a
/// negative mathematical value now that quantifier bodies encode faithful
/// unbounded `int` arithmetic. `+`, `*`, `/` and `%` are all non-negative on
/// non-negative operands, and every leaf whose static type is unsigned is
/// non-negative by Rust/Verus typing. An explicit `WrappingArith` subtraction is
/// excluded too — it is textually a `-` and the cheapest correct answer is to
/// decline rather than reason about its width.
///
/// The walk is EXHAUSTIVE (`walk_expr` visits every child, including quantifier
/// bodies, match arms and cast operands), so a `-` buried under a cast or a call
/// argument still blocks the fold. Declining is the fail-closed direction: the
/// comparison is then encoded and discharged by the solver as usual.
fn expr_is_subtraction_free(expr: &TrustVcExpr) -> bool {
    use crate::ir::ArithOp;
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

    struct V {
        found_subtraction: bool,
    }
    impl TrustVcExprVisitor for V {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.found_subtraction {
                return;
            }
            match expr {
                TrustVcExpr::Neg(_) => self.found_subtraction = true,
                TrustVcExpr::Arith {
                    op: ArithOp::Sub, ..
                }
                | TrustVcExpr::WrappingArith {
                    op: ArithOp::Sub, ..
                } => self.found_subtraction = true,
                _ => walk_expr(self, expr),
            }
        }
    }

    let mut v = V {
        found_subtraction: false,
    };
    v.visit_expr(expr);
    !v.found_subtraction
}

fn finite_seq_literal_elements(expr: &TrustVcExpr) -> Option<Vec<&TrustVcExpr>> {
    match expr {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if args.is_empty()
            && name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
            && name.contains("Seq_")
            && name.ends_with("_empty")
            && matches!(return_ty, TrustVcType::Seq(_)) =>
        {
            Some(Vec::new())
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 1 && matches!(ty, TrustVcType::Seq(_)) => {
            let mut elements = finite_seq_literal_elements(receiver)?;
            elements.push(&args[0]);
            Some(elements)
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Add | CollectionOp::Concat,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 1 && matches!(ty, TrustVcType::Seq(_)) => {
            let mut elements = finite_seq_literal_elements(receiver)?;
            elements.extend(finite_seq_literal_elements(&args[0])?);
            Some(elements)
        }
        TrustVcExpr::Cast {
            expr,
            to_ty: TrustVcType::Seq(_),
            ..
        } => finite_seq_literal_elements(expr),
        _ => None,
    }
}
