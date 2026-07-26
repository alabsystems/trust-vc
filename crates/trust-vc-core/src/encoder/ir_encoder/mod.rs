//! TrustVcExpr-to-ay Term encoding — the typed IR encoder.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides `encode_trust_vc_expr`, the parallel path to
//! `parse_syn_expr` that accepts typed `TrustVcExpr` nodes instead of
//! `syn::Expr` AST. All type information comes from the IR nodes —
//! no string parsing, no `syn::parse_str`, no width inference heuristics.
//!
//! Part of #1550 Phase 4 (#1865).

mod advanced;
mod arith;
pub(in crate::encoder) mod cast;
mod choose;

mod collection_methods;
mod collection_seq_inline;
mod collection_set_map_inline;
mod collections;
mod fn_call;
mod free_vars;
mod indexing;
mod ite_let;
mod logic;
mod match_datatype;
mod match_encode;
mod multiset;
pub(crate) mod normalize;
mod overflow_guard;
mod place_encoding;
mod prophecy;
pub(in crate::encoder) mod refutation;
mod saturating;
mod wrapping;

use ay_dpll::api::Term;

use crate::error::{TrustVcError, TrustVcResult};
use crate::expr_depth::validate_expr_depth;
use crate::ir::{IntConstKind, TrustVcExpr, TrustVcType};

use super::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    /// Encode a `TrustVcExpr` into a ay `Term`. No wildcard — new variants are compile errors.
    pub fn encode_trust_vc_expr(&mut self, expr: &TrustVcExpr) -> TrustVcResult<Term> {
        if self.expr_depth_guard_active {
            return self.encode_trust_vc_expr_inner(expr);
        }

        validate_expr_depth(expr, "IR encoding").map_err(|err| TrustVcError::Encoding {
            context: "encode expression",
            detail: err.to_string(),
        })?;

        crate::encoder::with_flag_unwind_safe!(self.expr_depth_guard_active, true, {
            self.encode_trust_vc_expr_inner(expr)
        })
    }

    /// Root-dispatch implementation for `encode_trust_vc_expr`.
    #[rustfmt::skip]
    fn encode_trust_vc_expr_inner(&mut self, expr: &TrustVcExpr) -> TrustVcResult<Term> {
        #[cfg(test)]
        if crate::encoder::verification::test_hooks::take_forced_trust_vc_expr_encode_panic() {
            panic!("forced encode_trust_vc_expr panic");
        }

        match expr {
            TrustVcExpr::UnitLit => Ok(super::unit::unit_term(self.solver)),
            TrustVcExpr::BoolLit(b) => Ok(self.solver.bool_const(*b)),
            TrustVcExpr::StringLit(value) => Ok(self.solver.string_const(value)),
            TrustVcExpr::IntLit { value, ty } => self.encode_int_lit(*value, ty),
            TrustVcExpr::IntConst { ty, kind } => self.encode_int_const(ty, kind),
            TrustVcExpr::Var { name, ty } => self.encode_var(name, ty),
            TrustVcExpr::Arith { op, left, right, ty } => self.encode_arith(*op, left, right, ty),
            TrustVcExpr::Compare { op, left, right } => self.encode_compare(*op, left, right),
            TrustVcExpr::Logic { op, left, right } => self.encode_logic(*op, left, right),
            TrustVcExpr::Not(inner) => self.encode_not(inner),
            TrustVcExpr::Neg(inner) => self.encode_neg(inner),
            TrustVcExpr::Implies { premise, conclusion } => {
                self.encode_implies(premise, conclusion)
            }
            TrustVcExpr::Ite { cond, then_branch, else_branch, ty } => {
                self.encode_ite(cond, then_branch, else_branch, ty)
            }
            TrustVcExpr::Let { name, ty, value, body } => self.encode_let(name, ty, value, body),
            TrustVcExpr::Cast { expr: inner, from_ty, to_ty } => {
                self.encode_cast(inner, from_ty, to_ty)
            }
            TrustVcExpr::CollectionOp { op, receiver, receiver_name, args, ty } => {
                self.encode_collection_op(*op, receiver, receiver_name.as_deref(), args, ty)
            }
            TrustVcExpr::Index { receiver, index, receiver_name, elem_ty } => {
                self.encode_index(receiver, index, receiver_name.as_deref(), elem_ty)
            }
            TrustVcExpr::WrappingArith { mode, op, left, right, ty } => {
                self.encode_wrapping_arith(*mode, *op, left, right, ty)
            }
            TrustVcExpr::Quantifier { kind, bound_vars, body, triggers, trigger_inference_mode } => {
                self.encode_quantifier(*kind, bound_vars, body, triggers.as_deref(), *trigger_inference_mode)
            }
            TrustVcExpr::FnCall { name, args, return_ty } => {
                self.encode_fn_call(name, args, return_ty)
            }
            TrustVcExpr::SpecClosure { .. } => Err(
                "SpecFn::new(...) closures cannot be encoded directly; they must be consumed by a supported higher-order combinator"
                    .to_string()
                    .into(),
            ),
            TrustVcExpr::Match { scrutinee, arms, ty } => {
                self.encode_match(scrutinee, arms, ty)
            }
            TrustVcExpr::SpecialArith { op, left, right, ty } => {
                self.encode_special_arith(*op, left, right, ty)
            }
            TrustVcExpr::Choose { var_name, var_ty, condition, key, also_assert } => {
                self.encode_choose(var_name, var_ty, condition, key, also_assert.as_deref())
            }
            TrustVcExpr::ReadPlace { place, ty } => self.encode_read_place(place, ty),
            TrustVcExpr::PlaceDisjoint { left, right } => self.encode_place_disjoint(left, right),
            TrustVcExpr::ProphecyNew { name, ty } => self.encode_prophecy_new(name, ty),
            TrustVcExpr::ProphecyResolve { name, value } => self.encode_prophecy_resolve(name, value),
        }
    }

    /// Encode a nested subexpression without re-entering the top-level
    /// validator/guard wrapper on every recursive step.
    pub(in crate::encoder) fn encode_subexpr(&mut self, expr: &TrustVcExpr) -> TrustVcResult<Term> {
        if self.expr_depth_guard_active {
            self.encode_trust_vc_expr_inner(expr)
        } else {
            self.encode_trust_vc_expr(expr)
        }
    }

    /// Re-type default `Int{32}` literals from operator context before encoding.
    ///
    /// IR lowering already coerces most unsuffixed literals to a surrounding
    /// integer type, but direct IR construction and future lowering regressions
    /// can still leave a default `Int{32}` in a wider/signedness-sensitive
    /// expression. When that happens, encoding the literal first as signed BV32
    /// and only then width-coercing it can sign-extend values like
    /// `3_000_000_000` into the wrong 64-bit term. Rewriting the literal to the
    /// surrounding operator type preserves the intended value before ay term
    /// construction. Part of #1560.
    fn encode_expr_with_integer_hint(
        &mut self,
        expr: &TrustVcExpr,
        hint_ty: Option<&TrustVcType>,
    ) -> TrustVcResult<Term> {
        if let Some(hint_ty) = hint_ty {
            if let Some(coerced) = Self::coerce_default_int_literal(expr, hint_ty) {
                return self.encode_subexpr(&coerced);
            }
        }
        self.encode_subexpr(expr)
    }

    fn coerce_bv_term_to_int_for_type(
        &mut self,
        term: Term,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        if !matches!(self.solver.term_sort(term), ay_dpll::api::Sort::BitVec(_)) {
            return Ok(term);
        }

        let converted = if ty.is_unsigned() {
            self.solver.try_bv2int(term).map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bv2int_signed(term)
                .map_err(|e| e.to_string())?
        };
        self.term_widths.remove(&converted);
        Ok(converted)
    }

    fn coerce_default_int_literal(
        expr: &TrustVcExpr,
        hint_ty: &TrustVcType,
    ) -> Option<TrustVcExpr> {
        if !matches!(
            hint_ty,
            TrustVcType::Int { .. }
                | TrustVcType::Uint { .. }
                | TrustVcType::MathInt
                | TrustVcType::Nat
                | TrustVcType::Real
        ) {
            return None;
        }

        match expr {
            TrustVcExpr::IntLit { value, ty } => {
                let hint_uses_unbounded_int = matches!(
                    hint_ty,
                    TrustVcType::MathInt | TrustVcType::Nat | TrustVcType::Real
                );
                let source_is_integer = matches!(
                    ty,
                    TrustVcType::Int { .. }
                        | TrustVcType::Uint { .. }
                        | TrustVcType::MathInt
                        | TrustVcType::Nat
                );
                if hint_uses_unbounded_int && source_is_integer {
                    return Some(TrustVcExpr::IntLit {
                        value: *value,
                        ty: hint_ty.clone(),
                    });
                }
                matches!(ty, TrustVcType::Int { width: 32 }).then(|| TrustVcExpr::IntLit {
                    value: *value,
                    ty: hint_ty.clone(),
                })
            }
            TrustVcExpr::Neg(inner) => {
                // Never coerce negative literals to unsigned types — Neg(IntLit)
                // represents a genuinely negative value (e.g., -1) which has no
                // meaningful unsigned interpretation. Coercing to Uint makes
                // encode_compare pick bvult instead of bvslt, producing wrong
                // results for mixed i32/u32 comparisons (#1769 regression from
                // equality substitution in #2187).
                if matches!(hint_ty, TrustVcType::Uint { .. } | TrustVcType::Nat) {
                    return None;
                }
                Self::coerce_default_int_literal(inner, hint_ty)
                    .map(|inner| TrustVcExpr::Neg(Box::new(inner)))
            }
            _ => None,
        }
    }

    // =================================================================
    // Literals
    // =================================================================

    /// Encode an integer literal with explicit type from the IR.
    ///
    /// For explicitly suffixed literals (i8, u32, etc.), uses the declared
    /// type width directly. For unsuffixed literals that defaulted to Int{32}
    /// during IR lowering, narrows to the variable-context width so that
    /// BV semantics match the surrounding type context (e.g., `128 > 127`
    /// in an i8 context uses BV(8), not BV(32)). This mirrors the string
    /// path's `infer_int_width()` behavior. Fixes #2094.
    fn encode_int_lit(&mut self, value: i128, ty: &TrustVcType) -> TrustVcResult<Term> {
        use super::types::{
            fits_in_bv, fits_in_signed_bv, min_bv_width_for_value, min_signed_bv_width_for_value,
        };
        use num_bigint::BigInt;

        // Real literal: integer value as rational constant (#2517).
        // Must be checked BEFORE int_mode() because use_int_arithmetic is true
        // when term_widths is empty (no BV variables), which includes Real-only
        // contexts. Without this priority, Real-typed IntLit nodes would be
        // encoded as Sort::Int instead of Sort::Real.
        if matches!(ty, TrustVcType::Real) {
            return if let Ok(v) = i64::try_from(value) {
                self.solver
                    .try_rational_const(v, 1)
                    .map_err(|e| e.to_string().into())
            } else {
                // Large values: use exact BigInt rational (fixes lossy f64 for > 2^53)
                let big = BigInt::from(value);
                self.solver
                    .try_rational_const_bigint(&big, &BigInt::from(1))
                    .map_err(|e| e.to_string().into())
            };
        }

        // MathInt/Nat or inside quantifier body → use Sort::Int
        if matches!(ty, TrustVcType::MathInt | TrustVcType::Nat) || self.int_mode() {
            return if let Ok(v) = i64::try_from(value) {
                Ok(self.solver.int_const(v))
            } else {
                Ok(self.solver.int_const_bigint(&BigInt::from(value)))
            };
        }

        // Bitvector literal — width comes from the type
        match ty {
            TrustVcType::Int { width } | TrustVcType::Uint { width } => {
                // For default-typed unsuffixed literals (Int{32}), narrow to
                // the variable context width if it's smaller, so an in-range
                // literal matches the surrounding narrow width without coercion
                // (e.g. `50` in an i8 context becomes BV(8) `50`). This is only
                // a *candidate* width: the signedness-correct fit check below
                // re-widens any value that would not be representable at this
                // width (so a positive out-of-signed-range literal like `200`
                // is NOT wrapped to a negative BV(8) value).
                let w = if *width == 32 && matches!(ty, TrustVcType::Int { .. }) {
                    let ctx_width = self.infer_int_width();
                    if ctx_width < 32 {
                        ctx_width
                    } else {
                        *width
                    }
                } else {
                    *width
                };
                let signed = matches!(ty, TrustVcType::Int { .. });

                // SOUNDNESS (casts-bitvec cluster): the encoded BV constant,
                // interpreted per `(actual_width, signed)`, MUST equal the
                // mathematical `value`; otherwise the literal silently becomes a
                // *different* constant and can manufacture a false `Verified`.
                //
                // For a SIGNED literal the value must fit the signed range of
                // `w`. A positive literal like `200` fits the *unsigned* byte
                // range but NOT the *signed* `i8` range, so `bv_const(200, 8)`
                // tagged signed is `0xC8 = -56` — silently rewriting e.g.
                // `x < 200` into `x < -56` (and, through `as i32` widening or a
                // unary `-`, aliasing the wrong value). Range-check against the
                // signedness-correct interpretation and widen to the smallest
                // width that PRESERVES the value when it does not fit, rather
                // than two's-complement wrapping it. Later width coercion
                // sign/zero-extends operands at comparison/op sites, so the
                // wider literal stays faithful.
                //
                // The BV path also applies to concrete-sort Skolemized forall
                // assertions, where bound vars stay BV-sorted so Rust wrapping
                // semantics remain precise without introducing Int-mode
                // `mod 2^w` arithmetic (#1553, #2669).
                let actual_width = if signed {
                    if fits_in_signed_bv(value, w) {
                        w
                    } else {
                        min_signed_bv_width_for_value(value)
                    }
                } else if fits_in_bv(value, w) {
                    w
                } else {
                    min_bv_width_for_value(value)
                };

                let term = if let Ok(v) = i64::try_from(value) {
                    self.solver
                        .try_bv_const(v, actual_width)
                        .map_err(|e| e.to_string())?
                } else {
                    self.solver
                        .try_bv_const_bigint(&BigInt::from(value), actual_width)
                        .map_err(|e| e.to_string())?
                };
                self.term_widths.insert(term, (actual_width, signed));
                Ok(term)
            }
            TrustVcType::Char => {
                let term = self
                    .solver
                    .try_bv_const(value as i64, 32)
                    .map_err(|e| e.to_string())?;
                self.term_widths.insert(term, (32, false));
                Ok(term)
            }
            TrustVcType::Bool => {
                // Boolean-typed integer literal: 0 = false, nonzero = true
                Ok(self.solver.bool_const(value != 0))
            }
            _ => Err(format!("Cannot encode integer literal {} with type {:?}", value, ty).into()),
        }
    }

    /// Encode an integer associated constant (T::MIN, T::MAX).
    fn encode_int_const(&mut self, ty: &TrustVcType, kind: &IntConstKind) -> TrustVcResult<Term> {
        use num_bigint::BigInt;
        let (width, signed) = match ty {
            TrustVcType::Int { width } => (*width, true),
            TrustVcType::Uint { width } => (*width, false),
            _ => return Err(format!("IntConst on non-integer type: {:?}", ty).into()),
        };

        // Use BigInt to avoid i128 overflow for width >= 128 (#2031)
        let value: BigInt = match (kind, signed) {
            (IntConstKind::Min, true) => wrapping::signed_bounds(width).0,
            (IntConstKind::Min, false) => BigInt::from(0),
            (IntConstKind::Max, true) => wrapping::signed_bounds(width).1,
            (IntConstKind::Max, false) => wrapping::unsigned_max(width),
        };

        if self.int_mode() {
            return if let Ok(v) = i64::try_from(&value) {
                Ok(self.solver.int_const(v))
            } else {
                Ok(self.solver.int_const_bigint(&value))
            };
        }

        let term = if let Ok(v) = i64::try_from(&value) {
            self.solver
                .try_bv_const(v, width)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_bv_const_bigint(&value, width)
                .map_err(|e| e.to_string())?
        };
        self.term_widths.insert(term, (width, signed));
        Ok(term)
    }

    // =================================================================
    // Variables
    // =================================================================

    /// Encode a variable reference. Checks local (quantifier-bound) vars first,
    /// then outer variables.
    ///
    /// Validates the IR-declared `ty` against parser context metadata and uses
    /// it to populate `term_widths` when the term is not already tracked.
    /// This ensures downstream width coercion and signedness checks use the
    /// correct type even for variables that were not in the initial
    /// `term_widths` population.
    ///
    /// Fixes #2029: previously discarded the `TrustVcType` parameter, allowing
    /// mismatches between IR-declared variable type and encoder context type.
    fn encode_var(&mut self, name: &str, ty: &TrustVcType) -> TrustVcResult<Term> {
        let (term, context_ty) = if let Some(term) = self.local_vars.get(name).copied() {
            (term, self.local_var_types.get(name).cloned())
        } else if let Some(term) = self.variables.get(name).copied() {
            (term, self.var_types.get(name).cloned())
        } else {
            return Err(format!(
                "undefined variable `{name}` — ensure it is declared as a function parameter, \
                 let-binding, or quantifier-bound variable visible in the current specification scope"
            ).into());
        };

        if let Some(expected_ty) = context_ty {
            let promoted_to_math_int = self.int_mode()
                && matches!(expected_ty, TrustVcType::MathInt | TrustVcType::Nat)
                && ty.is_integer();
            if expected_ty != *ty && !promoted_to_math_int {
                return Err(format!(
                    "Variable '{}' type mismatch: IR declared {:?}, context declared {:?}",
                    name, ty, expected_ty
                )
                .into());
            }
        }

        // Ensure term_widths is populated from the IR-declared type.
        // Skip in int_mode: quantifier bodies use Sort::Int, not BV.
        if !self.int_mode() {
            if let Some(w) = ty.bit_width() {
                if w > 0 {
                    let signed = !ty.is_unsigned();
                    if let Some((existing_w, existing_signed)) =
                        self.term_widths.get(&term).copied()
                    {
                        if existing_w != w || existing_signed != signed {
                            return Err(format!(
                                "Variable '{}' sort metadata mismatch: IR declared {:?}, tracked width={} signed={}",
                                name, ty, existing_w, existing_signed
                            )
                            .into());
                        }
                    } else {
                        self.term_widths.insert(term, (w, signed));
                    }
                }
            }
        }

        Ok(term)
    }
}

// =====================================================================
// Free helper functions
// =====================================================================

/// Check if a TrustVcExpr is a literal zero (for division/modulo by zero detection).
pub(super) fn is_trust_vc_literal_zero(expr: &TrustVcExpr) -> bool {
    matches!(expr, TrustVcExpr::IntLit { value: 0, .. })
}

/// Check if a TrustVcExpr is a literal one (for mul/div algebraic simplifications).
pub(super) fn is_trust_vc_literal_one(expr: &TrustVcExpr) -> bool {
    matches!(expr, TrustVcExpr::IntLit { value: 1, .. })
}

/// Extract the compile-time integer value of a literal expression, if any.
///
/// Recognizes a bare `IntLit` and the arithmetic negation of an `IntLit` (so a
/// literal divisor written `-3` is still detected). Returns `None` for every
/// non-literal (symbolic) expression. This is the soundness boundary for the
/// Euclidean div/mod-by-constant purification (#2778): only a genuine
/// compile-time constant divisor is recognized as decidable LIA+div; a symbolic
/// divisor returns `None` and stays on the native (fail-closed → Unknown) path.
pub(super) fn trust_vc_int_literal_value(expr: &TrustVcExpr) -> Option<i128> {
    match expr {
        TrustVcExpr::IntLit { value, .. } => Some(*value),
        TrustVcExpr::Neg(inner) => match inner.as_ref() {
            TrustVcExpr::IntLit { value, .. } => value.checked_neg(),
            _ => None,
        },
        _ => None,
    }
}
