//! Cast and Real-conversion encoding for TrustVcExpr IR.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::{Sort, Term};

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};

/// Discriminates the three fail-closed nat-cast lowerings that mint fresh
/// skolems, so the per-query memoization keyed by `(source_term, NatCastKind)`
/// never aliases casts with different semantics that happen to share a source
/// term (e.g. a Real source feeding both Real→Int and a hypothetical Real→Nat).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(clippy::enum_variant_names)] // `*ToNat` postfix names the cast target; intentional
pub(crate) enum NatCastKind {
    /// `r as nat` where `r: real` — floor skolem + nonnegativity guard.
    RealToNat,
    /// `i as nat` where `i` is a mathematical int — nonnegativity guard.
    IntToNat,
    /// `i as nat` where `i` is a signed finite-width (BV) int.
    SignedBvToNat,
}

impl<'a> AstExpressionParser<'a> {
    /// Encode a type cast (expr as to_ty).
    pub(super) fn encode_cast(
        &mut self,
        inner: &TrustVcExpr,
        declared_from_ty: &TrustVcType,
        to_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        // A cast reads its operand at the operand's OWN type — the sign that
        // decides how a narrower value is extended and how a bit-vector is
        // lifted to `int`. The node's declared `from_ty` is a producer's
        // claim; where it names another integer type it is not the operand's
        // (`Cast { x_u8, from_ty: i8 }` read 200 as -56), so the operand's own
        // integer type wins. An untyped literal takes the declared type when
        // it fits it (§5b rule 2), which changes nothing.
        let own_from = self.infer_operand_value_type(inner, Some(declared_from_ty));
        let integer = |ty: &TrustVcType| {
            matches!(
                ty,
                TrustVcType::Int { .. }
                    | TrustVcType::Uint { .. }
                    | TrustVcType::MathInt
                    | TrustVcType::Nat
            )
        };
        let from_ty = if integer(&own_from) && integer(declared_from_ty) {
            &own_from
        } else {
            declared_from_ty
        };
        if matches!((from_ty, to_ty), (TrustVcType::MathInt, TrustVcType::Nat)) {
            if let TrustVcExpr::Cast {
                expr: real_inner,
                from_ty: inner_from_ty,
                to_ty: inner_to_ty,
            } = inner
            {
                if matches!(
                    (inner_from_ty, inner_to_ty),
                    (TrustVcType::Real, TrustVcType::MathInt)
                ) {
                    let real_term = self.encode_subexpr(real_inner)?;
                    return self.cast_real_to_nat(real_term);
                }
            }
        }

        // An identity cast at a fixed-width type PINS its operand at that type
        // (a source `100i32`, `ir_lowering::atoms::typed_int_literal`; a
        // substituted `i32` value, `ir_lowering::pin_substituted_value`): an
        // `Int { width: 32 }` literal under it is exactly an `i32`, never the
        // placeholder that `encode_int_lit` narrows to the context width.
        // Narrowed, `100i32 + 100i32` beside an `i8` variable was computed in 8
        // bits (-56), and `assert!(100i32 + 100i32 < 0i32)` came back Verified.
        let pinned = from_ty == to_ty && crate::ir_lowering::is_fixed_width_int(from_ty);
        if pinned {
            self.default_int_literal_narrowing_suppressed += 1;
        }
        let inner_term = self.encode_subexpr(inner);
        if pinned {
            self.default_int_literal_narrowing_suppressed -= 1;
        }
        let inner_term = inner_term?;

        let result = self.encode_cast_term(inner_term, from_ty, to_ty)?;
        if self.scalar_casts.is_some() {
            let observation = (|| {
                let operand = crate::scalar_cast_capture::actual_term(self.solver, inner_term)?;
                let result = crate::scalar_cast_capture::actual_term(self.solver, result)?;
                Ok::<_, String>(crate::scalar_cast_capture::ScalarCastEmission {
                    declared_source: declared_from_ty.clone(),
                    effective_source: from_ty.clone(),
                    destination: to_ty.clone(),
                    operand_variable: match inner {
                        TrustVcExpr::Var { name, .. } => Some(name.clone()),
                        _ => None,
                    },
                    operand_term: operand.text,
                    operand_sort: operand.sort,
                    operand_bindings: operand.bindings,
                    result_term: result.text,
                    result_sort: result.sort,
                    result_bindings: result.bindings,
                })
            })();
            match observation {
                Ok(row) => {
                    let rows = self.scalar_casts.as_mut().expect("capture enabled");
                    if rows.len() < 512 {
                        rows.push(row);
                    } else {
                        self.scalar_cast_refusal = Some("too many cast emissions".into());
                    }
                }
                Err(reason) => self.scalar_cast_refusal = Some(reason),
            }
        }
        Ok(result)
    }

    fn encode_cast_term(
        &mut self,
        inner_term: Term,
        from_ty: &TrustVcType,
        to_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        if from_ty == to_ty {
            return Ok(inner_term);
        }

        // Verus quantifier witnesses often cast `nat` to mathematical `int`
        // before calling int-typed spec predicates. Both use the backend Int
        // sort; the Nat range guard carries the non-negativity constraint.
        if matches!((from_ty, to_ty), (TrustVcType::Nat, TrustVcType::MathInt)) {
            return Ok(inner_term);
        }

        // Finite-width integer -> mathematical int: preserve the source
        // value, using signed or unsigned BV-to-Int conversion as appropriate.
        // This is the bridge needed for Verus-style `collection.len() as int`.
        if matches!(to_ty, TrustVcType::MathInt)
            && matches!(from_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
        {
            return self.cast_finite_int_to_math_int(inner_term, from_ty);
        }

        // Finite-width integer -> nat: first interpret the source value as a
        // mathematical int, then apply the Nat subset cast. Unsigned BV sources
        // are nonnegative by construction; signed sources remain fail-closed
        // unless the current proof context establishes nonnegativity.
        if matches!(to_ty, TrustVcType::Nat)
            && matches!(from_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
        {
            return self.cast_finite_int_to_nat(inner_term, from_ty);
        }

        // Mathematical int/nat -> finite-width integer: Rust-style wrapping
        // into the target width, preserving target signedness metadata.
        if matches!(from_ty, TrustVcType::MathInt | TrustVcType::Nat)
            && matches!(to_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
        {
            return self.cast_math_int_to_finite_int(inner_term, to_ty);
        }

        // Bool -> integer: false=0, true=1
        if matches!(from_ty, TrustVcType::Bool) {
            if let Some(result) = self.cast_bool_to_int(inner_term, to_ty)? {
                return Ok(result);
            }
        }

        // Integer -> Bool: 0=false, nonzero=true
        if matches!(to_ty, TrustVcType::Bool) {
            if let Some(result) = self.cast_int_to_bool(inner_term, from_ty)? {
                return Ok(result);
            }
        }

        // Finite integer -> Real: first interpret the source BV as the
        // corresponding mathematical Int, then use SMT `to_real`.
        if matches!(to_ty, TrustVcType::Real)
            && matches!(from_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
        {
            let int_term = self.cast_finite_int_to_math_int(inner_term, from_ty)?;
            return self.cast_int_to_real(int_term);
        }

        // MathInt/Nat -> Real: mathematical coercion (#2517)
        if matches!(to_ty, TrustVcType::Real)
            && matches!(from_ty, TrustVcType::MathInt | TrustVcType::Nat)
        {
            return self.cast_int_to_real(inner_term);
        }

        // MathInt -> Nat: subset coercion; invalid negative casts are
        // unconstrained so proofs must establish nonnegativity before relying
        // on the cast result.
        if matches!((from_ty, to_ty), (TrustVcType::MathInt, TrustVcType::Nat)) {
            return self.cast_int_to_nat(inner_term);
        }

        // Real -> Nat: floor conversion, then subset coercion.
        if matches!((from_ty, to_ty), (TrustVcType::Real, TrustVcType::Nat)) {
            return self.cast_real_to_nat(inner_term);
        }

        // Real -> Int/MathInt: floor conversion (#2517)
        if matches!(from_ty, TrustVcType::Real)
            && matches!(
                to_ty,
                TrustVcType::Int { .. }
                    | TrustVcType::Uint { .. }
                    | TrustVcType::MathInt
                    | TrustVcType::Nat
            )
        {
            return self.cast_real_to_int(inner_term, to_ty);
        }

        // Float -> Float: precision change (e.g., f32 as f64). Part of #2680.
        if let (TrustVcType::Float { width: from_w }, TrustVcType::Float { width: to_w }) =
            (from_ty, to_ty)
        {
            if from_w != to_w {
                return self.cast_float_to_float(inner_term, *to_w);
            }
            return Ok(inner_term);
        }

        // Float -> Int/Uint: rounding conversion. Part of #2680.
        if matches!(from_ty, TrustVcType::Float { .. }) {
            if let TrustVcType::Int { width } | TrustVcType::Uint { width } = to_ty {
                let unsigned = to_ty.is_unsigned();
                return self.cast_float_to_int(inner_term, *width, unsigned);
            }
        }

        // Int/Uint -> Float: conversion with rounding. Part of #2680.
        if matches!(to_ty, TrustVcType::Float { .. })
            && matches!(from_ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
        {
            let unsigned = from_ty.is_unsigned();
            let to_w = match to_ty {
                TrustVcType::Float { width } => *width,
                _ => unreachable!(),
            };
            return self.cast_int_to_float(inner_term, to_w, unsigned);
        }

        // Float -> Real: exact mathematical real. Part of #2680.
        if matches!(from_ty, TrustVcType::Float { .. }) && matches!(to_ty, TrustVcType::Real) {
            return self
                .solver
                .try_fp_to_real(inner_term)
                .map_err(|e| e.to_string().into());
        }

        // Integer -> Integer: BV extension or truncation
        self.cast_int_to_int(inner_term, from_ty, to_ty)
    }

    fn cast_finite_int_to_math_int(
        &mut self,
        inner_term: Term,
        from_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        if !matches!(self.solver.term_sort(inner_term), Sort::BitVec(_)) {
            return Ok(inner_term);
        }

        let result = if matches!(from_ty, TrustVcType::Uint { .. }) {
            self.solver
                .try_bv2int(inner_term)
                .map_err(|e| e.to_string())?
        } else {
            let Sort::BitVec(bv_sort) = self.solver.term_sort(inner_term) else {
                return Ok(inner_term);
            };
            self.cast_signed_bv_to_math_int(inner_term, bv_sort.width)?
        };
        self.term_widths.remove(&result);
        Ok(result)
    }

    fn cast_signed_bv_to_math_int(&mut self, inner_term: Term, width: u32) -> TrustVcResult<Term> {
        let sign_bit = self
            .solver
            .try_bvextract(inner_term, width - 1, width - 1)
            .map_err(|e| e.to_string())?;
        let one = self.solver.try_bv_const(1, 1).map_err(|e| e.to_string())?;
        let is_negative = self
            .solver
            .try_eq(sign_bit, one)
            .map_err(|e| e.to_string())?;
        let unsigned = self
            .solver
            .try_bv2int(inner_term)
            .map_err(|e| e.to_string())?;
        let two_pow_width = self
            .solver
            .int_const_bigint(&(num_bigint::BigInt::from(1u8) << width));
        let signed = self
            .solver
            .try_sub(unsigned, two_pow_width)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_ite(is_negative, signed, unsigned)
            .map_err(|e| e.to_string().into())
    }

    fn cast_finite_int_to_nat(
        &mut self,
        inner_term: Term,
        from_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        if let Sort::BitVec(bv_sort) = self.solver.term_sort(inner_term) {
            if matches!(from_ty, TrustVcType::Int { .. }) {
                if let Some(cached) = self
                    .nat_cast_aliases
                    .get(&(inner_term, NatCastKind::SignedBvToNat))
                {
                    return Ok(*cached);
                }
                let zero = self
                    .solver
                    .try_bv_const(0, bv_sort.width)
                    .map_err(|e| e.to_string())?;
                let nonnegative = self
                    .solver
                    .try_bvsge(inner_term, zero)
                    .map_err(|e| e.to_string())?;
                let int_term = self
                    .solver
                    .try_bv2int(inner_term)
                    .map_err(|e| e.to_string())?;
                self.term_widths.remove(&int_term);
                let invalid = self
                    .solver
                    .fresh_var("__trust_vc_invalid_nat_cast", Sort::Int);
                let result = self
                    .solver
                    .try_ite(nonnegative, int_term, invalid)
                    .map_err(|e| e.to_string())?;
                self.nat_cast_aliases
                    .insert((inner_term, NatCastKind::SignedBvToNat), result);
                return Ok(result);
            }
        }

        let int_term = self.cast_finite_int_to_math_int(inner_term, from_ty)?;
        self.cast_int_to_nat(int_term)
    }

    fn cast_math_int_to_finite_int(
        &mut self,
        inner_term: Term,
        to_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let (TrustVcType::Int { width } | TrustVcType::Uint { width }) = to_ty else {
            return Err(format!(
                "unsupported cast from mathematical integer to `{}`",
                to_ty.to_type_string()
            )
            .into());
        };
        let signed = matches!(to_ty, TrustVcType::Int { .. });

        if self.int_mode() {
            return self.wrap_int_to_explicit_range(inner_term, *width, !signed);
        }

        let result = self
            .solver
            .try_int2bv(inner_term, *width)
            .map_err(|e| e.to_string())?;
        self.term_widths.insert(result, (*width, signed));
        Ok(result)
    }

    /// Cast from Bool to integer type. Returns None if to_ty isn't integer.
    fn cast_bool_to_int(
        &mut self,
        inner_term: Term,
        to_ty: &TrustVcType,
    ) -> TrustVcResult<Option<Term>> {
        match to_ty {
            TrustVcType::MathInt | TrustVcType::Nat => {
                let zero = self.solver.int_const(0);
                let one = self.solver.int_const(1);
                let result = self
                    .solver
                    .try_ite(inner_term, one, zero)
                    .map_err(|e| e.to_string())?;
                Ok(Some(result))
            }
            TrustVcType::Int { width } | TrustVcType::Uint { width } => {
                if self.int_mode() {
                    let zero = self.solver.int_const(0);
                    let one = self.solver.int_const(1);
                    let result = self
                        .solver
                        .try_ite(inner_term, one, zero)
                        .map_err(|e| e.to_string())?;
                    return Ok(Some(result));
                }
                let w = *width;
                let signed = matches!(to_ty, TrustVcType::Int { .. });
                let zero = self.solver.try_bv_const(0, w).map_err(|e| e.to_string())?;
                let one = self.solver.try_bv_const(1, w).map_err(|e| e.to_string())?;
                let result = self
                    .solver
                    .try_ite(inner_term, one, zero)
                    .map_err(|e| e.to_string())?;
                self.term_widths.insert(result, (w, signed));
                Ok(Some(result))
            }
            _ => Ok(None),
        }
    }

    /// Cast from integer type to Bool. Returns None if from_ty isn't integer.
    fn cast_int_to_bool(
        &mut self,
        inner_term: Term,
        from_ty: &TrustVcType,
    ) -> TrustVcResult<Option<Term>> {
        match from_ty {
            TrustVcType::Int { width } | TrustVcType::Uint { width } => {
                if self.int_mode() {
                    let zero = self.solver.int_const(0);
                    let eq = self
                        .solver
                        .try_eq(inner_term, zero)
                        .map_err(|e| e.to_string())?;
                    let result = self.solver.try_not(eq).map_err(|e| e.to_string())?;
                    return Ok(Some(result));
                }
                let zero = self
                    .solver
                    .try_bv_const(0, *width)
                    .map_err(|e| e.to_string())?;
                let eq = self
                    .solver
                    .try_eq(inner_term, zero)
                    .map_err(|e| e.to_string())?;
                Ok(Some(self.solver.try_not(eq).map_err(|e| e.to_string())?))
            }
            _ => Ok(None),
        }
    }

    /// Cast between integer types using BV extension or truncation.
    fn cast_int_to_int(
        &mut self,
        inner_term: Term,
        from_ty: &TrustVcType,
        to_ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let from_width = from_ty.bit_width();
        let to_width = to_ty.bit_width();

        match (from_width, to_width) {
            (Some(fw), Some(tw)) => {
                let to_signed = matches!(to_ty, TrustVcType::Int { .. });

                if self.int_mode() {
                    // In Int mode, casts are wrapping to the target range
                    let result = self.wrap_int_to_explicit_range(inner_term, tw, !to_signed)?;
                    return Ok(result);
                }

                if fw == tw {
                    // Same-width signedness reinterpret (e.g. `i32 as u32`,
                    // `u8 as i8`). Rust `as` between same-width integer types is
                    // a pure bit reinterpret: the value's bit pattern is
                    // preserved and only the signed/unsigned *interpretation*
                    // (which drives signed-vs-unsigned comparison and width
                    // coercion) changes.
                    //
                    // Reusing the SAME ay term and overwriting its tracked
                    // signedness destructively clobbers the source variable's
                    // metadata. A later `encode_var` of that variable under its
                    // declared signedness then trips the "sort metadata
                    // mismatch" guard, fail-closing `by(bit_vector)` cast cases
                    // that Verus discharges (cluster #2778: `test_eq_ineq`,
                    // `test_casting`, `test_clipping_and_casting`, …).
                    //
                    // Mint a fresh, bit-identical BV constant for the cast result
                    // carrying the new signedness, asserting it equal to the
                    // source. This is a sound definitional naming: the fresh var
                    // is equisatisfiable with `inner_term` and appears only as
                    // the cast result, so the source variable keeps its own
                    // signedness for its other occurrences.
                    self.reinterpret_bv_signedness(inner_term, tw, to_signed)
                } else if fw < tw {
                    // Widening: sign-extend or zero-extend
                    let from_signed = matches!(from_ty, TrustVcType::Int { .. });
                    let result = if from_signed {
                        self.solver
                            .try_bvsignext(inner_term, tw - fw)
                            .map_err(|e| e.to_string())?
                    } else {
                        self.solver
                            .try_bvzeroext(inner_term, tw - fw)
                            .map_err(|e| e.to_string())?
                    };
                    self.term_widths.insert(result, (tw, to_signed));
                    Ok(result)
                } else {
                    // Narrowing: extract low bits
                    let result = self
                        .solver
                        .try_bvextract(inner_term, tw - 1, 0)
                        .map_err(|e| e.to_string())?;
                    self.term_widths.insert(result, (tw, to_signed));
                    Ok(result)
                }
            }
            _ => Err(format!(
                "unsupported cast from `{}` to `{}` — trust_vc supports casts between \
                 integer types (u8..u128, i8..i128), int/nat, float types (f32, f64), \
                 and float-to-integer conversions",
                from_ty.to_type_string(),
                to_ty.to_type_string()
            )
            .into()),
        }
    }

    /// Lower a same-width signedness reinterpret (`i32 as u32`, `u8 as i8`, …)
    /// to a fresh, bit-identical BV term carrying the new signedness, without
    /// clobbering the source term's tracked metadata.
    ///
    /// The fresh constant `r` is asserted `r == inner_term` (bit equality), which
    /// is a sound definitional naming: `r` is equisatisfiable with `inner_term`
    /// and is used only as the cast result. Tracking `r` (rather than
    /// `inner_term`) with `to_signed` lets a shared source variable retain its
    /// own signedness for its other occurrences.
    ///
    /// The fresh-var define requires `inner_term` to be a FREE term. If it is a
    /// variable bound by a live ay quantifier, a global assert would capture it,
    /// so for that case (and any non-`BitVec(tw)` term that should not reach
    /// here) we preserve the prior in-place metadata update. That keeps the
    /// previous fail-closed behavior for the rare bound-variable reinterpret
    /// instead of risking an unsound capture.
    fn reinterpret_bv_signedness(
        &mut self,
        inner_term: Term,
        tw: u32,
        to_signed: bool,
    ) -> TrustVcResult<Term> {
        let is_free_bv = matches!(
            self.solver.term_sort(inner_term),
            Sort::BitVec(s) if s.width == tw
        ) && !self.is_quantifier_bound_term(inner_term);

        if !is_free_bv {
            self.term_widths.insert(inner_term, (tw, to_signed));
            return Ok(inner_term);
        }

        let fresh = self
            .solver
            .fresh_var("__trust_vc_signedness_cast", Sort::bitvec(tw));
        let eq = self
            .solver
            .try_eq(fresh, inner_term)
            .map_err(|e| e.to_string())?;
        self.solver.try_assert_term(eq).map_err(|e| e.to_string())?;
        self.term_widths.insert(fresh, (tw, to_signed));
        Ok(fresh)
    }

    /// Cast Float to Float (precision change). Uses `fp_to_fp` with RNE.
    /// Part of #2680 Slice 1.
    fn cast_float_to_float(&mut self, inner_term: Term, to_width: u32) -> TrustVcResult<Term> {
        let (eb, sb) = float_eb_sb(to_width)?;
        let rne = self
            .solver
            .try_fp_rounding_mode("RNE")
            .map_err(|e| e.to_string())?;
        self.solver
            .try_fp_to_fp(rne, inner_term, eb, sb)
            .map_err(|e| e.to_string().into())
    }

    /// Cast Float to signed/unsigned integer. Uses `fp_to_sbv`/`fp_to_ubv`
    /// with RTZ (round-to-zero, matching Rust `as` semantics).
    /// Part of #2680 Slice 1.
    fn cast_float_to_int(
        &mut self,
        inner_term: Term,
        width: u32,
        unsigned: bool,
    ) -> TrustVcResult<Term> {
        let rtz = self
            .solver
            .try_fp_rounding_mode("RTZ")
            .map_err(|e| e.to_string())?;
        let result = if unsigned {
            self.solver
                .try_fp_to_ubv(rtz, inner_term, width)
                .map_err(|e| e.to_string())?
        } else {
            self.solver
                .try_fp_to_sbv(rtz, inner_term, width)
                .map_err(|e| e.to_string())?
        };
        self.term_widths.insert(result, (width, !unsigned));
        Ok(result)
    }

    /// Cast signed/unsigned integer to Float. Uses `bv_to_fp`/`bv_to_fp_unsigned`
    /// with RNE. In int_mode, returns an error since ay-dpll lacks int_to_fp.
    /// Part of #2680 Slice 1.
    fn cast_int_to_float(
        &mut self,
        inner_term: Term,
        to_width: u32,
        unsigned: bool,
    ) -> TrustVcResult<Term> {
        let (eb, sb) = float_eb_sb(to_width)?;
        if self.int_mode() {
            return Err(format!(
                "Cast from integer to f{to_width} is not supported in int-mode \
                 (ay-dpll lacks int_to_fp)"
            )
            .into());
        }
        let rne = self
            .solver
            .try_fp_rounding_mode("RNE")
            .map_err(|e| e.to_string())?;
        if unsigned {
            self.solver
                .try_bv_to_fp_unsigned(rne, inner_term, eb, sb)
                .map_err(|e| e.to_string().into())
        } else {
            self.solver
                .try_bv_to_fp(rne, inner_term, eb, sb)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Cast mathematical integer to Real via SMT `to_real`.
    fn cast_int_to_real(&mut self, inner_term: Term) -> TrustVcResult<Term> {
        self.solver
            .try_int_to_real(inner_term)
            .map_err(|e| e.to_string().into())
    }

    /// Cast mathematical Int to Nat. The backend sort stays Int. Negative
    /// inputs produce an unconstrained value, matching a fail-closed partial
    /// subset cast without adding a side-channel predicate.
    fn cast_int_to_nat(&mut self, inner_term: Term) -> TrustVcResult<Term> {
        self.guard_nat_cast_nonnegative(inner_term)
    }

    /// Cast Real to Nat via a fresh floor Int plus Nat subset check.
    ///
    /// The lowered result is memoized on the source real term so that repeated
    /// encodings of the *same* `r as nat` (Real→Nat) within a single
    /// verification query denote the **same** ay term. Without this, each
    /// re-encoding minted a fresh `__trust_vc_real_floor` skolem and a fresh
    /// `__trust_vc_invalid_nat_cast` skolem, so a ground `nat_to_real(r as nat)`
    /// produced in an assertion and the matching ground-axiom instance
    /// `nat_to_real(r as nat) == (r as nat) as real` were applied to *distinct*
    /// argument terms and never connected. Sharing is sound: `floor(r)` is a
    /// function of `r` (pinned by `assert_real_floor_bounds`), and the invalid
    /// placeholder for one fixed expression is one fixed unknown. Part of the
    /// `nat_to_real` cast-argument def-axiom fix.
    fn cast_real_to_nat(&mut self, inner_term: Term) -> TrustVcResult<Term> {
        if let Some(cached) = self
            .nat_cast_aliases
            .get(&(inner_term, NatCastKind::RealToNat))
        {
            return Ok(*cached);
        }
        let int_term = self.solver.fresh_var("__trust_vc_real_floor", Sort::Int);
        self.assert_real_floor_bounds(inner_term, int_term)?;
        let result = self.guard_real_to_nat_cast_nonnegative(inner_term, int_term)?;
        self.nat_cast_aliases
            .insert((inner_term, NatCastKind::RealToNat), result);
        Ok(result)
    }

    fn guard_nat_cast_nonnegative(&mut self, int_term: Term) -> TrustVcResult<Term> {
        if let Some(cached) = self
            .nat_cast_aliases
            .get(&(int_term, NatCastKind::IntToNat))
        {
            return Ok(*cached);
        }
        let zero = self.solver.int_const(0);
        let nonnegative = self
            .solver
            .try_ge(int_term, zero)
            .map_err(|e| e.to_string())?;
        let invalid = self
            .solver
            .fresh_var("__trust_vc_invalid_nat_cast", Sort::Int);
        let result = self
            .solver
            .try_ite(nonnegative, int_term, invalid)
            .map_err(|e| e.to_string())?;
        self.nat_cast_aliases
            .insert((int_term, NatCastKind::IntToNat), result);
        Ok(result)
    }

    /// Encodes the Real→Nat subset guard as a fresh result constant pinned by
    /// two implications rather than a single `ite`:
    ///
    /// * `real >= 0  ==>  result == floor`
    /// * `real <  0  ==>  result == invalid`  (fresh, unconstrained skolem)
    ///
    /// This is logically *identical* to `ite(real >= 0, floor, invalid)` — the
    /// same two-case definition, neither strengthened nor weakened — so it
    /// preserves the established fail-closed semantics (a negative source leaves
    /// the result unconstrained). The implication form is chosen because, under a
    /// `real >= 0` proof assumption, the solver derives `result == floor` by a
    /// single modus-ponens equality. The previous `ite` left the equality
    /// trapped behind a case split buried inside `nat_to_real(int_to_real(.. +
    /// 1))`, which the solver did not eliminate in that nonlinear/real position —
    /// so `archimedean_nat`'s body assert `x < nat_to_real(x.floor() as nat + 1)`
    /// failed even though every supporting fact was present.
    fn guard_real_to_nat_cast_nonnegative(
        &mut self,
        real_term: Term,
        int_term: Term,
    ) -> TrustVcResult<Term> {
        let zero_int = self.solver.int_const(0);
        let zero_real = self
            .solver
            .try_int_to_real(zero_int)
            .map_err(|e| e.to_string())?;
        let nonnegative = self
            .solver
            .try_ge(real_term, zero_real)
            .map_err(|e| e.to_string())?;
        let negative = self
            .solver
            .try_not(nonnegative)
            .map_err(|e| e.to_string())?;
        let invalid = self
            .solver
            .fresh_var("__trust_vc_invalid_nat_cast", Sort::Int);
        let result = self.solver.fresh_var("__trust_vc_real_to_nat", Sort::Int);

        let valid_eq = self
            .solver
            .try_eq(result, int_term)
            .map_err(|e| e.to_string())?;
        let valid_impl = self
            .solver
            .try_implies(nonnegative, valid_eq)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(valid_impl)
            .map_err(|e| e.to_string())?;

        let invalid_eq = self
            .solver
            .try_eq(result, invalid)
            .map_err(|e| e.to_string())?;
        let invalid_impl = self
            .solver
            .try_implies(negative, invalid_eq)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(invalid_impl)
            .map_err(|e| e.to_string())?;

        // Floor bracket restated on `result` (the value the goal observes),
        // in Real terms, under the nonnegativity guard:
        //
        //   * `real >= 0  ==>  (result as real) <= real`           (lower)
        //   * `real >= 0  ==>  real < ((result + 1) as real)`      (upper)
        //
        // These are *logical consequences* of facts already asserted —
        // `assert_real_floor_bounds` pins `(int_term as real) <= real < (int_term
        // + 1 as real)`, and `nonnegative ==> result == int_term` is asserted
        // just above — so they add NO strength (they cannot make a false goal
        // verify; a negative source leaves them vacuous and `result`
        // unconstrained). Restating the bracket on `result` directly discharges
        // the floor-bracket / archimedean-witness goals through linear real
        // arithmetic, instead of requiring the solver to complete an
        // `int_to_real` congruence chain from the goal's `result` term back to
        // the bounds pinned on the floor skolem `int_term` — a step it currently
        // returns Unknown(incomplete) on.
        let result_real = self
            .solver
            .try_int_to_real(result)
            .map_err(|e| e.to_string())?;
        let lower_bracket = self
            .solver
            .try_le(result_real, real_term)
            .map_err(|e| e.to_string())?;
        let lower_impl = self
            .solver
            .try_implies(nonnegative, lower_bracket)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(lower_impl)
            .map_err(|e| e.to_string())?;

        let one = self.solver.int_const(1);
        let result_plus_one = self
            .solver
            .try_add(result, one)
            .map_err(|e| e.to_string())?;
        let result_plus_one_real = self
            .solver
            .try_int_to_real(result_plus_one)
            .map_err(|e| e.to_string())?;
        let upper_bracket = self
            .solver
            .try_lt(real_term, result_plus_one_real)
            .map_err(|e| e.to_string())?;
        let upper_impl = self
            .solver
            .try_implies(nonnegative, upper_bracket)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(upper_impl)
            .map_err(|e| e.to_string())?;

        Ok(result)
    }

    /// Cast Real to integer via SMT `to_int` (floor semantics).
    /// Target range wrapping applied for bounded integer types.
    fn cast_real_to_int(&mut self, inner_term: Term, to_ty: &TrustVcType) -> TrustVcResult<Term> {
        let int_term = self
            .solver
            .try_real_to_int(inner_term)
            .map_err(|e| e.to_string())?;
        match to_ty {
            TrustVcType::MathInt | TrustVcType::Nat => Ok(int_term),
            TrustVcType::Int { width } | TrustVcType::Uint { width } => {
                // Both int_mode and BV mode use explicit range wrapping.
                // Current ay-dpll exposes int2bv, but TrustVc keeps the
                // existing explicit-range path here because try_real_to_int
                // produces Sort::Int and range wrapping is the established
                // semantics in this encoder.
                self.wrap_int_to_explicit_range(int_term, *width, to_ty.is_unsigned())
            }
            _ => Err(format!("Cannot cast Real to {}", to_ty.to_type_string()).into()),
        }
    }

    fn assert_real_floor_bounds(&mut self, real_term: Term, int_term: Term) -> TrustVcResult<()> {
        let floor_real = self
            .solver
            .try_int_to_real(int_term)
            .map_err(|e| e.to_string())?;
        let lower = self
            .solver
            .try_le(floor_real, real_term)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(lower)
            .map_err(|e| e.to_string())?;

        let one = self.solver.int_const(1);
        let floor_plus_one = self
            .solver
            .try_add(int_term, one)
            .map_err(|e| e.to_string())?;
        let floor_plus_one_real = self
            .solver
            .try_int_to_real(floor_plus_one)
            .map_err(|e| e.to_string())?;
        let upper = self
            .solver
            .try_lt(real_term, floor_plus_one_real)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_assert_term(upper)
            .map_err(|e| e.to_string().into())
    }
}

/// Returns (exponent_bits, significand_bits) for a given float width.
/// Matches the IEEE 754 standard parameters used in `types::float_sort`.
/// Part of #2680 Slice 1.
fn float_eb_sb(width: u32) -> TrustVcResult<(u32, u32)> {
    match width {
        16 => Ok((5, 11)),
        32 => Ok((8, 24)),
        64 => Ok((11, 53)),
        128 => Ok((15, 113)),
        other => Err(format!(
            "unsupported float width f{other} — trust_vc supports f16, f32, f64, and f128 \
             (IEEE 754 binary16/32/64/128)"
        )
        .into()),
    }
}
