// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Wrapping, checked, and saturating arithmetic encoding for TrustVcExpr IR.
//!
//! `Checked` mode encodes overflow-checked arithmetic (not Rust's `Option<T>`
//! semantics): BV result + overflow predicates in side channel (#1785).

use ay_dpll::api::Term;
use num_bigint::BigInt;

use crate::ir::{ArithOp, TrustVcExpr, TrustVcType, WrappingMode};

use crate::encoder::arith_semantics::resolve_expr_wrap;
use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    /// Encode wrapping/checked/saturating arithmetic methods.
    ///
    /// In int_mode (quantifier bodies), ALL modes use Int arithmetic:
    /// - Wrapping: delegates to `encode_int_arith` (modular wrap).
    /// - Checked: Int arithmetic + overflow checks comparing result to type bounds.
    /// - Saturating: Int arithmetic + clamping result to [min, max].
    ///
    /// Fixes #2030: Checked/Saturating no longer fall through to BV ops on
    /// Int-sorted terms. The explicit Int-range checks mirror the BV overflow
    /// predicates used in the non-int_mode path.
    pub(super) fn encode_wrapping_arith(
        &mut self,
        mode: WrappingMode,
        op: ArithOp,
        left: &TrustVcExpr,
        right: &TrustVcExpr,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        // In int_mode, ALL wrapping modes use Int arithmetic.
        // Wrapping: modular wrap. Checked: overflow check. Saturating: clamp.
        // Fixes #2030: previously only Wrapping used Int path; Checked/Saturating
        // fell through to BV ops on Int-sorted terms, causing sort mismatches.
        if self.int_mode() {
            return match mode {
                WrappingMode::Wrapping => {
                    // An explicit Wrapping node (Verus builtin `add`/`sub`/`mul`,
                    // Rust `wrapping_*`) is *defined* as finite-width truncation.
                    // In `use_int_arithmetic` mode (by(nonlinear_arith) / measure
                    // queries) `encode_int_arith` suppresses the scope-derived
                    // wrap because ordinary spec arithmetic there is unbounded
                    // math — but that suppression must not erase the truncating
                    // semantics of an explicit wrapping op, or the builtin `mul`
                    // becomes unbounded and upstream `nonlinear.rs::test4_fails`
                    // wrongly verifies (#2778). Apply the type-derived modular
                    // wrap here; for MathInt/Nat `ty` there is no width and the
                    // exact math result is returned unchanged.
                    if self.use_int_arithmetic {
                        if let Some(width) = ty.bit_width().filter(|w| {
                            *w > 0 && matches!(op, ArithOp::Add | ArithOp::Sub | ArithOp::Mul)
                        }) {
                            // Modular-congruence pushdown (#2778, upstream
                            // nonlinear.rs test6): operands that are themselves
                            // same-width truncating +/-/* nodes contribute only
                            // their residue mod 2^width to this node's wrap, so
                            // their RAW (unwrapped) ring value may be used
                            // instead — Z -> Z/2^w is a ring homomorphism, and
                            // both the unsigned wrap `s mod 2^w` and the signed
                            // re-centering `((s + 2^(w-1)) mod 2^w) - 2^(w-1)`
                            // are congruent to `s` mod 2^w. This turns nested
                            // wrap chains like `add(mul(x, x), x)` vs
                            // `mul(x, add(x, 1))` into a SINGLE outer wrap over
                            // plain polynomials, which the solver decides by
                            // ring normalization; the nested-`mod` form is
                            // undecided (fail-closed Unknown). Exact semantics
                            // preservation, not a relaxation: each stripped
                            // operand is replaced by a mod-2^w-congruent value
                            // under a mod-2^w context.
                            let left_term = self.encode_int_mod_congruent_operand(left, width)?;
                            let right_term = self.encode_int_mod_congruent_operand(right, width)?;
                            let result = self.encode_int_arith(
                                op, left_term, right_term, false, false, ty, None,
                            )?;
                            return self.wrap_int_with_ctx(result, Some((width, ty.is_unsigned())));
                        }
                    }
                    let left_term = self.encode_subexpr(left)?;
                    let right_term = self.encode_subexpr(right)?;
                    // Wrapping arithmetic is always finite-width (never the
                    // MathInt/Nat Euclidean path), so the literal-divisor
                    // purification never fires here: pass `None`.
                    let result =
                        self.encode_int_arith(op, left_term, right_term, false, false, ty, None)?;
                    // Apply the type-derived truncation HERE, unconditionally.
                    // `encode_int_arith` declines the wrap in two modes now — the
                    // long-standing `use_int_arithmetic` one, and (new) inside a
                    // quantifier body, where ordinary spec `+`/`-`/`*` is
                    // mathematical `int`. An explicit `WrappingArith` node is
                    // *defined* as finite-width truncation, so it must not inherit
                    // either relaxation: without this, `forall|x: u8|
                    // x.wrapping_add(1) >= 1` would wrongly verify. For MathInt/Nat
                    // `ty` there is no width and the exact math result is returned.
                    let wrap_ctx = ty.bit_width().map(|w| (w, ty.is_unsigned()));
                    self.wrap_int_with_ctx(result, wrap_ctx)
                }
                WrappingMode::Checked => {
                    let left_term = self.encode_subexpr(left)?;
                    let right_term = self.encode_subexpr(right)?;
                    self.encode_int_checked(op, left_term, right_term, ty)
                }
                WrappingMode::Saturating => {
                    let left_term = self.encode_subexpr(left)?;
                    let right_term = self.encode_subexpr(right)?;
                    self.encode_int_saturating(op, left_term, right_term, ty)
                }
            };
        }
        let left_term = self.encode_subexpr(left)?;
        let right_term = self.encode_subexpr(right)?;

        let (left_term, right_term) = self.coerce_bv_widths(left_term, right_term)?;

        // Derive width/signedness from the WrappingArith node's own `ty`
        // (authoritative Rust type) as primary source. Fall back to operand
        // term_widths only when ty lacks BV info. Fixes #2100: FnCall results
        // without term_widths entries no longer cause incorrect defaults.
        let ty_width_info: Option<(u32, bool)> = ty.bit_width().map(|w| (w, !ty.is_unsigned()));
        let coerced_width_info = ty_width_info.or_else(|| {
            self.term_widths
                .get(&left_term)
                .or_else(|| self.term_widths.get(&right_term))
                .copied()
        });

        let result = match op {
            ArithOp::Add => self
                .solver
                .try_bvadd(left_term, right_term)
                .map_err(|e| e.to_string())?,
            ArithOp::Sub => self
                .solver
                .try_bvsub(left_term, right_term)
                .map_err(|e| e.to_string())?,
            ArithOp::Mul => self
                .solver
                .try_bvmul(left_term, right_term)
                .map_err(|e| e.to_string())?,
            ArithOp::Div | ArithOp::Rem => {
                return Err(
                    format!("Wrapping {:?}/{:?} not supported for div/rem", mode, op).into(),
                )
            }
        };

        match mode {
            WrappingMode::Wrapping => {
                if let Some(wi) = coerced_width_info {
                    self.term_widths.insert(result, wi);
                }
                Ok(result)
            }
            WrappingMode::Checked => {
                // Overflow-checked (#1785): BV result + overflow side-channel, not Option<T>.
                // Signedness: same-type in Rust (e.g., u8.checked_add(u8)).
                // Use receiver's declared signedness, not operands_are_unsigned which
                // requires BOTH operands unsigned. Literals lack term_widths entries
                // and default to signed, causing false positives/negatives.
                // Parity: methods.rs:731-740 (#1987, #2011).
                let is_signed = coerced_width_info.map(|(_, s)| s).unwrap_or(true);
                match op {
                    ArithOp::Add => {
                        let no_overflow = self
                            .solver
                            .try_bvadd_no_overflow(left_term, right_term, is_signed)
                            .map_err(|e| {
                                format!("Failed to create checked_add overflow check: {}", e)
                            })?;
                        self.overflow_checks
                            .push(("checked_add overflow".into(), no_overflow));
                        if is_signed {
                            let no_underflow = self
                                .solver
                                .try_bvadd_no_underflow(left_term, right_term)
                                .map_err(|e| {
                                    format!("Failed to create checked_add underflow check: {}", e)
                                })?;
                            self.overflow_checks
                                .push(("checked_add underflow".into(), no_underflow));
                        }
                    }
                    ArithOp::Sub => {
                        let no_underflow = self
                            .solver
                            .try_bvsub_no_underflow(left_term, right_term, is_signed)
                            .map_err(|e| {
                                format!("Failed to create checked_sub underflow check: {}", e)
                            })?;
                        self.overflow_checks
                            .push(("checked_sub underflow".into(), no_underflow));
                        if is_signed {
                            let no_overflow = self
                                .solver
                                .try_bvsub_no_overflow(left_term, right_term)
                                .map_err(|e| {
                                    format!("Failed to create checked_sub overflow check: {}", e)
                                })?;
                            self.overflow_checks
                                .push(("checked_sub overflow".into(), no_overflow));
                        }
                    }
                    ArithOp::Mul => {
                        let no_overflow = self
                            .solver
                            .try_bvmul_no_overflow(left_term, right_term, is_signed)
                            .map_err(|e| {
                                format!("Failed to create checked_mul overflow check: {}", e)
                            })?;
                        self.overflow_checks
                            .push(("checked_mul overflow".into(), no_overflow));
                        if is_signed {
                            let no_underflow = self
                                .solver
                                .try_bvmul_no_underflow(left_term, right_term)
                                .map_err(|e| {
                                    format!("Failed to create checked_mul underflow check: {}", e)
                                })?;
                            self.overflow_checks
                                .push(("checked_mul underflow".into(), no_underflow));
                        }
                    }
                    ArithOp::Div | ArithOp::Rem => {
                        return Err(format!(
                            "checked_{} is not supported — use standard division/remainder \
                             with explicit zero-divisor checks in requires!/ensures! instead",
                            if matches!(op, ArithOp::Div) {
                                "div"
                            } else {
                                "rem"
                            }
                        )
                        .into())
                    }
                }
                if let Some(wi) = coerced_width_info {
                    self.term_widths.insert(result, wi);
                }
                Ok(result)
            }
            WrappingMode::Saturating => {
                // Use receiver-derived signedness, not operands_are_unsigned.
                // Parity: methods.rs:836-842 (#1987, #2011).
                let unsigned = coerced_width_info.map(|(_, s)| !s).unwrap_or(false);
                if let Some((width, _)) = coerced_width_info {
                    let clamped =
                        self.clamp_to_bounds(result, left_term, right_term, width, unsigned, op)?;
                    if let Some(wi) = coerced_width_info {
                        self.term_widths.insert(clamped, wi);
                    }
                    Ok(clamped)
                } else {
                    Err(
                        "Saturating arithmetic requires known type width; cannot encode without bounds"
                            .to_string()
                            .into(),
                    )
                }
            }
        }
    }

    /// Encode an operand that sits under a same-width truncating wrap,
    /// stripping nested same-width truncating `+`/`-`/`*` wraps to their raw
    /// ring values (#2778 modular-congruence pushdown; see
    /// `encode_wrapping_arith`).
    ///
    /// SOUNDNESS: the returned term is congruent mod `2^width` to the
    /// operand's exact value — for a same-width Wrapping node the raw
    /// `l op r` differs from the wrapped value by a multiple of `2^width`
    /// (both the unsigned and the signed re-centered wrap), and the enclosing
    /// caller ALWAYS reduces mod `2^width`, where congruent operands of
    /// `+`/`-`/`*` yield equal results. Any other expression (including
    /// Div/Rem wraps, Checked/Saturating modes, and different widths) is
    /// encoded exactly via `encode_subexpr`.
    fn encode_int_mod_congruent_operand(
        &mut self,
        expr: &TrustVcExpr,
        width: u32,
    ) -> TrustVcResult<Term> {
        if let TrustVcExpr::WrappingArith {
            mode: WrappingMode::Wrapping,
            op,
            left,
            right,
            ty,
        } = expr
        {
            if matches!(op, ArithOp::Add | ArithOp::Sub | ArithOp::Mul)
                && ty.bit_width() == Some(width)
                && width > 0
            {
                let left_term = self.encode_int_mod_congruent_operand(left, width)?;
                let right_term = self.encode_int_mod_congruent_operand(right, width)?;
                return self.encode_int_arith(*op, left_term, right_term, false, false, ty, None);
            }
        }
        self.encode_subexpr(expr)
    }

    /// Overflow-checked arithmetic in Int mode (#2030, #1785).
    ///
    /// Performs the operation with Int arithmetic, wraps the result to the
    /// target range, then adds an overflow check: `unwrapped == wrapped`.
    /// When the check fails, the verification condition reports overflow.
    /// Returns the wrapped Int result (not `Option<T>`).
    ///
    /// Uses `resolve_expr_wrap` for the type > quantifier scope priority chain.
    fn encode_int_checked(
        &mut self,
        op: ArithOp,
        left: Term,
        right: Term,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let scope_sem = self.current_quantifier_wrap_semantics();
        let wrap_ctx = if self.use_int_arithmetic {
            None
        } else {
            resolve_expr_wrap(ty, scope_sem)
        };

        let raw_result = match op {
            ArithOp::Add => self
                .solver
                .try_add(left, right)
                .map_err(|e| e.to_string())?,
            ArithOp::Sub => self
                .solver
                .try_sub(left, right)
                .map_err(|e| e.to_string())?,
            ArithOp::Mul => self
                .solver
                .try_mul(left, right)
                .map_err(|e| e.to_string())?,
            ArithOp::Div | ArithOp::Rem => {
                return Err(
                    format!("Checked {:?} not supported for div/rem in int mode", op).into(),
                )
            }
        };

        let wrapped = self.wrap_int_with_ctx(raw_result, wrap_ctx)?;

        // Guard: only collect at quantifier_depth==0 (#2557 — same as arith add/sub/mul).
        if wrap_ctx.is_some() && self.quantifier_depth == 0 {
            if let Some(no_overflow) = self.int_result_in_wrap_range_ctx(raw_result, wrap_ctx)? {
                let label = match op {
                    ArithOp::Add => "checked_add overflow",
                    ArithOp::Sub => "checked_sub overflow",
                    ArithOp::Mul => "checked_mul overflow",
                    ArithOp::Div | ArithOp::Rem => unreachable!(),
                };
                self.overflow_checks.push((label.into(), no_overflow));
            }
        }

        Ok(wrapped)
    }

    /// Saturating arithmetic in Int mode (#2030).
    ///
    /// Performs the operation with Int arithmetic, then clamps the result to
    /// [min, max] for the target type using ITE chains.
    ///
    /// Uses `resolve_expr_wrap` for the type > quantifier scope priority chain.
    fn encode_int_saturating(
        &mut self,
        op: ArithOp,
        left: Term,
        right: Term,
        ty: &TrustVcType,
    ) -> TrustVcResult<Term> {
        let scope_sem = self.current_quantifier_wrap_semantics();
        let wrap_ctx = if self.use_int_arithmetic {
            None
        } else {
            resolve_expr_wrap(ty, scope_sem)
        };

        let raw_result = match op {
            ArithOp::Add => self
                .solver
                .try_add(left, right)
                .map_err(|e| e.to_string())?,
            ArithOp::Sub => self
                .solver
                .try_sub(left, right)
                .map_err(|e| e.to_string())?,
            ArithOp::Mul => self
                .solver
                .try_mul(left, right)
                .map_err(|e| e.to_string())?,
            ArithOp::Div | ArithOp::Rem => {
                return Err(
                    format!("Saturating {:?} not supported for div/rem in int mode", op).into(),
                )
            }
        };

        match wrap_ctx {
            Some((width, true)) => {
                // Unsigned saturating: clamp to [0, 2^width - 1]
                let max_bigint = unsigned_max(width);
                let max_term = self.solver.int_const_bigint(&max_bigint);
                let zero = self.solver.int_const(0);

                let too_high =
                    self.solver.try_gt(raw_result, max_term).map_err(|e| e.to_string())?;
                let too_low =
                    self.solver.try_lt(raw_result, zero).map_err(|e| e.to_string())?;
                let clamped = self
                    .solver
                    .try_ite(too_high, max_term, raw_result)
                    .map_err(|e| e.to_string())?;
                let clamped =
                    self.solver.try_ite(too_low, zero, clamped).map_err(|e| e.to_string())?;
                Ok(clamped)
            }
            Some((width, false)) => {
                // Signed saturating: clamp to [-(2^(w-1)), 2^(w-1) - 1]
                let (min_bigint, max_bigint) = signed_bounds(width);
                let min_term = self.solver.int_const_bigint(&min_bigint);
                let max_term = self.solver.int_const_bigint(&max_bigint);

                let too_high =
                    self.solver.try_gt(raw_result, max_term).map_err(|e| e.to_string())?;
                let too_low =
                    self.solver.try_lt(raw_result, min_term).map_err(|e| e.to_string())?;
                let clamped = self
                    .solver
                    .try_ite(too_high, max_term, raw_result)
                    .map_err(|e| e.to_string())?;
                let clamped = self
                    .solver
                    .try_ite(too_low, min_term, clamped)
                    .map_err(|e| e.to_string())?;
                Ok(clamped)
            }
            None => {
                Err(
                    "Saturating arithmetic in int mode requires wrap context; cannot encode without bounds"
                        .to_string()
                        .into(),
                )
            }
        }
    }
}

/// Compute unsigned max value (2^width - 1) without i128 overflow.
/// Safe for all widths including 128.
pub(super) fn unsigned_max(width: u32) -> BigInt {
    if width >= 128 {
        (BigInt::from(1u8) << width) - BigInt::from(1u8)
    } else {
        BigInt::from((1u128 << width) - 1)
    }
}

/// Compute signed bounds (min, max) = (-(2^(width-1)), 2^(width-1) - 1) without i128 overflow.
/// Safe for all widths including 128.
pub(super) fn signed_bounds(width: u32) -> (BigInt, BigInt) {
    if width >= 128 {
        let half = BigInt::from(1u8) << (width - 1);
        (-half.clone(), half - 1)
    } else {
        let half = 1i128 << (width - 1);
        (BigInt::from(-half), BigInt::from(half - 1))
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::{signed_bounds, unsigned_max};

    #[test]
    fn test_unsigned_max_large_widths() {
        let one = BigInt::from(1u8);

        for width in [128, 192, 256] {
            let expected = (one.clone() << width) - one.clone();
            assert_eq!(
                unsigned_max(width),
                expected,
                "unsigned_max({width}) should equal 2^{width} - 1",
            );
        }
    }

    #[test]
    fn test_signed_bounds_large_widths() {
        let one = BigInt::from(1u8);

        for width in [128, 192, 193, 256] {
            let half: BigInt = one.clone() << (width - 1);
            let expected = (-half.clone(), half - one.clone());
            assert_eq!(
                signed_bounds(width),
                expected,
                "signed_bounds({width}) should equal (-2^{}, 2^{} - 1)",
                width - 1,
                width - 1,
            );
        }
    }

    /// DISCRIMINATING: width=1 boundary — u1 max is 1 (single bit).
    #[test]
    fn test_unsigned_max_width_1() {
        assert_eq!(unsigned_max(1), BigInt::from(1), "u1 max must be 1");
    }

    /// DISCRIMINATING: width=0 degenerate — unsigned_max(0) = 0.
    /// Documents that width=0 produces a degenerate range where 0 is the
    /// only representable value. Not reachable in production (TrustVcType
    /// widths are always > 0), but pinning behavior prevents silent changes.
    #[test]
    fn test_unsigned_max_width_0_degenerate() {
        assert_eq!(
            unsigned_max(0),
            BigInt::from(0),
            "unsigned_max(0) = (1<<0)-1 = 0 (degenerate)"
        );
    }

    /// DISCRIMINATING: width=1 boundary — i1 range is [-1, 0].
    #[test]
    fn test_signed_bounds_width_1() {
        let (min, max) = signed_bounds(1);
        assert_eq!(min, BigInt::from(-1), "i1 min must be -1");
        assert_eq!(max, BigInt::from(0), "i1 max must be 0");
    }

    /// BOUNDARY: width=0 causes panic in signed_bounds due to `width - 1`
    /// underflow (u32::MAX shift). This documents the panic as a known
    /// defensive gap — width=0 is unreachable via TrustVcType parsing.
    #[test]
    fn test_signed_bounds_width_0_panics() {
        let result = std::panic::catch_unwind(|| signed_bounds(0));
        assert!(
            result.is_err(),
            "signed_bounds(0) must panic (width-1 underflow); got: {:?}",
            result
        );
    }

    /// DISCRIMINATING: standard widths (8, 16, 32, 64) produce correct bounds.
    /// Cross-checks signed_bounds against unsigned_max: signed_max = unsigned_max / 2.
    #[test]
    fn test_signed_unsigned_consistency_standard_widths() {
        for width in [8, 16, 32, 64] {
            let umax = unsigned_max(width);
            let (smin, smax) = signed_bounds(width);
            // unsigned_max = 2^w - 1; signed_max = 2^(w-1) - 1
            // So signed_max = (unsigned_max - 1) / 2
            assert_eq!(
                smax,
                (&umax - BigInt::from(1)) / BigInt::from(2),
                "signed_max({width}) must be (unsigned_max-1)/2"
            );
            // signed_min = -(signed_max + 1)
            assert_eq!(
                smin,
                -(&smax + BigInt::from(1)),
                "signed_min({width}) must be -(signed_max+1)"
            );
        }
    }
}
