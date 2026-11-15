//! Operator encoding — Int-mode wrapping, truncation, and shift overflow helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The string-path operator parser (`parse_binary_op`, `parse_unary_op`, etc.)
//! was removed in #2099 after the typed IR pipeline (#1927) superseded it.
//! Remaining helpers are used by the IR encoder (`ir_encoder/arith.rs`,
//! `ir_encoder/logic.rs`, `ir_encoder/wrapping.rs`, `ir_encoder/advanced.rs`).

use ay_dpll::api::{Sort, Term};
use num_bigint::BigInt;

use crate::error::TrustVcResult;

use super::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    /// Wraps an Int arithmetic result using an explicit wrapping context (#2036).
    ///
    /// Takes a caller-provided `(width, is_unsigned)` tuple. Returns the result
    /// unchanged when `ctx` is `None`.
    pub(super) fn wrap_int_with_ctx(
        &mut self,
        result: Term,
        ctx: Option<(u32, bool)>,
    ) -> TrustVcResult<Term> {
        let (width, is_unsigned) = match ctx {
            Some(wrap) => wrap,
            None => return Ok(result),
        };
        self.wrap_int_to_explicit_range(result, width, is_unsigned)
    }

    /// Returns a predicate stating that `result` is already inside the target
    /// integer range for `ctx`, so wrapping would be a no-op.
    ///
    /// This is equivalent to `result == wrap(result)` but avoids modulo terms
    /// that ay-dpll often classifies as `Unknown(Incomplete)` in quantifier
    /// bodies. Explicit range bounds keep the predicate in linear integer
    /// arithmetic for add/sub/mul/neg overflow checks.
    pub(super) fn int_result_in_wrap_range_ctx(
        &mut self,
        result: Term,
        ctx: Option<(u32, bool)>,
    ) -> TrustVcResult<Option<Term>> {
        let Some((width, is_unsigned)) = ctx else {
            return Ok(None);
        };

        if width == 0 {
            let zero = self.solver.int_const(0);
            return self
                .solver
                .try_eq(result, zero)
                .map(Some)
                .map_err(|e| e.to_string().into());
        }

        let lower = if is_unsigned {
            BigInt::from(0u8)
        } else {
            -(BigInt::from(1u8) << (width - 1))
        };
        let upper_exclusive = if is_unsigned {
            BigInt::from(1u8) << width
        } else {
            BigInt::from(1u8) << (width - 1)
        };

        let lower_term = self.solver.int_const_bigint(&lower);
        let upper_term = self.solver.int_const_bigint(&upper_exclusive);
        let ge_lower = self
            .solver
            .try_ge(result, lower_term)
            .map_err(|e| e.to_string())?;
        let lt_upper = self
            .solver
            .try_lt(result, upper_term)
            .map_err(|e| e.to_string())?;
        let in_range = self
            .solver
            .try_and(ge_lower, lt_upper)
            .map_err(|e| e.to_string())?;
        Ok(Some(in_range))
    }

    /// Int-mode signed Div/Rem overflow check with explicit context (#2036).
    ///
    /// Takes a caller-provided `(width, is_unsigned)` tuple.
    pub(super) fn int_mode_signed_div_rem_no_overflow_ctx(
        &mut self,
        left: Term,
        right: Term,
        ctx: Option<(u32, bool)>,
    ) -> Option<Term> {
        let (width, is_unsigned) = ctx?;
        if is_unsigned || width == 0 {
            return None;
        }

        let min_value = -(BigInt::from(1u128) << (width - 1));
        let min_term = self.solver.int_const_bigint(&min_value);
        let neg_one = self.solver.int_const(-1);
        let is_min = self.solver.try_eq(left, min_term).ok()?;
        let is_neg_one = self.solver.try_eq(right, neg_one).ok()?;
        let is_overflow_pair = self.solver.try_and(is_min, is_neg_one).ok()?;
        self.solver.try_not(is_overflow_pair).ok()
    }

    /// Wraps an Int value to an explicit BV range (#1842).
    ///
    /// For unsigned (width w): `result mod 2^w` -> range [0, 2^w - 1]
    /// For signed (width w): `((result + 2^(w-1)) mod 2^w) - 2^(w-1)`
    ///
    /// Used by arithmetic wrapping (via `wrap_int_with_ctx`) and by
    /// cast encoding in Int mode (where the target type determines the range).
    pub(super) fn wrap_int_to_explicit_range(
        &mut self,
        result: Term,
        width: u32,
        is_unsigned: bool,
    ) -> TrustVcResult<Term> {
        let modulus = BigInt::from(1u128) << width;
        let modulus_term = self.solver.int_const_bigint(&modulus);

        if is_unsigned {
            // Unsigned: result mod 2^w
            self.solver
                .try_modulo(result, modulus_term)
                .map_err(|e| format!("Failed to create unsigned wrapping: {}", e).into())
        } else {
            // Signed: ((result + 2^(w-1)) mod 2^w) - 2^(w-1)
            let half = BigInt::from(1u128) << (width - 1);
            let half_term = self.solver.int_const_bigint(&half);
            let shifted = self
                .solver
                .try_add(result, half_term)
                .map_err(|e| e.to_string())?;
            let wrapped = self
                .solver
                .try_modulo(shifted, modulus_term)
                .map_err(|e| format!("Failed to create signed wrapping: {}", e))?;
            let half_term2 = self.solver.int_const_bigint(&half);
            self.solver
                .try_sub(wrapped, half_term2)
                .map_err(|e| e.to_string().into())
        }
    }

    /// Truncation-toward-zero integer division (#1824).
    ///
    /// Rust `/` truncates toward zero; SMT-LIB `div` uses Euclidean semantics
    /// (rounds toward -inf). For non-negative operands they agree. For negative
    /// operands they diverge: e.g. (-7)/2 is -3 in Rust but -4 in SMT-LIB.
    ///
    /// Encoding: `trunc_div(a, b) = ite(same_sign(a,b), div(|a|,|b|), -div(|a|,|b|))`
    /// where `same_sign(a,b) = (a >= 0) == (b >= 0)`.
    ///
    /// This is correct because `div(|a|, |b|)` with non-negative arguments equals
    /// floor division, which is the magnitude of the truncated quotient.
    pub(super) fn int_truncation_div(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let zero = self.solver.int_const(0);
        let a_nonneg = self.solver.try_ge(a, zero).map_err(|e| e.to_string())?;
        let zero2 = self.solver.int_const(0);
        let b_nonneg = self.solver.try_ge(b, zero2).map_err(|e| e.to_string())?;
        // same_sign: both non-negative or both negative
        let same_sign = self
            .solver
            .try_eq(a_nonneg, b_nonneg)
            .map_err(|e| e.to_string())?;

        let abs_a = self.solver.try_abs(a).map_err(|e| e.to_string())?;
        let abs_b = self.solver.try_abs(b).map_err(|e| e.to_string())?;
        let abs_div = self
            .solver
            .try_int_div(abs_a, abs_b)
            .map_err(|e| format!("Integer division failed: {}", e))?;
        let neg_abs_div = self.solver.try_neg(abs_div).map_err(|e| e.to_string())?;

        self.solver
            .try_ite(same_sign, abs_div, neg_abs_div)
            .map_err(|e| e.to_string().into())
    }

    /// Truncation-toward-zero integer remainder (#1824).
    ///
    /// Rust `%` returns a remainder whose sign follows the dividend:
    /// `a % b = a - b * trunc_div(a, b)`. SMT-LIB `mod` always returns
    /// a non-negative value.
    pub(super) fn int_truncation_rem(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        let trunc_div = self.int_truncation_div(a, b)?;
        let product = self
            .solver
            .try_mul(b, trunc_div)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_sub(a, product)
            .map_err(|e| e.to_string().into())
    }

    /// Euclidean integer division — rounds toward -inf so the paired remainder
    /// is always non-negative (#2778, cluster mirroring Verus operator
    /// semantics).
    ///
    /// This matches Rust's `i*::div_euclid` / `u*::div_euclid` and Verus's
    /// Euclidean `/` on `int`: the quotient `q` and remainder `r` satisfy
    /// `q*b + r == a` with `0 <= r < |b|`. It is the dual of
    /// [`int_truncation_div`], which instead rounds toward zero (Rust `/`).
    ///
    /// Soundness: the ay solver's `try_int_div` (`mk_intdiv`) is *defined* with
    /// SMT-LIB Euclidean semantics — `a = b*(div a b) + (mod a b)` with
    /// `0 <= (mod a b) < |b|`. So Euclidean division is exactly `try_int_div`
    /// with no sign-correction wrapper (unlike the truncated path, which has to
    /// reconstruct the magnitude from `div(|a|,|b|)`). Division by zero stays
    /// under-specified by the solver — the encoder never folds it — matching
    /// the existing truncated path's treatment, so callers remain responsible
    /// for emitting a `b != 0` obligation.
    pub(super) fn int_euclidean_div(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        self.solver
            .try_int_div(a, b)
            .map_err(|e| format!("Euclidean integer division failed: {}", e).into())
    }

    /// Euclidean integer remainder — always non-negative (#2778).
    ///
    /// Matches Rust's `*::rem_euclid` and Verus's Euclidean `%` on `int`:
    /// the result `r` satisfies `0 <= r < |b|` and `int_euclidean_div(a,b)*b +
    /// r == a`. It is the dual of [`int_truncation_rem`], whose sign follows
    /// the dividend.
    ///
    /// Soundness: identical to [`int_euclidean_div`] — the solver's
    /// `try_modulo` (`mk_mod`) is the SMT-LIB Euclidean `mod`, which is exactly
    /// the non-negative remainder. No sign correction is required.
    pub(super) fn int_euclidean_mod(&mut self, a: Term, b: Term) -> TrustVcResult<Term> {
        self.solver
            .try_modulo(a, b)
            .map_err(|e| format!("Euclidean integer remainder failed: {}", e).into())
    }

    /// Model signed MIN/-1 overflow as undefined inside quantifier bodies (#1873).
    ///
    /// At `quantifier_depth > 0`, pushing to `overflow_checks` is ineffective
    /// because the bound variables become free at the outer assertion scope
    /// (#2557). Instead, replace the result with `ite(is_overflow, fresh, result)`
    /// so the verifier cannot assume any particular value when Rust would panic.
    ///
    /// Returns `Some(guarded_result)` if the type is signed and a guard was
    /// added; `None` if unsigned or no wrap context (caller keeps original).
    pub(super) fn int_div_rem_overflow_as_undefined(
        &mut self,
        left: Term,
        right: Term,
        result: Term,
        ctx: Option<(u32, bool)>,
        op_label: &str,
    ) -> TrustVcResult<Option<Term>> {
        let Some((width, is_unsigned)) = ctx else {
            return Ok(None);
        };
        if is_unsigned || width == 0 {
            return Ok(None);
        }

        let min_value = -(BigInt::from(1u128) << (width - 1));
        let min_term = self.solver.int_const_bigint(&min_value);
        let neg_one = self.solver.int_const(-1);
        let is_min = self
            .solver
            .try_eq(left, min_term)
            .map_err(|e| e.to_string())?;
        let is_neg_one = self
            .solver
            .try_eq(right, neg_one)
            .map_err(|e| e.to_string())?;
        let is_overflow = self
            .solver
            .try_and(is_min, is_neg_one)
            .map_err(|e| e.to_string())?;

        let fresh = self
            .solver
            .fresh_var(&format!("__int_{}_min_panic", op_label), Sort::Int);
        let guarded = self
            .solver
            .try_ite(is_overflow, fresh, result)
            .map_err(|e| e.to_string())?;
        Ok(Some(guarded))
    }

    /// Add a shift overflow check — not gated by `check_overflow`.
    ///
    /// Shift amount must be < bit width. In Rust, shifting by >= bit width can
    /// panic when overflow checks are enabled and otherwise uses target/runtime
    /// behavior that must not be silently assumed by verification. The
    /// `check_overflow` flag controls arithmetic overflow detection; shift bounds
    /// are enforced separately via `bitshift_behavior` (#1868, #2586).
    /// Callers must gate on `bitshift_behavior.should_check()` before calling.
    /// `lhs_width` is the resolved LHS bit width (the value being shifted).
    /// Callers must resolve the width before invoking this helper (#2297).
    /// The bound constant is created in the shift-amount sort so bvult remains
    /// well-typed even for mixed-width shifts (e.g., u32 << u64).
    ///
    /// `check_name` is the complete diagnostic label recorded for this check.
    /// On failure it surfaces verbatim in the `possible {check_name} in '...'`
    /// counterexample message, so callers pass the byte-exact upstream phrasing
    /// (e.g. `left shift overflow`, or `bit shift underflow/overflow` for a
    /// signed/possibly-negative shift amount — #2778). The helper does not
    /// reshape it.
    pub(super) fn check_shift_overflow(
        &mut self,
        shift_amount: Term,
        lhs_width: u32,
        check_name: &str,
    ) -> TrustVcResult<()> {
        // The amount's width is its sort's (a hash-consed amount's
        // `term_widths` entry may be contested; its width never is).
        let shift_amount_width = self
            .bv_term_width(shift_amount)
            .or_else(|| self.term_widths.width(&shift_amount))
            .unwrap_or(lhs_width);
        let width_const = self
            .solver
            .try_bv_const(lhs_width as i64, shift_amount_width)
            .map_err(|e| e.to_string())?;
        let in_range = self
            .solver
            .try_bvult(shift_amount, width_const)
            .map_err(|e| format!("Failed to create {} check: {}", check_name, e))?;
        self.overflow_checks
            .push((check_name.to_string().into(), in_range));
        Ok(())
    }
}
