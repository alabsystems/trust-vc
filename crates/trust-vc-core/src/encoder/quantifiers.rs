//! Quantifier encoding — forall/exists parsing and sort mapping.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Term;
use num_bigint::BigInt;

use crate::error::TrustVcResult;

use super::AstExpressionParser;

impl<'a> AstExpressionParser<'a> {
    /// Wraps the quantifier body with range guards for all integer-typed bound variables.
    ///
    /// For unsigned types: `0 <= x < 2^w`
    /// For signed types: `-2^(w-1) <= x < 2^(w-1)`
    ///
    /// For forall: `range(x) => body(x)` (body only needs to hold in range)
    /// For exists: `range(x) && body(x)` (witness must be in range)
    ///
    /// This ensures quantifier domains match Rust's concrete integer types (#1519).
    /// Without these guards, `forall |x: i32| ...` ranges over all mathematical integers,
    /// and `forall |x: u32| ...` allows negative values.
    pub(super) fn add_integer_range_guards(
        &mut self,
        bound_vars: &[(String, crate::ir::TrustVcType, Term)],
        body: Term,
        is_forall: bool,
    ) -> TrustVcResult<Term> {
        let mut guarded = body;
        for (_name, ty, term) in bound_vars {
            if matches!(ty, crate::ir::TrustVcType::Char) {
                // Rust `char` is a Unicode scalar value: its domain excludes the
                // UTF-16 surrogate band U+D800..=U+DFFF and is capped at U+10FFFF.
                // The plain `integer_range_bounds(Char)` = [0, 2^32) guard omits
                // both, which lets a surrogate / out-of-range existential witness
                // be manufactured (round8 findings 20/21). Use the full
                // scalar-value predicate instead. #2564 follow-up.
                let valid = self.char_domain_guard(*term)?;
                guarded = if is_forall {
                    self.solver
                        .try_implies(valid, guarded)
                        .map_err(|e| e.to_string())?
                } else {
                    self.solver
                        .try_and(valid, guarded)
                        .map_err(|e| e.to_string())?
                };
                continue;
            }
            if let Some((lower_val, upper_val)) = integer_range_bounds(ty) {
                let lower_term = self.solver.int_const_bigint(&lower_val);
                let lower = self
                    .solver
                    .try_ge(*term, lower_term)
                    .map_err(|e| e.to_string())?;
                let upper_term = self.solver.int_const_bigint(&upper_val);
                let upper = self
                    .solver
                    .try_lt(*term, upper_term)
                    .map_err(|e| e.to_string())?;
                let range = self
                    .solver
                    .try_and(lower, upper)
                    .map_err(|e| e.to_string())?;
                if is_forall {
                    guarded = self
                        .solver
                        .try_implies(range, guarded)
                        .map_err(|e| e.to_string())?;
                } else {
                    guarded = self
                        .solver
                        .try_and(range, guarded)
                        .map_err(|e| e.to_string())?;
                }
            } else if let Some(lower_val) = lower_bound_only(ty) {
                // Lower-only bound (e.g., Nat >= 0). Part of #2418/#2423.
                let lower_term = self.solver.int_const_bigint(&lower_val);
                let guard = self
                    .solver
                    .try_ge(*term, lower_term)
                    .map_err(|e| e.to_string())?;
                if is_forall {
                    guarded = self
                        .solver
                        .try_implies(guard, guarded)
                        .map_err(|e| e.to_string())?;
                } else {
                    guarded = self
                        .solver
                        .try_and(guard, guarded)
                        .map_err(|e| e.to_string())?;
                }
            }
        }
        Ok(guarded)
    }

    /// Build the integer-domain Unicode scalar-value predicate for a
    /// quantifier-bound `char`:
    /// `0 <= c <= 0x10FFFF && (c < 0xD800 || c > 0xDFFF)`.
    ///
    /// Quantifier-bound `char` vars are Int-sorted (`quantifier_sort_for_type`),
    /// so this is the Int-sorted analogue of `unicode::build_valid_char_predicate`
    /// (which constrains the BV32 carrier of *declared* char variables). Applying
    /// it as the quantifier range guard fixes both the false existential witness
    /// over the surrogate gap / above U+10FFFF (round8 findings 20/21) and the
    /// dual over-rejection of a true `forall c. (c as u32) <= 0x10FFFF`.
    pub(in crate::encoder) fn char_domain_guard(&mut self, term: Term) -> TrustVcResult<Term> {
        let zero = self.solver.int_const(0);
        let max_scalar = self.solver.int_const(0x10FFFF);
        let surrogate_lo = self.solver.int_const(0xD800);
        let surrogate_hi = self.solver.int_const(0xDFFF);
        let ge_zero = self.solver.try_ge(term, zero).map_err(|e| e.to_string())?;
        let le_max = self
            .solver
            .try_le(term, max_scalar)
            .map_err(|e| e.to_string())?;
        let below = self
            .solver
            .try_lt(term, surrogate_lo)
            .map_err(|e| e.to_string())?;
        let above = self
            .solver
            .try_gt(term, surrogate_hi)
            .map_err(|e| e.to_string())?;
        let not_surrogate = self
            .solver
            .try_or(below, above)
            .map_err(|e| e.to_string())?;
        let in_range = self
            .solver
            .try_and(ge_zero, le_max)
            .map_err(|e| e.to_string())?;
        self.solver
            .try_and(in_range, not_surrogate)
            .map_err(|e| e.to_string().into())
    }
}

/// Returns `(lower_inclusive, upper_exclusive)` range bounds for an integer type.
///
/// For unsigned types: `(0, 2^w)` — e.g., u32 maps to `[0, 2^32)`.
/// For signed types: `(-2^(w-1), 2^(w-1))` — e.g., i32 maps to `[-2^31, 2^31)`.
///
/// Returns `None` for non-integer types (e.g., bool).
///
/// Uses arbitrary-precision BigInt for bounds that exceed i64 range.
/// Fixes #1660 (unsigned) and extends to signed types for #1519.
pub(in crate::encoder) fn integer_range_bounds(
    ty: &crate::ir::TrustVcType,
) -> Option<(BigInt, BigInt)> {
    match ty {
        crate::ir::TrustVcType::Uint { width } => {
            let w = *width;
            if w == 128 {
                Some((
                    BigInt::from(0),
                    BigInt::from(1u128 << 64) * BigInt::from(1u128 << 64),
                ))
            } else {
                Some((BigInt::from(0), BigInt::from(1u128 << w)))
            }
        }
        crate::ir::TrustVcType::Char => Some((BigInt::from(0), BigInt::from(1u128 << 32))),
        crate::ir::TrustVcType::Int { width } => {
            let w = *width;
            if w == 128 {
                let half = BigInt::from(1u128 << 64) * BigInt::from(1u128 << 63);
                Some((-half.clone(), half))
            } else {
                let half = 1i128 << (w - 1);
                Some((BigInt::from(-half), BigInt::from(half)))
            }
        }
        _ => None,
    }
}

/// Returns a lower-only bound for types with a minimum but no maximum.
///
/// For `Nat`: lower bound is 0 (non-negative unbounded integer).
/// Returns `None` for types handled by `integer_range_bounds` or types
/// with no meaningful bound (e.g., MathInt, Bool).
///
/// Part of #2418/#2423: ensures `forall |n: nat| ...` gets `n >= 0` guard.
pub(in crate::encoder) fn lower_bound_only(ty: &crate::ir::TrustVcType) -> Option<BigInt> {
    match ty {
        crate::ir::TrustVcType::Nat => Some(BigInt::from(0)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;

    /// Direct unit tests for integer_range_bounds — these are truly discriminating
    /// because they verify the exact bound values, unlike the quantifier integration
    /// tests which all return Unknown due to ay-dpll's CEGQI limitation.
    ///
    /// The #1660 bug was: u64 upper bound was i64::MAX instead of 2^64.
    /// Integration tests cannot catch this because ay-dpll returns Unknown regardless
    /// of whether the bound is i64::MAX or 2^64.

    #[test]
    fn test_u64_upper_bound_is_2_pow_64_not_i64_max() {
        // This is the #1660 regression test. The old buggy code used i64::MAX.
        let (lower, upper) = integer_range_bounds(&TrustVcType::Uint { width: 64 }).unwrap();
        assert_eq!(lower, BigInt::from(0));
        // 2^64 = 18446744073709551616
        let expected_upper = BigInt::from(1u128 << 64);
        assert_eq!(
            upper,
            expected_upper,
            "u64 upper bound must be 2^64 ({}), not i64::MAX ({}). Regression: #1660",
            expected_upper,
            BigInt::from(i64::MAX)
        );
        // Explicitly verify it is NOT i64::MAX
        assert_ne!(upper, BigInt::from(i64::MAX));
    }

    #[test]
    fn test_usize_aliases_pointer_width_uint() {
        // usize normalizes to Uint { width: pointer_width() }
        let pw = crate::ir::pointer_width();
        let pw_bounds = integer_range_bounds(&TrustVcType::Uint { width: pw }).unwrap();
        let usize_ty = TrustVcType::from_str("usize").unwrap();
        let usize_bounds = integer_range_bounds(&usize_ty).unwrap();
        assert_eq!(
            pw_bounds, usize_bounds,
            "usize must alias pointer-width uint bounds"
        );
    }

    #[test]
    fn test_isize_aliases_pointer_width_int() {
        // isize normalizes to Int { width: pointer_width() }
        let pw = crate::ir::pointer_width();
        let pw_bounds = integer_range_bounds(&TrustVcType::Int { width: pw }).unwrap();
        let isize_ty = TrustVcType::from_str("isize").unwrap();
        let isize_bounds = integer_range_bounds(&isize_ty).unwrap();
        assert_eq!(
            pw_bounds, isize_bounds,
            "isize must alias pointer-width int bounds"
        );
    }

    #[test]
    fn test_unsigned_bounds_are_zero_to_2_pow_w() {
        let cases: &[(TrustVcType, u128)] = &[
            (TrustVcType::Uint { width: 8 }, 1u128 << 8),
            (TrustVcType::Uint { width: 16 }, 1u128 << 16),
            (TrustVcType::Uint { width: 32 }, 1u128 << 32),
            (TrustVcType::Uint { width: 64 }, 1u128 << 64),
        ];
        for (ty, expected_upper) in cases {
            let (lower, upper) = integer_range_bounds(ty)
                .unwrap_or_else(|| panic!("integer_range_bounds({:?}) returned None", ty));
            assert_eq!(lower, BigInt::from(0), "{:?} lower bound", ty);
            assert_eq!(upper, BigInt::from(*expected_upper), "{:?} upper bound", ty);
        }
    }

    #[test]
    fn test_signed_bounds_are_neg_half_to_half() {
        let cases: &[(TrustVcType, i128, i128)] = &[
            (TrustVcType::Int { width: 8 }, -(1i128 << 7), 1i128 << 7),
            (TrustVcType::Int { width: 16 }, -(1i128 << 15), 1i128 << 15),
            (TrustVcType::Int { width: 32 }, -(1i128 << 31), 1i128 << 31),
            (TrustVcType::Int { width: 64 }, -(1i128 << 63), 1i128 << 63),
        ];
        for (ty, expected_lower, expected_upper) in cases {
            let (lower, upper) = integer_range_bounds(ty)
                .unwrap_or_else(|| panic!("integer_range_bounds({:?}) returned None", ty));
            assert_eq!(lower, BigInt::from(*expected_lower), "{:?} lower bound", ty);
            assert_eq!(upper, BigInt::from(*expected_upper), "{:?} upper bound", ty);
        }
    }

    #[test]
    fn test_u128_bounds() {
        let (lower, upper) = integer_range_bounds(&TrustVcType::Uint { width: 128 }).unwrap();
        assert_eq!(lower, BigInt::from(0));
        // 2^128 = (2^64) * (2^64)
        let expected = BigInt::from(1u128 << 64) * BigInt::from(1u128 << 64);
        assert_eq!(upper, expected, "u128 upper bound must be 2^128");
    }

    #[test]
    fn test_i128_bounds() {
        let (lower, upper) = integer_range_bounds(&TrustVcType::Int { width: 128 }).unwrap();
        // 2^127 = (2^64) * (2^63)
        let half = BigInt::from(1u128 << 64) * BigInt::from(1u128 << 63);
        assert_eq!(lower, -half.clone(), "i128 lower bound must be -2^127");
        assert_eq!(upper, half, "i128 upper bound must be 2^127");
    }

    #[test]
    fn test_bool_returns_none() {
        assert!(integer_range_bounds(&TrustVcType::Bool).is_none());
    }

    #[test]
    fn test_non_integer_returns_none() {
        assert!(integer_range_bounds(&TrustVcType::Real).is_none());
        assert!(integer_range_bounds(&TrustVcType::MathInt).is_none());
        assert!(integer_range_bounds(&TrustVcType::Nat).is_none());
    }

    /// Char maps to [0, 2^32) — same as u32 since char is a Unicode scalar value.
    /// Fixes #2564: Char bound variables now get proper range guards in quantifiers.
    #[test]
    fn test_char_bounds_match_u32() {
        let (lower, upper) =
            integer_range_bounds(&TrustVcType::Char).expect("Char must return Some bounds");
        assert_eq!(lower, BigInt::from(0), "Char lower bound must be 0");
        assert_eq!(
            upper,
            BigInt::from(1u128 << 32),
            "Char upper bound must be 2^32"
        );
        // Verify identical to u32 bounds
        let (u32_lower, u32_upper) =
            integer_range_bounds(&TrustVcType::Uint { width: 32 }).unwrap();
        assert_eq!(lower, u32_lower, "Char and u32 lower bounds must match");
        assert_eq!(upper, u32_upper, "Char and u32 upper bounds must match");
    }

    // === lower_bound_only (#2418/#2423) ===

    #[test]
    fn test_nat_lower_bound_is_zero() {
        let bound = lower_bound_only(&TrustVcType::Nat);
        assert_eq!(bound, Some(BigInt::from(0)), "Nat lower bound must be 0");
    }

    #[test]
    fn test_math_int_has_no_lower_bound() {
        assert!(lower_bound_only(&TrustVcType::MathInt).is_none());
    }

    #[test]
    fn test_bv_types_have_no_lower_bound_only() {
        // BV types use integer_range_bounds (both bounds), not lower_bound_only.
        assert!(lower_bound_only(&TrustVcType::Uint { width: 32 }).is_none());
        assert!(lower_bound_only(&TrustVcType::Int { width: 32 }).is_none());
    }

    /// DISCRIMINATING: u1 range is [0, 2) = {0, 1}.
    #[test]
    fn test_u1_range_bounds() {
        let (lower, upper) = integer_range_bounds(&TrustVcType::Uint { width: 1 }).unwrap();
        assert_eq!(lower, BigInt::from(0), "u1 lower must be 0");
        assert_eq!(upper, BigInt::from(2), "u1 upper (exclusive) must be 2");
    }

    /// DISCRIMINATING: i1 range is [-1, 1) = {-1, 0}.
    #[test]
    fn test_i1_range_bounds() {
        let (lower, upper) = integer_range_bounds(&TrustVcType::Int { width: 1 }).unwrap();
        assert_eq!(lower, BigInt::from(-1), "i1 lower must be -1");
        assert_eq!(upper, BigInt::from(1), "i1 upper (exclusive) must be 1");
    }

    /// BOUNDARY: Int{width:0} panics on `1i128 << (w-1)` underflow.
    /// Documents the width=0 defensive gap — unreachable via TrustVcType parsing.
    #[test]
    fn test_i0_range_bounds_panics() {
        let result =
            std::panic::catch_unwind(|| integer_range_bounds(&TrustVcType::Int { width: 0 }));
        assert!(
            result.is_err(),
            "Int{{width:0}} must panic on shift underflow; got: {:?}",
            result
        );
    }

    /// BOUNDARY: Uint{width:0} produces degenerate range [0, 1) = {0}.
    /// 1u128 << 0 = 1, so range is [0, 1). Not reachable in production.
    #[test]
    fn test_u0_range_bounds_degenerate() {
        let (lower, upper) = integer_range_bounds(&TrustVcType::Uint { width: 0 }).unwrap();
        assert_eq!(lower, BigInt::from(0), "u0 lower must be 0");
        assert_eq!(upper, BigInt::from(1), "u0 upper (exclusive) must be 1");
    }

    /// DISCRIMINATING: integer_range_bounds signed lower and upper match
    /// the two's complement formula for standard widths.
    /// lower == -2^(w-1), upper == 2^(w-1) (exclusive).
    /// Cross-checks the separate implementations in quantifiers.rs vs
    /// ir_encoder/wrapping.rs which compute the same values independently.
    #[test]
    fn test_integer_range_bounds_signed_formula_standard() {
        for width in [1u32, 8, 16, 32, 64] {
            let (lower, upper) = integer_range_bounds(&TrustVcType::Int { width }).unwrap();
            // Two's complement: min = -2^(w-1), exclusive upper = 2^(w-1)
            let half = BigInt::from(1i128 << (width - 1));
            assert_eq!(
                lower,
                -half.clone(),
                "signed lower mismatch at width={width}"
            );
            assert_eq!(upper, half, "signed upper mismatch at width={width}");
        }
    }
}
