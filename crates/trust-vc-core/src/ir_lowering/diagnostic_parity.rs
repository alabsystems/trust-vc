//! Diagnostic-parity surface: byte-exact upstream Verus error messages.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module reproduces, *byte for byte*, the diagnostic strings that
//! upstream Verus emits for the highest-frequency `error`-verdict categories in
//! issue #2778. When `trust-vc` detects one of these conditions soundly, it
//! fails closed with a [`LoweringError`] whose `Display` text *contains the
//! exact upstream substring* asserted by the ported Verus suite
//! (`assert_vir_error_msg`, which does a substring `contains` check). The
//! strings are taken from the pinned Verus checkout
//! `a40d57c73650cd3648b09386bfdb96ab5c270626`:
//!
//! - `rust_verify/src/rust_to_vir_expr.rs::check_lit_int`
//!   → `format!("integer literal out of range {:?}", range)`
//! - `vir/src/bitvector_to_air.rs`
//!   → `format!("IntRange error: expected finite-width integer for bit-vector, got {:?}", typ)`
//!   → `format!("error: bit_vector prover cannot handle type `{:}`", ...)`
//!   → `"not supported: bit-shift with possibly negative shift (If you believe \
//!      this value is always nonnegative, try casting the RHS to an unsigned type)"`
//!
//! SOUNDNESS: every helper here is fail-closed and only constructs a message
//! after the caller has *proven* the condition holds (e.g. a concrete literal
//! whose value provably escapes its declared type's range). None of these
//! helpers fabricate a passing verdict — they only convert an already-detected
//! error into the parity-correct text.

use crate::ir::TrustVcType;

use super::error::LoweringError;

/// Renders a [`TrustVcType`] as the upstream Verus `IntRange` `Debug` form used
/// in the `integer literal out of range <IntRange>` diagnostic.
///
/// Mirrors `vir::ast::IntRange`'s derived `Debug`:
/// `U(n)`, `I(n)`, `USize`, `ISize`, `Char`, `Int`, `Nat`. Returns `None` for
/// non-integer types (a literal-range check never reaches them).
///
/// Note: `usize`/`isize` lower to `Uint`/`Int { width: pointer_width() }` in the
/// IR, which loses the `USize`/`ISize` distinction. We therefore render the
/// fixed-width form (`U(64)`/`I(64)` on a 64-bit target) for them. This affects
/// only the trailing `IntRange` token of the message, never the asserted
/// substring `integer literal out of range`.
pub(super) fn int_range_debug(ty: &TrustVcType) -> Option<String> {
    match ty {
        TrustVcType::Uint { width } => Some(format!("U({width})")),
        TrustVcType::Int { width } => Some(format!("I({width})")),
        TrustVcType::Char => Some("Char".to_string()),
        TrustVcType::MathInt => Some("Int".to_string()),
        TrustVcType::Nat => Some("Nat".to_string()),
        _ => None,
    }
}

/// Returns `true` iff `value` is representable in `ty`'s integer range.
///
/// This is the *sound* gate that guards every "out of range" diagnostic: the
/// caller must only emit the error when this returns `false`. The bounds match
/// the encoder's own range predicates exactly:
/// - unsigned `uN`: `0 <= value < 2^N`
/// - signed `iN`: `-(2^(N-1)) <= value <= 2^(N-1) - 1`
/// - `char`: a Unicode scalar value
/// - `int`: always (unbounded)
/// - `nat`: `value >= 0`
///
/// Non-integer types return `true` (no literal-range obligation applies); the
/// caller is responsible for never invoking the diagnostic on them.
pub(super) fn int_literal_fits(value: i128, ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::Uint { width } => {
            if *width == 0 || value < 0 {
                return false;
            }
            if *width >= 128 {
                return true;
            }
            (value as u128) < (1u128 << width)
        }
        TrustVcType::Int { width } => {
            if *width == 0 {
                return false;
            }
            if *width >= 128 {
                return true;
            }
            let min = -(1i128 << (width - 1));
            let max = (1i128 << (width - 1)) - 1;
            value >= min && value <= max
        }
        TrustVcType::Char => is_unicode_scalar_value(value),
        TrustVcType::MathInt => true,
        TrustVcType::Nat => value >= 0,
        // Non-integer types carry no literal-range obligation.
        _ => true,
    }
}

/// Verus `unicode.rs` scalar-value predicate: `[0, 0xD800) ∪ [0xE000, 0x10FFFF]`.
fn is_unicode_scalar_value(value: i128) -> bool {
    (0..=0x10FFFF).contains(&value) && !(0xD800..=0xDFFF).contains(&value)
}

/// The Verus-faithful `check_lit_int` equivalent for an integer literal.
///
/// `value` is the *signed* literal value already accounting for any leading
/// unary negation (so `-129i8` arrives here as `value == -129`, `ty == i8`).
/// Returns the byte-exact `integer literal out of range <IntRange>` error when
/// the value escapes `ty`'s range; otherwise `Ok(())`.
///
/// Only integer literal types (`uN`/`iN`/`char`) can ever fail. `int`/`nat` are
/// unbounded-from-above and never out of range here (a negative literal typed
/// `nat` is rejected earlier by type checking, not by this range check).
pub(super) fn check_int_literal_in_range(
    value: i128,
    ty: &TrustVcType,
) -> Result<(), LoweringError> {
    if int_literal_fits(value, ty) {
        return Ok(());
    }
    // Only emit the parity message for types that have an IntRange rendering.
    // Anything else cannot be an integer literal and must not reach here.
    let Some(range) = int_range_debug(ty) else {
        return Ok(());
    };
    Err(LoweringError::IntegerLiteralOutOfRange(format!(
        "integer literal out of range {range}"
    )))
}

/// Byte-exact upstream message for a `by(bit_vector)` proof that mentions a
/// value of non-finite-width integer type (`int`/`nat`).
///
/// Reproduces `bitvector_to_air.rs::bitvector_expect_finite`:
/// `format!("IntRange error: expected finite-width integer for bit-vector, got {:?}", typ)`.
/// The asserted upstream substring is `expected finite-width integer`.
pub(crate) fn bit_vector_expected_finite_width(ty: &TrustVcType) -> LoweringError {
    LoweringError::BitVectorUnsupportedType(format!(
        "IntRange error: expected finite-width integer for bit-vector, got {}",
        bit_vector_typ_debug(ty)
    ))
}

/// Byte-exact upstream message for a `by(bit_vector)` proof that mentions a
/// value of a type the bit-vector prover cannot model at all (e.g. a
/// user-defined datatype).
///
/// Reproduces `bitvector_to_air.rs`:
/// `format!("error: bit_vector prover cannot handle type `{:}`", typ_to_diagnostic_str(typ))`.
/// The asserted upstream substring is `bit_vector prover cannot handle type
/// `<diagnostic name>``. `diagnostic_name` must be the fully-qualified,
/// crate-prefixed Verus diagnostic name (e.g. `test_crate::X`).
pub(crate) fn bit_vector_cannot_handle_type(diagnostic_name: &str) -> LoweringError {
    LoweringError::BitVectorUnsupportedType(format!(
        "error: bit_vector prover cannot handle type `{diagnostic_name}`"
    ))
}

/// Byte-exact upstream message for a bit-shift whose shift amount is possibly
/// negative (a signed RHS not provably non-negative).
///
/// Reproduces `bitvector_to_air.rs`:
/// `"not supported: bit-shift with possibly negative shift (If you believe this \
///   value is always nonnegative, try casting the RHS to an unsigned type)"`.
/// The asserted upstream substring is `bit-shift with possibly negative shift`.
pub(crate) fn bit_shift_possibly_negative() -> LoweringError {
    LoweringError::BitShiftPossiblyNegativeShift(
        "not supported: bit-shift with possibly negative shift (If you believe this value is \
         always nonnegative, try casting the RHS to an unsigned type)"
            .to_string(),
    )
}

/// Renders a [`TrustVcType`] using the `Debug`-shaped form Verus's
/// `bitvector_expect_finite` prints for the `got {:?}` slot.
///
/// Verus prints the VIR `Typ` (an `Arc<TypX>`); for the cases that reach the
/// finite-width check this is always `Int(IntRange::Int)` or
/// `Int(IntRange::Nat)`. We reproduce the `Int(<IntRange>)` shape for integer
/// types and fall back to the canonical type string otherwise. Only the
/// asserted substring (`expected finite-width integer`) is load-bearing.
fn bit_vector_typ_debug(ty: &TrustVcType) -> String {
    match int_range_debug(ty) {
        Some(range) => format!("Int({range})"),
        None => ty.to_type_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u8_literal_300_is_out_of_range_with_exact_message() {
        let err = check_int_literal_in_range(300, &TrustVcType::Uint { width: 8 })
            .expect_err("300 does not fit u8");
        assert_eq!(
            err.to_string(),
            "integer literal out of range U(8)",
            "must reproduce upstream rust_to_vir_expr.rs check_lit_int message byte-for-byte"
        );
        // Upstream `assert_vir_error_msg` substring.
        assert!(err.to_string().contains("integer literal out of range"));
    }

    #[test]
    fn u8_literal_256_is_out_of_range() {
        let err = check_int_literal_in_range(256, &TrustVcType::Uint { width: 8 })
            .expect_err("256 does not fit u8");
        assert_eq!(err.to_string(), "integer literal out of range U(8)");
    }

    #[test]
    fn u8_literal_255_fits() {
        assert!(check_int_literal_in_range(255, &TrustVcType::Uint { width: 8 }).is_ok());
    }

    #[test]
    fn i8_positive_128_is_out_of_range() {
        let err = check_int_literal_in_range(128, &TrustVcType::Int { width: 8 })
            .expect_err("128 does not fit i8 (max 127)");
        assert_eq!(err.to_string(), "integer literal out of range I(8)");
    }

    #[test]
    fn i8_negative_128_fits_as_min() {
        // -128i8 is i8::MIN and must be accepted (the inner positive literal
        // would not fit, but the negated value does).
        assert!(check_int_literal_in_range(-128, &TrustVcType::Int { width: 8 }).is_ok());
    }

    #[test]
    fn i8_negative_129_is_out_of_range() {
        let err = check_int_literal_in_range(-129, &TrustVcType::Int { width: 8 })
            .expect_err("-129 does not fit i8 (min -128)");
        assert_eq!(err.to_string(), "integer literal out of range I(8)");
    }

    #[test]
    fn i128_full_range_literals_fit() {
        assert!(check_int_literal_in_range(i128::MAX, &TrustVcType::Int { width: 128 }).is_ok());
        assert!(check_int_literal_in_range(i128::MIN, &TrustVcType::Int { width: 128 }).is_ok());
    }

    #[test]
    fn u128_large_literal_fits() {
        // A large but non-negative value fits u128; width >= 128 accepts any
        // representable i128-carried value (the BV encoding handles wrap
        // precisely). Negative values never fit an unsigned type.
        assert!(check_int_literal_in_range(i128::MAX, &TrustVcType::Uint { width: 128 }).is_ok());
        assert!(!int_literal_fits(-1, &TrustVcType::Uint { width: 128 }));
    }

    #[test]
    fn math_int_and_nat_never_out_of_range_above() {
        assert!(check_int_literal_in_range(i128::MAX, &TrustVcType::MathInt).is_ok());
        assert!(check_int_literal_in_range(0, &TrustVcType::Nat).is_ok());
    }

    #[test]
    fn bit_vector_expected_finite_width_message_is_byte_exact() {
        let err = bit_vector_expected_finite_width(&TrustVcType::MathInt);
        assert_eq!(
            err.to_string(),
            "IntRange error: expected finite-width integer for bit-vector, got Int(Int)"
        );
        // Upstream `assert_vir_error_msg` substring.
        assert!(err.to_string().contains("expected finite-width integer"));
    }

    #[test]
    fn bit_vector_cannot_handle_type_message_is_byte_exact() {
        let err = bit_vector_cannot_handle_type("test_crate::X");
        assert_eq!(
            err.to_string(),
            "error: bit_vector prover cannot handle type `test_crate::X`"
        );
        // Upstream `assert_vir_error_msg` substring.
        assert!(err
            .to_string()
            .contains("bit_vector prover cannot handle type `test_crate::X`"));
    }

    #[test]
    fn bit_shift_possibly_negative_message_is_byte_exact() {
        let err = bit_shift_possibly_negative();
        assert_eq!(
            err.to_string(),
            "not supported: bit-shift with possibly negative shift (If you believe this value is \
             always nonnegative, try casting the RHS to an unsigned type)"
        );
        // Upstream `assert_vir_error_msg` substring.
        assert!(err
            .to_string()
            .contains("bit-shift with possibly negative shift"));
    }
}
