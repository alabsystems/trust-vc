//! Const-eval regressions for typed literal comparisons and value fitting.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// try_const_eval_typed: BV range check missing — false Verified risk
// ========================================================================
//
// The typed const-eval path (eval.rs:213) compares IntLit i128 values with
// native Rust semantics, ignoring the TrustVcType width. The legacy string
// path (eval.rs:28) correctly checks fits_in_signed_bv before comparing.
//
// For an IntLit with value 128 and ty Int{8}, native i128 says 128 > 127
// is true. But in signed BV(8), 128 wraps to -128, so 128 > 127 is FALSE.
// If try_const_eval_typed returns Some(true), verify_assertion short-circuits
// the solver and reports Verified — a false positive.

/// DISCRIMINATING: try_const_eval_typed must NOT short-circuit when literal
/// values exceed the BV range of their declared type.
///
/// 128 > 127 is true in i128, but false in signed i8 (128 wraps to -128).
/// If try_const_eval_typed ignores the type width, it returns Some(true) —
/// which would cause a false Verified result via the solver short-circuit.
#[test]
fn test_try_const_eval_typed_rejects_out_of_bv_range_comparison() {
    // Build: 128i8 > 127i8  (true in i128, false in signed BV(8))
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 128,
            ty: TrustVcType::Int { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 127,
            ty: TrustVcType::Int { width: 8 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);

    // Correct behavior: return None (don't short-circuit, defer to solver).
    // BUG behavior: returns Some(true) because 128 > 127 in native i128.
    assert_ne!(
        result,
        Some(true),
        "SOUNDNESS BUG: try_const_eval_typed returns true for 128i8 > 127i8, \
         but 128 wraps to -128 in signed BV(8). The solver short-circuit would \
         incorrectly report Verified."
    );
}

/// DISCRIMINATING: try_const_eval_typed must NOT return true for unsigned
/// overflow case: 256u8 > 255u8 is true in i128, false in BV(8) where
/// 256 wraps to 0.
#[test]
fn test_try_const_eval_typed_rejects_unsigned_overflow_comparison() {
    // Build: 256u8 > 255u8  (true in i128, false in u8 where 256 wraps to 0)
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 256,
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 255,
            ty: TrustVcType::Uint { width: 8 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    assert_ne!(
        result,
        Some(true),
        "SOUNDNESS BUG: try_const_eval_typed returns true for 256u8 > 255u8, \
         but 256 wraps to 0 in BV(8). False Verified risk."
    );
}

/// CONTROL: Values within BV range should still be const-evaluated correctly.
/// 5 > 3 with Int{32} — both values fit, so const-eval should work.
#[test]
fn test_try_const_eval_typed_in_range_works() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 5,
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 3,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    // For in-range values, const-eval should return the correct answer.
    // Some(true) is correct here because 5 > 3 in both i128 and i32.
    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    assert_eq!(
        result,
        Some(true),
        "Control: 5 > 3 within i32 range should const-eval to true"
    );
}

// #2100 regression tests moved to ir_soundness_2100.rs (file size split).

/// DISCRIMINATING: Equality comparison at BV boundary.
/// IntLit{value: 256, ty: Uint{8}} == IntLit{value: 0, ty: Uint{8}}
/// In i128: 256 != 0, so result is false.
/// In BV(8): 256 mod 256 = 0, so result is true.
/// try_const_eval_typed should return None (defer to solver), not Some(false).
#[test]
fn test_try_const_eval_typed_rejects_boundary_equality() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::IntLit {
            value: 256,
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Uint { width: 8 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    // Correct: None (don't short-circuit).
    // BUG: Some(false) because 256 != 0 in i128, but 256 == 0 in u8.
    assert_ne!(
        result,
        Some(false),
        "SOUNDNESS BUG: try_const_eval_typed returns false for 256u8 == 0u8, \
         but 256 wraps to 0 in BV(8). This could cause a valid assertion to \
         be incorrectly sent to the solver without the short-circuit (benign \
         but indicates the const-eval is wrong)."
    );
}

// ========================================================================
// ========================================================================
// Algorithm audit: value_fits_in_type Uint{128} negative value bug
// ========================================================================

/// DISCRIMINATING: value_fits_in_type must reject negative values for
/// Uint{128}. Previously, the width >= 128 early return came before the
/// value < 0 check, so value_fits_in_type(-1, Uint{128}) returned true.
/// This allowed try_const_eval_typed to fold comparisons involving negative
/// values typed as u128, producing incorrect results.
#[test]
fn test_value_fits_in_type_rejects_negative_for_uint128() {
    // Build: -1u128 > 0u128 — should NOT be const-folded because -1
    // does not fit in Uint{128}.
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: -1,
            ty: TrustVcType::Uint { width: 128 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Uint { width: 128 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    // Correct: None (defer to solver) because -1 doesn't fit in u128.
    // BUG: Some(true) because -1 as u128 = u128::MAX > 0.
    assert_eq!(
        result, None,
        "SOUNDNESS BUG: try_const_eval_typed should return None for -1u128 > 0u128 \
         because -1 does not fit in Uint{{128}}. The width >= 128 early return must \
         not bypass the negative value check."
    );
}

/// CONTROL: positive values should still be accepted for Uint{128}.
#[test]
fn test_value_fits_in_type_accepts_positive_for_uint128() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 100,
            ty: TrustVcType::Uint { width: 128 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 50,
            ty: TrustVcType::Uint { width: 128 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    assert_eq!(
        result,
        Some(true),
        "Positive values that fit in u128 should be const-evaluated correctly."
    );
}

// ========================================================================
// Algorithm audit: const-eval unsigned detection OR vs AND inconsistency
// ========================================================================

/// DISCRIMINATING: Mixed Int/Uint comparison must NOT use unsigned semantics
/// in const-eval. The encoder (ir_encoder/arith.rs) uses AND semantics
/// (both must be Uint for unsigned comparison). The const-eval path must
/// agree to avoid the const-eval returning a different result than the
/// solver would.
///
/// Scenario: Compare -1i32 < 1u32
/// - OR semantics (BUG): unsigned → -1 as u128 = u128::MAX → MAX < 1 = false
/// - AND semantics (CORRECT): signed → -1 < 1 = true (matching solver)
#[test]
fn test_const_eval_mixed_signedness_uses_and_semantics() {
    // Build: -1i32 < 1u32 — mixed Int/Uint types.
    // value_fits_in_type(-1, Int{32}) = true (fits in signed i32)
    // value_fits_in_type(1, Uint{32}) = true (fits in unsigned u32)
    // With AND semantics: NOT unsigned (Int && Uint = false), use signed → -1 < 1 = true
    // With OR semantics (BUG): unsigned (Int || Uint = true), cast to u128 → MAX < 1 = false
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(TrustVcExpr::IntLit {
            value: -1,
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Uint { width: 32 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    // With AND semantics: signed path, -1 < 1 = Some(true)
    // With OR semantics (BUG): unsigned path, u128::MAX < 1 = Some(false)
    assert_ne!(
        result,
        Some(false),
        "SOUNDNESS BUG: const-eval uses OR semantics for unsigned detection. \
         Mixed Int/Uint comparison -1i32 < 1u32 must use signed comparison \
         (AND semantics, matching ir_encoder/arith.rs #1769), not unsigned."
    );
}

/// CONTROL: Both-unsigned comparison should still use unsigned semantics.
#[test]
fn test_const_eval_both_unsigned_uses_unsigned_semantics() {
    // Build: 5u32 > 3u32 — both Uint, should use unsigned comparison.
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 5,
            ty: TrustVcType::Uint { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 3,
            ty: TrustVcType::Uint { width: 32 },
        }),
    };

    let result = AYEncoder::try_const_eval_typed(&expr, 32);
    assert_eq!(
        result,
        Some(true),
        "Both-unsigned comparison should still be const-evaluated as unsigned."
    );
}

// ========================================================================
// value_fits_in_type boundary tests via try_const_eval_typed
// ========================================================================

/// Signed i8: max value (127) should fit, max+1 (128) should not.
#[test]
fn test_value_fits_signed_i8_boundary() {
    // 127i8 > 0i8 — should const-fold (127 fits in i8)
    let fits = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 127,
            ty: TrustVcType::Int { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 8 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&fits, 32),
        Some(true),
        "127 fits in i8, should const-fold to true"
    );

    // 128i8 > 0i8 — should NOT const-fold (128 overflows i8)
    let overflows = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 128,
            ty: TrustVcType::Int { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 8 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&overflows, 32),
        None,
        "128 does not fit in i8, should defer to solver"
    );
}

/// Signed i8: min value (-128) should fit, min-1 (-129) should not.
#[test]
fn test_value_fits_signed_i8_negative_boundary() {
    // -128i8 < 0i8 — should const-fold (-128 fits in i8)
    let fits = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(TrustVcExpr::IntLit {
            value: -128,
            ty: TrustVcType::Int { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 8 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&fits, 32),
        Some(true),
        "-128 fits in i8, should const-fold to true"
    );

    // -129i8 < 0i8 — should NOT const-fold (-129 underflows i8)
    let underflows = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(TrustVcExpr::IntLit {
            value: -129,
            ty: TrustVcType::Int { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 8 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&underflows, 32),
        None,
        "-129 does not fit in i8, should defer to solver"
    );
}

/// Unsigned u8: max value (255) should fit, max+1 (256) should not.
#[test]
fn test_value_fits_unsigned_u8_boundary() {
    // 255u8 > 254u8 — should const-fold
    let fits = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 255,
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 254,
            ty: TrustVcType::Uint { width: 8 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&fits, 32),
        Some(true),
        "255 fits in u8, should const-fold to true"
    );

    // 256u8 > 0u8 — should NOT const-fold (256 overflows u8)
    let overflows = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 256,
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Uint { width: 8 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&overflows, 32),
        None,
        "256 does not fit in u8, should defer to solver"
    );
}

/// MathInt: all values fit, including extreme i128 values.
#[test]
fn test_value_fits_mathint_always() {
    // i128::MAX > 0 as MathInt — should const-fold
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: i128::MAX,
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::MathInt,
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&expr, 32),
        Some(true),
        "i128::MAX fits in MathInt, should const-fold"
    );

    // i128::MIN < 0 as MathInt — should const-fold
    let neg = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(TrustVcExpr::IntLit {
            value: i128::MIN,
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::MathInt,
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&neg, 32),
        Some(true),
        "i128::MIN fits in MathInt, should const-fold"
    );
}

/// #2149: Mixed default/explicit types. Left is default Int{32} with value 128,
/// right is explicit Int{8}. Context width is 8. The old guard required BOTH
/// operands to be Int{32}, so this case was missed — 128 fits in i32 but wraps
/// to -128 in BV(8), making "128 > 0" false in the actual encoding.
#[test]
fn test_context_width_guard_mixed_default_explicit_types() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 128,
            ty: TrustVcType::Int { width: 32 }, // default unsuffixed
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 8 }, // explicit i8
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&expr, 8),
        None,
        "128 in default Int{{32}} wraps to -128 in context_width=8. Must defer to solver."
    );
}

/// Uint{0} should reject all values (zero-width type has no representable values).
#[test]
fn test_value_fits_uint_width_zero_rejects_all() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Uint { width: 0 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Uint { width: 0 },
        }),
    };
    assert_eq!(
        AYEncoder::try_const_eval_typed(&expr, 32),
        None,
        "Uint{{0}} has no representable values, should defer to solver"
    );
}
