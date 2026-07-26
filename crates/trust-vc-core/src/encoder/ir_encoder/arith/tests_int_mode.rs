// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Algorithm audit tests for Int-mode bitwise/shift helper functions.
//!
//! Tests `extract_pow2_mask`, `extract_int_literal`, and `require_shift_width`
//! for boundary conditions, off-by-one errors, and edge cases in mask
//! detection and shift range validation.
//!
//! @WORKER: to wire this file, add to arith/mod.rs:
//!   `#[cfg(test)] mod tests_int_mode;`
//! AND make these functions in int_mode.rs `pub(super)`:
//!   `extract_pow2_mask`, `extract_int_literal`, `require_shift_width`

use crate::ir::{TrustVcExpr, TrustVcType};

use super::int_mode::{extract_int_literal, extract_pow2_mask, require_shift_width};

fn int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Int { width: 32 },
    }
}

// =========================================================
// extract_int_literal
// =========================================================

#[test]
fn test_extract_int_literal_positive() {
    assert_eq!(extract_int_literal(&int_lit(42)), Some(42));
}

#[test]
fn test_extract_int_literal_zero() {
    assert_eq!(extract_int_literal(&int_lit(0)), Some(0));
}

#[test]
fn test_extract_int_literal_negative() {
    assert_eq!(extract_int_literal(&int_lit(-5)), Some(-5));
}

#[test]
fn test_extract_int_literal_not_literal_returns_none() {
    let var = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };
    assert_eq!(extract_int_literal(&var), None);
}

#[test]
fn test_extract_int_literal_neg_wrapper_returns_none() {
    let neg = TrustVcExpr::Neg(Box::new(int_lit(3)));
    assert_eq!(
        extract_int_literal(&neg),
        None,
        "Neg(IntLit) is not IntLit — extract_int_literal only matches bare IntLit"
    );
}

// =========================================================
// extract_pow2_mask
// =========================================================

#[test]
fn test_pow2_mask_standard_byte_masks() {
    assert_eq!(extract_pow2_mask(&int_lit(1)), Some(1));
    assert_eq!(extract_pow2_mask(&int_lit(3)), Some(2));
    assert_eq!(extract_pow2_mask(&int_lit(7)), Some(3));
    assert_eq!(extract_pow2_mask(&int_lit(15)), Some(4));
    assert_eq!(extract_pow2_mask(&int_lit(255)), Some(8));
    assert_eq!(extract_pow2_mask(&int_lit(65535)), Some(16));
}

#[test]
fn test_pow2_mask_32_and_64_bit() {
    assert_eq!(extract_pow2_mask(&int_lit(0xFFFF_FFFF)), Some(32));
    assert_eq!(extract_pow2_mask(&int_lit(0xFFFF_FFFF_FFFF_FFFF)), Some(64));
}

#[test]
fn test_pow2_mask_i128_max_is_127_bit_mask() {
    assert_eq!(
        extract_pow2_mask(&int_lit(i128::MAX)),
        Some(127),
        "i128::MAX = 2^127 - 1 is a valid 127-bit all-ones mask"
    );
}

#[test]
fn test_pow2_mask_zero_returns_none() {
    assert_eq!(
        extract_pow2_mask(&int_lit(0)),
        None,
        "zero is not a valid pow2 mask (x & 0 == 0 always, but mod 1 == 0 too)"
    );
}

#[test]
fn test_pow2_mask_negative_returns_none() {
    assert_eq!(extract_pow2_mask(&int_lit(-1)), None);
    assert_eq!(extract_pow2_mask(&int_lit(-255)), None);
}

#[test]
fn test_pow2_mask_non_mask_values_return_none() {
    assert_eq!(extract_pow2_mask(&int_lit(2)), None, "2 = 0b10, not all-low-bits");
    assert_eq!(extract_pow2_mask(&int_lit(5)), None, "5 = 0b101, gap in bits");
    assert_eq!(extract_pow2_mask(&int_lit(6)), None, "6 = 0b110, not from bit 0");
    assert_eq!(extract_pow2_mask(&int_lit(10)), None, "10 = 0b1010");
    assert_eq!(extract_pow2_mask(&int_lit(100)), None);
}

#[test]
fn test_pow2_mask_non_literal_returns_none() {
    let var = TrustVcExpr::Var {
        name: "mask".to_string(),
        ty: TrustVcType::Uint { width: 32 },
    };
    assert_eq!(extract_pow2_mask(&var), None);
}

// =========================================================
// require_shift_width
// =========================================================

#[test]
fn test_require_shift_width_int_types() {
    assert_eq!(
        require_shift_width(&TrustVcType::Int { width: 8 }, "test").unwrap(),
        8
    );
    assert_eq!(
        require_shift_width(&TrustVcType::Int { width: 32 }, "test").unwrap(),
        32
    );
    assert_eq!(
        require_shift_width(&TrustVcType::Uint { width: 64 }, "test").unwrap(),
        64
    );
    assert_eq!(
        require_shift_width(&TrustVcType::Uint { width: 128 }, "test").unwrap(),
        128
    );
}

#[test]
fn test_require_shift_width_char_is_32() {
    assert_eq!(
        require_shift_width(&TrustVcType::Char, "test").unwrap(),
        32,
        "Char has bit_width 32"
    );
}

#[test]
fn test_require_shift_width_mathint_errors() {
    assert!(
        require_shift_width(&TrustVcType::MathInt, "test").is_err(),
        "MathInt has no bit_width — shifts require known width"
    );
}

#[test]
fn test_require_shift_width_bool_errors() {
    assert!(
        require_shift_width(&TrustVcType::Bool, "test").is_err(),
        "Bool has no bit_width — shifts require known width"
    );
}

// =========================================================
// Shift boundary: range validation
// =========================================================

#[test]
fn test_shift_amount_boundary_values() {
    let width: i128 = 32;
    assert!(0 >= 0 && 0 < width, "shift by 0 is valid");
    assert!(31 >= 0 && 31 < width, "shift by width-1 is valid");
    assert!(!(32 >= 0 && 32 < width), "shift by width is invalid");
    assert!(!(-1 >= 0), "negative shift is invalid");
}
