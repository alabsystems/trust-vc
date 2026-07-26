// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Width inference, BV range, and generic arg parsing tests.

use super::*;

// ========================================================================
// split_generic_args
// ========================================================================

#[test]
fn test_split_generic_args_simple() {
    assert_eq!(split_generic_args("K, V"), Some(("K", " V")));
}

#[test]
fn test_split_generic_args_nested() {
    assert_eq!(
        split_generic_args("Map<A, B>, C"),
        Some(("Map<A, B>", " C"))
    );
}

#[test]
fn test_split_generic_args_no_comma() {
    assert_eq!(split_generic_args("i32"), None);
}

#[test]
fn test_split_generic_args_deeply_nested() {
    assert_eq!(
        split_generic_args("Map<Seq<i32>, Set<u64>>, bool"),
        Some(("Map<Seq<i32>, Set<u64>>", " bool"))
    );
}

#[test]
fn test_split_generic_args_empty() {
    assert_eq!(split_generic_args(""), None);
}

// ========================================================================
// infer_int_width_from_types
// ========================================================================

#[test]
fn test_infer_int_width_empty() {
    let types: Vec<TrustVcType> = vec![];
    assert_eq!(infer_int_width_from_types(types.iter()), 32);
}

#[test]
fn test_infer_int_width_single() {
    let types = [TrustVcType::Int { width: 64 }];
    assert_eq!(infer_int_width_from_types(types.iter()), 64);
}

#[test]
fn test_infer_int_width_majority() {
    // Two i32 vs one i64 — i32 wins by count
    let types = [
        TrustVcType::Int { width: 32 },
        TrustVcType::Int { width: 32 },
        TrustVcType::Int { width: 64 },
    ];
    assert_eq!(infer_int_width_from_types(types.iter()), 32);
}

#[test]
fn test_infer_int_width_tie_favors_wider() {
    // One i32 and one i64 — tie broken by wider width
    let types = [
        TrustVcType::Int { width: 32 },
        TrustVcType::Int { width: 64 },
    ];
    assert_eq!(infer_int_width_from_types(types.iter()), 64);
}

#[test]
fn test_infer_int_width_skips_bool() {
    // bool has width 0, should be excluded
    let types = [
        TrustVcType::Bool,
        TrustVcType::Bool,
        TrustVcType::Int { width: 32 },
    ];
    assert_eq!(infer_int_width_from_types(types.iter()), 32);
}

#[test]
fn test_infer_int_width_skips_math_int() {
    // MathInt has width 0, should be excluded; i64 is the only BV type
    let types = [TrustVcType::MathInt, TrustVcType::Int { width: 64 }];
    assert_eq!(infer_int_width_from_types(types.iter()), 64);
}

#[test]
fn test_infer_int_width_only_bools() {
    // Only bools: no width > 0, falls back to 32
    let types = [TrustVcType::Bool, TrustVcType::Bool];
    assert_eq!(infer_int_width_from_types(types.iter()), 32);
}

// ========================================================================
// fits_in_signed_bv
// ========================================================================

#[test]
fn test_fits_in_signed_bv_8bit() {
    // i8: [-128, 127]
    assert!(fits_in_signed_bv(-128, 8));
    assert!(fits_in_signed_bv(127, 8));
    assert!(!fits_in_signed_bv(-129, 8));
    assert!(!fits_in_signed_bv(128, 8));
}

#[test]
fn test_fits_in_signed_bv_32bit() {
    // i32: [-2^31, 2^31-1] = [-2147483648, 2147483647]
    assert!(fits_in_signed_bv(-2147483648, 32));
    assert!(fits_in_signed_bv(2147483647, 32));
    assert!(!fits_in_signed_bv(-2147483649, 32));
    assert!(!fits_in_signed_bv(2147483648, 32));
}

#[test]
fn test_fits_in_signed_bv_64bit() {
    // i64: [-2^63, 2^63-1]
    assert!(fits_in_signed_bv(i64::MIN as i128, 64));
    assert!(fits_in_signed_bv(i64::MAX as i128, 64));
    assert!(!fits_in_signed_bv(i64::MIN as i128 - 1, 64));
    assert!(!fits_in_signed_bv(i64::MAX as i128 + 1, 64));
}

#[test]
fn test_fits_in_signed_bv_width_zero() {
    assert!(!fits_in_signed_bv(0, 0));
}

#[test]
fn test_fits_in_signed_bv_width_128() {
    assert!(fits_in_signed_bv(i128::MIN, 128));
    assert!(fits_in_signed_bv(i128::MAX, 128));
    assert!(fits_in_signed_bv(0, 128));
}

#[test]
fn test_fits_in_signed_bv_width_greater_than_128() {
    assert!(fits_in_signed_bv(i128::MAX, 256));
}

// ========================================================================
// fits_in_bv (signed OR unsigned range)
// ========================================================================

#[test]
fn test_fits_in_bv_8bit_signed_range() {
    assert!(fits_in_bv(-128, 8));
    assert!(fits_in_bv(127, 8));
}

#[test]
fn test_fits_in_bv_8bit_unsigned_range() {
    // Unsigned range [128, 255] also accepted (#1651/#1673 fix)
    assert!(fits_in_bv(128, 8));
    assert!(fits_in_bv(255, 8));
    assert!(!fits_in_bv(256, 8));
}

#[test]
fn test_fits_in_bv_8bit_out_of_range() {
    assert!(!fits_in_bv(-129, 8));
    assert!(!fits_in_bv(256, 8));
}

#[test]
fn test_fits_in_bv_width_zero() {
    assert!(!fits_in_bv(0, 0));
}

#[test]
fn test_fits_in_bv_32bit_boundaries() {
    // u32::MAX = 4294967295 fits unsigned
    assert!(fits_in_bv(4294967295, 32));
    assert!(!fits_in_bv(4294967296, 32));
    // i32::MIN = -2147483648 fits signed
    assert!(fits_in_bv(-2147483648, 32));
    assert!(!fits_in_bv(-2147483649, 32));
}

#[test]
fn test_fits_in_bv_u64_max() {
    assert!(fits_in_bv(u64::MAX as i128, 64));
    assert!(!fits_in_bv(u64::MAX as i128 + 1, 64));
}

// ========================================================================
// min_bv_width_for_value
// ========================================================================

#[test]
fn test_min_bv_width_for_value_small() {
    assert_eq!(min_bv_width_for_value(0), 8);
    assert_eq!(min_bv_width_for_value(127), 8); // i8::MAX
    assert_eq!(min_bv_width_for_value(-128), 8); // i8::MIN
}

#[test]
fn test_min_bv_width_for_value_unsigned_8bit() {
    // #1872: values in unsigned-only u8 range [128, 255] fit in BV8
    assert_eq!(min_bv_width_for_value(128), 8);
    assert_eq!(min_bv_width_for_value(255), 8); // u8::MAX
    assert_eq!(min_bv_width_for_value(256), 16); // first value needing BV16
}

#[test]
fn test_min_bv_width_for_value_needs_16() {
    assert_eq!(min_bv_width_for_value(-129), 16); // below i8::MIN
    assert_eq!(min_bv_width_for_value(256), 16); // above u8::MAX
}

#[test]
fn test_min_bv_width_for_value_unsigned_16bit() {
    // #1872: values in unsigned-only u16 range [32768, 65535] fit in BV16
    assert_eq!(min_bv_width_for_value(32768), 16); // i16::MAX + 1
    assert_eq!(min_bv_width_for_value(65535), 16); // u16::MAX
    assert_eq!(min_bv_width_for_value(65536), 32); // first value needing BV32
}

#[test]
fn test_min_bv_width_for_value_needs_32() {
    assert_eq!(min_bv_width_for_value(-32769), 32); // below i16::MIN
    assert_eq!(min_bv_width_for_value(65536), 32); // above u16::MAX
}

#[test]
fn test_min_bv_width_for_value_unsigned_32bit() {
    // #1872: values in unsigned-only u32 range [2^31, 2^32 - 1] fit in BV32
    assert_eq!(min_bv_width_for_value(2147483648), 32); // i32::MAX + 1
    assert_eq!(min_bv_width_for_value(4294967295), 32); // u32::MAX
    assert_eq!(min_bv_width_for_value(4294967296), 64); // first value needing BV64
}

#[test]
fn test_min_bv_width_for_value_needs_64() {
    assert_eq!(min_bv_width_for_value(-2147483649), 64); // below i32::MIN
    assert_eq!(min_bv_width_for_value(4294967296), 64); // above u32::MAX
}

#[test]
fn test_min_bv_width_for_value_unsigned_64bit() {
    // #1872: values in unsigned-only u64 range [2^63, 2^64 - 1] fit in BV64
    assert_eq!(min_bv_width_for_value(i64::MAX as i128 + 1), 64); // 2^63
    assert_eq!(min_bv_width_for_value(u64::MAX as i128), 64); // 2^64 - 1
    assert_eq!(min_bv_width_for_value(u64::MAX as i128 + 1), 128); // first needing BV128
}

#[test]
fn test_min_bv_width_for_value_needs_128() {
    assert_eq!(min_bv_width_for_value(u64::MAX as i128 + 1), 128); // above u64::MAX
    assert_eq!(min_bv_width_for_value(i64::MIN as i128 - 1), 128); // below i64::MIN
}

#[test]
fn test_min_bv_width_for_value_i128_extremes() {
    assert_eq!(min_bv_width_for_value(i128::MAX), 128);
    assert_eq!(min_bv_width_for_value(i128::MIN), 128);
}

// ========================================================================
// min_signed_bv_width_for_value (casts-bitvec literal-width soundness)
// ========================================================================
//
// A SIGNED literal must be encoded at a width whose SIGNED range holds the
// value; otherwise it wraps into a different (negative) value. This is the
// signedness-correct companion to `min_bv_width_for_value`: where the latter
// keeps `200` at BV8 (it fits the UNSIGNED byte range), the signed variant
// must widen `200` to BV16 so the value `200` is preserved, not aliased to
// `-56`.

/// DISCRIMINATING: a positive in-signed-range value keeps the narrow width.
#[test]
fn test_min_signed_bv_width_in_signed_range() {
    assert_eq!(min_signed_bv_width_for_value(0), 8);
    assert_eq!(min_signed_bv_width_for_value(127), 8); // i8::MAX
    assert_eq!(min_signed_bv_width_for_value(-128), 8); // i8::MIN
}

/// DISCRIMINATING: a positive value in the UNSIGNED-only byte range
/// `[128, 255]` does NOT fit signed BV8 and must widen to BV16 (where the
/// signed range `[-32768, 32767]` holds it) — this is the fix that prevents
/// `200i8` from aliasing `-56`.
#[test]
fn test_min_signed_bv_width_unsigned_only_byte_range_widens() {
    assert_eq!(min_signed_bv_width_for_value(128), 16); // i8::MAX + 1
    assert_eq!(min_signed_bv_width_for_value(200), 16); // the cluster witness
    assert_eq!(min_signed_bv_width_for_value(255), 16); // u8::MAX
                                                        // Contrast with the signed-OR-unsigned helper, which keeps these at BV8.
    assert_eq!(min_bv_width_for_value(200), 8);
}

/// DISCRIMINATING: boundary at each width — `2^(w-1)` widens, `2^(w-1) - 1`
/// stays.
#[test]
fn test_min_signed_bv_width_boundaries() {
    assert_eq!(min_signed_bv_width_for_value(32767), 16); // i16::MAX
    assert_eq!(min_signed_bv_width_for_value(32768), 32); // i16::MAX + 1
    assert_eq!(min_signed_bv_width_for_value(65535), 32); // u16::MAX
    assert_eq!(min_signed_bv_width_for_value(2147483647), 32); // i32::MAX
    assert_eq!(min_signed_bv_width_for_value(2147483648), 64); // i32::MAX + 1
    assert_eq!(min_signed_bv_width_for_value(i64::MAX as i128), 64);
    assert_eq!(min_signed_bv_width_for_value(i64::MAX as i128 + 1), 128);
}

/// DISCRIMINATING: negative values fit the signed range directly (no widening
/// beyond what the magnitude requires).
#[test]
fn test_min_signed_bv_width_negative() {
    assert_eq!(min_signed_bv_width_for_value(-1), 8);
    assert_eq!(min_signed_bv_width_for_value(-129), 16); // below i8::MIN
    assert_eq!(min_signed_bv_width_for_value(i128::MIN), 128);
}

/// The chosen width's signed range MUST actually hold the value (the soundness
/// invariant the encoder relies on).
#[test]
fn test_min_signed_bv_width_result_is_signed_fitting() {
    for v in [128i128, 200, 255, 256, 32768, -129, 2147483648] {
        let w = min_signed_bv_width_for_value(v);
        assert!(
            fits_in_signed_bv(v, w),
            "min_signed_bv_width_for_value({v}) = {w} must satisfy fits_in_signed_bv"
        );
    }
}
