//! Unit tests for model_render.rs helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn bv(value: i64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: BigInt::from(value),
        width,
    }
}

#[test]
fn test_render_model_value_seq_element() {
    // render_model_value used by Seq/Set/Map element rendering
    let result = render_model_value(&bv(42, 32), &TrustVcType::Int { width: 32 });
    assert_eq!(result, "42");
}

#[test]
fn test_bv_to_signed_positive() {
    assert_eq!(bv_to_signed(&BigInt::from(42), 32), BigInt::from(42));
}

#[test]
fn test_bv_to_signed_negative() {
    // -1 in 32-bit two's complement = 0xFFFFFFFF = 4294967295
    let neg_one = BigInt::from(0xFFFFFFFFu64);
    assert_eq!(bv_to_signed(&neg_one, 32), BigInt::from(-1));
}

#[test]
fn test_bv_to_signed_min() {
    // -128 in 8-bit = 0x80 = 128
    assert_eq!(bv_to_signed(&BigInt::from(128), 8), BigInt::from(-128));
}

#[test]
fn test_bv_to_unsigned_basic() {
    assert_eq!(bv_to_unsigned(&BigInt::from(255), 8), BigInt::from(255));
}

#[test]
fn test_bv_to_unsigned_wraps() {
    // 256 in 8-bit wraps to 0
    assert_eq!(bv_to_unsigned(&BigInt::from(256), 8), BigInt::from(0));
}

#[test]
fn test_render_model_value_bool() {
    assert_eq!(
        render_model_value(&ModelValue::Bool(true), &TrustVcType::Bool),
        "true"
    );
    assert_eq!(
        render_model_value(&ModelValue::Bool(false), &TrustVcType::Bool),
        "false"
    );
}

#[test]
fn test_render_model_value_unit() {
    assert_eq!(
        render_model_value(&ModelValue::Bool(true), &TrustVcType::Unit),
        "()"
    );
}

#[test]
fn test_render_model_value_signed_int() {
    let neg = bv(0xFFFFFFFF, 32);
    assert_eq!(
        render_model_value(&neg, &TrustVcType::Int { width: 32 }),
        "-1"
    );
}

#[test]
fn test_render_model_value_unsigned_int() {
    let val = bv(255, 8);
    assert_eq!(
        render_model_value(&val, &TrustVcType::Uint { width: 8 }),
        "255"
    );
}

#[test]
fn test_render_model_value_math_int() {
    let val = ModelValue::Int(BigInt::from(9999));
    assert_eq!(render_model_value(&val, &TrustVcType::MathInt), "9999");
}

#[test]
fn test_render_model_value_char() {
    let val = bv(65, 32); // 'A'
    assert_eq!(render_model_value(&val, &TrustVcType::Char), "'A'");
}

#[test]
fn test_render_model_value_char_control() {
    let val = bv(0, 32); // NUL
    assert_eq!(render_model_value(&val, &TrustVcType::Char), "'\\u{0}'");
}

#[test]
fn test_model_values_equal_bv() {
    assert!(model_values_equal(&bv(42, 32), &bv(42, 32)));
    assert!(!model_values_equal(&bv(42, 32), &bv(43, 32)));
    assert!(!model_values_equal(&bv(42, 32), &bv(42, 64)));
}

#[test]
fn test_model_values_equal_bool() {
    assert!(model_values_equal(
        &ModelValue::Bool(true),
        &ModelValue::Bool(true)
    ));
    assert!(!model_values_equal(
        &ModelValue::Bool(true),
        &ModelValue::Bool(false)
    ));
}

#[test]
fn test_model_values_equal_cross_type() {
    assert!(!model_values_equal(&ModelValue::Bool(true), &bv(1, 1)));
}

#[test]
fn test_bv_to_signed_zero_width() {
    assert_eq!(bv_to_signed(&BigInt::from(5), 0), BigInt::from(0));
}

#[test]
fn test_bv_to_unsigned_zero_width() {
    assert_eq!(bv_to_unsigned(&BigInt::from(5), 0), BigInt::from(0));
}

#[test]
fn test_trust_vc_type_display_name() {
    assert_eq!(trust_vc_type_display_name(&TrustVcType::Bool), "bool");
    assert_eq!(
        trust_vc_type_display_name(&TrustVcType::Int { width: 32 }),
        "i32"
    );
    assert_eq!(
        trust_vc_type_display_name(&TrustVcType::Uint { width: 64 }),
        "u64"
    );
    assert_eq!(trust_vc_type_display_name(&TrustVcType::MathInt), "int");
    assert_eq!(trust_vc_type_display_name(&TrustVcType::Char), "char");
    assert_eq!(
        trust_vc_type_display_name(&TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 32 }))),
        "Seq<u32>"
    );
    assert_eq!(
        trust_vc_type_display_name(&TrustVcType::Map(
            Box::new(TrustVcType::String),
            Box::new(TrustVcType::Int { width: 64 })
        )),
        "Map<String, i64>"
    );
}
