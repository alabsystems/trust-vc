//! Pure helper tests for measure inference utilities.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::decreases_runtime::{infer_measure_type, measure_type_bit_width, sanitize_measure_name};

// ========================================================================
// sanitize_measure_name tests (Issue #1569)
// ========================================================================

#[test]
fn test_sanitize_measure_name_distinct_operators() {
    // x + y and x - y must produce distinct sanitized names (fixes #1569)
    let add = sanitize_measure_name("x + y");
    let sub = sanitize_measure_name("x - y");
    assert_ne!(
        add, sub,
        "x + y and x - y must produce distinct sanitized names, both got: {}",
        add
    );
}

#[test]
fn test_sanitize_measure_name_all_operators_distinct() {
    // All arithmetic operators must produce distinct names
    let add = sanitize_measure_name("x + y");
    let sub = sanitize_measure_name("x - y");
    let mul = sanitize_measure_name("x * y");
    let div = sanitize_measure_name("x / y");
    let modulo = sanitize_measure_name("x % y");

    let names = [&add, &sub, &mul, &div, &modulo];
    for i in 0..names.len() {
        for j in (i + 1)..names.len() {
            assert_ne!(
                names[i], names[j],
                "Operators at index {} and {} collide: both = {}",
                i, j, names[i]
            );
        }
    }
}

#[test]
fn test_sanitize_measure_name_simple_variable() {
    // Simple variable names should pass through unchanged
    assert_eq!(sanitize_measure_name("n"), "n");
    assert_eq!(sanitize_measure_name("count"), "count");
    assert_eq!(sanitize_measure_name("my_var"), "my_var");
}

#[test]
fn test_sanitize_measure_name_spaces_removed() {
    // Spaces should be stripped for compact names
    let with_spaces = sanitize_measure_name("x + y");
    assert!(
        !with_spaces.contains(' '),
        "Sanitized name should not contain spaces"
    );
}

#[test]
fn test_sanitize_measure_name_never_starts_with_a_digit() {
    assert_eq!(sanitize_measure_name("10u64 - i"), "m_10u64_minus_i");
}

// --- measure_type_bit_width tests (#1726) ---

#[test]
fn test_measure_type_bit_width_standard_types() {
    assert_eq!(measure_type_bit_width("u8"), 8);
    assert_eq!(measure_type_bit_width("i8"), 8);
    assert_eq!(measure_type_bit_width("u16"), 16);
    assert_eq!(measure_type_bit_width("i16"), 16);
    assert_eq!(measure_type_bit_width("u32"), 32);
    assert_eq!(measure_type_bit_width("i32"), 32);
    assert_eq!(measure_type_bit_width("u64"), 64);
    assert_eq!(measure_type_bit_width("i64"), 64);
    assert_eq!(measure_type_bit_width("u128"), 128);
    assert_eq!(measure_type_bit_width("i128"), 128);
    assert_eq!(measure_type_bit_width("usize"), crate::ir::pointer_width());
    assert_eq!(measure_type_bit_width("isize"), crate::ir::pointer_width());
    assert_eq!(measure_type_bit_width("bool"), 0);
    assert_eq!(measure_type_bit_width("String"), 0);
}

// --- infer_measure_type tests (#1726) ---

#[test]
fn test_infer_measure_type_simple_variable() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::Uint { width: 64 });
    let ty = infer_measure_type(&ctx, "n").expect("declared var should resolve");
    assert_eq!(ty, &crate::ir::TrustVcType::Uint { width: 64 });
}

#[test]
fn test_infer_measure_type_expression_first_wider() {
    // n: u64, i: u32 — expression "n - i" should return u64 (widest)
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::Uint { width: 64 });
    ctx.declare_var_typed("i", crate::ir::TrustVcType::Uint { width: 32 });
    let ty = infer_measure_type(&ctx, "n - i").expect("declared vars should resolve");
    assert_eq!(ty, &crate::ir::TrustVcType::Uint { width: 64 });
}

#[test]
fn test_infer_measure_type_expression_second_wider() {
    // i: u32, n: u64 — expression "i - n" should still return u64 (widest)
    // This is the #1726 regression: old code returned u32 (first match)
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("i", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("n", crate::ir::TrustVcType::Uint { width: 64 });
    let ty = infer_measure_type(&ctx, "i - n").expect("declared vars should resolve");
    assert_eq!(ty, &crate::ir::TrustVcType::Uint { width: 64 });
}

#[test]
fn test_infer_measure_type_same_width() {
    // Both u32 — any match is fine
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Uint { width: 32 });
    let ty = infer_measure_type(&ctx, "a + b").expect("declared vars should resolve");
    assert_eq!(ty, &crate::ir::TrustVcType::Uint { width: 32 });
}

#[test]
fn test_infer_measure_type_three_vars_widest_wins() {
    // a: u8, b: u32, c: u64 — should return u64
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Uint { width: 8 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("c", crate::ir::TrustVcType::Uint { width: 64 });
    let ty = infer_measure_type(&ctx, "a + b + c").expect("declared vars should resolve");
    assert_eq!(ty, &crate::ir::TrustVcType::Uint { width: 64 });
}

#[test]
fn test_infer_measure_type_no_matching_variable_returns_none() {
    // No declared variables — returns None instead of panicking (#1955).
    let ctx = crate::vc::VerificationContext::new();
    assert!(infer_measure_type(&ctx, "x - y").is_none());
}
