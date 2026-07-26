//! Mixed unsigned type comparison tests (#1475).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests verify that comparisons between unsigned integer types of
//! different widths use zero-extension (not sign-extension) to widen the
//! narrower operand via `coerce_bv_widths`.
//!
//! Discriminating property: for unsigned values with the high bit set,
//! zero-extension preserves the unsigned value while sign-extension
//! produces a much larger bit pattern. Comparisons using the wrong
//! extension produce incorrect results.
//!
//! Coverage gap: `unsigned_arith_signedness.rs` tests same-width signedness
//! discrimination (bvudiv vs bvsdiv). This file tests cross-width unsigned
//! comparisons where `coerce_bv_widths` must zero-extend.

use super::*;

fn uint_var(name: &str, width: u32) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::Var {
        name: name.to_string(),
        ty: crate::ir::TrustVcType::Uint { width },
    }
}

/// Encode a mixed-width unsigned comparison, constrain operands to concrete
/// values, and return the satisfiability of the comparison.
///
/// Sets up two unsigned BV variables (`a` at `a_width`, `b` at `b_width`),
/// encodes `a <op> b`, constrains them to `a_val` and `b_val`, asserts the
/// comparison result, and returns `check_sat()`.
fn mixed_unsigned_cmp_sat(
    op: crate::ir_expr::CompareOp,
    a_width: u32,
    b_width: u32,
    a_val: i64,
    b_val: i64,
) -> SolveResult {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let a = solver.declare_const("a", Sort::bitvec(a_width));
    variables.insert("a".to_string(), a);
    var_types.insert(
        "a".to_string(),
        crate::ir::TrustVcType::Uint { width: a_width },
    );

    let b = solver.declare_const("b", Sort::bitvec(b_width));
    variables.insert("b".to_string(), b);
    var_types.insert(
        "b".to_string(),
        crate::ir::TrustVcType::Uint { width: b_width },
    );

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = crate::ir_expr::TrustVcExpr::Compare {
        op,
        left: Box::new(uint_var("a", a_width)),
        right: Box::new(uint_var("b", b_width)),
    };
    let cmp_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("mixed-width unsigned comparison should encode");

    let a_bv = parser.solver.try_bv_const(a_val, a_width).unwrap();
    let b_bv = parser.solver.try_bv_const(b_val, b_width).unwrap();
    let eq_a = parser.solver.try_eq(a, a_bv).unwrap();
    let eq_b = parser.solver.try_eq(b, b_bv).unwrap();
    parser.solver.try_assert_term(eq_a).unwrap();
    parser.solver.try_assert_term(eq_b).unwrap();
    parser.solver.try_assert_term(cmp_term).unwrap();

    parser.solver.try_check_sat().unwrap().into_inner()
}

// ========================================================================
// u8 vs u16 comparisons
// ========================================================================

/// DISCRIMINATING: u8(200) < u16(300) must be true (zero-extension).
///
/// u8 value 200 = 0xC8 (high bit set).
///   Zero-ext to u16: 0x00C8 (200) → 200 < 300 = true ✓
///   Sign-ext to u16: 0xFFC8 (65480) → 65480 < 300 = false ✗
///
/// If `coerce_bv_widths` incorrectly sign-extends the u8 operand,
/// the comparison result flips from true to false.
#[test]
fn test_mixed_u8_u16_lt_high_bit_discriminates_extension() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Lt, 8, 16, 200, 300),
        SolveResult::Sat,
        "u8(200) < u16(300) must be Sat. If sign-extension is used, \
         0xFFC8 (65480) < 300 is false and this becomes Unsat (#1475)"
    );
}

/// DISCRIMINATING: u8(200) == u16(200) must be true (zero-extension).
///
/// u8 value 200 = 0xC8, zero-ext to u16 = 0x00C8 (200) → equal ✓
/// With sign-ext: 0xFFC8 (65480) ≠ 200 → not equal ✗
#[test]
fn test_mixed_u8_u16_eq_high_bit_discriminates_extension() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Eq, 8, 16, 200, 200),
        SolveResult::Sat,
        "u8(200) == u16(200) must be Sat. Zero-ext: 0x00C8 == 0x00C8. \
         Sign-ext: 0xFFC8 != 0x00C8 would make this Unsat (#1475)"
    );
}

/// CONTROL: u8(50) < u16(100) verifies regardless of extension method.
///
/// Value 50 = 0x32 (high bit clear). Both zero-ext and sign-ext produce
/// 0x0032, so the comparison result is the same either way.
#[test]
fn test_mixed_u8_u16_lt_safe_values_control() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Lt, 8, 16, 50, 100),
        SolveResult::Sat,
        "u8(50) < u16(100) should always be Sat (control test)"
    );
}

// ========================================================================
// u16 vs u32 comparisons
// ========================================================================

/// DISCRIMINATING: u16(40000) < u32(50000) must be true (zero-extension).
///
/// u16 value 40000 = 0x9C40 (high bit set).
///   Zero-ext to u32: 0x00009C40 (40000) → 40000 < 50000 = true ✓
///   Sign-ext to u32: 0xFFFF9C40 (4294941760) → 4294941760 < 50000 = false ✗
#[test]
fn test_mixed_u16_u32_lt_high_bit_discriminates_extension() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Lt, 16, 32, 40000, 50000),
        SolveResult::Sat,
        "u16(40000) < u32(50000) must be Sat. Sign-ext would produce \
         0xFFFF9C40 (4294941760) making this Unsat (#1475)"
    );
}

/// DISCRIMINATING: u16(40000) == u32(40000) must be true (zero-extension).
///
/// u16 value 40000 = 0x9C40, zero-ext to u32 = 0x00009C40 (40000) → equal ✓
/// Sign-ext: 0xFFFF9C40 (4294941760) ≠ 40000 → not equal ✗
#[test]
fn test_mixed_u16_u32_eq_high_bit_discriminates_extension() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Eq, 16, 32, 40000, 40000),
        SolveResult::Sat,
        "u16(40000) == u32(40000) must be Sat. Sign-ext: 0xFFFF9C40 != 0x00009C40 (#1475)"
    );
}

/// CONTROL: u16(1000) <= u32(2000) verifies regardless of extension.
///
/// Value 1000 = 0x03E8 (high bit clear). Extension method doesn't matter.
#[test]
fn test_mixed_u16_u32_le_safe_values_control() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Le, 16, 32, 1000, 2000),
        SolveResult::Sat,
        "u16(1000) <= u32(2000) should always be Sat (control test)"
    );
}

// ========================================================================
// u32 vs u64 comparisons
// ========================================================================

/// DISCRIMINATING: u32(3_000_000_000) < u64(4_000_000_000) must be true.
///
/// u32 value 3_000_000_000 = 0xB2D05E00 (high bit set).
///   Zero-ext to u64: 0x00000000_B2D05E00 (3B) → 3B < 4B = true ✓
///   Sign-ext to u64: 0xFFFFFFFF_B2D05E00 (huge) → huge < 4B = false ✗
#[test]
fn test_mixed_u32_u64_lt_high_bit_discriminates_extension() {
    assert_eq!(
        mixed_unsigned_cmp_sat(
            crate::ir_expr::CompareOp::Lt,
            32,
            64,
            3_000_000_000,
            4_000_000_000,
        ),
        SolveResult::Sat,
        "u32(3B) < u64(4B) must be Sat. Sign-ext would produce \
         0xFFFFFFFF_B2D05E00 making this Unsat (#1475)"
    );
}

/// DISCRIMINATING: u32(3_000_000_000) == u64(3_000_000_000) must be true.
///
/// Zero-ext: 0x00000000_B2D05E00 == 0x00000000_B2D05E00 → true ✓
/// Sign-ext: 0xFFFFFFFF_B2D05E00 ≠ 0x00000000_B2D05E00 → false ✗
#[test]
fn test_mixed_u32_u64_eq_high_bit_discriminates_extension() {
    assert_eq!(
        mixed_unsigned_cmp_sat(
            crate::ir_expr::CompareOp::Eq,
            32,
            64,
            3_000_000_000,
            3_000_000_000,
        ),
        SolveResult::Sat,
        "u32(3B) == u64(3B) must be Sat. Sign-ext would make the widened \
         u32 value differ from the u64 value (#1475)"
    );
}

/// CONTROL: u32(100) < u64(200) verifies regardless of extension.
///
/// Value 100 = 0x00000064 (high bit clear). Extension method doesn't matter.
#[test]
fn test_mixed_u32_u64_lt_safe_values_control() {
    assert_eq!(
        mixed_unsigned_cmp_sat(crate::ir_expr::CompareOp::Lt, 32, 64, 100, 200),
        SolveResult::Sat,
        "u32(100) < u64(200) should always be Sat (control test)"
    );
}
