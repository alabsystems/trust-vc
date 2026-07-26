//! Missing operand metadata and non-BV `ty` fallback tests for checked
//! and saturating arithmetic (add and sub paths).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Merged from ir_soundness_2100.rs and ir_soundness_2100_sub_fallback.rs
//! into a single submodule (#2145).

use super::*;

// ========================================================================
// Missing operand metadata fallback (add paths)
// ========================================================================

/// DISCRIMINATING: checked_add must derive signedness from WrappingArith `ty`
/// even when operand term_width metadata is missing.
///
/// Pre-fix fallback used metadata-only inference and defaulted to signed when
/// metadata was absent, emitting an unsigned-underflow check that should not
/// exist for `u8.checked_add`.
#[test]
fn test_2100_checked_add_uses_ty_when_operand_metadata_missing() {
    let mut env = QuantifierTestEnv::new();
    let u8 = TrustVcType::Uint { width: 8 };

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types.insert("x".to_string(), u8.clone());
    env.var_types.insert("y".to_string(), u8.clone());

    let mut parser = env.parser_with_overflow();

    // Simulate missing width metadata on opaque operands.
    parser.term_widths.remove(&x);
    parser.term_widths.remove(&y);

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Checked,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8.clone(),
        }),
        ty: u8.clone(),
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2100: checked_add with missing operand metadata must still encode via ty fallback: {:?}",
        result.err()
    );

    let checks = std::mem::take(&mut parser.overflow_checks);
    assert!(
        checks.iter().any(|(name, _)| name.contains("checked_add")),
        "#2100: checked_add must emit overflow check, got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
    assert!(
        !checks.iter().any(|(name, _)| name.contains("underflow")),
        "#2100 SOUNDNESS: u8.checked_add emitted underflow check with missing metadata, got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// DISCRIMINATING: saturating_add must clamp using WrappingArith `ty` when
/// operand term metadata is missing.
///
/// Pre-fix behavior without width metadata could return an unclamped raw
/// BV result (wrapping semantics) instead of saturating semantics.
#[test]
fn test_2100_saturating_add_uses_ty_when_operand_metadata_missing() {
    let mut env = QuantifierTestEnv::new();
    let u8 = TrustVcType::Uint { width: 8 };

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types.insert("x".to_string(), u8.clone());
    env.var_types.insert("y".to_string(), u8.clone());

    let mut parser = env.parser();

    // Simulate missing width metadata on opaque operands.
    parser.term_widths.remove(&x);
    parser.term_widths.remove(&y);

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8.clone(),
        }),
        ty: u8,
    };

    let sat_result = parser
        .encode_trust_vc_expr(&expr)
        .expect("#2100: saturating_add with missing operand metadata must encode");
    drop(parser);

    let val_255 = env.solver.try_bv_const(255i64, 8).unwrap();
    let val_1 = env.solver.try_bv_const(1i64, 8).unwrap();
    let x_is_255 = env.solver.try_eq(x, val_255).unwrap();
    let y_is_1 = env.solver.try_eq(y, val_1).unwrap();
    let boundary = env.solver.try_and(x_is_255, y_is_1).unwrap();
    let result_is_255 = env.solver.try_eq(sat_result, val_255).unwrap();
    let should_hold = env.solver.try_implies(boundary, result_is_255).unwrap();

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(should_hold).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2100 SOUNDNESS: saturating_add(255, 1) with missing metadata must clamp to 255, got: {:?}",
        sat
    );
}

// ========================================================================
// Non-BV `ty` fallback (add paths)
// ========================================================================

/// DISCRIMINATING: when `WrappingArith.ty` is non-BV, checked arithmetic must
/// fall back to operand metadata (if available) instead of defaulting signed.
#[test]
fn test_2100_checked_add_non_bv_ty_uses_operand_metadata_fallback() {
    let mut env = QuantifierTestEnv::new();
    let u8 = TrustVcType::Uint { width: 8 };

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types.insert("x".to_string(), u8.clone());
    env.var_types.insert("y".to_string(), u8.clone());

    let mut parser = env.parser_with_overflow();
    assert_eq!(
        parser.term_widths.get(&x).copied(),
        Some((8, false)),
        "test setup: x should have pre-populated u8 metadata"
    );
    assert_eq!(
        parser.term_widths.get(&y).copied(),
        Some((8, false)),
        "test setup: y should have pre-populated u8 metadata"
    );

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Checked,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8.clone(),
        }),
        // Non-BV type: forces #2100 fallback path from ty -> operand metadata.
        ty: TrustVcType::Opaque("legacy-u8".to_string()),
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2100: checked_add with non-BV ty should encode via operand metadata fallback: {:?}",
        result.err()
    );

    let checks = std::mem::take(&mut parser.overflow_checks);
    assert!(
        checks.iter().any(|(name, _)| name.contains("checked_add")),
        "#2100: checked_add must emit overflow check, got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
    assert!(
        !checks.iter().any(|(name, _)| name.contains("underflow")),
        "#2100 SOUNDNESS: non-BV ty fallback used signed defaults instead of operand metadata: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// DISCRIMINATING: when `WrappingArith.ty` is non-BV, saturating arithmetic
/// must still clamp via operand metadata fallback when metadata exists.
#[test]
fn test_2100_saturating_add_non_bv_ty_uses_operand_metadata_fallback() {
    let mut env = QuantifierTestEnv::new();
    let u8 = TrustVcType::Uint { width: 8 };

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types.insert("x".to_string(), u8.clone());
    env.var_types.insert("y".to_string(), u8.clone());

    let mut parser = env.parser();
    assert_eq!(
        parser.term_widths.get(&x).copied(),
        Some((8, false)),
        "test setup: x should have pre-populated u8 metadata"
    );
    assert_eq!(
        parser.term_widths.get(&y).copied(),
        Some((8, false)),
        "test setup: y should have pre-populated u8 metadata"
    );

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8.clone(),
        }),
        // Non-BV type: forces #2100 fallback path from ty -> operand metadata.
        ty: TrustVcType::Opaque("legacy-u8".to_string()),
    };

    let sat_result = parser
        .encode_trust_vc_expr(&expr)
        .expect("#2100: saturating_add with non-BV ty should encode via metadata fallback");
    drop(parser);

    let val_255 = env.solver.try_bv_const(255i64, 8).unwrap();
    let val_1 = env.solver.try_bv_const(1i64, 8).unwrap();
    let x_is_255 = env.solver.try_eq(x, val_255).unwrap();
    let y_is_1 = env.solver.try_eq(y, val_1).unwrap();
    let boundary = env.solver.try_and(x_is_255, y_is_1).unwrap();
    let result_is_255 = env.solver.try_eq(sat_result, val_255).unwrap();
    let should_hold = env.solver.try_implies(boundary, result_is_255).unwrap();

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(should_hold).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2100 SOUNDNESS: non-BV ty fallback failed to clamp saturating_add(255,1) to 255, got: {:?}",
        sat
    );
}

// ========================================================================
// Non-BV `ty` fallback (sub paths)
// ========================================================================

/// DISCRIMINATING: when `WrappingArith.ty` is non-BV, checked subtraction must
/// use operand metadata fallback and preserve unsigned semantics.
#[test]
fn test_2100_checked_sub_non_bv_ty_uses_operand_metadata_fallback() {
    let mut env = QuantifierTestEnv::new();
    let u8 = TrustVcType::Uint { width: 8 };

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types.insert("x".to_string(), u8.clone());
    env.var_types.insert("y".to_string(), u8.clone());

    let mut parser = env.parser_with_overflow();
    assert_eq!(
        parser.term_widths.get(&x).copied(),
        Some((8, false)),
        "test setup: x should have pre-populated u8 metadata"
    );
    assert_eq!(
        parser.term_widths.get(&y).copied(),
        Some((8, false)),
        "test setup: y should have pre-populated u8 metadata"
    );

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Checked,
        op: ArithOp::Sub,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8.clone(),
        }),
        // Non-BV type: forces #2100 fallback path from ty -> operand metadata.
        ty: TrustVcType::Opaque("legacy-u8".to_string()),
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2100: checked_sub with non-BV ty should encode via operand metadata fallback: {:?}",
        result.err()
    );

    let checks = std::mem::take(&mut parser.overflow_checks);
    assert!(
        checks
            .iter()
            .any(|(name, _)| name.contains("checked_sub underflow")),
        "#2100: checked_sub must emit underflow check, got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
    assert!(
        !checks
            .iter()
            .any(|(name, _)| name.contains("checked_sub overflow")),
        "#2100 SOUNDNESS: non-BV ty fallback used signed defaults for checked_sub: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// DISCRIMINATING: when `WrappingArith.ty` is non-BV, saturating subtraction
/// must still clamp via operand metadata fallback when metadata exists.
#[test]
fn test_2100_saturating_sub_non_bv_ty_uses_operand_metadata_fallback() {
    let mut env = QuantifierTestEnv::new();
    let u8 = TrustVcType::Uint { width: 8 };

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    let y = env.solver.declare_const("y", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.variables.insert("y".to_string(), y);
    env.var_types.insert("x".to_string(), u8.clone());
    env.var_types.insert("y".to_string(), u8.clone());

    let mut parser = env.parser();
    assert_eq!(
        parser.term_widths.get(&x).copied(),
        Some((8, false)),
        "test setup: x should have pre-populated u8 metadata"
    );
    assert_eq!(
        parser.term_widths.get(&y).copied(),
        Some((8, false)),
        "test setup: y should have pre-populated u8 metadata"
    );

    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Sub,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: u8.clone(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "y".to_string(),
            ty: u8.clone(),
        }),
        // Non-BV type: forces #2100 fallback path from ty -> operand metadata.
        ty: TrustVcType::Opaque("legacy-u8".to_string()),
    };

    let sat_result = parser
        .encode_trust_vc_expr(&expr)
        .expect("#2100: saturating_sub with non-BV ty should encode via metadata fallback");
    drop(parser);

    let zero = env.solver.try_bv_const(0i64, 8).unwrap();
    let one = env.solver.try_bv_const(1i64, 8).unwrap();
    let x_is_zero = env.solver.try_eq(x, zero).unwrap();
    let y_is_one = env.solver.try_eq(y, one).unwrap();
    let boundary = env.solver.try_and(x_is_zero, y_is_one).unwrap();
    let result_is_zero = env.solver.try_eq(sat_result, zero).unwrap();
    let should_hold = env.solver.try_implies(boundary, result_is_zero).unwrap();

    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(should_hold).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2100 SOUNDNESS: non-BV ty fallback failed to clamp saturating_sub(0,1) to 0, got: {:?}",
        sat
    );
}
