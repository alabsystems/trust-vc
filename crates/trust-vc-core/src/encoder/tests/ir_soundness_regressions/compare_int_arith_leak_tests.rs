// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for compare.rs use_int_arithmetic error-path state leak.
//!
//! compare.rs:238-244 saves and restores `use_int_arithmetic` around BV-mode
//! comparison encoding. If either `encode_expr_with_integer_hint` call fails
//! with `?`, the restore on line 244 is skipped, permanently flipping the
//! encoder to BV mode. Same class as #2511 (match_int_arith_leak).
//!
//! The fix is an RAII guard (or explicit restore on the error path) so that
//! `use_int_arithmetic` is always restored regardless of how the encoding
//! exits.
//!
//! @WORKER: to wire this file, add to ir_soundness_regressions/mod.rs:
//!   `mod compare_int_arith_leak_tests;`
//! AND fix compare.rs:238-244 to restore use_int_arithmetic on the error path
//! (RAII guard or explicit catch). The error-path test WILL FAIL until the
//! fix is applied.

use super::*;

// ========================================================================
// Compare BV toggle: success path (should already pass)
// ========================================================================

/// CONTROL: compare encoding with valid BV operands in an all-Int context
/// should preserve use_int_arithmetic. This mirrors the match_int_arith_leak
/// success-path test but exercises the compare.rs BV toggle path.
///
/// Exercises compare.rs:229-244 use_bv_compare path.
#[test]
fn test_compare_bv_toggle_preserves_int_mode_on_success() {
    let mut env = QuantifierTestEnv::new();

    // MathInt variable — use_int_arithmetic starts true (no term_widths)
    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "precondition: all-MathInt context should start with use_int_arithmetic = true"
    );

    // Encode a comparison between two BV-typed literals.
    // Both operands have bit_width → both_explicit_bv = true.
    // With use_int_arithmetic = true and quantifier_depth = 0,
    // use_bv_compare should activate.
    let compare_expr = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 2,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let result = parser.encode_trust_vc_expr(&compare_expr);
    assert!(
        result.is_ok(),
        "BV compare should succeed: {:?}",
        result.err()
    );

    // use_int_arithmetic must be restored after successful compare encoding
    assert!(
        parser.use_int_arithmetic,
        "use_int_arithmetic must be restored after successful BV compare encoding"
    );
}

// ========================================================================
// Compare BV toggle: error path (#2511 class — RAII guard needed)
// ========================================================================

/// DISCRIMINATING: compare encoding error must NOT leak use_int_arithmetic.
///
/// When both compare operands have BV types in an int-mode context,
/// compare.rs:238-244 temporarily sets use_int_arithmetic = false.
/// If encoding fails (e.g., undefined variable), the `?` operator on
/// line 242 propagates the error WITHOUT restoring the flag.
///
/// This test WILL FAIL until the RAII guard is applied to compare.rs.
/// When it passes, the fix is correct.
#[test]
fn test_compare_bv_toggle_restores_int_mode_on_encoding_error() {
    let mut env = QuantifierTestEnv::new();

    // MathInt variable — use_int_arithmetic starts true
    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "precondition: use_int_arithmetic = true in all-MathInt context"
    );

    // Compare with both sides having BV types (Int{32}) triggers use_bv_compare.
    // Left side references an undefined variable to force an encoding error.
    // The error propagates via ? on compare.rs:242, skipping restore on :244.
    let compare_expr = TrustVcExpr::Compare {
        op: CompareOp::Lt,
        left: Box::new(TrustVcExpr::Var {
            name: "undefined_bv_var_for_leak_test".into(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let result = parser.encode_trust_vc_expr(&compare_expr);
    assert!(
        result.is_err(),
        "encoding should fail for undefined variable"
    );

    // CRITICAL: use_int_arithmetic must be restored to true after the error.
    // BUG (compare.rs:238-244): the save/restore pattern uses ? without RAII,
    // so the error path skips the restore, permanently flipping to BV mode.
    // Same class as #2511 (match_int_arith_leak).
    assert!(
        parser.use_int_arithmetic,
        "use_int_arithmetic must be restored after compare encoding error. \
         Without RAII guard, the ? on compare.rs:242 skips the restore on :244, \
         permanently flipping the encoder to BV mode. Same class as #2511."
    );
}

/// DISCRIMINATING: MathInt arithmetic must succeed AFTER a failed BV compare
/// encoding. Without the fix, Int arithmetic on Sort::Int terms would use BV
/// operations, causing sort mismatches.
#[test]
fn test_int_arithmetic_works_after_failed_bv_compare() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();

    // First: trigger the compare error path to leak the flag
    let bad_compare = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "nonexistent_var".into(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let _ = parser.encode_trust_vc_expr(&bad_compare); // intentionally ignore error

    // Second: encode MathInt arithmetic that requires Int mode.
    // Without the fix, use_int_arithmetic = false, and this MathInt arithmetic
    // attempts BV encoding on Sort::Int terms → sort mismatch.
    let arith_expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "n".into(),
                ty: TrustVcType::MathInt,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "n".into(),
                ty: TrustVcType::MathInt,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
    };

    let result = parser.encode_trust_vc_expr(&arith_expr);
    assert!(
        result.is_ok(),
        "MathInt arithmetic after failed BV compare should succeed in all-Int context, \
         got error: {:?}. Without RAII guard, use_int_arithmetic leaks to false.",
        result.err()
    );
}
