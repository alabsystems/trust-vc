//! Regression tests for #2179: encode_neg uses scope-only wrap context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests that `encode_neg` in int_mode uses per-expression type priority
//! via `resolve_expr_wrap`, not just the quantifier scope's narrowest width.
//! Before the fix, negation of a u32 expression inside a forall with u8
//! bound vars would wrap to u8 range instead of u32.

use super::*;

// ========================================================================
// #2179: encode_neg wraps to scope width instead of expression type
// ========================================================================

/// STRUCTURAL: mixed-width negation in quantifier must encode successfully.
/// Overflow checks are suppressed inside quantifiers (#2557: quantifier_depth
/// guard prevents bound-variable scope leaks). The wrap context still uses
/// expression type (i32, not u8 scope), but no checks are collected.
///
/// Setup: forall |x: u8| { -y >= -(2^31) } where y: i32.
#[test]
fn test_2179_neg_uses_expr_type_not_scope_width() {
    let mut env = QuantifierTestEnv::new();

    // Add outer variable y: i32 (signed, width 32)
    let y_term = env.solver.fresh_var("y", Sort::Int);
    env.variables.insert("y".to_string(), y_term);
    env.var_types
        .insert("y".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser_with_overflow();

    // forall |x: u8| { (-y) >= i32::MIN }
    // The key: x has width 8, y has width 32.
    // encode_neg uses expression type (i32) for wrap context, not scope (u8).
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }))),
            right: Box::new(TrustVcExpr::IntLit {
                value: i32::MIN as i128,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2179: mixed-width negation in quantifier must not fail: {:?}",
        result.err()
    );

    // #2557: overflow checks are suppressed at quantifier_depth > 0 to prevent
    // bound-variable scope leaks. Verify no checks are collected.
    let checks = parser.take_overflow_checks();
    let neg_checks: Vec<_> = checks
        .iter()
        .filter(|(name, _)| name.contains("negation"))
        .collect();
    assert!(
        neg_checks.is_empty(),
        "#2557: negation overflow checks must be suppressed inside quantifiers. Got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// CONTROL: same-width case — negation of i8 inside forall with i8
/// bound var. Scope and expression widths match, so #2179 bug has no
/// effect. Regression guard for the non-mixed-width path.
#[test]
fn test_2179_neg_same_width_as_scope() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: i8| { (-x) >= -128 }
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 8 },
            }))),
            right: Box::new(TrustVcExpr::IntLit {
                value: -128,
                ty: TrustVcType::Int { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2179 control: same-width negation must succeed: {:?}",
        result.err()
    );
}

/// STRUCTURAL: wider expression inside narrower quantifier scope.
/// Negation of i64 variable inside forall with i16 bound var.
/// Encoding must succeed; overflow checks suppressed at depth > 0 (#2557).
#[test]
fn test_2179_neg_i64_in_i16_scope() {
    let mut env = QuantifierTestEnv::new();

    let y_term = env.solver.fresh_var("y", Sort::Int);
    env.variables.insert("y".to_string(), y_term);
    env.var_types
        .insert("y".to_string(), TrustVcType::Int { width: 64 });

    let mut parser = env.parser_with_overflow();

    // forall |x: i16| { (-y) == (-y) }
    // Trivially true, but the wrap context determines the modular range.
    let neg_y = TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Int { width: 64 },
    }));
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 16 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(neg_y.clone()),
            right: Box::new(neg_y),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2179: i64 negation in i16 scope must succeed: {:?}",
        result.err()
    );

    // #2557: overflow checks suppressed inside quantifiers.
    let checks = parser.take_overflow_checks();
    let neg_checks: Vec<_> = checks
        .iter()
        .filter(|(name, _)| name.contains("negation"))
        .collect();
    assert!(
        neg_checks.is_empty(),
        "#2557: negation overflow checks must be suppressed inside quantifiers. Got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// CONTROL: negation of a composed arithmetic expression inside a
/// quantifier where scope and expression type are both i8.
/// #2179 bug has no effect when widths match. Regression guard for
/// the composed-expression path through `infer_expr_type`.
#[test]
fn test_2179_neg_composed_arith_uses_expr_type() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: i8| { -(x + x) >= -256 }
    // Arith{..., ty: Int{8}} → infer_expr_type returns Int{8}
    // resolve_expr_wrap uses the expression type (i8), same as scope here.
    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 8 },
    };
    let sum = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(x.clone()),
        right: Box::new(x),
        ty: TrustVcType::Int { width: 8 },
    };
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Neg(Box::new(sum))),
            right: Box::new(TrustVcExpr::IntLit {
                value: -256,
                ty: TrustVcType::Int { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2179: negation of arith expression in quantifier must succeed: {:?}",
        result.err()
    );
}

// ========================================================================
// #2179/#2557 interaction tests: overflow checks suppressed in quantifiers
// ========================================================================
//
// After #2557 (quantifier_depth guard), overflow checks are correctly
// suppressed inside quantifiers to prevent bound-variable scope leaks.
// These tests verify encoding succeeds and no spurious checks leak out.

/// Encoding of negation in quantifier with mixed widths (i32 expr in u8
/// scope) must succeed. Overflow checks suppressed by #2557. This is the
/// positive control: the encoding itself is correct even without checks.
#[test]
fn test_2179_neg_i32_overflow_check_holds_for_in_range_value() {
    let mut env = QuantifierTestEnv::new();

    let y_term = env.solver.fresh_var("y", Sort::Int);
    env.variables.insert("y".to_string(), y_term);
    env.var_types
        .insert("y".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser_with_overflow();

    // forall |x: u8| { (-y) >= i32::MIN }
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }))),
            right: Box::new(TrustVcExpr::IntLit {
                value: i32::MIN as i128,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(result.is_ok(), "encoding failed: {:?}", result.err());

    // #2557: overflow checks suppressed inside quantifiers.
    let checks = parser.take_overflow_checks();
    let neg_checks: Vec<_> = checks
        .iter()
        .filter(|(name, _)| name.contains("negation"))
        .collect();
    assert!(
        neg_checks.is_empty(),
        "#2557: overflow checks must be suppressed inside quantifiers. Got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}

/// Encoding of negation at i32::MIN boundary in quantifier must succeed.
/// Overflow checks suppressed by #2557. This is the negative control:
/// even the boundary case (where -i32::MIN would overflow) encodes
/// without emitting checks inside the quantifier body.
#[test]
fn test_2179_neg_i32_overflow_check_fires_at_min() {
    let mut env = QuantifierTestEnv::new();

    let y_term = env.solver.fresh_var("y", Sort::Int);
    env.variables.insert("y".to_string(), y_term);
    env.var_types
        .insert("y".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser_with_overflow();

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }))),
            right: Box::new(TrustVcExpr::IntLit {
                value: i32::MIN as i128,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(result.is_ok(), "encoding failed: {:?}", result.err());

    // #2557: overflow checks suppressed inside quantifiers.
    let checks = parser.take_overflow_checks();
    let neg_checks: Vec<_> = checks
        .iter()
        .filter(|(name, _)| name.contains("negation"))
        .collect();
    assert!(
        neg_checks.is_empty(),
        "#2557: overflow checks must be suppressed inside quantifiers. Got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}
