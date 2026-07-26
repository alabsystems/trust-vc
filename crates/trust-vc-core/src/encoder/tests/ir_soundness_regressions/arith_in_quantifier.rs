//! #2030 regressions: checked/saturating arithmetic in quantifier bodies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// #2030 regression: Checked/Saturating in int_mode must not sort-mismatch
// ========================================================================
//
// Before the fix, only WrappingMode::Wrapping used the Int path inside
// quantifier bodies. Checked and Saturating fell through to BV operations,
// which panicked on Int-sorted terms (sort mismatch).

/// Checked add inside a quantifier body on u8 must succeed (no sort-mismatch panic).
/// Pre-fix: this would attempt BV operations on Int-sorted terms.
/// Note: overflow_checks are correctly suppressed inside quantifier bodies per #2557
/// (quantifier_depth > 0 guard). The result.is_ok() confirms the #2030 fix is intact.
#[test]
fn test_2030_checked_add_in_quantifier_u8() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: u8| checked_add(x, 1) >= 0
    // The key test: WrappingArith(Checked, Add) inside a quantifier body.
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::WrappingArith {
                mode: WrappingMode::Checked,
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Uint { width: 8 },
                }),
                ty: TrustVcType::Uint { width: 8 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2030 regression: checked_add in quantifier must not panic, got: {:?}",
        result.err()
    );
}

/// Saturating sub inside a quantifier body on i32 must succeed and clamp correctly.
/// Pre-fix: this would attempt BV operations on Int-sorted terms.
/// Semantic check: at x=i32::MIN, saturating_sub(x, 1) should equal i32::MIN (clamped).
#[test]
fn test_2030_saturating_sub_in_quantifier_i32() {
    let mut env = QuantifierTestEnv::new();

    // Simulate quantifier context: push scope with i32 bound var.
    let bound_vars = vec![("x".to_string(), TrustVcType::Int { width: 32 })];
    let x = env.solver.declare_const("x", Sort::Int);
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser();
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&bound_vars);

    let sat_sub = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Saturating,
        op: ArithOp::Sub,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Int { width: 32 },
        }),
        ty: TrustVcType::Int { width: 32 },
    };

    let result_term = parser
        .encode_trust_vc_expr(&sat_sub)
        .expect("#2030: saturating_sub in int_mode must not panic");
    parser.pop_quantifier_scope();
    drop(parser);

    // Semantic check: at x = i32::MIN (-2^31), saturating_sub(x, 1) = i32::MIN.
    let min_val = -(1i64 << 31);
    let min_term = env.solver.int_const(min_val);
    let x_is_min = env.solver.try_eq(x, min_term).unwrap();
    let min_term2 = env.solver.int_const(min_val);
    let result_is_min = env.solver.try_eq(result_term, min_term2).unwrap();
    let should_hold = env.solver.try_implies(x_is_min, result_is_min).unwrap();
    env.solver.try_push().unwrap();
    let neg = env.solver.try_not(should_hold).unwrap();
    env.solver.try_assert_term(neg).unwrap();
    let sat = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2030: saturating_sub(MIN, 1) should clamp to MIN, got: {:?}",
        sat
    );
}

/// Checked mul inside a quantifier body must succeed (no sort-mismatch panic).
/// Note: overflow_checks are correctly suppressed inside quantifier bodies per #2557
/// (quantifier_depth > 0 guard). The result.is_ok() confirms the #2030 fix is intact.
#[test]
fn test_2030_checked_mul_in_quantifier_u8() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser_with_overflow();

    // forall |x: u8| checked_mul(x, 2) >= 0
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(TrustVcExpr::WrappingArith {
                mode: WrappingMode::Checked,
                op: ArithOp::Mul,
                left: Box::new(TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 2,
                    ty: TrustVcType::Uint { width: 8 },
                }),
                ty: TrustVcType::Uint { width: 8 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 8 },
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2030: checked_mul encoding failed: {:?}",
        result.err()
    );
}

/// Checked add OUTSIDE a quantifier (depth==0) must emit overflow checks.
/// Maintains coverage of the overflow check emission path that #2557 intentionally
/// preserves at the outer scope.
#[test]
fn test_2030_checked_add_outside_quantifier_emits_overflow() {
    let mut env = QuantifierTestEnv::new();
    let a = env.solver.declare_const("a", Sort::bitvec(8));
    env.variables.insert("a".to_string(), a);
    env.var_types
        .insert("a".to_string(), TrustVcType::Uint { width: 8 });
    let mut parser = env.parser_with_overflow();

    // Direct checked_add on u8, no Quantifier wrapper (quantifier_depth==0).
    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Checked,
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "a".into(),
            ty: TrustVcType::Uint { width: 8 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Uint { width: 8 },
        }),
        ty: TrustVcType::Uint { width: 8 },
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2030: checked_add outside quantifier must not panic, got: {:?}",
        result.err()
    );

    let checks = std::mem::take(&mut parser.overflow_checks);
    assert!(
        checks.iter().any(|(n, _)| n.contains("checked_add")),
        "checked_add outside quantifier must emit overflow check, got: {:?}",
        checks.iter().map(|(n, _)| n.as_ref()).collect::<Vec<_>>()
    );
}
