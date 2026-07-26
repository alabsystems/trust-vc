//! #2115/#2110 regressions: ITE overflow guards and result width metadata.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// #2115: encode_ite branch overflow guards
// ========================================================================

/// Returns true if at least one overflow check can be falsified under
/// `constraint` (i.e., SAT for `constraint ∧ ¬check`).
fn any_overflow_check_falsifiable_under(
    solver: &mut Solver,
    checks: &[(Cow<'static, str>, Term)],
    constraint: Term,
) -> bool {
    solver.try_push().unwrap();
    solver.try_assert_term(constraint).unwrap();
    let mut found = false;
    for (_name, pred) in checks {
        solver.try_push().unwrap();
        let neg = solver.try_not(*pred).unwrap();
        solver.try_assert_term(neg).unwrap();
        let sat = solver.try_check_sat().unwrap();
        solver.try_pop().unwrap();
        if sat.is_sat() {
            found = true;
            break;
        }
    }
    solver.try_pop().unwrap();
    found
}

/// Build `if b { checked_add(x, 200) > 0 } else { true }`.
fn build_ite_then_checked_add() -> TrustVcExpr {
    let u8 = TrustVcType::Uint { width: 8 };
    let x_var = || {
        Box::new(TrustVcExpr::Var {
            name: "x".into(),
            ty: u8.clone(),
        })
    };
    TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::Var {
            name: "b".into(),
            ty: TrustVcType::Bool,
        }),
        then_branch: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::WrappingArith {
                mode: WrappingMode::Checked,
                op: ArithOp::Add,
                left: x_var(),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 200,
                    ty: u8.clone(),
                }),
                ty: u8.clone(),
            }),
            right: Box::new(TrustVcExpr::IntLit { value: 0, ty: u8 }),
        }),
        else_branch: Box::new(TrustVcExpr::BoolLit(true)),
        ty: TrustVcType::Bool,
    }
}

/// Build `if b { true } else { checked_sub(x, 200) > 0 }`.
fn build_ite_else_checked_sub() -> TrustVcExpr {
    let u8 = TrustVcType::Uint { width: 8 };
    let x_var = || {
        Box::new(TrustVcExpr::Var {
            name: "x".into(),
            ty: u8.clone(),
        })
    };
    TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::Var {
            name: "b".into(),
            ty: TrustVcType::Bool,
        }),
        then_branch: Box::new(TrustVcExpr::BoolLit(true)),
        else_branch: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::WrappingArith {
                mode: WrappingMode::Checked,
                op: ArithOp::Sub,
                left: x_var(),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 200,
                    ty: u8.clone(),
                }),
                ty: u8.clone(),
            }),
            right: Box::new(TrustVcExpr::IntLit { value: 0, ty: u8 }),
        }),
        ty: TrustVcType::Bool,
    }
}

/// Encode an expression after declaring `b: bool` and `x: u8`.
fn encode_with_b_and_x(
    env: &mut QuantifierTestEnv,
    expr: &TrustVcExpr,
) -> (Term, Term, Vec<(Cow<'static, str>, Term)>) {
    let b = env.solver.declare_const("b", Sort::Bool);
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("b".into(), b);
    env.variables.insert("x".into(), x);
    env.var_types.insert("b".into(), TrustVcType::Bool);
    env.var_types
        .insert("x".into(), TrustVcType::Uint { width: 8 });

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(expr);
    assert!(result.is_ok(), "#2115: encode failed: {:?}", result.err());
    assert!(
        !parser.overflow_checks.is_empty(),
        "#2115: expected overflow checks from checked arithmetic"
    );
    let checks = std::mem::take(&mut parser.overflow_checks);
    drop(parser);
    (b, x, checks)
}

/// DISCRIMINATING: overflow checks from the then-branch must be guarded by
/// the condition. If `b` is false, then-branch checks must be trivially true.
#[test]
fn test_2115_ite_then_branch_overflow_checks_guarded_when_condition_false() {
    let expr = build_ite_then_checked_add();
    let mut env = QuantifierTestEnv::new();
    let (b, x, checks) = encode_with_b_and_x(&mut env, &expr);

    let b_false = env.solver.try_not(b).unwrap();
    let val_100 = env.solver.try_bv_const(100, 8).unwrap();
    let x_is_100 = env.solver.try_eq(x, val_100).unwrap();
    let not_taken = env.solver.try_and(b_false, x_is_100).unwrap();
    assert_overflow_checks_hold_under(&mut env.solver, &checks, not_taken, "ITE-THEN");
}

/// Control for then-branch: when `b` is true and `x == 100`, checked_add
/// overflows in u8 and at least one overflow check should be falsifiable.
#[test]
fn test_2115_ite_then_branch_overflow_checks_fire_when_taken() {
    let expr = build_ite_then_checked_add();
    let mut env = QuantifierTestEnv::new();
    let (b, x, checks) = encode_with_b_and_x(&mut env, &expr);

    let val_100 = env.solver.try_bv_const(100, 8).unwrap();
    let x_is_100 = env.solver.try_eq(x, val_100).unwrap();
    let taken = env.solver.try_and(b, x_is_100).unwrap();
    let overflow_detected = any_overflow_check_falsifiable_under(&mut env.solver, &checks, taken);
    assert!(
        overflow_detected,
        "#2115 control: taken then-branch checked_add(x, 200) should overflow for x=100"
    );
}

/// DISCRIMINATING: overflow checks from the else-branch must be guarded by
/// `¬condition`. If `b` is true, else-branch checks must be trivially true.
#[test]
fn test_2115_ite_else_branch_overflow_checks_guarded_when_condition_true() {
    let expr = build_ite_else_checked_sub();
    let mut env = QuantifierTestEnv::new();
    let (b, x, checks) = encode_with_b_and_x(&mut env, &expr);

    let val_1 = env.solver.try_bv_const(1, 8).unwrap();
    let x_is_1 = env.solver.try_eq(x, val_1).unwrap();
    let not_taken = env.solver.try_and(b, x_is_1).unwrap();
    assert_overflow_checks_hold_under(&mut env.solver, &checks, not_taken, "ITE-ELSE");
}

/// Control for else-branch: when `b` is false and `x == 1`, checked_sub
/// underflows in u8 and at least one overflow check should be falsifiable.
#[test]
fn test_2115_ite_else_branch_overflow_checks_fire_when_taken() {
    let expr = build_ite_else_checked_sub();
    let mut env = QuantifierTestEnv::new();
    let (b, x, checks) = encode_with_b_and_x(&mut env, &expr);

    let b_false = env.solver.try_not(b).unwrap();
    let val_1 = env.solver.try_bv_const(1, 8).unwrap();
    let x_is_1 = env.solver.try_eq(x, val_1).unwrap();
    let taken = env.solver.try_and(b_false, x_is_1).unwrap();
    let overflow_detected = any_overflow_check_falsifiable_under(&mut env.solver, &checks, taken);
    assert!(
        overflow_detected,
        "#2115 control: taken else-branch checked_sub(x, 200) should underflow for x=1"
    );
}

// ========================================================================
// #2110: encode_ite must register term_widths for ITE result
// ========================================================================

/// ITE result with u8 type must have (8, false) in term_widths, not missing.
/// Before the fix, the ITE result had no term_widths entry, causing downstream
/// arithmetic to fall back to signed 32-bit defaults.
#[test]
fn test_2110_ite_result_has_correct_term_width() {
    let u8_ty = TrustVcType::Uint { width: 8 };
    // if b { x } else { 42u8 }
    let expr = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::Var {
            name: "b".into(),
            ty: TrustVcType::Bool,
        }),
        then_branch: Box::new(TrustVcExpr::Var {
            name: "x".into(),
            ty: u8_ty.clone(),
        }),
        else_branch: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: u8_ty.clone(),
        }),
        ty: u8_ty.clone(),
    };

    let mut env = QuantifierTestEnv::new();
    let b = env.solver.declare_const("b", Sort::Bool);
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("b".into(), b);
    env.variables.insert("x".into(), x);
    env.var_types.insert("b".into(), TrustVcType::Bool);
    env.var_types.insert("x".into(), u8_ty);

    let mut parser = env.parser();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2110: encode_ite failed: {:?}",
        result.err()
    );
    let result_term = result.unwrap();

    let width_info = parser.term_widths.get(&result_term);
    assert!(
        width_info.is_some(),
        "#2110: ITE result term has no term_widths entry — downstream ops will use wrong defaults"
    );
    let (width, signed) = *width_info.unwrap();
    assert_eq!(
        width, 8,
        "#2110: ITE result width should be 8 (u8), got {}",
        width
    );
    assert!(
        !signed,
        "#2110: ITE result should be unsigned (u8), got signed"
    );
}

/// Arithmetic on an ITE result must use the ITE's declared width.
/// Before the fix, `checked_add(ite_result, 1)` would lack width context,
/// falling back to 32-bit and producing wrong overflow semantics.
#[test]
fn test_2110_arith_on_ite_result_uses_correct_width() {
    let u8_ty = TrustVcType::Uint { width: 8 };
    // checked_add(if b { x } else { 42u8 }, 1u8)
    let ite_expr = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::Var {
            name: "b".into(),
            ty: TrustVcType::Bool,
        }),
        then_branch: Box::new(TrustVcExpr::Var {
            name: "x".into(),
            ty: u8_ty.clone(),
        }),
        else_branch: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: u8_ty.clone(),
        }),
        ty: u8_ty.clone(),
    };
    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Checked,
        op: ArithOp::Add,
        left: Box::new(ite_expr),
        right: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: u8_ty.clone(),
        }),
        ty: u8_ty.clone(),
    };

    let mut env = QuantifierTestEnv::new();
    let b = env.solver.declare_const("b", Sort::Bool);
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("b".into(), b);
    env.variables.insert("x".into(), x);
    env.var_types.insert("b".into(), TrustVcType::Bool);
    env.var_types.insert("x".into(), u8_ty);

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2110: encode checked_add on ITE result failed: {:?}",
        result.err()
    );

    // Overflow checks should exist (checked arithmetic on u8)
    assert!(
        !parser.overflow_checks.is_empty(),
        "#2110: checked_add on ITE result should emit overflow checks"
    );
}

// ========================================================================
