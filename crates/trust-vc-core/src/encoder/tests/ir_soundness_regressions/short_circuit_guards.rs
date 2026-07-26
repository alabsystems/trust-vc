//! #2107 regressions: short-circuit overflow guard encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// #2107: encode_logic short-circuit overflow guard
// ========================================================================

/// Build `left_cmp(x, 0) OP (checked_add(x, 200) > 0)` and verify that
/// overflow checks are guarded (trivially true when x=0).
fn assert_2107_short_circuit_guard(logic_op: LogicOp, left_cmp: CompareOp, label: &str) {
    let u8 = TrustVcType::Uint { width: 8 };
    let x_var = || {
        Box::new(TrustVcExpr::Var {
            name: "x".into(),
            ty: u8.clone(),
        })
    };
    let zero = || {
        Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: u8.clone(),
        })
    };
    let expr = TrustVcExpr::Logic {
        op: logic_op,
        left: Box::new(TrustVcExpr::Compare {
            op: left_cmp,
            left: x_var(),
            right: zero(),
        }),
        right: Box::new(TrustVcExpr::Compare {
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
            right: zero(),
        }),
    };

    let mut env = QuantifierTestEnv::new();
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".into(), x);
    env.var_types.insert("x".into(), u8);

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2107 {}: encode failed: {:?}",
        label,
        result.err()
    );
    assert!(
        !parser.overflow_checks.is_empty(),
        "#2107 {}: no overflow checks",
        label
    );
    let checks = std::mem::take(&mut parser.overflow_checks);
    drop(parser);

    let bv_zero = env.solver.try_bv_const(0, 8).unwrap();
    let x_is_zero = env.solver.try_eq(x, bv_zero).unwrap();
    assert_overflow_checks_hold_under(&mut env.solver, &checks, x_is_zero, label);
}

/// DISCRIMINATING: && overflow checks guarded by left condition (#2107).
#[test]
fn test_2107_and_short_circuit_guards_overflow_checks() {
    assert_2107_short_circuit_guard(LogicOp::And, CompareOp::Ne, "AND");
}

/// DISCRIMINATING: || overflow checks guarded by ¬left (#2107).
#[test]
fn test_2107_or_short_circuit_guards_overflow_checks() {
    assert_2107_short_circuit_guard(LogicOp::Or, CompareOp::Eq, "OR");
}
