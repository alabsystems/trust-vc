//! #2584 regression: promoted compare fallback must respect local shadowing.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The #2584 fix disables the #2557 BV compare fallback when a comparison
//! references variables promoted to MathInt/Nat in measure mode. That check
//! must honor local binding scopes: a shadowed inner `u8` let-binding named
//! `n` must not be mistaken for an outer promoted `MathInt` `n`.

use super::*;

#[test]
fn test_2584_shadowed_let_binding_keeps_bv_compare_fallback() {
    let mut env = QuantifierTestEnv::new();
    let outer_n = env.solver.declare_const("n", Sort::Int);
    env.variables.insert("n".to_string(), outer_n);
    env.var_types.insert("n".to_string(), TrustVcType::MathInt);

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "#2584 precondition: outer MathInt context should enable int mode"
    );

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Let {
            name: "n".to_string(),
            ty: u8_ty(),
            value: Box::new(TrustVcExpr::IntLit {
                value: 255,
                ty: u8_ty(),
            }),
            body: Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Var {
                    name: "n".to_string(),
                    ty: u8_ty(),
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: u8_ty(),
                }),
                ty: u8_ty(),
            }),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 255,
            ty: u8_ty(),
        }),
    };

    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("#2584: shadowed let-bound u8 comparison should encode");

    env.solver
        .try_assert_term(term)
        .expect("#2584: encoded comparison should assert");
    let sat = env
        .solver
        .try_check_sat()
        .expect("#2584: solver should check shadowed compare");
    assert!(
        sat.is_unsat(),
        "#2584 SOUNDNESS: shadowed let-bound u8 compare must use BV semantics \
         (255u8 + 1 wraps to 0, so 0 > 255 is false); got {sat:?}"
    );
}
