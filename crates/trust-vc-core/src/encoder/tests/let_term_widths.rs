//! Let-binding term_widths registration tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Fixes #2116: encode_let must register term_widths for let-bound values
//! so downstream checked arithmetic has correct width/signedness info.

use super::*;

use crate::ir::{ArithOp, CompareOp, TrustVcType};
use crate::ir_expr::TrustVcExpr;

/// Test that encode_let registers term_widths for the let-bound value.
///
/// Constructs: `let v: u64 = f(x); v.checked_add(1)`
/// Without #2116 fix, checked_add would not find width info for `v`'s term
/// and could default to wrong signedness (signed i32 instead of unsigned u64).
#[test]
fn test_2116_let_bound_fncall_has_term_widths() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(64));
    let f = solver
        .try_declare_fun("f", &[Sort::bitvec(64)], Sort::bitvec(64))
        .unwrap();

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);

    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), TrustVcType::Uint { width: 64 });

    let mut functions = std::collections::HashMap::new();
    functions.insert("f".to_string(), f);

    let mut collection_lengths = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Build: let v: u64 = f(x); v > 0
    // The comparison exercises term_widths for signedness (unsigned u64).
    let ir = TrustVcExpr::Let {
        name: "v".to_string(),
        ty: TrustVcType::Uint { width: 64 },
        value: Box::new(TrustVcExpr::FnCall {
            name: "f".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 64 },
            }],
            return_ty: TrustVcType::Uint { width: 64 },
        }),
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "v".to_string(),
                ty: TrustVcType::Uint { width: 64 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 64 },
            }),
        }),
    };

    // Should encode without error — if term_widths is missing,
    // downstream operations may fail or produce incorrect results.
    let result = parser.encode_trust_vc_expr(&ir);
    assert!(
        result.is_ok(),
        "encode_let with FnCall value should succeed: {:?}",
        result.err()
    );
}

/// Test that let-bound variable from checked arithmetic has width info
/// for subsequent use. This exercises the chain:
///   let v: i32 = x + y; v.checked_add(1)
///
/// The checked_add in the body needs term_widths for v's value term.
#[test]
fn test_2116_let_bound_arith_checked_add_in_body() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);

    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), TrustVcType::Int { width: 32 });

    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Build: let v: i32 = x + y; v.checked_add(1) > 0
    let ir = TrustVcExpr::Let {
        name: "v".to_string(),
        ty: TrustVcType::Int { width: 32 },
        value: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            ty: TrustVcType::Int { width: 32 },
        }),
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::WrappingArith {
                mode: crate::ir_expr::WrappingMode::Checked,
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Var {
                    name: "v".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }),
                right: Box::new(TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Int { width: 32 },
                }),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
    };

    let result = parser.encode_trust_vc_expr(&ir);
    assert!(
        result.is_ok(),
        "encode_let with checked_add in body should succeed: {:?}",
        result.err()
    );

    // The encode should have generated overflow checks for the checked_add
    assert!(
        !parser.overflow_checks.is_empty(),
        "checked_add in let body should produce overflow checks"
    );
}
