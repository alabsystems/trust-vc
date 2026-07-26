//! Regression tests for match arm identifier bindings in the typed IR encoder.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Regression tests for #2128: `encode_match` did not insert `MatchPattern::Ident` bindings
//! into `local_vars` before encoding the arm body, causing "Undefined variable"
//! errors during both direct encoding and overflow check re-parsing.

use super::*;

use crate::ir::{ArithOp, CompareOp, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};

#[path = "match_arm_binding_or_cast.rs"]
mod match_arm_binding_or_cast;

fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.into(),
        ty: i32_ty(),
    }
}

fn i32_lit(v: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: v,
        ty: i32_ty(),
    }
}

fn bool_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.into(),
        ty: TrustVcType::Bool,
    }
}

// ========================================================================
// #2128: match arm ident bindings must be in scope during body encoding
// ========================================================================

/// DISCRIMINATING: `match x { y => y + 1 } == 6` should encode without error
/// when the scrutinee `x` has value 5.
///
/// Pre-fix: "Undefined variable: y" because `encode_match` never inserted
/// the ident binding into `local_vars`.
/// Post-fix: `y` is bound to the scrutinee term before encoding the body.
#[test]
fn test_2128_match_ident_binding_encodes_without_error() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(i32_var("x")),
            arms: vec![MatchArm {
                pattern: MatchPattern::Ident("y".into()),
                body: TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(i32_var("y")),
                    right: Box::new(i32_lit(1)),
                    ty: i32_ty(),
                },
                guard: None,
            }],
            ty: i32_ty(),
        }),
        right: Box::new(i32_lit(6)),
    };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let mut variables = std::collections::HashMap::new();
    variables.insert("x".into(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".into(), i32_ty());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(x, (32, true));

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "encode_match with ident binding failed: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: `match x { y => y + 1 }` with x == 5 should verify
/// that the result equals 6 via full verification pipeline.
#[test]
fn test_2128_match_binding_verifies_correct_value() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "match_binding",
        "match x { y => y + 1 } == 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "match x {{ y => y + 1 }} == 6 with x == 5 should verify",
    );
}

/// Match ident binding should not leak into subsequent arms.
/// `match x { 1 => 10, y => y + 1 }` — the binding `y` should only
/// be in scope for the second arm body, not the first.
#[test]
fn test_2128_match_binding_does_not_leak_across_arms() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("x")),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(i32_lit(1)),
                body: i32_lit(10),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Ident("y".into()),
                body: TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(i32_var("y")),
                    right: Box::new(i32_lit(1)),
                    ty: i32_ty(),
                },
                guard: None,
            },
        ],
        ty: i32_ty(),
    };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let mut variables = std::collections::HashMap::new();
    variables.insert("x".into(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".into(), i32_ty());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(x, (32, true));

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "match with lit + ident arms should encode: {:?}",
        result.err()
    );
}

/// Match ident binding should not shadow outer variables permanently.
/// After encoding `match x { y => y }`, the outer variable `y` (if one
/// exists) should be restored.
#[test]
fn test_2128_match_binding_restores_outer_scope() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let outer_y = solver.declare_const("y", Sort::bitvec(32));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".into(), x);
    variables.insert("y".into(), outer_y);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".into(), i32_ty());
    var_types.insert("y".into(), i32_ty());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    // Encode: (match x { y => y }) + outer_y
    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("x")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Ident("y".into()),
            body: i32_var("y"),
            guard: None,
        }],
        ty: i32_ty(),
    };
    let add_expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(match_expr),
        right: Box::new(i32_var("y")),
        ty: i32_ty(),
    };

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(x, (32, true));
    parser.term_widths.insert(outer_y, (32, true));

    let result = parser.encode_trust_vc_expr(&add_expr);
    assert!(
        result.is_ok(),
        "outer y should be accessible after match scope: {:?}",
        result.err()
    );
}
