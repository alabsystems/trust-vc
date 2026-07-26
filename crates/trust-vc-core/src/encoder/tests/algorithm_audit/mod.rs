//! Algorithm audit regression tests: correctness, off-by-one, boundary conditions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests target specific algorithmic bugs found during Prover audit.
//! Most tests are DISCRIMINATING — they would fail (or pass trivially) if
//! the bug existed. Exceptions are documented inline (e.g., smoke tests).

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::{MatchArm, MatchPattern, QuantifierKind, TrustVcExpr};

mod match_exhaustiveness;
mod normalization_boundaries;
mod quantifier_boundaries;

// ========================================================================
// Test infrastructure — match expression helpers
// ========================================================================

fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: i32_ty(),
    }
}

fn i32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: i32_ty(),
    }
}

fn lit_arm(pattern_val: i128, body_val: i128) -> MatchArm {
    MatchArm {
        pattern: MatchPattern::Lit(i32_lit(pattern_val)),
        body: i32_lit(body_val),
        guard: None,
    }
}

fn wildcard_arm(body_val: i128) -> MatchArm {
    MatchArm {
        pattern: MatchPattern::Wildcard,
        body: i32_lit(body_val),
        guard: None,
    }
}

/// Set up a solver with x: i32, try to encode a match expression.
/// Returns Ok((solver, x_term, match_term)) on success, Err(message) on failure.
fn try_encode_match_on_x(arms: Vec<MatchArm>) -> Result<(Solver, Term, Term), String> {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));

    let mut variables = std::collections::HashMap::new();
    variables.insert("x".to_string(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".to_string(), i32_ty());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("x")),
        arms,
        ty: i32_ty(),
    };

    let match_term = parser
        .encode_trust_vc_expr(&match_expr)
        .map_err(|e| e.to_string())?;
    drop(parser);

    Ok((solver, x, match_term))
}

/// Set up a solver with x: i32, encode a match expression, return (solver, x_term, match_term).
/// Panics if encoding fails.
fn encode_match_on_x(arms: Vec<MatchArm>) -> (Solver, Term, Term) {
    try_encode_match_on_x(arms).expect("encode_match should succeed")
}

/// Assert: when x=x_val, match_term equals expected_val.
fn assert_match_at(solver: &mut Solver, x: Term, match_term: Term, x_val: i64, expected: i64) {
    solver.try_push().unwrap();
    let x_const = solver.try_bv_const(x_val, 32).unwrap();
    let expected_const = solver.try_bv_const(expected, 32).unwrap();
    let eq_x = solver.try_eq(x, x_const).unwrap();
    solver.try_assert_term(eq_x).unwrap();
    let neq_match = solver.try_neq(match_term, expected_const).unwrap();
    solver.try_assert_term(neq_match).unwrap();
    let result = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    assert!(
        result.is_unsat(),
        "match at x={} should return {}",
        x_val,
        expected
    );
}
