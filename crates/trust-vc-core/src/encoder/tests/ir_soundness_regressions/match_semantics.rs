//! #2035 regressions: match arm condition preservation and exhaustiveness.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::types::sort_for_type;

// ========================================================================
// #2035 regression: encode_match must not drop last non-wildcard condition
// ========================================================================
//
// Before the fix, when the last arm (in reverse order, i.e., the first arm
// in source order) had a non-wildcard pattern and no else branch existed,
// the code used the arm's body as the unconditional default — dropping the
// condition entirely. This is unsound because the match could be
// non-exhaustive.

/// Match with two literal arms and no wildcard must return an error.
/// Pre-fix: the first arm's condition was silently dropped.
#[test]
fn test_2035_match_non_exhaustive_returns_error() {
    let mut env = QuantifierTestEnv::new();

    // Set up a variable for scrutinee
    let x_sort = sort_for_type(&TrustVcType::Int { width: 32 });
    let x = env.solver.declare_const("x", x_sort);
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser();

    // match x { 1 => true, 2 => false }
    // No wildcard arm — non-exhaustive. Must error, not silently use arm 1
    // as the unconditional default.
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Int { width: 32 },
                }),
                body: TrustVcExpr::BoolLit(true),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: 2,
                    ty: TrustVcType::Int { width: 32 },
                }),
                body: TrustVcExpr::BoolLit(false),
                guard: None,
            },
        ],
        ty: TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_err(),
        "#2035 regression: non-exhaustive match must return error, got Ok"
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("Non-exhaustive"),
        "#2035: error message should mention non-exhaustive, got: {}",
        err_msg
    );
}

/// Match with wildcard arm must succeed (baseline control).
#[test]
fn test_2035_match_with_wildcard_succeeds() {
    let mut env = QuantifierTestEnv::new();

    let x_sort = sort_for_type(&TrustVcType::Int { width: 32 });
    let x = env.solver.declare_const("x", x_sort);
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser();

    // match x { 1 => true, _ => false }
    // Has wildcard — exhaustive. Must succeed.
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Int { width: 32 },
                }),
                body: TrustVcExpr::BoolLit(true),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: TrustVcExpr::BoolLit(false),
                guard: None,
            },
        ],
        ty: TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2035 control: match with wildcard must succeed, got: {:?}",
        result.err()
    );
}

/// Assert that `scrutinee == input_val => match_result == expected_val` via solver.
fn assert_match_arm_maps_to(
    solver: &mut Solver,
    scrutinee: Term,
    match_result: Term,
    input_val: i64,
    expected_val: i64,
    width: u32,
    label: &str,
) {
    let input = solver.try_bv_const(input_val, width).unwrap();
    let expected = solver.try_bv_const(expected_val, width).unwrap();
    let is_input = solver.try_eq(scrutinee, input).unwrap();
    let is_expected = solver.try_eq(match_result, expected).unwrap();
    let implication = solver.try_implies(is_input, is_expected).unwrap();
    solver.try_push().unwrap();
    let neg = solver.try_not(implication).unwrap();
    solver.try_assert_term(neg).unwrap();
    let sat = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "#2035: {} — solver found counterexample: {:?}",
        label,
        sat
    );
}

/// Build a match expression: match scrutinee { val1 => body1, val2 => body2, _ => default }.
fn build_three_arm_match(ty: TrustVcType, vals: [(i128, i128); 2], default: i128) -> TrustVcExpr {
    TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: ty.clone(),
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: vals[0].0,
                    ty: ty.clone(),
                }),
                body: TrustVcExpr::IntLit {
                    value: vals[0].1,
                    ty: ty.clone(),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Lit(TrustVcExpr::IntLit {
                    value: vals[1].0,
                    ty: ty.clone(),
                }),
                body: TrustVcExpr::IntLit {
                    value: vals[1].1,
                    ty: ty.clone(),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: TrustVcExpr::IntLit {
                    value: default,
                    ty: ty.clone(),
                },
                guard: None,
            },
        ],
        ty,
    }
}

/// Match with three arms (lit, lit, wildcard) must preserve all conditions.
/// The first two literal arms must both contribute ITE conditions.
#[test]
fn test_2035_match_preserves_all_arm_conditions() {
    let mut env = QuantifierTestEnv::new();

    let x_sort = sort_for_type(&TrustVcType::Int { width: 32 });
    let x = env.solver.declare_const("x", x_sort);
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser();

    // match x { 1 => 10, 2 => 20, _ => 30 }
    let expr = build_three_arm_match(TrustVcType::Int { width: 32 }, [(1, 10), (2, 20)], 30);
    let match_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("match with wildcard must succeed");
    drop(parser);

    assert_match_arm_maps_to(&mut env.solver, x, match_term, 1, 10, 32, "x=1 -> 10");
    assert_match_arm_maps_to(&mut env.solver, x, match_term, 2, 20, 32, "x=2 -> 20");
}
