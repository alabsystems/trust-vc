//! Match overflow guard tests — overflow checks from match arm bodies must be
//! guarded by the arm condition so they only fire when the arm is taken.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Fixes #2114. Parallel to #2107 (encode_logic) and #2111 (encode_implies).
//! Pattern: same as encode_ite overflow guard (mod.rs:327-344).

use super::*;

use std::borrow::Cow;

use crate::ir::{ArithOp, TrustVcType, WrappingMode};
use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};

// ========================================================================
// Test infrastructure
// ========================================================================

struct MatchTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl MatchTestEnv {
    fn new() -> Self {
        MatchTestEnv {
            solver: Solver::try_new(Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser_with_overflow(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::with_overflow_checking(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
            true,
        )
    }
}

fn u8_ty() -> TrustVcType {
    TrustVcType::Uint { width: 8 }
}

fn x_var() -> Box<TrustVcExpr> {
    Box::new(TrustVcExpr::Var {
        name: "x".into(),
        ty: u8_ty(),
    })
}

fn a_var() -> Box<TrustVcExpr> {
    Box::new(TrustVcExpr::Var {
        name: "a".into(),
        ty: u8_ty(),
    })
}

fn b_var() -> Box<TrustVcExpr> {
    Box::new(TrustVcExpr::Var {
        name: "b".into(),
        ty: u8_ty(),
    })
}

fn u8_lit(v: i128) -> Box<TrustVcExpr> {
    Box::new(TrustVcExpr::IntLit {
        value: v,
        ty: u8_ty(),
    })
}

/// Build: `match x { 1u8 => checked_add(a, b), _ => 0u8 }`
///
/// All types are u8 so sorts match in pattern comparison.
/// The checked_add in the first arm emits overflow checks. These should
/// be guarded by `x == 1` so they don't fire when x != 1.
fn build_match_with_checked_add() -> TrustVcExpr {
    TrustVcExpr::Match {
        scrutinee: x_var(),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(*u8_lit(1)),
                body: TrustVcExpr::WrappingArith {
                    mode: WrappingMode::Checked,
                    op: ArithOp::Add,
                    left: a_var(),
                    right: b_var(),
                    ty: u8_ty(),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: *u8_lit(0),
                guard: None,
            },
        ],
        ty: u8_ty(),
    }
}

/// Declare all-u8 variables and encode the expression, returning overflow checks.
fn encode_and_extract_checks(
    env: &mut MatchTestEnv,
    expr: &TrustVcExpr,
) -> Vec<(Cow<'static, str>, Term)> {
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".into(), x);
    env.var_types.insert("x".into(), u8_ty());

    let a = env.solver.declare_const("a", Sort::bitvec(8));
    env.variables.insert("a".into(), a);
    env.var_types.insert("a".into(), u8_ty());

    let b = env.solver.declare_const("b", Sort::bitvec(8));
    env.variables.insert("b".into(), b);
    env.var_types.insert("b".into(), u8_ty());

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    parser.term_widths.insert(a, (8, false));
    parser.term_widths.insert(b, (8, false));
    let result = parser.encode_trust_vc_expr(expr);
    assert!(result.is_ok(), "encode failed: {:?}", result.err());
    assert!(
        !parser.overflow_checks.is_empty(),
        "checked_add in match arm must emit overflow checks"
    );
    std::mem::take(&mut parser.overflow_checks)
}

/// Check whether any overflow check is falsifiable under the given constraint.
fn any_check_falsifiable(
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
        }
    }
    solver.try_pop().unwrap();
    found
}

// ========================================================================
// #2114: match arm overflow checks must be guarded by arm condition
// ========================================================================

/// DISCRIMINATING: When x != 1 (arm condition is false), overflow checks
/// from checked_add(a, b) in the first arm should be trivially satisfied
/// because they are guarded by `¬(x == 1) ∨ no_overflow`.
///
/// Pre-fix: unguarded checks are falsifiable when x != 1 (a=200, b=200 overflows).
/// Post-fix: guarded checks are NOT falsifiable when x != 1.
#[test]
fn test_2114_match_arm_overflow_guarded_when_condition_false() {
    let expr = build_match_with_checked_add();
    let mut env = MatchTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x != 1: the first arm's condition is false
    let x = *env.variables.get("x").unwrap();
    let bv1 = env.solver.try_bv_const(1, 8).unwrap();
    let x_eq_1 = env.solver.try_eq(x, bv1).unwrap();
    let x_ne_1 = env.solver.try_not(x_eq_1).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_ne_1);

    // After #2114 fix: overflow checks are guarded, NOT falsifiable when x != 1
    assert!(
        !falsifiable,
        "BUG: overflow checks from match arm body are NOT guarded by the arm \
         condition — they are falsifiable even when the arm is not taken (x != 1). \
         This is #2114."
    );
}

/// Control: When x == 1 (arm condition is true), checked_add(a, b)
/// overflow checks MUST be falsifiable (a=200, b=200 overflows u8).
#[test]
fn test_2114_match_arm_overflow_fires_when_condition_true() {
    let expr = build_match_with_checked_add();
    let mut env = MatchTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x == 1: the first arm's condition is true
    let x = *env.variables.get("x").unwrap();
    let bv1 = env.solver.try_bv_const(1, 8).unwrap();
    let x_eq_1 = env.solver.try_eq(x, bv1).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_eq_1);

    assert!(
        falsifiable,
        "Control: when match arm condition IS true (x == 1), checked_add(a, b) \
         must be able to overflow for some (a, b) — overflow check should be falsifiable"
    );
}

/// DISCRIMINATING: With multiple conditional arms, each arm's overflow checks
/// must be guarded by its own condition only.
///
/// `match x { 1 => checked_add(a, b), 2 => checked_add(a, 100), _ => 0 }`
/// When x == 0, neither arm condition is true — all checks should be guarded.
#[test]
fn test_2114_multi_arm_each_guarded_independently() {
    let expr = TrustVcExpr::Match {
        scrutinee: x_var(),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(*u8_lit(1)),
                body: TrustVcExpr::WrappingArith {
                    mode: WrappingMode::Checked,
                    op: ArithOp::Add,
                    left: a_var(),
                    right: b_var(),
                    ty: u8_ty(),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Lit(*u8_lit(2)),
                body: TrustVcExpr::WrappingArith {
                    mode: WrappingMode::Checked,
                    op: ArithOp::Add,
                    left: a_var(),
                    right: u8_lit(100),
                    ty: u8_ty(),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: *u8_lit(0),
                guard: None,
            },
        ],
        ty: u8_ty(),
    };

    let mut env = MatchTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // With multiple checked_add arms, we should have overflow checks from both
    assert!(
        checks.len() >= 2,
        "Expected at least 2 overflow checks (one per checked arm), got {}",
        checks.len()
    );

    // x == 0: neither arm condition is true — ALL overflow checks should be guarded
    let x = *env.variables.get("x").unwrap();
    let bv0 = env.solver.try_bv_const(0, 8).unwrap();
    let x_eq_0 = env.solver.try_eq(x, bv0).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_eq_0);
    assert!(
        !falsifiable,
        "When x == 0 (no arm condition true), ALL overflow checks from both \
         arms should be guarded and not falsifiable"
    );
}

// ========================================================================
// #2128: match arm bindings must be available during overflow check encoding
// ========================================================================

/// Build: `match x { y => checked_add(y, 1u8) }`
///
/// The `Ident` pattern binds `y` to the scrutinee `x`. The arm body uses
/// `y` in a checked_add, which emits overflow checks. The typed-IR encoder
/// must insert `y` into `local_vars` before encoding the arm body, otherwise
/// `y` is undefined and encoding fails. Regression for #2128.
fn build_match_with_ident_binding_checked_add() -> TrustVcExpr {
    TrustVcExpr::Match {
        scrutinee: x_var(),
        arms: vec![MatchArm {
            pattern: MatchPattern::Ident("y".into()),
            body: TrustVcExpr::WrappingArith {
                mode: WrappingMode::Checked,
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Var {
                    name: "y".into(),
                    ty: u8_ty(),
                }),
                right: u8_lit(1),
                ty: u8_ty(),
            },
            guard: None,
        }],
        ty: u8_ty(),
    }
}

/// DISCRIMINATING: Match with Ident binding must encode successfully and emit
/// overflow checks. Pre-fix: fails with "Undefined variable: y" because the
/// typed-IR encoder did not insert bindings into local_vars for Ident patterns.
#[test]
fn test_2128_match_ident_binding_overflow_checks_emitted() {
    let expr = build_match_with_ident_binding_checked_add();
    let mut env = MatchTestEnv::new();

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".into(), x);
    env.var_types.insert("x".into(), u8_ty());

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "BUG #2128: match with Ident binding failed to encode: {:?}",
        result.err()
    );
    assert!(
        !parser.overflow_checks.is_empty(),
        "checked_add in match arm body with Ident binding must emit overflow checks"
    );
}

// ========================================================================
// #2563: wildcard arm overflow checks must be guarded
// ========================================================================

/// Build: `match x { 0u8 => 0u8, _ => checked_add(a, b) }`
///
/// The wildcard arm has a checked_add that emits overflow checks. These
/// should be guarded by "conditional arm did NOT match" so they only fire
/// when the wildcard is actually taken.
fn build_match_with_wildcard_checked_add() -> TrustVcExpr {
    TrustVcExpr::Match {
        scrutinee: x_var(),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(*u8_lit(0)),
                body: *u8_lit(0),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: TrustVcExpr::WrappingArith {
                    mode: WrappingMode::Checked,
                    op: ArithOp::Add,
                    left: a_var(),
                    right: b_var(),
                    ty: u8_ty(),
                },
                guard: None,
            },
        ],
        ty: u8_ty(),
    }
}

/// DISCRIMINATING: When x == 0 (conditional arm matches), overflow checks
/// from the wildcard arm's checked_add(a, b) should be guarded and NOT
/// falsifiable — the wildcard body is not executed.
///
/// Pre-fix: wildcard overflow checks are unguarded, so they fire even when
/// x == 0 (conditional arm taken). a=200, b=200 overflows u8, producing a
/// false counterexample.
/// Post-fix: wildcard checks are guarded by OR(all conditional arm
/// conditions), so when x == 0 the checks are trivially satisfied.
#[test]
fn test_2563_wildcard_arm_overflow_guarded_when_conditional_arm_matches() {
    let expr = build_match_with_wildcard_checked_add();
    let mut env = MatchTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x == 0: the conditional arm matches, wildcard is NOT taken
    let x = *env.variables.get("x").unwrap();
    let bv0 = env.solver.try_bv_const(0, 8).unwrap();
    let x_eq_0 = env.solver.try_eq(x, bv0).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_eq_0);
    assert!(
        !falsifiable,
        "BUG #2563: wildcard arm overflow checks are NOT guarded — they are \
         falsifiable even when the conditional arm is taken (x == 0). \
         Wildcard checks should only fire when the wildcard arm is reached."
    );
}

/// Control: When x != 0 (wildcard arm is taken), checked_add(a, b)
/// overflow checks MUST be falsifiable (a=200, b=200 overflows u8).
#[test]
fn test_2563_wildcard_arm_overflow_fires_when_wildcard_taken() {
    let expr = build_match_with_wildcard_checked_add();
    let mut env = MatchTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x == 5: no conditional arm matches, wildcard IS taken
    let x = *env.variables.get("x").unwrap();
    let bv5 = env.solver.try_bv_const(5, 8).unwrap();
    let x_eq_5 = env.solver.try_eq(x, bv5).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_eq_5);
    assert!(
        falsifiable,
        "Control: when wildcard arm IS taken (x == 5), checked_add(a, b) \
         must be able to overflow for some (a, b) — overflow check should be falsifiable"
    );
}

/// DISCRIMINATING: Multi-arm match with wildcard. Two conditional arms plus
/// a wildcard with overflow. When any conditional arm matches, wildcard
/// overflow checks should be guarded.
///
/// `match x { 0 => 0, 1 => 1, _ => checked_add(a, b) }`
#[test]
fn test_2563_multi_arm_wildcard_overflow_guarded() {
    let expr = TrustVcExpr::Match {
        scrutinee: x_var(),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(*u8_lit(0)),
                body: *u8_lit(0),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Lit(*u8_lit(1)),
                body: *u8_lit(1),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: TrustVcExpr::WrappingArith {
                    mode: WrappingMode::Checked,
                    op: ArithOp::Add,
                    left: a_var(),
                    right: b_var(),
                    ty: u8_ty(),
                },
                guard: None,
            },
        ],
        ty: u8_ty(),
    };

    let mut env = MatchTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x == 1: second conditional arm matches, wildcard NOT taken
    let x = *env.variables.get("x").unwrap();
    let bv1 = env.solver.try_bv_const(1, 8).unwrap();
    let x_eq_1 = env.solver.try_eq(x, bv1).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_eq_1);
    assert!(
        !falsifiable,
        "BUG #2563: wildcard overflow checks falsifiable when x == 1 \
         (conditional arm matches). Multi-arm wildcard guard must use \
         OR of all conditional arm conditions."
    );
}

/// DISCRIMINATING: Overflow checks from a match with Ident binding must be
/// falsifiable (the binding is the scrutinee, so `y + 1` can overflow when
/// `x == 255`). This confirms the binding maps to the correct term.
#[test]
fn test_2128_match_ident_binding_overflow_check_falsifiable() {
    let expr = build_match_with_ident_binding_checked_add();
    let mut env = MatchTestEnv::new();

    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".into(), x);
    env.var_types.insert("x".into(), u8_ty());

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(result.is_ok(), "encode failed: {:?}", result.err());
    let checks = std::mem::take(&mut parser.overflow_checks);
    assert!(!checks.is_empty(), "expected overflow checks");

    // x == 255: y + 1 overflows u8
    let bv255 = env.solver.try_bv_const(255, 8).unwrap();
    let x_eq_255 = env.solver.try_eq(x, bv255).unwrap();

    let falsifiable = any_check_falsifiable(&mut env.solver, &checks, x_eq_255);
    assert!(
        falsifiable,
        "When x == 255, match {{ y => y + 1 }} must be able to overflow u8 — \
         overflow check should be falsifiable"
    );
}
