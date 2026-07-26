//! Implies overflow guard tests — encode_implies does not guard conclusion
//! overflow checks behind the premise.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Parallel to #2107 (encode_logic short-circuit guards): `encode_implies`
//! encodes both premise and conclusion eagerly but does not guard overflow
//! checks from the conclusion behind the premise. For `p ==> c`, if `c`
//! generates overflow checks they should be guarded: `¬p ∨ no_overflow`,
//! because when the premise is false the conclusion is vacuously true and
//! its overflow behavior is irrelevant.

use super::*;

use std::borrow::Cow;

use crate::ir::{ArithOp, CompareOp, TrustVcType, WrappingMode};
use crate::ir_expr::TrustVcExpr;

// ========================================================================
// Test infrastructure
// ========================================================================

struct ImpliesTestEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl ImpliesTestEnv {
    fn new() -> Self {
        ImpliesTestEnv {
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

fn u8_lit(v: i128) -> Box<TrustVcExpr> {
    Box::new(TrustVcExpr::IntLit {
        value: v,
        ty: u8_ty(),
    })
}

/// Build `(x > 200) ==> (checked_add(x, 200) > 0)`.
fn build_implies_with_checked_add() -> TrustVcExpr {
    TrustVcExpr::Implies {
        premise: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: x_var(),
            right: u8_lit(200),
        }),
        conclusion: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::WrappingArith {
                mode: WrappingMode::Checked,
                op: ArithOp::Add,
                left: x_var(),
                right: u8_lit(200),
                ty: u8_ty(),
            }),
            right: u8_lit(0),
        }),
    }
}

/// Encode the expression and extract overflow checks.
fn encode_and_extract_checks(
    env: &mut ImpliesTestEnv,
    expr: &TrustVcExpr,
) -> Vec<(Cow<'static, str>, Term)> {
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".into(), x);
    env.var_types.insert("x".into(), u8_ty());

    let mut parser = env.parser_with_overflow();
    parser.term_widths.insert(x, (8, false));
    let result = parser.encode_trust_vc_expr(expr);
    assert!(result.is_ok(), "encode failed: {:?}", result.err());
    assert!(
        !parser.overflow_checks.is_empty(),
        "checked_add must emit overflow checks"
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
// #2111: encode_implies overflow checks from conclusion must be guarded
// ========================================================================

/// DISCRIMINATING: overflow checks from the conclusion of `==>` should be
/// guarded by the premise. When x <= 200 (premise false), the overflow
/// check from checked_add(x, 200) should be trivially satisfied.
#[test]
fn test_implies_conclusion_overflow_not_guarded_by_premise() {
    let expr = build_implies_with_checked_add();
    let mut env = ImpliesTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x <= 200: premise is false, overflow checks should be trivially true
    let x = *env.variables.get("x").unwrap();
    let bv200 = env.solver.try_bv_const(200, 8).unwrap();
    let x_le_200 = env.solver.try_bvule(x, bv200).unwrap();

    let unguarded = any_check_falsifiable(&mut env.solver, &checks, x_le_200);

    assert!(
        !unguarded,
        "overflow checks from implies conclusion must be guarded by premise: \
         with x <= 200 (premise false), no overflow check should be falsifiable"
    );
}

/// Control: when the premise IS true (x > 200), checked_add(x, 200)
/// overflows for x in 201..=255. The overflow check must be falsifiable.
#[test]
fn test_implies_overflow_check_fires_when_premise_true() {
    let expr = build_implies_with_checked_add();
    let mut env = ImpliesTestEnv::new();
    let checks = encode_and_extract_checks(&mut env, &expr);

    // x > 200: premise is true, overflow should be detectable
    let x = *env.variables.get("x").unwrap();
    let bv200 = env.solver.try_bv_const(200, 8).unwrap();
    let x_gt_200 = env.solver.try_bvugt(x, bv200).unwrap();

    let overflow_detected = any_check_falsifiable(&mut env.solver, &checks, x_gt_200);

    assert!(
        overflow_detected,
        "Control: when premise is true (x > 200), checked_add(x, 200) must \
         overflow for some x — overflow check should be falsifiable"
    );
}
