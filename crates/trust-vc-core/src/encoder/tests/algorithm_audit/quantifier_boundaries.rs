// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Quantifier wrapping context: only first bound variable's width used (#2036)
// ========================================================================

/// DISCRIMINATING: IR-level test that multi-type quantifier encodes without crash.
/// Verifies explicit quantifier scope state is restored after encoding.
#[test]
fn test_quantifier_multi_bound_var_wrapping_width() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // forall |i: u8, j: u32| j + 200 == j + 200 (tautology, tests encoding)
    let j_plus_200 = TrustVcExpr::Arith {
        op: crate::ir_expr::ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "j".to_string(),
            ty: TrustVcType::Uint { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 200,
            ty: TrustVcType::Uint { width: 32 },
        }),
        ty: TrustVcType::Uint { width: 32 },
    };

    let quant_expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![
            ("i".to_string(), TrustVcType::Uint { width: 8 }),
            ("j".to_string(), TrustVcType::Uint { width: 32 }),
        ],
        body: Box::new(TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Eq,
            left: Box::new(j_plus_200.clone()),
            right: Box::new(j_plus_200),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&quant_expr);
    assert!(
        result.is_ok(),
        "multi-type quantifier should encode: {:?}",
        result.err()
    );
    assert!(
        parser.quantifier_scopes.is_empty(),
        "quantifier_scopes should be restored after encode"
    );
    assert_eq!(
        parser.quantifier_depth, 0,
        "quantifier_depth should be restored after encode"
    );
    assert_eq!(
        parser.bv_quantifier_depth, 0,
        "bv_quantifier_depth should be restored after encode"
    );
}

/// DISCRIMINATING: quantifier scope + locals must be restored on encoding errors.
#[test]
fn test_quantifier_scope_restored_after_body_error() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Body references an undefined variable, forcing encode_quantifier to error.
    let quant_expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("i".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Eq,
            left: Box::new(i32_var("missing")),
            right: Box::new(i32_lit(0)),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let err = parser
        .encode_trust_vc_expr(&quant_expr)
        .expect_err("undefined variable in quantifier body must error");
    assert!(
        err.to_string().contains("undefined variable"),
        "Expected undefined-variable error, got: {}",
        err
    );
    assert_eq!(
        parser.quantifier_depth, 0,
        "quantifier_depth should be restored on error"
    );
    assert_eq!(
        parser.bv_quantifier_depth, 0,
        "bv_quantifier_depth should be restored on error"
    );
    assert!(
        parser.quantifier_scopes.is_empty(),
        "quantifier_scopes should be restored on error"
    );
    assert!(
        parser.local_vars.is_empty(),
        "local variable bindings should be restored on error"
    );
    assert!(
        parser.local_var_types.is_empty(),
        "local variable type bindings should be restored on error"
    );
}

/// DISCRIMINATING: finite BitVector quantifiers stay in BV arithmetic while
/// still restoring both quantifier-depth counters.
#[test]
fn test_bit_vector_finite_quantifier_depth_restored() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.solver_mode = Some(crate::vc::SolverMode::BitVector);

    let x = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Uint { width: 8 },
    };
    let x_and_x = TrustVcExpr::SpecialArith {
        op: crate::ir_expr::SpecialArithOp::BitAnd,
        left: Box::new(x.clone()),
        right: Box::new(x.clone()),
        ty: TrustVcType::Uint { width: 8 },
    };
    let quant_expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
        body: Box::new(TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Eq,
            left: Box::new(x_and_x),
            right: Box::new(x),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&quant_expr);
    assert!(
        result.is_ok(),
        "finite BV quantifier should encode in BV mode: {:?}",
        result.err()
    );
    assert_eq!(parser.quantifier_depth, 0);
    assert_eq!(parser.bv_quantifier_depth, 0);
    assert!(parser.quantifier_scopes.is_empty());
    assert!(parser.local_vars.is_empty());
    assert!(parser.local_var_types.is_empty());
}

/// DISCRIMINATING: forall |i: u8, j: u32| j + 1 > j should NOT verify.
#[test]
fn test_forall_multi_var_u8_u32_add_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "multi_var_overflow",
        "forall(|i: u8, j: u32| j + 1 > j)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall(|i: u8, j: u32| j + 1 > j) must NOT verify — overflow at u32::MAX",
    );
}

/// CONTROL: forall |i: u8, j: u32| j + 1 >= 0 should verify.
#[test]
fn test_forall_multi_var_u8_u32_add_nonneg_control() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "multi_var_nonneg",
        "forall(|i: u8, j: u32| j + 1 >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|i: u8, j: u32| j + 1 >= 0) should verify (control test).",
    );
}

// ========================================================================
// Quantifier trigger propagation to ay E-matching (#2034)
// ========================================================================

/// DISCRIMINATING: trigger uses no bound vars, so forwarding triggers to ay
/// must error (`InvalidTrigger`).
///
/// Regression for #2034: this test fails if trigger terms are silently ignored.
#[test]
fn test_quantifier_with_triggers_no_crash() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let y = solver.declare_const("y", Sort::Int);
    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();

    let mut variables = std::collections::HashMap::new();
    variables.insert("y".to_string(), y);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("y".to_string(), i32_ty());
    let mut collection_lengths = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    functions.insert("f".to_string(), f);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode with triggers
    let quant_with_triggers = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Eq,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_var("x")),
        }),
        // Invalid trigger if forwarded: f(y) contains no bound variable `x`.
        triggers: Some(vec![vec![TrustVcExpr::FnCall {
            name: "f".to_string(),
            args: vec![i32_var("y")],
            return_ty: i32_ty(),
        }]]),
        trigger_inference_mode: None,
    };

    let result = parser.encode_trust_vc_expr(&quant_with_triggers);
    assert!(
        result.is_err(),
        "Invalid trigger f(y) must be rejected when triggers are forwarded \
         to ay (regression #2034). Got: {:?}",
        result
    );
}
