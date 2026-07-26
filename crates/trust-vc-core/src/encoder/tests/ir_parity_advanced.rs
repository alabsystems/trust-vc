//! IR-only encoder tests for advanced TrustVcExpr encoding: cast, let-binding,
//! match expressions, function calls, and integer constants (MIN/MAX).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Dual-path parity tests (string path vs IR path) were removed in #2099
//! after the string-path parser was deleted. These IR-only tests exercise
//! ir_encoder paths not covered by the main encoder test suite.
//!
//! Part of #1865 Phase 4.

use super::*;

use crate::ir::{IntConstKind, MatchArm, MatchPattern, TrustVcExpr, TrustVcType};

// =====================================================================
// Test environment
// =====================================================================

struct AdvParityEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl AdvParityEnv {
    /// Environment with `x: i32` and `y: i32` (BV32, signed).
    fn new_i32() -> Self {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let x = solver.declare_const("x", Sort::bitvec(32));
        let y = solver.declare_const("y", Sort::bitvec(32));

        let mut variables = std::collections::HashMap::new();
        variables.insert("x".to_string(), x);
        variables.insert("y".to_string(), y);

        let mut var_types = std::collections::HashMap::new();
        var_types.insert("x".to_string(), TrustVcType::Int { width: 32 });
        var_types.insert("y".to_string(), TrustVcType::Int { width: 32 });

        AdvParityEnv {
            solver,
            variables,
            collection_lengths: std::collections::HashMap::new(),
            var_types,
            functions: std::collections::HashMap::new(),
        }
    }

    /// Environment with `a: bool` and `b: bool`.
    fn new_bool() -> Self {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let a = solver.declare_const("a", Sort::Bool);
        let b = solver.declare_const("b", Sort::Bool);

        let mut variables = std::collections::HashMap::new();
        variables.insert("a".to_string(), a);
        variables.insert("b".to_string(), b);

        let mut var_types = std::collections::HashMap::new();
        var_types.insert("a".to_string(), TrustVcType::Bool);
        var_types.insert("b".to_string(), TrustVcType::Bool);

        AdvParityEnv {
            solver,
            variables,
            collection_lengths: std::collections::HashMap::new(),
            var_types,
            functions: std::collections::HashMap::new(),
        }
    }

    /// Environment with `x: u8` (BV8, unsigned).
    fn new_u8() -> Self {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let x = solver.declare_const("x", Sort::bitvec(8));

        let mut variables = std::collections::HashMap::new();
        variables.insert("x".to_string(), x);

        let mut var_types = std::collections::HashMap::new();
        var_types.insert("x".to_string(), TrustVcType::Uint { width: 8 });

        AdvParityEnv {
            solver,
            variables,
            collection_lengths: std::collections::HashMap::new(),
            var_types,
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }
}

// Helper constructors

fn x_i32() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    }
}

fn i32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Int { width: 32 },
    }
}

fn u8_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Uint { width: 8 },
    }
}

fn x_u8() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Uint { width: 8 },
    }
}

fn not_chain(depth: usize) -> TrustVcExpr {
    let mut expr = TrustVcExpr::BoolLit(true);
    for _ in 0..depth {
        expr = TrustVcExpr::Not(Box::new(expr));
    }
    expr
}

// =====================================================================
// Cast tests (IR-only)
// =====================================================================

#[test]
fn test_ir_encoder_rejects_over_depth_limit() {
    let mut env = AdvParityEnv::new_bool();
    let mut parser = env.parser();
    let expr = not_chain(crate::expr_depth::MAX_EXPR_DEPTH + 1);

    let err = parser
        .encode_trust_vc_expr(&expr)
        .expect_err("over-limit IR encoding must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("expression depth exceeds internal limit"),
        "expected depth-limit error, got: {message}",
    );
    assert!(
        message.contains("IR encoding"),
        "expected encoder stage in error, got: {message}",
    );
}

/// IR-only: Cast u8 → i32 (widening, unsigned to signed, zero-extend).
#[test]
fn test_cast_u8_to_i32_widening() {
    let mut env = AdvParityEnv::new_u8();
    // Add a 32-bit variable for comparison
    let y = env.solver.declare_const("y", Sort::bitvec(32));
    env.variables.insert("y".to_string(), y);
    env.var_types
        .insert("y".to_string(), TrustVcType::Int { width: 32 });

    let ir = TrustVcExpr::Cast {
        expr: Box::new(x_u8()),
        from_ty: TrustVcType::Uint { width: 8 },
        to_ty: TrustVcType::Int { width: 32 },
    };

    // Verify the cast produces a term (IR-only, no string equivalent)
    let mut parser = env.parser();
    let result = parser.encode_trust_vc_expr(&ir);
    assert!(
        result.is_ok(),
        "u8 → i32 widening cast should encode: {:?}",
        result.err()
    );
}

// =====================================================================
// Match tests (IR-only)
// =====================================================================

/// IR-only: non-exhaustive match (no wildcard, last arm has condition) → error.
#[test]
fn test_match_non_exhaustive_returns_error() {
    let mut env = AdvParityEnv::new_i32();

    let ir = TrustVcExpr::Match {
        scrutinee: Box::new(x_i32()),
        arms: vec![MatchArm {
            pattern: MatchPattern::Lit(i32_lit(0)),
            body: TrustVcExpr::BoolLit(true),
            guard: None,
        }],
        ty: TrustVcType::Bool,
    };

    let mut parser = env.parser();
    let result = parser.encode_trust_vc_expr(&ir);
    assert!(result.is_err(), "Non-exhaustive match should return error");
    assert!(
        result.unwrap_err().to_string().contains("Non-exhaustive"),
        "Error should mention non-exhaustive"
    );
}

/// IR-only: match with ident pattern (irrefutable binding, treated as wildcard).
#[test]
fn test_match_ident_pattern_is_irrefutable() {
    let mut env = AdvParityEnv::new_i32();

    let ir = TrustVcExpr::Match {
        scrutinee: Box::new(x_i32()),
        arms: vec![MatchArm {
            pattern: MatchPattern::Ident("val".to_string()),
            body: TrustVcExpr::BoolLit(true),
            guard: None,
        }],
        ty: TrustVcType::Bool,
    };

    // Ident pattern is irrefutable → body is always the result
    let mut parser = env.parser();
    let ir_term = parser
        .encode_trust_vc_expr(&ir)
        .expect("ident-pattern match should encode");
    drop(parser);

    let true_term = env.solver.bool_const(true);
    let neq = env.solver.try_neq(ir_term, true_term).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(neq).unwrap();
    let result = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();

    assert!(
        result.is_unsat(),
        "ident-pattern match should equal body: got {:?}",
        result
    );
}

// =====================================================================
// Function call tests (IR-only)
// =====================================================================

/// IR-only: function call with undefined function → error.
#[test]
fn test_fn_call_undefined_returns_error() {
    let mut env = AdvParityEnv::new_i32();

    let ir = TrustVcExpr::FnCall {
        name: "undefined_fn".to_string(),
        args: vec![x_i32()],
        return_ty: TrustVcType::Int { width: 32 },
    };

    let mut parser = env.parser();
    let result = parser.encode_trust_vc_expr(&ir);
    assert!(result.is_err(), "Undefined function should return error");
    assert!(
        result
            .unwrap_err()
            .to_string()
            .contains("Undefined function"),
        "Error should mention undefined function"
    );
}

// =====================================================================
// IntConst (MIN/MAX) tests (IR-only)
// =====================================================================

/// IR-only: u8::MAX (255) encodes correctly.
#[test]
fn test_int_const_u8_max() {
    let mut env = AdvParityEnv::new_u8();

    let ir_max = TrustVcExpr::IntConst {
        ty: TrustVcType::Uint { width: 8 },
        kind: IntConstKind::Max,
    };
    let ir_lit = u8_lit(255);

    // Both should produce the same BV8 term
    let mut parser1 = env.parser();
    let max_term = parser1
        .encode_trust_vc_expr(&ir_max)
        .expect("u8::MAX should encode");
    drop(parser1);

    let mut parser2 = env.parser();
    let lit_term = parser2
        .encode_trust_vc_expr(&ir_lit)
        .expect("255u8 should encode");
    drop(parser2);

    let neq = env.solver.try_neq(max_term, lit_term).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(neq).unwrap();
    let result = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();

    assert!(
        result.is_unsat(),
        "u8::MAX should equal 255u8: got {:?}",
        result
    );
}

/// IR-only: u8::MIN (0) encodes correctly.
#[test]
fn test_int_const_u8_min() {
    let mut env = AdvParityEnv::new_u8();

    let ir_min = TrustVcExpr::IntConst {
        ty: TrustVcType::Uint { width: 8 },
        kind: IntConstKind::Min,
    };
    let ir_lit = u8_lit(0);

    let mut parser1 = env.parser();
    let min_term = parser1
        .encode_trust_vc_expr(&ir_min)
        .expect("u8::MIN should encode");
    drop(parser1);

    let mut parser2 = env.parser();
    let lit_term = parser2
        .encode_trust_vc_expr(&ir_lit)
        .expect("0u8 should encode");
    drop(parser2);

    let neq = env.solver.try_neq(min_term, lit_term).unwrap();
    env.solver.try_push().unwrap();
    env.solver.try_assert_term(neq).unwrap();
    let result = env.solver.try_check_sat().unwrap();
    env.solver.try_pop().unwrap();

    assert!(
        result.is_unsat(),
        "u8::MIN should equal 0u8: got {:?}",
        result
    );
}

/// IR-only: IntConst on non-integer type → error.
#[test]
fn test_int_const_on_bool_returns_error() {
    let mut env = AdvParityEnv::new_bool();

    let ir = TrustVcExpr::IntConst {
        ty: TrustVcType::Bool,
        kind: IntConstKind::Max,
    };

    let mut parser = env.parser();
    let result = parser.encode_trust_vc_expr(&ir);
    assert!(result.is_err(), "IntConst on Bool should return error");
}
