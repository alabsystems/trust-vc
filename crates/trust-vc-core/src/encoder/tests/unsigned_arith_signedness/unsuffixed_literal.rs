//! Pipeline gap tests: unsuffixed literals arriving with Int{32} type in
//! unsigned arithmetic contexts, plus unsigned overflow checks with
//! unsuffixed operands.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from unsigned_arith_signedness/mod.rs (#2145).

use super::*;

/// Helper: unsuffixed literal carrying default `Int{32}` type.
/// Used to model direct IR inputs that bypass literal coercion.
fn unsuffixed_lit(value: i128) -> crate::ir_expr::TrustVcExpr {
    crate::ir_expr::TrustVcExpr::IntLit {
        value,
        ty: crate::ir::TrustVcType::Int { width: 32 },
    }
}

/// PIPELINE GAP: u32 variable divided by unsuffixed literal (direct IR).
///
/// Right operand has `Int{32}`. Encoder must still use unsigned semantics
/// because the arithmetic expression type is `Uint{32}`.
///
/// For x = 0xFFFF_FFF0u32 (4294967280):
///   bvudiv: 4294967280 / 16 = 268435455 (0x0FFF_FFFF) — CORRECT
///   bvsdiv: -16 / 16 = -1 (0xFFFF_FFFF) — WRONG
#[test]
fn test_ir_unsigned_div_unsuffixed_literal_pipeline_gap() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Direct IR: right operand remains unsuffixed Int{32}.
    let expr = crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Div,
        left: Box::new(unsigned_var("x")),
        right: Box::new(unsuffixed_lit(16)),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    };

    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 / unsuffixed literal should encode");

    // Set x = 0xFFFF_FFF0u32
    let x_val = parser
        .solver
        .try_bv_const(0xFFFF_FFF0_u32 as i64, 32)
        .unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // Assert result == 0x0FFF_FFFF (correct unsigned division)
    let expected = parser.solver.try_bv_const(0x0FFF_FFFF_i64, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "PIPELINE GAP: u32 / unsuffixed literal must use bvudiv. \
         0xFFFF_FFF0u32 / 16 = 0x0FFFFFFF (bvudiv), not 0xFFFFFFFF (bvsdiv)."
    );
}

/// PIPELINE GAP: u32 unsuffixed literal divided by variable (direct IR).
///
/// Left operand has `Int{32}` while expression type is `Uint{32}`.
#[test]
fn test_ir_unsigned_div_unsuffixed_literal_lhs_pipeline_gap() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Direct IR: left operand remains unsuffixed Int{32}.
    let expr = crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Div,
        left: Box::new(unsuffixed_lit(0x8000_0000)),
        right: Box::new(unsigned_var("x")),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    };

    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("unsuffixed literal / u32 variable should encode");

    // Set x = 2 so signed and unsigned division diverge.
    let x_val = parser.solver.try_bv_const(2, 32).unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // Assert result == 0x4000_0000 (correct unsigned division).
    let expected = parser.solver.try_bv_const(0x4000_0000_i64, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "PIPELINE GAP: 0x80000000 / x with x=2 must use bvudiv for Uint{{32}}. \
         Expected 0x40000000, not 0xC0000000 from bvsdiv."
    );
}

/// PIPELINE GAP: u32 variable modulo unsuffixed literal (direct IR).
///
/// Same gap as division: right operand is `IntLit{Int{32}}`.
///
/// For x = 0x8000_0003u32 (2147483651):
///   bvurem: 2147483651 % 3 = 2 — CORRECT
///   bvsrem: -2147483645 % 3 = -2 (0xFFFFFFFE) — WRONG
#[test]
fn test_ir_unsigned_rem_unsuffixed_literal_pipeline_gap() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Direct IR: right operand remains unsuffixed Int{32}.
    let expr = crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Rem,
        left: Box::new(unsigned_var("x")),
        right: Box::new(unsuffixed_lit(3)),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    };

    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("u32 % unsuffixed literal should encode");

    // Set x = 0x8000_0003u32
    let x_val = parser
        .solver
        .try_bv_const(0x8000_0003_u32 as i64, 32)
        .unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // Assert result == 2 (correct unsigned remainder)
    let expected = parser.solver.try_bv_const(2, 32).unwrap();
    let eq = parser.solver.try_eq(result_term, expected).unwrap();
    parser.solver.try_assert_term(eq).unwrap();

    assert_eq!(
        parser.solver.try_check_sat().unwrap(),
        SolveResult::Sat,
        "PIPELINE GAP: u32 %% unsuffixed literal must use bvurem. \
         0x8000_0003u32 %% 3 = 2 (bvurem), not 0xFFFFFFFE (bvsrem)."
    );
}

/// PIPELINE GAP: u32 addition overflow check with unsuffixed literal.
///
/// For u32: 0x7FFF_FFFF + 1 does NOT overflow u32. But if encode_arith
/// sees the literal 1 as `Int{32}`, it may use signed overflow checks,
/// which would flag i32::MAX + 1 as overflow.
#[test]
fn test_ir_unsigned_add_overflow_unsuffixed_literal_pipeline_gap() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 32 };
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), ty.clone());

    let mut parser = make_unsigned_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Direct IR: right operand remains unsuffixed Int{32}.
    let add_expr = crate::ir_expr::TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(unsigned_var("x")),
        right: Box::new(unsuffixed_lit(1)),
        ty: crate::ir::TrustVcType::Uint { width: 32 },
    };

    parser.overflow_checks.clear();
    parser
        .encode_trust_vc_expr(&add_expr)
        .expect("u32 + unsuffixed literal should encode");

    // Set x = 0x7FFF_FFFF (i32::MAX). u32 addition does NOT overflow.
    let x_val = parser.solver.try_bv_const(0x7FFF_FFFF_i64, 32).unwrap();
    let eq_x = parser.solver.try_eq(x, x_val).unwrap();
    parser.solver.try_assert_term(eq_x).unwrap();

    // All overflow checks must be satisfiable (no false positive for u32)
    for (name, check) in &parser.overflow_checks {
        parser.solver.try_push().unwrap();
        parser.solver.try_assert_term(*check).unwrap();
        let sat = parser.solver.try_check_sat().unwrap();
        parser.solver.try_pop().unwrap();
        assert_eq!(
            sat,
            SolveResult::Sat,
            "PIPELINE GAP: u32 overflow check '{}' at x=0x7FFFFFFF with unsuffixed \
             literal: 0x7FFFFFFF + 1 = 0x80000000 is within u32 range. False positive \
             means signed overflow check used because unsuffixed literal has Int{{32}} type.",
            name
        );
    }
}
