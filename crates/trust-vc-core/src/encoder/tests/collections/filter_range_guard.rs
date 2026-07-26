//! Regression test for Seq::filter axiom1 range guard (#2528).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Without the range guard, the filter axiom universally quantifies the
//! predicate over ALL indices (including out-of-bounds "junk" region of
//! the SMT array). This can make the axiom unsatisfiable, causing false
//! verification via vacuous truth.

use super::*;

use crate::ir::{CollectionOp, CompareOp, TrustVcExpr, TrustVcType};
use ay_dpll::api::{ArraySort, Logic, SolveResult, Sort};

/// DISCRIMINATING: filter result's out-of-bounds region must be unconstrained.
///
/// Setup: Seq `s` of length 2, filter with `|x| x > 0`.
/// Access result at index 5 (out of bounds) and assert it equals 0.
///
/// With range guard (CORRECT): `bvult(5, result_len)` is false (since
/// result_len <= 2), so the predicate implication is vacuously true.
/// result[5] is unconstrained, so result[5] == 0 is SAT.
///
/// Without range guard (BUG): the axiom forces `pred(result[5])` =
/// `result[5] > 0`, which conflicts with result[5] == 0 -> UNSAT.
/// This UNSAT makes downstream assertions vacuously true (false verification).
#[test]
fn test_seq_filter_out_of_bounds_unconstrained_after_range_guard() {
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    // Declare Seq<i32> variable "s" with length 2.
    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let s = solver.declare_const("s", seq_sort);
    variables.insert("s".to_string(), s);
    var_types.insert(
        "s".to_string(),
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    let len = solver.try_bv_const(2, pw).unwrap();
    collection_lengths.insert("s".to_string(), len);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Build: s.filter(|x: i32| x > 0)
    let closure = TrustVcExpr::SpecClosure {
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        ty: TrustVcType::SpecFn(
            vec![TrustVcType::Int { width: 32 }],
            Box::new(TrustVcType::Bool),
        ),
    };
    let filter_expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::SeqFilter,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![closure],
        ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    };

    let result_term = parser
        .encode_trust_vc_expr(&filter_expr)
        .expect("filter encoding should succeed");

    // Access result at out-of-bounds index 5.
    let idx_5 = parser.solver.try_bv_const(5, pw).unwrap();
    let result_at_5 = parser
        .solver
        .try_select(result_term, idx_5)
        .expect("select should succeed");

    // Assert result[5] == 0 (signed i32 zero).
    let zero = parser.solver.try_bv_const(0, 32).unwrap();
    let eq_zero = parser
        .solver
        .try_eq(result_at_5, zero)
        .expect("eq should succeed");
    parser
        .solver
        .try_assert_term(eq_zero)
        .expect("assert should succeed");

    // Check SAT: with the range guard fix, out-of-bounds indices are
    // unconstrained, so result[5] == 0 is satisfiable. Without the fix,
    // the unguarded axiom forces result[5] > 0, making this UNSAT.
    let result = parser.solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "filter result's out-of-bounds region must be unconstrained \
         (range guard missing -> #2528 regression)"
    );
}

/// CORRECTNESS: filter encoding should succeed on a basic predicate.
#[test]
fn test_seq_filter_encoding_succeeds() {
    let pw = crate::ir::pointer_width();
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let s = solver.declare_const("s", seq_sort);
    variables.insert("s".to_string(), s);
    var_types.insert(
        "s".to_string(),
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    let len = solver.try_bv_const(10, pw).unwrap();
    collection_lengths.insert("s".to_string(), len);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let closure = TrustVcExpr::SpecClosure {
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        ty: TrustVcType::SpecFn(
            vec![TrustVcType::Int { width: 32 }],
            Box::new(TrustVcType::Bool),
        ),
    };
    let filter_expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::SeqFilter,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![closure],
        ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    };

    let result = parser.encode_trust_vc_expr(&filter_expr);
    assert!(
        result.is_ok(),
        "Seq::filter encoding should succeed: {:?}",
        result.err()
    );
}
