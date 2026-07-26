//! Regression tests for Seq::map_values/map/concat/shifted_seq range guards (#2572).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Without range guards, these axioms universally quantify over ALL indices
//! (including out-of-bounds "junk" region of the SMT array). This can produce
//! unsatisfiable constraints when the closure/operation constrains junk indices,
//! leading to false verification via vacuous truth.

use super::*;

use crate::ir::{ArithOp, CollectionOp, TrustVcExpr, TrustVcType};
use ay_dpll::api::{ArraySort, Logic, SolveResult, Sort};

/// DISCRIMINATING: map_values result's out-of-bounds region must be unconstrained.
///
/// Setup: Seq `s` of length 2, `map_values(|x| x + 1)`.
/// Assert `result[5] == source[5]` at out-of-bounds index 5.
///
/// With range guard (CORRECT): `bvult(5, 2)` is false, so the axiom
/// implication is vacuously true. `result[5]` is unconstrained, making
/// `result[5] == source[5]` trivially SAT (both unconstrained at index 5).
///
/// Without range guard (BUG): the axiom forces `result[5] == source[5] + 1`,
/// conflicting with `result[5] == source[5]` (implies `1 == 0` in BV32) -> UNSAT.
/// This UNSAT makes downstream assertions vacuously true (false verification).
#[test]
fn test_seq_map_values_out_of_bounds_unconstrained_after_range_guard() {
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
    let len = solver.try_bv_const(2, pw).unwrap();
    collection_lengths.insert("s".to_string(), len);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Build: s.map_values(|x: i32| x + 1)
    let closure = TrustVcExpr::SpecClosure {
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 32 },
            }),
            ty: TrustVcType::Int { width: 32 },
        }),
        ty: TrustVcType::SpecFn(
            vec![TrustVcType::Int { width: 32 }],
            Box::new(TrustVcType::Int { width: 32 }),
        ),
    };
    let map_values_expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::SeqMapValues,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![closure],
        ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    };

    let result_term = parser
        .encode_trust_vc_expr(&map_values_expr)
        .expect("map_values encoding should succeed");

    // Access both result and source at out-of-bounds index 5.
    let idx_5 = parser.solver.try_bv_const(5, pw).unwrap();
    let result_at_5 = parser
        .solver
        .try_select(result_term, idx_5)
        .expect("select result should succeed");
    let source_at_5 = parser
        .solver
        .try_select(s, idx_5)
        .expect("select source should succeed");

    // Assert result[5] == source[5] (NOT source[5] + 1).
    // Without range guard: axiom forces result[5] == source[5] + 1,
    // so result[5] == source[5] implies 1 == 0 -> UNSAT.
    // With range guard: result[5] unconstrained -> SAT.
    let eq = parser
        .solver
        .try_eq(result_at_5, source_at_5)
        .expect("eq should succeed");
    parser
        .solver
        .try_assert_term(eq)
        .expect("assert should succeed");

    let result = parser.solver.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "map_values result's out-of-bounds region must be unconstrained \
         (range guard missing -> #2572 regression)"
    );
}
