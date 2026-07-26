//! Match-arm shadowing regressions for Seq collection combinators.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{CollectionOp, MatchArm, MatchPattern, TrustVcExpr, TrustVcType};
use ay_dpll::api::{ArraySort, Sort, Term};
use std::collections::HashMap;

fn seq_u32_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(u32_ty()))
}

fn spec_fn_to_seq_u32() -> TrustVcType {
    TrustVcType::SpecFn(vec![u32_ty()], Box::new(seq_u32_ty()))
}

fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

fn seq_push(receiver: TrustVcExpr, receiver_name: &str, value: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Push,
        receiver: Box::new(receiver),
        receiver_name: Some(receiver_name.to_string()),
        args: vec![value],
        ty: seq_u32_ty(),
    }
}

fn flat_map_shadowing_closure(pattern: MatchPattern, body_value: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::SpecClosure {
        params: vec![("item".to_string(), u32_ty())],
        body: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(var("scrutinee", u32_ty())),
            arms: vec![MatchArm::new(
                pattern,
                seq_push(var("empty", seq_u32_ty()), "empty", body_value),
            )],
            ty: seq_u32_ty(),
        }),
        ty: spec_fn_to_seq_u32(),
    }
}

fn with_seq_parser<R>(f: impl FnOnce(&mut AstExpressionParser<'_>, Term) -> R) -> R {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let pw = crate::ir::pointer_width();
    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let src = solver.fresh_var("src", seq_sort.clone());
    let empty = solver.fresh_var("empty", seq_sort);
    let scrutinee = solver.fresh_var("scrutinee", Sort::bitvec(32));

    let variables = HashMap::from([
        ("src".to_string(), src),
        ("empty".to_string(), empty),
        ("scrutinee".to_string(), scrutinee),
    ]);
    let var_types = HashMap::from([
        ("src".to_string(), seq_u32_ty()),
        ("empty".to_string(), seq_u32_ty()),
        ("scrutinee".to_string(), u32_ty()),
    ]);
    let mut collection_lengths = HashMap::from([
        ("src".to_string(), solver.try_bv_const(2, pw).unwrap()),
        ("empty".to_string(), solver.try_bv_const(0, pw).unwrap()),
    ]);
    let functions = HashMap::new();
    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    f(&mut parser, src)
}

#[test]
fn test_seq_flat_map_match_arm_shadowing_is_treated_as_binder_free() {
    with_seq_parser(|parser, src| {
        let closure = flat_map_shadowing_closure(
            MatchPattern::Ident("item".to_string()),
            var("item", u32_ty()),
        );

        parser
            .encode_seq_flat_map(src, Some("src"), &[closure])
            .expect("match-arm-bound item should shadow the outer flat_map binder");
    });
}

#[test]
fn test_seq_flat_map_match_arm_unshadowed_outer_binder_still_fails_closed() {
    with_seq_parser(|parser, src| {
        let closure = flat_map_shadowing_closure(
            MatchPattern::Ident("inner".to_string()),
            var("item", u32_ty()),
        );

        let error = parser
            .encode_seq_flat_map(src, Some("src"), &[closure])
            .expect_err("outer flat_map binder use inside the arm must stay restricted");
        let message = error.to_string();
        assert!(
            message.contains("binder-dependent bodies"),
            "unexpected flat_map failure reason: {message}"
        );
    });
}
