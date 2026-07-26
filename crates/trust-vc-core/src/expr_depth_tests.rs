// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::{QuantifierKind, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};
use crate::ir_place::{PlaceProjection, TrustVcPlace};

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn bool_chain(depth: usize) -> TrustVcExpr {
    let mut expr = TrustVcExpr::BoolLit(true);
    for _ in 1..depth {
        expr = TrustVcExpr::Not(Box::new(expr));
    }
    expr
}

fn int_chain(depth: usize) -> TrustVcExpr {
    let mut expr = TrustVcExpr::IntLit {
        value: 0,
        ty: i32_ty(),
    };
    for _ in 1..depth {
        expr = TrustVcExpr::Neg(Box::new(expr));
    }
    expr
}

#[test]
fn test_validate_expr_depth_accepts_exact_limit() {
    let expr = bool_chain(MAX_EXPR_DEPTH);
    assert_eq!(validate_expr_depth(&expr, "boundary"), Ok(()));
}

#[test]
fn test_validate_expr_depth_rejects_trigger_over_limit() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: Some(vec![vec![bool_chain(MAX_EXPR_DEPTH)]]),
        trigger_inference_mode: None,
    };

    let err = validate_expr_depth(&expr, "trigger-depth").expect_err("trigger depth must fail");
    assert_eq!(
        err,
        ExprDepthError {
            limit: MAX_EXPR_DEPTH,
            stage: "trigger-depth",
        }
    );
}

#[test]
fn test_validate_expr_depth_rejects_match_pattern_literal_over_limit() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: i32_ty(),
        }),
        arms: vec![MatchArm::new(
            MatchPattern::Lit(bool_chain(MAX_EXPR_DEPTH)),
            TrustVcExpr::BoolLit(true),
        )],
        ty: TrustVcType::Bool,
    };

    let err = validate_expr_depth(&expr, "pattern-depth").expect_err("pattern depth must fail");
    assert_eq!(err.stage, "pattern-depth");
}

#[test]
fn test_validate_expr_depth_rejects_place_index_over_limit() {
    let expr = TrustVcExpr::ReadPlace {
        place: TrustVcPlace {
            root_name: "seq".to_string(),
            root_ty: TrustVcType::Seq(Box::new(i32_ty())),
            projections: vec![PlaceProjection::Index {
                index: int_chain(MAX_EXPR_DEPTH),
                elem_ty: i32_ty(),
            }],
            place_ty: i32_ty(),
        },
        ty: i32_ty(),
    };

    let err =
        validate_expr_depth(&expr, "place-index-depth").expect_err("place index depth must fail");
    assert_eq!(err.stage, "place-index-depth");
}
