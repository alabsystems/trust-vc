// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for TrustVcExpr query methods.
//!
//! Tests `contains_quantifier()`, `has_non_skolemized_quantifier()`,
//! `references_collection()`, and `may_emit_overflow_checks()` — query methods
//! that gate critical verification behavior.

mod query_methods;
mod visitor_and_fold;

use super::i32_ty;
use crate::ir::TrustVcType;
use crate::ir_expr::*;

fn var_x() -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "x".into(),
        ty: i32_ty(),
    }
}

fn lit_1() -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: 1,
        ty: i32_ty(),
    }
}

fn simple_forall_no_triggers() -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: None,
        trigger_inference_mode: None,
    }
}

fn simple_forall_with_triggers() -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: Some(vec![vec![var_x()]]),
        trigger_inference_mode: None,
    }
}

fn simple_exists() -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("x".into(), i32_ty())],
        body: Box::new(TrustVcExpr::BoolLit(true)),
        triggers: None,
        trigger_inference_mode: None,
    }
}

fn collection_len_op() -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".into(),
            ty: TrustVcType::Seq(Box::new(i32_ty())),
        }),
        receiver_name: Some("s".into()),
        args: vec![],
        ty: TrustVcType::Uint { width: 64 },
    }
}

fn index_expr() -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".into(),
            ty: TrustVcType::Seq(Box::new(i32_ty())),
        }),
        index: Box::new(lit_1()),
        receiver_name: Some("s".into()),
        elem_ty: i32_ty(),
    }
}

fn add_expr() -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(var_x()),
        right: Box::new(lit_1()),
        ty: i32_ty(),
    }
}
