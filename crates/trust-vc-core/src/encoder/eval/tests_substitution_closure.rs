// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::substitution::substitute_inline_calls;
use crate::ir::{TrustVcExpr, TrustVcType};

#[test]
fn test_substitute_inline_calls_recurses_into_spec_closure() {
    let closure = TrustVcExpr::SpecClosure {
        params: vec![("item".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::FnCall {
            name: "helper".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "item".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty: TrustVcType::Int { width: 32 },
        }),
        ty: TrustVcType::Int { width: 32 },
    };

    let helper_body = TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Int { width: 32 },
        }),
        ty: TrustVcType::Int { width: 32 },
    };
    let inline_bodies = std::collections::HashMap::from([(
        "helper".to_string(),
        (
            vec!["x".to_string()],
            vec![TrustVcType::Int { width: 32 }],
            helper_body,
        ),
    )]);

    let result = substitute_inline_calls(&closure, &inline_bodies);

    match &result {
        TrustVcExpr::SpecClosure { body, .. } => match body.as_ref() {
            TrustVcExpr::Arith { left, right, .. } => {
                match left.as_ref() {
                    TrustVcExpr::Var { name, .. } => assert_eq!(name, "item"),
                    other => panic!("inlined arg should be 'item', got {:?}", other),
                }
                match right.as_ref() {
                    TrustVcExpr::IntLit { value: 1, .. } => {}
                    other => panic!("inlined constant should be 1, got {:?}", other),
                }
            }
            other => panic!(
                "inlined closure body should be Arith (item + 1), got {:?}",
                other
            ),
        },
        other => panic!("result should be SpecClosure, got {:?}", other),
    }
}
