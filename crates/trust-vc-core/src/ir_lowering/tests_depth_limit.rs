//! Tests for expression depth guardrails in IR lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;

#[test]
fn test_lower_syn_expr_rejects_over_depth_limit() {
    let mut env = TypeEnv::new();
    env.insert("x".to_string(), TrustVcType::Int { width: 32 });

    let nesting = crate::expr_depth::MAX_EXPR_DEPTH + 1;
    let mut expr: syn::Expr = syn::parse_quote!(x);
    for _ in 0..nesting {
        expr = syn::Expr::Paren(syn::ExprParen {
            attrs: Vec::new(),
            paren_token: Default::default(),
            expr: Box::new(expr),
        });
    }

    let err = lower_syn_expr(&expr, &env).expect_err("over-limit lowering must fail closed");
    assert_eq!(
        err,
        LoweringError::ExpressionTooDeep {
            limit: crate::expr_depth::MAX_EXPR_DEPTH,
            stage: "IR lowering",
        }
    );
}
