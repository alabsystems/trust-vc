//! Tests for binary and unary operator lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::*;

use super::tests_support::env_with;

// === Binary operations ===

#[test]
fn lower_add() {
    let expr: syn::Expr = syn::parse_str("x + y").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            ..
        }
    ));
}

#[test]
fn lower_seq_add_operator_as_concat() {
    let expr: syn::Expr = syn::parse_str("s + t").unwrap();
    let env = env_with(&[("s", "Seq<i32>"), ("t", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).unwrap();

    match result {
        TrustVcExpr::CollectionOp {
            op,
            receiver,
            receiver_name,
            args,
            ty,
        } => {
            assert_eq!(op, CollectionOp::Add);
            assert_eq!(receiver_name.as_deref(), Some("s"));
            assert_eq!(
                ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(matches!(
                receiver.as_ref(),
                TrustVcExpr::Var { name, .. } if name == "s"
            ));
            assert_eq!(args.len(), 1);
            assert!(matches!(
                &args[0],
                TrustVcExpr::Var { name, .. } if name == "t"
            ));
        }
        other => panic!("Seq + Seq should lower as CollectionOp::Add, got {other:?}"),
    }
}

#[test]
fn lower_comparison() {
    let expr: syn::Expr = syn::parse_str("x < y").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::Compare {
            op: CompareOp::Lt,
            ..
        }
    ));
}

#[test]
fn lower_internal_math_int_result_promotes_nested_finite_arithmetic() {
    let expr: syn::Expr = syn::parse_str("__trust_vc_math_int_expr((x + x) + x)").unwrap();
    let env = env_with(&[("x", "u16")]).with_source_catalog_math_int_marker();
    let result = lower_syn_expr(&expr, &env).unwrap();

    let TrustVcExpr::Arith { left, ty, .. } = result else {
        panic!("math-int marker should preserve the arithmetic tree");
    };
    assert_eq!(ty, TrustVcType::MathInt);
    assert!(matches!(
        left.as_ref(),
        TrustVcExpr::Arith {
            ty: TrustVcType::MathInt,
            ..
        }
    ));
}

#[test]
fn lower_internal_math_int_result_preserves_explicit_wrapping_boundary() {
    let expr: syn::Expr = syn::parse_str("__trust_vc_math_int_expr(x.wrapping_add(x))").unwrap();
    let env = env_with(&[("x", "u16")]).with_source_catalog_math_int_marker();
    let result = lower_syn_expr(&expr, &env).unwrap();

    assert!(matches!(
        result,
        TrustVcExpr::Cast {
            expr,
            from_ty: TrustVcType::Uint { width: 16 },
            to_ty: TrustVcType::MathInt,
        } if matches!(expr.as_ref(), TrustVcExpr::WrappingArith { .. })
    ));
}

#[test]
fn lower_authored_math_int_marker_without_capability_fails_closed() {
    let expr: syn::Expr = syn::parse_str("__trust_vc_math_int_expr(x + x)").unwrap();
    let err = lower_syn_expr(&expr, &env_with(&[("x", "u16")]))
        .expect_err("the source-catalog marker must default to unavailable");
    assert!(err
        .to_string()
        .contains("reserved source-catalog math-int marker"));
}

#[test]
fn lower_logical_and() {
    let expr: syn::Expr = syn::parse_str("a && b").unwrap();
    let env = env_with(&[("a", "bool"), ("b", "bool")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::Logic {
            op: LogicOp::And,
            ..
        }
    ));
}

#[test]
fn lower_bool_xor_as_inequality() {
    let expr: syn::Expr = syn::parse_str("a ^ b").unwrap();
    let env = env_with(&[("a", "bool"), ("b", "bool")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::Compare {
            op: CompareOp::Ne,
            ..
        }
    ));
}

#[test]
fn lower_shift_left() {
    let expr: syn::Expr = syn::parse_str("x << 2").unwrap();
    let env = env_with(&[("x", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl,
            ..
        }
    ));
}

// === Unary operations ===

#[test]
fn lower_not() {
    let expr: syn::Expr = syn::parse_str("!x").unwrap();
    let env = env_with(&[("x", "bool")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(result, TrustVcExpr::Not(_)));
}

#[test]
fn lower_neg() {
    let expr: syn::Expr = syn::parse_str("-x").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(result, TrustVcExpr::Neg(_)));
}

#[test]
fn lower_shared_reference_deref_is_transparent() {
    let expr: syn::Expr = syn::parse_str("*x").unwrap();
    let mut env = env_with(&[("x", "i32")]);
    env.insert_erased_shared_ref_var("x".to_string());
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::Var {
            name,
            ty: TrustVcType::Int { width: 32 }
        } if name == "x"
    ));
}

#[test]
fn lower_deref_without_reference_provenance_fails_closed() {
    let expr: syn::Expr = syn::parse_str("*x").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env);
    assert!(matches!(
        result,
        Err(LoweringError::UnsupportedUnOp(message))
            if message.contains("only supported for erased immutable reference variables")
    ));
}

#[test]
fn lower_over_deref_fails_closed() {
    let expr: syn::Expr = syn::parse_str("**x").unwrap();
    let mut env = env_with(&[("x", "i32")]);
    env.insert_erased_shared_ref_var("x".to_string());
    let result = lower_syn_expr(&expr, &env);
    assert!(matches!(
        result,
        Err(LoweringError::UnsupportedUnOp(message))
            if message.contains("only supported for erased immutable reference variables")
    ));
}
