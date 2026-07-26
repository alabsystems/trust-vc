// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cast and index expression lowering tests.

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

#[test]
fn lower_array_index() {
    let expr: syn::Expr = syn::parse_str("arr[0]").unwrap();
    let env = env_with(&[("arr", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(result, TrustVcExpr::Index { .. }));
}

#[test]
fn lower_native_array_index() {
    let expr: syn::Expr = syn::parse_str("arr[2usize]").unwrap();
    let env = env_with(&[("arr", "[u8; 4]")]);
    let result = lower_syn_expr(&expr, &env).expect("native array index should lower");
    match result {
        TrustVcExpr::Index {
            receiver,
            receiver_name,
            elem_ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("arr"));
            assert_eq!(elem_ty, TrustVcType::Uint { width: 8 });
            assert!(matches!(
                receiver.as_ref(),
                TrustVcExpr::Var {
                    name,
                    ty: TrustVcType::Array(_, 4)
                } if name == "arr"
            ));
        }
        other => panic!("expected native array Index expression, got {other:?}"),
    }
}

#[test]
fn lower_native_array_tuple_field_access() {
    let expr: syn::Expr = syn::parse_str("arr[0usize].1").unwrap();
    let env = env_with(&[("arr", "[(u64, u64); 3]")]);
    let result =
        lower_syn_expr(&expr, &env).expect("tuple field after native array index should lower");
    assert!(matches!(
        result,
        TrustVcExpr::FnCall { ref args, return_ty: TrustVcType::Uint { width: 64 }, .. }
            if matches!(args.as_slice(), [TrustVcExpr::Index { .. }])
    ));
}

#[test]
fn lower_nested_array_literal_second_index_does_not_reuse_outer_constructor_name() {
    let expr: syn::Expr = syn::parse_str("[[0u64, 1u64], [2u64, 3u64]][1usize][0usize]").unwrap();
    let env = TypeEnv::new();
    let result = lower_syn_expr(&expr, &env).expect("nested array literal index should lower");
    match result {
        TrustVcExpr::Index {
            receiver_name,
            receiver,
            elem_ty,
            ..
        } => {
            assert_eq!(receiver_name, None);
            assert_eq!(elem_ty, TrustVcType::Uint { width: 64 });
            assert!(matches!(receiver.as_ref(), TrustVcExpr::Index { .. }));
        }
        other => panic!("expected nested Index expression, got {other:?}"),
    }
}

#[test]
fn lower_map_bracket_index() {
    let expr: syn::Expr = syn::parse_str("m[5]").unwrap();
    let env = env_with(&[("m", "Map<i32, bool>")]);
    let result = lower_syn_expr(&expr, &env).expect("Map bracket index should lower");
    match result {
        TrustVcExpr::Index {
            receiver,
            index,
            receiver_name,
            elem_ty,
        } => {
            assert_eq!(receiver_name.as_deref(), Some("m"));
            assert_eq!(elem_ty, TrustVcType::Bool);
            assert!(matches!(
                receiver.as_ref(),
                TrustVcExpr::Var {
                    name,
                    ty: TrustVcType::Map(_, _)
                } if name == "m"
            ));
            assert!(matches!(
                index.as_ref(),
                TrustVcExpr::IntLit {
                    value: 5,
                    ty: TrustVcType::Int { width: 32 }
                }
            ));
        }
        other => panic!("expected Map Index expression, got {other:?}"),
    }
}

#[test]
fn lower_index_non_collection_receiver_fails_closed() {
    let expr: syn::Expr = syn::parse_str("x[0]").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("index on non-collection must fail");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference for invalid index receiver, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("indexing requires Seq/Map/array receiver"),
        "error should mention Seq/Map/array receiver requirement, got: {msg}",
    );
    assert!(
        msg.contains("i32"),
        "error should include concrete receiver type, got: {msg}",
    );
}

#[test]
fn lower_array_literal_desugars_to_seq_pushes() {
    let expr: syn::Expr = syn::parse_str("[1u8, 2u8, 3u8]").unwrap();
    let env = TypeEnv::new();
    let result = lower_syn_expr(&expr, &env).expect("array literal should lower");
    assert_eq!(
        infer_expr_type(&result),
        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
    );
    assert_eq!(seq_push_depth(&result), 3);
}

#[test]
fn lower_array_repeat_desugars_to_seq_pushes() {
    let expr: syn::Expr = syn::parse_str("[7u8; 3]").unwrap();
    let env = TypeEnv::new();
    let result = lower_syn_expr(&expr, &env).expect("array repeat should lower");
    assert_eq!(
        infer_expr_type(&result),
        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
    );
    assert_eq!(seq_push_depth(&result), 3);
}

fn seq_push_depth(expr: &TrustVcExpr) -> usize {
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver,
            ..
        } => 1 + seq_push_depth(receiver),
        TrustVcExpr::FnCall { args, .. } if args.is_empty() => 0,
        other => panic!("expected seq push chain, got {other:?}"),
    }
}

#[test]
fn lower_cast_normal_produces_cast_expr() {
    let expr: syn::Expr = syn::parse_str("x as u64").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).expect("normal cast should lower");
    match result {
        TrustVcExpr::Cast {
            ref expr,
            ref from_ty,
            ref to_ty,
        } => {
            assert_eq!(*from_ty, TrustVcType::Int { width: 32 });
            assert_eq!(*to_ty, TrustVcType::Uint { width: 64 });
            assert!(
                matches!(expr.as_ref(), TrustVcExpr::Var { name, .. } if name == "x"),
                "inner should be Var x, got: {expr:?}"
            );
        }
        other => panic!("expected Cast, got: {other:?}"),
    }
}

#[test]
fn lower_cast_to_bool_rejected() {
    let expr: syn::Expr = syn::parse_str("x as bool").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("cast to bool should be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported cast target type: bool"),
        "error should mention bool rejection, got: {msg}"
    );
}

#[test]
fn lower_cast_unsigned_to_signed() {
    let expr: syn::Expr = syn::parse_str("y as i32").unwrap();
    let env = env_with(&[("y", "u64")]);
    let result = lower_syn_expr(&expr, &env).expect("unsigned to signed cast should lower");
    match result {
        TrustVcExpr::Cast {
            ref from_ty,
            ref to_ty,
            ..
        } => {
            assert_eq!(*from_ty, TrustVcType::Uint { width: 64 });
            assert_eq!(*to_ty, TrustVcType::Int { width: 32 });
        }
        other => panic!("expected Cast, got: {other:?}"),
    }
}
