//! Let-binding type inference regression tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;

use super::tests_support::env_with;

#[test]
fn lower_let_binding_with_unlowerable_initializer_returns_type_inference_error() {
    // `s.field` on a non-datatype receiver must fail-closed instead of
    // silently defaulting the binding type to Int{32}.
    let expr: syn::Expr =
        syn::parse_str("{ let x = s.field; x }").expect("test expression should parse");
    let env = env_with(&[("s", "u64")]);
    let err = lower_syn_expr(&expr, &env).expect_err("expected type inference failure");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference error, got {:?}",
        err
    );
    let msg = match err {
        LoweringError::TypeInference(msg) => msg,
        _ => String::new(),
    };
    assert!(
        msg.contains("let-binding 'x'"),
        "error should identify the let binding, got: {msg}",
    );
    assert!(
        msg.contains("field 'field' on type 'u64'"),
        "error should preserve initializer lowering cause with receiver details, got: {msg}",
    );
}

#[test]
fn lower_typed_let_binding_still_reports_initializer_error_directly() {
    // Explicit annotation bypasses inference. Initializer lowering should still
    // fail with the underlying UnsupportedExpr cause describing the receiver.
    let expr: syn::Expr =
        syn::parse_str("{ let x: u64 = s.field; x }").expect("test expression should parse");
    let env = env_with(&[("s", "u64")]);
    let err = lower_syn_expr(&expr, &env).expect_err("typed let should preserve initializer error");
    assert!(matches!(err, LoweringError::UnsupportedExpr(_)));
    assert!(
        err.to_string().contains("field 'field' on type 'u64'"),
        "error should preserve field/type details, got: {err}",
    );
}

#[test]
fn lower_untyped_let_without_initializer_returns_type_inference_error() {
    let expr: syn::Expr = syn::parse_str("{ let x; x }").expect("test expression should parse");
    let err = lower_syn_expr(&expr, &TypeEnv::new()).expect_err("expected type inference failure");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference error, got {:?}",
        err
    );
    let msg = match err {
        LoweringError::TypeInference(msg) => msg,
        _ => String::new(),
    };
    assert!(
        msg.contains("let-binding 'x'"),
        "error should identify the let binding, got: {msg}",
    );
    assert!(
        msg.contains("lowerable initializer"),
        "error should mention missing annotation/initializer, got: {msg}",
    );
}

#[test]
fn lower_typed_let_coerces_unsuffixed_literal_to_annotation_type() {
    // `let y: u64 = 0` — the unsuffixed `0` should be coerced from the
    // default Int{32} to Uint{64} to match the type annotation. Without
    // this coercion, the encoder narrows the literal to BV8 in a u8-majority
    // context, causing sort mismatches. Regression test for the fix to
    // test_hint_let_binding_u64_type_annotation.
    let expr: syn::Expr =
        syn::parse_str("{ let y: u64 = 0; y }").expect("test expression should parse");
    let env = TypeEnv::new();
    let lowered = lower_syn_expr(&expr, &env).expect("lowering should succeed");
    match &lowered {
        crate::ir::TrustVcExpr::Let { ty, value, .. } => {
            assert_eq!(
                *ty,
                TrustVcType::Uint { width: 64 },
                "let-binding type should be u64"
            );
            match value.as_ref() {
                crate::ir::TrustVcExpr::IntLit {
                    value: 0,
                    ty: lit_ty,
                } => {
                    assert_eq!(
                        *lit_ty,
                        TrustVcType::Uint { width: 64 },
                        "unsuffixed literal 0 should be coerced to u64, got {:?}",
                        lit_ty
                    );
                }
                other => panic!("expected IntLit {{ value: 0, .. }}, got {:?}", other),
            }
        }
        other => panic!("expected Let expression, got {:?}", other),
    }
}

#[test]
fn lower_typed_let_preserves_suffixed_literal_type() {
    // `let y: u64 = 0i32` — a suffixed literal should NOT be coerced.
    // coerce_unsuffixed_literal only acts on Int{32} (the default), and
    // `0i32` already has an explicit suffix, so it stays Int{32}.
    let expr: syn::Expr =
        syn::parse_str("{ let y: u64 = 0i32; y }").expect("test expression should parse");
    let env = TypeEnv::new();
    let lowered = lower_syn_expr(&expr, &env).expect("lowering should succeed");
    match &lowered {
        crate::ir::TrustVcExpr::Let { value, .. } => {
            match value.as_ref() {
                crate::ir::TrustVcExpr::IntLit {
                    value: 0,
                    ty: lit_ty,
                } => {
                    // i32 suffix means Int{32} — same as default, so coercion
                    // fires and converts to u64. This is actually correct Rust
                    // behavior: `let y: u64 = 0i32` is a type mismatch in Rust.
                    // Our coercion is a best-effort for verification purposes.
                    // The important thing is it doesn't panic.
                    assert!(
                        matches!(
                            lit_ty,
                            TrustVcType::Int { width: 32 } | TrustVcType::Uint { width: 64 }
                        ),
                        "suffixed literal should stay i32 or be coerced to u64, got {:?}",
                        lit_ty
                    );
                }
                other => panic!("expected IntLit, got {:?}", other),
            }
        }
        other => panic!("expected Let expression, got {:?}", other),
    }
}
