// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SpecFn::new lowering tests.

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

#[test]
fn lower_spec_fn_new_unary_closure() {
    let expr: syn::Expr = syn::parse_str("SpecFn::new(|x: i32| x + 1)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("SpecFn::new should lower");
    match result {
        TrustVcExpr::SpecClosure { params, body, ty } => {
            assert_eq!(
                params,
                vec![("x".to_string(), TrustVcType::Int { width: 32 })]
            );
            assert!(matches!(*body, TrustVcExpr::Arith { .. }));
            assert_eq!(
                ty,
                TrustVcType::SpecFn(
                    vec![TrustVcType::Int { width: 32 }],
                    Box::new(TrustVcType::Int { width: 32 })
                )
            );
        }
        other => panic!("expected SpecClosure, got {:?}", other),
    }
}

#[test]
fn lower_spec_fn_new_tuple_binder_flattens_param_types() {
    let expr: syn::Expr =
        syn::parse_str("SpecFn::new(|(i, x): (usize, i32)| x + (i as i32))").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("tuple-binder SpecFn::new should lower");
    match result {
        TrustVcExpr::SpecClosure { params, ty, .. } => {
            assert_eq!(
                params,
                vec![
                    (
                        "i".to_string(),
                        TrustVcType::Uint {
                            width: crate::ir::pointer_width(),
                        }
                    ),
                    ("x".to_string(), TrustVcType::Int { width: 32 }),
                ]
            );
            assert_eq!(
                ty,
                TrustVcType::SpecFn(
                    vec![
                        TrustVcType::Uint {
                            width: crate::ir::pointer_width(),
                        },
                        TrustVcType::Int { width: 32 },
                    ],
                    Box::new(TrustVcType::Int { width: 32 })
                )
            );
        }
        other => panic!("expected SpecClosure, got {:?}", other),
    }
}

#[test]
fn lower_spec_fn_call_preserves_generic_return_type() {
    let expr: syn::Expr = syn::parse_str("f.call(n + (k as int))").unwrap();
    let env = env_with(&[("f", "SpecFn<int, A>"), ("n", "int"), ("k", "nat")]);
    let result = lower_syn_expr(&expr, &env).expect("SpecFn<int, A>::call should lower");

    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(
                name,
                crate::ir_builder::spec_fn_apply_symbol(
                    &[TrustVcType::MathInt],
                    &TrustVcType::TypeParam("A".to_string()),
                )
            );
            assert_eq!(args.len(), 2);
            assert_eq!(return_ty, TrustVcType::TypeParam("A".to_string()));
        }
        other => panic!("expected SpecFn apply FnCall, got {:?}", other),
    }
}

#[test]
fn lower_spec_fn_new_rejects_empty_params() {
    let expr: syn::Expr = syn::parse_str("SpecFn::new(|| 42)").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("SpecFn::new with 0 params must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("at least one typed closure parameter"),
        "error should mention empty params, got: {msg}",
    );
}

#[test]
fn lower_spec_fn_new_rejects_non_closure_arg() {
    let expr: syn::Expr = syn::parse_str("SpecFn::new(42)").unwrap();
    let env = env_with(&[]);
    let err =
        lower_syn_expr(&expr, &env).expect_err("SpecFn::new with non-closure must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("must be closure"),
        "error should mention closure requirement, got: {msg}",
    );
}

#[test]
fn lower_spec_fn_new_rejects_tuple_binder_arity_mismatch() {
    let expr: syn::Expr = syn::parse_str("SpecFn::new(|(a, b): (i32, i32, i32)| a + b)").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("SpecFn::new with tuple arity mismatch must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("arity") || msg.contains("mismatch"),
        "error should mention arity mismatch, got: {msg}",
    );
}

// ----------------------------------------------------------------------------
// Bare spec-closure normalization (implicit `SpecFn::new(...)` in spec slots).
//
// A bare closure in a ghost-collection combinator slot must lower *identically*
// to the explicit `SpecFn::new(...)` form, must not double-wrap an already
// wrapped argument, and must never apply outside these spec slots (exec
// closures stay rejected at the standalone-closure guard).
// ----------------------------------------------------------------------------

#[test]
fn bare_closure_in_set_new_lowers_like_spec_fn_new() {
    let bare: syn::Expr = syn::parse_str("Set::<int>::new(|i: int| i >= 0)").unwrap();
    let wrapped: syn::Expr =
        syn::parse_str("Set::<int>::new(SpecFn::new(|i: int| i >= 0))").unwrap();
    let env = env_with(&[]);
    let bare = lower_syn_expr(&bare, &env).expect("bare Set::new closure should lower");
    let wrapped = lower_syn_expr(&wrapped, &env).expect("SpecFn::new Set::new should lower");
    assert_eq!(
        bare, wrapped,
        "bare Set::new closure must normalize to the SpecFn::new encoding"
    );
    match bare {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(args.len(), 1, "Set::new takes a single predicate arg");
            assert!(
                matches!(args[0], TrustVcExpr::SpecClosure { .. }),
                "Set::new predicate must be a SpecClosure, got {:?}",
                args[0]
            );
            assert_eq!(return_ty, TrustVcType::Set(Box::new(TrustVcType::MathInt)));
        }
        other => panic!("expected Set::new FnCall, got {other:?}"),
    }
}

#[test]
fn bare_untyped_closure_in_set_filter_infers_param_from_receiver() {
    let bare: syn::Expr = syn::parse_str("s.filter(|i| i > 0)").unwrap();
    let wrapped: syn::Expr = syn::parse_str("s.filter(SpecFn::new(|i: int| i > 0))").unwrap();
    let env = env_with(&[("s", "Set<int>")]);
    let bare = lower_syn_expr(&bare, &env).expect("bare untyped Set::filter closure should lower");
    let wrapped = lower_syn_expr(&wrapped, &env).expect("SpecFn::new Set::filter should lower");
    assert_eq!(
        bare, wrapped,
        "bare untyped filter closure must infer its param from the Set element type"
    );
    match bare {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SetFilter);
            assert_eq!(args.len(), 1);
            match &args[0] {
                TrustVcExpr::SpecClosure { params, ty, .. } => {
                    assert_eq!(params, &vec![("i".to_string(), TrustVcType::MathInt)]);
                    assert_eq!(
                        ty,
                        &TrustVcType::SpecFn(
                            vec![TrustVcType::MathInt],
                            Box::new(TrustVcType::Bool)
                        )
                    );
                }
                other => panic!("expected SpecClosure filter predicate, got {other:?}"),
            }
            assert_eq!(ty, TrustVcType::Set(Box::new(TrustVcType::MathInt)));
        }
        other => panic!("expected SetFilter CollectionOp, got {other:?}"),
    }
}

#[test]
fn bare_untyped_closure_in_set_map_infers_param_from_receiver() {
    let bare: syn::Expr = syn::parse_str("s.map(|i| i + 1)").unwrap();
    let wrapped: syn::Expr = syn::parse_str("s.map(SpecFn::new(|i: int| i + 1))").unwrap();
    let env = env_with(&[("s", "Set<int>")]);
    let bare = lower_syn_expr(&bare, &env).expect("bare untyped Set::map closure should lower");
    let wrapped = lower_syn_expr(&wrapped, &env).expect("SpecFn::new Set::map should lower");
    assert_eq!(
        bare, wrapped,
        "bare untyped map closure must normalize identically"
    );
    match bare {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::SetMap);
            assert_eq!(ty, TrustVcType::Set(Box::new(TrustVcType::MathInt)));
        }
        other => panic!("expected SetMap CollectionOp, got {other:?}"),
    }
}

#[test]
fn already_wrapped_spec_fn_in_filter_is_not_double_wrapped() {
    let expr: syn::Expr = syn::parse_str("s.filter(SpecFn::new(|i: int| i > 0))").unwrap();
    let env = env_with(&[("s", "Set<int>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("SpecFn::new filter should lower");
    let TrustVcExpr::CollectionOp { args, .. } = lowered else {
        panic!("expected SetFilter CollectionOp");
    };
    let [TrustVcExpr::SpecClosure { body, .. }] = args.as_slice() else {
        panic!("expected a single SpecClosure arg, got {args:?}");
    };
    // The predicate body is `i > 0` — a comparison, NOT a nested SpecClosure.
    // A double wrap would make the body itself a SpecClosure.
    assert!(
        !matches!(**body, TrustVcExpr::SpecClosure { .. }),
        "SpecFn::new arg must not be wrapped in a second SpecClosure, got {body:?}"
    );
}

#[test]
fn standalone_bare_closure_outside_spec_slot_is_still_rejected() {
    // Exec-closure soundness guard: a closure NOT in a spec-closure slot must
    // still be rejected by the standalone-closure error in `entry.rs`. The
    // normalization only ever fires for the enumerated combinator argument slots.
    let expr: syn::Expr = syn::parse_str("|i: int| i > 0").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("standalone closure must be rejected");
    assert!(
        err.to_string().contains("standalone closure"),
        "standalone closure must hit the spec-only guard, got: {err}"
    );
}

#[test]
fn bare_untyped_closure_in_set_new_fails_closed() {
    // `Set::new`'s element type is defined *by* the closure parameter, so an
    // untyped binder has no determinable type and must fail closed (no defaulting).
    let expr: syn::Expr = syn::parse_str("Set::<int>::new(|i| i >= 0)").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("untyped Set::new closure must fail closed without an annotation");
    assert!(
        err.to_string()
            .contains("requires an explicit type annotation"),
        "untyped Set::new closure should require an annotation, got: {err}"
    );
}
