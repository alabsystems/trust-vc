// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Collection-surface lowering tests (Seq, Set, Multiset, Map, String/str).

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

fn expect_lowered_collection_op(
    expr_src: &str,
    bindings: &[(&str, &str)],
    expected_op: CollectionOp,
    expected_ty: TrustVcType,
) {
    let expr: syn::Expr = syn::parse_str(expr_src).unwrap();
    let env = env_with(bindings);
    let result = lower_syn_expr(&expr, &env)
        .unwrap_or_else(|err| panic!("expected '{expr_src}' to lower successfully, got {err:?}"));
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, expected_op, "unexpected op for '{expr_src}'");
            assert_eq!(ty, expected_ty, "unexpected type for '{expr_src}'");
        }
        other => panic!("expected CollectionOp for '{expr_src}', got {other:?}"),
    }
}

#[test]
fn lower_collection_len() {
    let expr: syn::Expr = syn::parse_str("s.len()").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            ..
        }
    ));
}

#[test]
fn lower_collection_empty_constructor_to_typed_constant() {
    let expr: syn::Expr = syn::parse_str("trust_vc_types::Seq::<i32>::empty().push(10)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("typed Seq::empty() chain should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver,
            args,
            receiver_name,
            ty,
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "constructor-backed push should preserve a stable receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert!(
                        name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX),
                        "collection constructor should use dedicated symbol, got {name}"
                    );
                    assert!(args.is_empty(), "collection constructor must be zero-arity");
                    assert_eq!(return_ty, ty);
                }
                other => panic!("expected zero-arity constructor constant, got {other:?}"),
            }
        }
        other => panic!("expected Push collection op, got {other:?}"),
    }
}

#[test]
fn lower_collection_new_constructor_alias_chain_to_typed_constant() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Seq::<i32>::new().push_back(10)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("typed Seq::new().push_back() should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver,
            args,
            receiver_name,
            ty,
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "constructor-backed push_back should preserve a stable receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert!(
                        name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX),
                        "collection constructor should use dedicated symbol, got {name}"
                    );
                    assert!(args.is_empty(), "collection constructor must be zero-arity");
                    assert_eq!(return_ty, ty);
                }
                other => panic!("expected zero-arity constructor constant, got {other:?}"),
            }
        }
        other => panic!("expected Push collection op, got {other:?}"),
    }
}

#[test]
fn lower_set_new_constructor_intersection_alias() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Set::<i32>::new().intersection(other)").unwrap();
    let env = env_with(&[("other", "Set<i32>")]);
    let result =
        lower_syn_expr(&expr, &env).expect("typed Set::new().intersection() chain should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Intersect,
            receiver,
            args,
            receiver_name,
            ty,
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "constructor-backed intersection should preserve a stable receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert!(
                        name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX),
                        "collection constructor should use dedicated symbol, got {name}"
                    );
                    assert!(args.is_empty(), "collection constructor must be zero-arity");
                    assert_eq!(
                        return_ty,
                        TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
                    );
                }
                other => panic!("expected zero-arity constructor constant, got {other:?}"),
            }
        }
        other => panic!("expected Intersect collection op, got {other:?}"),
    }
}

#[test]
fn lower_map_new_constructor_contains_alias() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Map::<i32, bool>::new().contains(5)").unwrap();
    let env = env_with(&[]);
    let result =
        lower_syn_expr(&expr, &env).expect("typed Map::new().contains() chain should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::ContainsKey,
            receiver,
            args,
            receiver_name,
            ty,
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Bool);
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "constructor-backed contains should preserve a stable receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert!(
                        name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX),
                        "collection constructor should use dedicated symbol, got {name}"
                    );
                    assert!(args.is_empty(), "collection constructor must be zero-arity");
                    assert_eq!(
                        return_ty,
                        TrustVcType::Map(
                            Box::new(TrustVcType::Int { width: 32 }),
                            Box::new(TrustVcType::Bool)
                        )
                    );
                }
                other => panic!("expected zero-arity constructor constant, got {other:?}"),
            }
        }
        other => panic!("expected ContainsKey collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_new_constructor_stays_unsupported() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Multiset::<i32>::new().contains(10)").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("Multiset::new() should stay unsupported");
    assert!(
        matches!(
            err,
            LoweringError::TypeInference(_)
                | LoweringError::UnsupportedMethod(_)
                | LoweringError::UnsupportedExpr(_)
        ),
        "expected Multiset::new() to fail closed, got {err:?}"
    );
    assert!(
        err.to_string().contains("new"),
        "expected Multiset::new() rejection to mention the unsupported constructor, got {err}"
    );
}

#[test]
fn lower_multiset_empty_constructor_contains_chain() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Multiset::<i32>::empty().contains(10)").unwrap();
    let env = env_with(&[]);
    let result =
        lower_syn_expr(&expr, &env).expect("typed Multiset::empty().contains() chain should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Contains,
            receiver,
            args,
            receiver_name,
            ty,
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Bool);
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "constructor-backed contains should preserve a stable receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert!(
                        name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX),
                        "collection constructor should use dedicated symbol, got {name}"
                    );
                    assert!(args.is_empty(), "collection constructor must be zero-arity");
                    assert_eq!(
                        return_ty,
                        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
                    );
                }
                other => panic!("expected zero-arity constructor constant, got {other:?}"),
            }
        }
        other => panic!("expected Contains collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_insert_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("ms.insert(10)").unwrap();
    let env = env_with(&[("ms", "Multiset<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("multiset insert should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("ms"));
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
            );
        }
        other => panic!("expected Insert collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_count_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("ms.count(10)").unwrap();
    let env = env_with(&[("ms", "Multiset<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("multiset count should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Count,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("ms"));
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Nat);
        }
        other => panic!("expected Count collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_u64_count_coerces_unsuffixed_literal_arg() {
    let expr: syn::Expr = syn::parse_str("ms.count(5)").unwrap();
    let env = env_with(&[("ms", "Multiset<u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("Multiset<u64>::count(5) should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Count,
            args,
            ty,
            ..
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Nat);
            assert_eq!(
                infer_expr_type(&args[0]),
                TrustVcType::Uint { width: 64 },
                "unsuffixed count key should inherit the Multiset<u64> element type"
            );
        }
        other => panic!("expected Count collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_u64_insert_coerces_unsuffixed_literal_arg() {
    let expr: syn::Expr = syn::parse_str("ms.insert(5)").unwrap();
    let env = env_with(&[("ms", "Multiset<u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("Multiset<u64>::insert(5) should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            args,
            ty,
            ..
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Multiset(Box::new(TrustVcType::Uint { width: 64 }))
            );
            assert_eq!(
                infer_expr_type(&args[0]),
                TrustVcType::Uint { width: 64 },
                "unsuffixed insert key should inherit the Multiset<u64> element type"
            );
        }
        other => panic!("expected Insert collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_u64_remove_coerces_unsuffixed_literal_arg() {
    let expr: syn::Expr = syn::parse_str("ms.remove(5)").unwrap();
    let env = env_with(&[("ms", "Multiset<u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("Multiset<u64>::remove(5) should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Remove,
            args,
            ty,
            ..
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Multiset(Box::new(TrustVcType::Uint { width: 64 }))
            );
            assert_eq!(
                infer_expr_type(&args[0]),
                TrustVcType::Uint { width: 64 },
                "unsuffixed remove key should inherit the Multiset<u64> element type"
            );
        }
        other => panic!("expected Remove collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_usize_insert_remove_count_coerces_unsuffixed_literal_args() {
    let expr: syn::Expr = syn::parse_str("ms.insert(5).remove(5).count(5)").unwrap();
    let env = env_with(&[("ms", "Multiset<usize>")]);
    let result = lower_syn_expr(&expr, &env)
        .expect("Multiset<usize>::insert(5).remove(5).count(5) should lower");
    let usize_ty = TrustVcType::parse_or_opaque("usize");
    let multiset_usize_ty = TrustVcType::Multiset(Box::new(usize_ty.clone()));

    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Count,
            receiver,
            args,
            ty,
            ..
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Nat);
            assert_eq!(
                infer_expr_type(&args[0]),
                usize_ty.clone(),
                "unsuffixed count key should inherit the Multiset<usize> element type"
            );
            match *receiver {
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::Remove,
                    receiver: remove_receiver,
                    args: remove_args,
                    ty: remove_ty,
                    ..
                } => {
                    assert_eq!(remove_ty, multiset_usize_ty.clone());
                    assert_eq!(remove_args.len(), 1);
                    assert_eq!(
                        infer_expr_type(&remove_args[0]),
                        usize_ty.clone(),
                        "unsuffixed remove key should inherit the Multiset<usize> element type"
                    );
                    match *remove_receiver {
                        TrustVcExpr::CollectionOp {
                            op: CollectionOp::Insert,
                            args: insert_args,
                            ty: insert_ty,
                            ..
                        } => {
                            assert_eq!(insert_ty, multiset_usize_ty);
                            assert_eq!(insert_args.len(), 1);
                            assert_eq!(
                                infer_expr_type(&insert_args[0]),
                                usize_ty,
                                "unsuffixed insert key should inherit the Multiset<usize> element type"
                            );
                        }
                        other => panic!("expected nested Insert collection op, got {other:?}"),
                    }
                }
                other => panic!("expected nested Remove collection op, got {other:?}"),
            }
        }
        other => panic!("expected Count collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_choose_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("ms.choose()").unwrap();
    let env = env_with(&[("ms", "Multiset<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("multiset choose should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Choose,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("ms"));
            assert!(args.is_empty(), "choose() takes no arguments");
            assert_eq!(ty, TrustVcType::Int { width: 32 });
        }
        other => panic!("expected Choose collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_choose_rejects_arguments() {
    let expr: syn::Expr = syn::parse_str("ms.choose(10)").unwrap();
    let env = env_with(&[("ms", "Multiset<i32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("choose() with arguments must fail");
    assert!(
        err.to_string().contains("requires 0 arguments"),
        "unexpected choose() arity error: {err}"
    );
}

#[test]
fn lower_set_choose_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("s.choose()").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("set choose should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Choose,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("s"));
            assert!(args.is_empty(), "choose() takes no arguments");
            assert_eq!(ty, TrustVcType::Int { width: 32 });
        }
        other => panic!("expected Choose collection op, got {other:?}"),
    }
}

#[test]
fn lower_set_finite_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("s.finite()").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("set finite should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Finite,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("s"));
            assert!(args.is_empty(), "finite() takes no arguments");
            assert_eq!(ty, TrustVcType::Bool);
        }
        other => panic!("expected Finite collection op, got {other:?}"),
    }
}

#[test]
fn lower_multiset_remove_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("ms.remove(10)").unwrap();
    let env = env_with(&[("ms", "Multiset<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("multiset remove should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Remove,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("ms"));
            assert_eq!(args.len(), 1);
            assert_eq!(
                ty,
                TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
            );
        }
        other => panic!("expected Remove collection op, got {other:?}"),
    }
}

#[test]
fn lower_map_index_method_as_get() {
    let expr: syn::Expr = syn::parse_str("m.index(5)").unwrap();
    let env = env_with(&[("m", "Map<i32, bool>")]);
    let result = lower_syn_expr(&expr, &env).unwrap_or_else(|err| {
        panic!("Map::index method should lower as get, got {err:?}");
    });
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Get,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("m"));
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Bool);
        }
        other => panic!("expected Get collection op, got {other:?}"),
    }
}

#[cfg(not(feature = "native-strings"))]
#[test]
fn lower_string_view_returns_seq_char() {
    let expr: syn::Expr = syn::parse_str("s.view()").unwrap();
    let env = env_with(&[("s", "String")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::View,
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".to_string(),
                ty: TrustVcType::String,
            }),
            receiver_name: Some("s".to_string()),
            args: vec![],
            ty: TrustVcType::Seq(Box::new(TrustVcType::Char)),
        }
    );
}

#[cfg(not(feature = "native-strings"))]
#[test]
fn lower_str_view_returns_seq_char() {
    let expr: syn::Expr = syn::parse_str("s.view()").unwrap();
    let env = env_with(&[("s", "str")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::View,
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".to_string(),
                ty: TrustVcType::StrSlice,
            }),
            receiver_name: Some("s".to_string()),
            args: vec![],
            ty: TrustVcType::Seq(Box::new(TrustVcType::Char)),
        }
    );
}

#[cfg(not(feature = "native-strings"))]
#[test]
fn lower_string_len_is_rejected_with_view_hint() {
    let expr: syn::Expr = syn::parse_str("s.len()").unwrap();
    let env = env_with(&[("s", "String")]);
    let err = lower_syn_expr(&expr, &env).expect_err("direct String::len must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported in this slice"),
        "unexpected error: {msg}"
    );
    assert!(
        msg.contains("s.view()"),
        "error must point users to view(): {msg}"
    );
}

#[cfg(not(feature = "native-strings"))]
#[test]
fn lower_str_len_is_rejected_with_view_hint() {
    let expr: syn::Expr = syn::parse_str("s.len()").unwrap();
    let env = env_with(&[("s", "str")]);
    let err = lower_syn_expr(&expr, &env).expect_err("direct str::len must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    let msg = err.to_string();
    assert!(
        msg.contains("unsupported in this slice"),
        "unexpected error: {msg}"
    );
    assert!(
        msg.contains("s.view()"),
        "error must point users to view(): {msg}"
    );
}

#[cfg(feature = "native-strings")]
#[test]
fn lower_string_len_lowers_directly() {
    let expr: syn::Expr = syn::parse_str("s.len()").unwrap();
    let env = env_with(&[("s", "String")]);
    let result = lower_syn_expr(&expr, &env).expect("direct String::len should lower");
    assert_eq!(
        result,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".to_string(),
                ty: TrustVcType::String,
            }),
            receiver_name: Some("s".to_string()),
            args: vec![],
            ty: TrustVcType::Uint {
                width: crate::ir::pointer_width(),
            },
        }
    );
}

#[cfg(feature = "native-strings")]
#[test]
fn lower_string_contains_lowers_directly() {
    let expr: syn::Expr = syn::parse_str("s.contains(\"ell\")").unwrap();
    let env = env_with(&[("s", "String")]);
    let result = lower_syn_expr(&expr, &env).expect("String::contains should lower");
    assert_eq!(
        result,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Contains,
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".to_string(),
                ty: TrustVcType::String,
            }),
            receiver_name: Some("s".to_string()),
            args: vec![TrustVcExpr::StringLit("ell".into())],
            ty: TrustVcType::Bool,
        }
    );
}

#[cfg(feature = "native-strings")]
#[test]
fn lower_string_starts_with_lowers_to_native_fn() {
    let expr: syn::Expr = syn::parse_str("s.starts_with(\"he\")").unwrap();
    let env = env_with(&[("s", "String")]);
    let result = lower_syn_expr(&expr, &env).expect("String::starts_with should lower");
    assert_eq!(
        result,
        TrustVcExpr::FnCall {
            name: NATIVE_STRING_STARTS_WITH_FN.to_string(),
            args: vec![
                TrustVcExpr::Var {
                    name: "s".to_string(),
                    ty: TrustVcType::String,
                },
                TrustVcExpr::StringLit("he".into()),
            ],
            return_ty: TrustVcType::Bool,
        }
    );
}

#[cfg(feature = "native-strings")]
#[test]
fn lower_string_ends_with_lowers_to_native_fn() {
    let expr: syn::Expr = syn::parse_str("s.ends_with(\"lo\")").unwrap();
    let env = env_with(&[("s", "String")]);
    let result = lower_syn_expr(&expr, &env).expect("String::ends_with should lower");
    assert_eq!(
        result,
        TrustVcExpr::FnCall {
            name: NATIVE_STRING_ENDS_WITH_FN.to_string(),
            args: vec![
                TrustVcExpr::Var {
                    name: "s".to_string(),
                    ty: TrustVcType::String,
                },
                TrustVcExpr::StringLit("lo".into()),
            ],
            return_ty: TrustVcType::Bool,
        }
    );
}

#[cfg(feature = "native-strings")]
#[test]
fn lower_string_view_lowers_to_seq_char_bridge() {
    let expr: syn::Expr = syn::parse_str("s.view()").unwrap();
    let env = env_with(&[("s", "String")]);
    let result = lower_syn_expr(&expr, &env).expect("view() should lower under native-strings");
    assert_eq!(
        result,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::View,
            receiver: Box::new(TrustVcExpr::Var {
                name: "s".to_string(),
                ty: TrustVcType::String,
            }),
            receiver_name: Some("s".to_string()),
            args: vec![],
            ty: TrustVcType::Seq(Box::new(TrustVcType::Char)),
        }
    );
}

#[test]
fn lower_collection_get_non_collection_receiver_fails_closed() {
    let expr: syn::Expr = syn::parse_str("x.get(0)").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("get() on non-collection must fail");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference for invalid get() receiver, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("requires Seq/Map/array receiver"),
        "error should mention Seq/Map/array receiver requirement, got: {msg}",
    );
    assert!(
        msg.contains("i32"),
        "error should include concrete receiver type, got: {msg}",
    );
}

#[test]
fn lower_collection_first_non_collection_receiver_fails_closed() {
    let expr: syn::Expr = syn::parse_str("x.first()").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("first() on non-collection must fail");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference for invalid first() receiver, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("first"),
        "error should include operation name, got: {msg}",
    );
    assert!(
        msg.contains("requires Seq/Map/array receiver"),
        "error should mention Seq/Map/array receiver requirement, got: {msg}",
    );
    assert!(
        msg.contains("i32"),
        "error should include concrete receiver type, got: {msg}",
    );
}

#[test]
fn lower_collection_last_non_collection_receiver_fails_closed() {
    let expr: syn::Expr = syn::parse_str("x.last()").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("last() on non-collection must fail");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference for invalid last() receiver, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("last"),
        "error should include operation name, got: {msg}",
    );
    assert!(
        msg.contains("requires Seq/Map/array receiver"),
        "error should mention Seq/Map/array receiver requirement, got: {msg}",
    );
    assert!(
        msg.contains("i32"),
        "error should include concrete receiver type, got: {msg}",
    );
}

#[test]
fn lower_map_dom_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("m.dom()").unwrap();
    let env = env_with(&[("m", "Map<i32, u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("map dom should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Dom,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("m"));
            assert!(args.is_empty(), "dom() takes no arguments, got: {args:?}");
            assert_eq!(
                ty,
                TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 })),
                "dom() on Map<i32, u64> should return Set<i32>"
            );
        }
        other => panic!("expected Dom collection op, got: {other:?}"),
    }
}

#[test]
fn lower_map_contains_key_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("m.contains_key(k)").unwrap();
    let env = env_with(&[("m", "Map<i32, u64>"), ("k", "i32")]);
    let result = lower_syn_expr(&expr, &env).expect("map contains_key should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::ContainsKey,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("m"));
            assert_eq!(args.len(), 1, "contains_key takes 1 argument");
            assert_eq!(ty, TrustVcType::Bool, "contains_key returns Bool");
        }
        other => panic!("expected ContainsKey collection op, got: {other:?}"),
    }
}

#[test]
fn lower_map_contains_key_with_literal_arg() {
    let expr: syn::Expr = syn::parse_str("m.contains_key(42)").unwrap();
    let env = env_with(&[("m", "Map<i32, u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("contains_key with literal should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::ContainsKey,
            args,
            ty,
            ..
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Bool);
            assert!(
                matches!(&args[0], TrustVcExpr::IntLit { value, .. } if *value == 42),
                "argument should be integer literal 42, got: {:?}",
                args[0]
            );
        }
        other => panic!("expected ContainsKey collection op, got: {other:?}"),
    }
}

#[test]
fn lower_map_contains_value_produces_collection_op() {
    let expr: syn::Expr = syn::parse_str("m.contains_value(v)").unwrap();
    let env = env_with(&[("m", "Map<i32, u64>"), ("v", "u64")]);
    let result = lower_syn_expr(&expr, &env).expect("map contains_value should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::ContainsValue,
            receiver_name,
            args,
            ty,
            ..
        } => {
            assert_eq!(receiver_name.as_deref(), Some("m"));
            assert_eq!(args.len(), 1, "contains_value takes 1 argument");
            assert_eq!(ty, TrustVcType::Bool, "contains_value returns Bool");
        }
        other => panic!("expected ContainsValue collection op, got: {other:?}"),
    }
}

#[test]
fn lower_seq_reverse_produces_collection_op() {
    expect_lowered_collection_op(
        "s.reverse()",
        &[("s", "Seq<i32>")],
        CollectionOp::Reverse,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
}

#[test]
fn lower_seq_no_duplicates_produces_collection_op() {
    expect_lowered_collection_op(
        "s.no_duplicates()",
        &[("s", "Seq<i32>")],
        CollectionOp::NoDuplicates,
        TrustVcType::Bool,
    );
}

#[test]
fn lower_seq_to_set_produces_collection_op() {
    expect_lowered_collection_op(
        "s.to_set()",
        &[("s", "Seq<i32>")],
        CollectionOp::ToSet,
        TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 })),
    );
}

#[test]
fn lower_seq_to_multiset_produces_collection_op() {
    expect_lowered_collection_op(
        "s.to_multiset()",
        &[("s", "Seq<i32>")],
        CollectionOp::ToMultiset,
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 })),
    );
}

#[test]
fn lower_trust_wp_compat_alias_methods_match_canonical_collection_ops() {
    let seq_i32 = TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }));
    let set_i32 = TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }));

    expect_lowered_collection_op(
        "s.push_back(10)",
        &[("s", "Seq<i32>")],
        CollectionOp::Push,
        seq_i32.clone(),
    );
    expect_lowered_collection_op(
        "s.pop_back()",
        &[("s", "Seq<i32>")],
        CollectionOp::DropLast,
        seq_i32.clone(),
    );
    expect_lowered_collection_op(
        "s.subsequence(0, 2)",
        &[("s", "Seq<i32>")],
        CollectionOp::Subrange,
        seq_i32.clone(),
    );
    expect_lowered_collection_op(
        "s.set(1, 9)",
        &[("s", "Seq<i32>")],
        CollectionOp::Update,
        seq_i32,
    );
    expect_lowered_collection_op(
        "left.intersection(right)",
        &[("left", "Set<i32>"), ("right", "Set<i32>")],
        CollectionOp::Intersect,
        set_i32.clone(),
    );
    expect_lowered_collection_op(
        "left.is_subset(right)",
        &[("left", "Set<i32>"), ("right", "Set<i32>")],
        CollectionOp::Subset,
        TrustVcType::Bool,
    );
    expect_lowered_collection_op(
        "left.is_superset(right)",
        &[("left", "Set<i32>"), ("right", "Set<i32>")],
        CollectionOp::Superset,
        TrustVcType::Bool,
    );
    expect_lowered_collection_op(
        "m.contains(k)",
        &[("m", "Map<i32, bool>"), ("k", "i32")],
        CollectionOp::ContainsKey,
        TrustVcType::Bool,
    );
    expect_lowered_collection_op(
        "m.lookup(k)",
        &[("m", "Map<i32, bool>"), ("k", "i32")],
        CollectionOp::Get,
        TrustVcType::Bool,
    );
}

#[test]
fn lower_set_subset_returns_bool() {
    let expr: syn::Expr = syn::parse_str("a.subset(b)").unwrap();
    let env = env_with(&[("a", "Set<i32>"), ("b", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::subset should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::Subset);
            assert_eq!(ty, TrustVcType::Bool);
        }
        other => panic!("expected Subset CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_set_superset_returns_bool() {
    let expr: syn::Expr = syn::parse_str("a.superset(b)").unwrap();
    let env = env_with(&[("a", "Set<i32>"), ("b", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::superset should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::Superset);
            assert_eq!(ty, TrustVcType::Bool);
        }
        other => panic!("expected Superset CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_set_difference_returns_receiver_type() {
    let expr: syn::Expr = syn::parse_str("a.difference(b)").unwrap();
    let env = env_with(&[("a", "Set<i32>"), ("b", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::difference should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::Difference);
            assert_eq!(
                ty,
                TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
            );
        }
        other => panic!("expected Difference CollectionOp, got {:?}", other),
    }
}

// ========================================================================
// Multiset::difference / sub / singleton  (#2604)
// ========================================================================

#[test]
fn lower_multiset_difference_produces_collection_op() {
    expect_lowered_collection_op(
        "ms.difference(other)",
        &[("ms", "Multiset<i32>"), ("other", "Multiset<i32>")],
        CollectionOp::Difference,
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 })),
    );
}

#[test]
fn lower_multiset_sub_produces_difference_op() {
    expect_lowered_collection_op(
        "ms.sub(other)",
        &[("ms", "Multiset<i32>"), ("other", "Multiset<i32>")],
        CollectionOp::Difference,
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 })),
    );
}

#[test]
fn lower_multiset_add_produces_union_op() {
    expect_lowered_collection_op(
        "ms.add(other)",
        &[("ms", "Multiset<i32>"), ("other", "Multiset<i32>")],
        CollectionOp::Union,
        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 })),
    );
}

#[test]
fn lower_multiset_singleton_desugars_to_insert_over_empty() {
    let expr: syn::Expr = syn::parse_str("trust_vc_types::Multiset::<i32>::singleton(5)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Multiset::singleton(5) should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            receiver_name,
            ty,
        } => {
            assert_eq!(args.len(), 1, "singleton desugars to insert with 1 arg");
            assert_eq!(
                ty,
                TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "singleton should preserve constructor-backed receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::FnCall {
                    name,
                    args: ctor_args,
                    return_ty,
                } => {
                    assert!(
                        name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX),
                        "inner receiver should be a zero-arity empty constructor, got {name}"
                    );
                    assert!(ctor_args.is_empty(), "empty constructor must be zero-arity");
                    assert_eq!(
                        return_ty,
                        TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 }))
                    );
                }
                other => panic!("expected zero-arity empty constructor, got {other:?}"),
            }
        }
        other => panic!("expected Insert CollectionOp from singleton, got {other:?}"),
    }
}

#[test]
fn lower_multiset_singleton_chain_preserves_receiver_name() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Multiset::<i32>::singleton(5).count(5)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Multiset::singleton(5).count(5) should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Count,
            receiver,
            receiver_name,
            ..
        } => {
            assert!(
                receiver_name
                    .as_deref()
                    .is_some_and(|name| name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX)),
                "chained count should resolve constructor-backed receiver name, got {receiver_name:?}"
            );
            match *receiver {
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::Insert,
                    ..
                } => {} // expected: singleton desugared to insert
                other => panic!("expected Insert from singleton desugar, got {other:?}"),
            }
        }
        other => panic!("expected Count CollectionOp, got {other:?}"),
    }
}

#[test]
fn public_seq_surface_methods_do_not_return_unsupported_method() {
    let env = env_with(&[("s", "Seq<i32>"), ("t", "Seq<i32>")]);
    let cases = [
        "s.len()",
        "s.is_empty()",
        "s.index(0)",
        "s.get(0)",
        "s.push(1)",
        "s.push_back(1)",
        "s.add(t)",
        "s.concat(t)",
        "s.first()",
        "s.last()",
        "s.update(0, 1)",
        "s.set(0, 1)",
        "s.drop_last()",
        "s.pop_back()",
        "s.drop_first()",
        "s.take(1)",
        "s.skip(1)",
        "s.subrange(0, 1)",
        "s.subsequence(0, 1)",
        "s.contains(1)",
        "Seq::<i32>::from_fn(3usize, SpecFn::new(|i: usize| i as i32))",
        "Seq::<i32>::new(3usize, SpecFn::new(|i: usize| i as i32))",
        "s.map_values(SpecFn::new(|x: i32| x + 1))",
        "s.map(SpecFn::new(|(i, x): (usize, i32)| x + (i as i32)))",
        "s.filter(SpecFn::new(|x: i32| x > 0))",
        "s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x + 1)))",
        "s.fold_left(0, SpecFn::new(|acc: i32, x: i32| acc + x))",
        "s.fold_right(0, SpecFn::new(|x: i32, acc: i32| x - acc))",
        "s.to_set()",
        "s.to_multiset()",
        "s.reverse()",
        "s.no_duplicates()",
    ];

    for expr_src in cases {
        let expr: syn::Expr = syn::parse_str(expr_src).unwrap();
        let result = lower_syn_expr(&expr, &env);
        if let Err(LoweringError::UnsupportedMethod(msg)) = &result {
            panic!("public Seq method '{expr_src}' returned UnsupportedMethod: {msg}");
        }
        result.unwrap_or_else(|err| {
            panic!("expected '{expr_src}' to lower successfully, got {err:?}")
        });
    }
}

#[test]
fn lower_seq_new_generator_alias_to_synthetic_builtin() {
    let expr: syn::Expr =
        syn::parse_str("Seq::<i32>::new(3usize, SpecFn::new(|i: usize| i as i32))").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::new(len, generator) should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, crate::ir_lowering::SEQ_FROM_FN_BUILTIN);
            assert_eq!(args.len(), 2);
            assert_eq!(
                return_ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(matches!(
                &args[0],
                TrustVcExpr::IntLit {
                    value: 3,
                    ty: TrustVcType::Uint { .. },
                }
            ));
            assert!(matches!(&args[1], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected Seq::new synthetic FnCall, got {other:?}"),
    }
}

#[test]
fn lower_seq_from_fn_to_synthetic_builtin() {
    let expr: syn::Expr = syn::parse_str(
        "trust_vc_types::Seq::<i32>::from_fn(3usize, SpecFn::new(|i: usize| i as i32))",
    )
    .unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::from_fn should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, crate::ir_lowering::SEQ_FROM_FN_BUILTIN);
            assert_eq!(args.len(), 2);
            assert_eq!(
                return_ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert!(matches!(
                &args[0],
                TrustVcExpr::IntLit {
                    value: 3,
                    ty: TrustVcType::Uint { .. },
                }
            ));
            assert!(matches!(&args[1], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected Seq::from_fn synthetic FnCall, got {other:?}"),
    }
}

#[test]
fn lower_seq_from_fn_coerces_unsuffixed_literal_body_to_explicit_elem_type() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Seq::<usize>::from_fn(3usize, SpecFn::new(|i: usize| 0))")
            .unwrap();
    let env = env_with(&[]);
    let result =
        lower_syn_expr(&expr, &env).expect("Seq::<usize>::from_fn literal body should lower");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(
                return_ty,
                TrustVcType::Seq(Box::new(TrustVcType::Uint {
                    width: crate::ir::pointer_width()
                }))
            );
            let TrustVcExpr::SpecClosure { body, ty, .. } = &args[1] else {
                panic!("expected SpecClosure arg, got {:?}", args[1]);
            };
            assert!(matches!(
                body.as_ref(),
                TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::Uint { .. },
                }
            ));
            assert!(matches!(
                ty,
                TrustVcType::SpecFn(_, ret_ty)
                    if matches!(ret_ty.as_ref(), TrustVcType::Uint { width } if *width == crate::ir::pointer_width())
            ));
        }
        other => panic!("expected Seq::from_fn synthetic FnCall, got {other:?}"),
    }
}

#[test]
fn lower_seq_from_fn_rejects_non_usize_length_expression() {
    let expr: syn::Expr =
        syn::parse_str("trust_vc_types::Seq::<i32>::from_fn(n, SpecFn::new(|i: usize| i as i32))")
            .unwrap();
    let env = env_with(&[("n", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("non-usize Seq::from_fn len must fail");
    let message = err.to_string();
    assert!(
        message.contains("length argument must be usize"),
        "error should explain the usize length requirement, got: {message}"
    );
}
