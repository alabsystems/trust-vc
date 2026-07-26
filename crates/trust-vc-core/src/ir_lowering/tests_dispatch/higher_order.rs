// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Higher-order collection combinator lowering tests (map_values, filter,
//! flat_map, fold_left, fold_right, map, mk_map, map_entries, filter_keys).

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

#[test]
fn lower_seq_map_values_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("s.map_values(SpecFn::new(|x: i32| x + 1)).index(0)").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::map_values should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: outer_op,
            receiver: outer_recv,
            args: outer_args,
            ty: outer_ty,
            ..
        } => {
            assert_eq!(outer_op, CollectionOp::Get);
            assert_eq!(outer_ty, TrustVcType::Int { width: 32 });
            assert_eq!(outer_args.len(), 1);
            match outer_recv.as_ref() {
                TrustVcExpr::CollectionOp { op, args, ty, .. } => {
                    assert_eq!(*op, CollectionOp::SeqMapValues);
                    assert_eq!(args.len(), 1);
                    assert_eq!(
                        *ty,
                        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
                    );
                    assert!(matches!(args[0], TrustVcExpr::SpecClosure { .. }));
                }
                other => panic!("expected inner CollectionOp, got {:?}", other),
            }
        }
        other => panic!("expected Get(CollectionOp), got {:?}", other),
    }
}

#[test]
fn lower_set_filter_with_spec_fn_arg() {
    let expr: syn::Expr = syn::parse_str("s.filter(SpecFn::new(|x: i32| x > 0))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::filter should lower");
    match result {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SetFilter);
            assert_eq!(
                ty,
                TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SetFilter CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_set_filter_rejects_non_bool_predicate() {
    let expr: syn::Expr = syn::parse_str("s.filter(SpecFn::new(|x: i32| x + 1))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("Set::filter must reject non-bool predicates");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::filter requires SpecFn<i32, bool>"),
        "error should mention Set::filter predicate signature, got: {msg}",
    );
}

#[test]
fn lower_seq_filter_with_spec_fn_arg() {
    let expr: syn::Expr = syn::parse_str("s.filter(SpecFn::new(|x: i32| x > 0))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::filter should lower");
    match result {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SeqFilter);
            assert_eq!(
                ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SeqFilter CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_seq_filter_rejects_non_bool_predicate() {
    let expr: syn::Expr = syn::parse_str("s.filter(SpecFn::new(|x: i32| x + 1))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("Seq::filter must reject non-bool predicates");
    let msg = err.to_string();
    assert!(
        msg.contains("Seq::filter requires SpecFn<i32, bool>"),
        "error should mention Seq::filter predicate signature, got: {msg}",
    );
}

#[test]
fn lower_seq_flat_map_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("s.flat_map(SpecFn::new(|x: i32| Seq::<i32>::empty().push(x + 1)))")
            .unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::flat_map should lower");
    match result {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SeqFlatMap);
            assert_eq!(
                ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SeqFlatMap CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_seq_flat_map_rejects_non_seq_return() {
    let expr: syn::Expr = syn::parse_str("s.flat_map(SpecFn::new(|x: i32| x + 1))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let err =
        lower_syn_expr(&expr, &env).expect_err("Seq::flat_map must reject non-sequence returns");
    let msg = err.to_string();
    assert!(
        msg.contains("Seq::flat_map requires SpecFn<i32, Seq<Ret>>"),
        "error should mention Seq::flat_map return signature, got: {msg}",
    );
}

#[test]
fn lower_seq_fold_left_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("s.fold_left(0, SpecFn::new(|acc: i32, x: i32| acc + x))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::fold_left should lower");
    match result {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SeqFoldLeft);
            assert_eq!(ty, TrustVcType::Int { width: 32 });
            assert_eq!(args.len(), 2);
            assert!(matches!(args[1], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SeqFoldLeft CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_seq_fold_left_rejects_wrong_signature() {
    let expr: syn::Expr =
        syn::parse_str("s.fold_left(0, SpecFn::new(|x: i32, acc: u32| x as u32 + acc))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("Seq::fold_left must reject mismatched accumulator/element signatures");
    let msg = err.to_string();
    assert!(
        msg.contains("Seq::fold_left requires initial accumulator plus SpecFn<(i32, i32), i32>"),
        "error should mention Seq::fold_left signature, got: {msg}",
    );
}

#[test]
fn lower_seq_fold_right_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("s.fold_right(0, SpecFn::new(|x: i32, acc: i32| x - acc))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::fold_right should lower");
    match result {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SeqFoldRight);
            assert_eq!(ty, TrustVcType::Int { width: 32 });
            assert_eq!(args.len(), 2);
            assert!(matches!(args[1], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SeqFoldRight CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_seq_fold_right_rejects_wrong_signature() {
    let expr: syn::Expr =
        syn::parse_str("s.fold_right(false, SpecFn::new(|acc: bool, x: i32| acc || x > 0))")
            .unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("Seq::fold_right must reject element/accumulator order mismatches");
    let msg = err.to_string();
    assert!(
        msg.contains("Seq::fold_right requires initial accumulator plus SpecFn<(i32, bool), bool>"),
        "error should mention Seq::fold_right signature, got: {msg}",
    );
}

#[test]
fn lower_set_map_with_spec_fn_arg() {
    let expr: syn::Expr = syn::parse_str("s.map(SpecFn::new(|x: i32| x as u64))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::map should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::SetMap);
            match ty {
                TrustVcType::Set(_) => {}
                other => panic!("expected Set<_> result type, got {:?}", other),
            }
        }
        other => panic!("expected SetMap CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_set_map_rejects_wrong_param_type() {
    let expr: syn::Expr = syn::parse_str("s.map(SpecFn::new(|x: u32| x))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("Set::map must reject mismatched input type");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::map requires SpecFn<i32, Ret>"),
        "error should mention Set::map input signature, got: {msg}",
    );
}

#[test]
fn lower_set_mk_map_with_spec_fn_arg() {
    let expr: syn::Expr = syn::parse_str("s.mk_map(SpecFn::new(|x: i32| x as u64))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::mk_map should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::SetMkMap);
            match ty {
                TrustVcType::Map(key, value) => {
                    assert_eq!(*key, TrustVcType::Int { width: 32 });
                    assert_eq!(*value, TrustVcType::Uint { width: 64 });
                }
                other => panic!("expected Map<_, _> result type, got {:?}", other),
            }
        }
        other => panic!("expected SetMkMap CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_set_mk_map_rejects_wrong_param_type() {
    let expr: syn::Expr = syn::parse_str("s.mk_map(SpecFn::new(|x: u32| x))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let err =
        lower_syn_expr(&expr, &env).expect_err("Set::mk_map must reject mismatched input type");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::mk_map requires SpecFn<i32, Ret>"),
        "error should mention Set::mk_map input signature, got: {msg}",
    );
}

#[test]
fn lower_map_map_values_with_spec_fn_arg() {
    let expr: syn::Expr = syn::parse_str("m.map_values(SpecFn::new(|v: i32| v + 1))").unwrap();
    let env = env_with(&[("m", "Map<u32, i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Map::map_values should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::MapMapValues);
            match ty {
                TrustVcType::Map(_, _) => {}
                other => panic!("expected Map<_, _> result type, got {:?}", other),
            }
        }
        other => panic!("expected MapMapValues CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_map_map_entries_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("m.map_entries(SpecFn::new(|k: u32, v: i32| v + 1))").unwrap();
    let env = env_with(&[("m", "Map<u32, i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Map::map_entries should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::MapMapEntries);
            match ty {
                TrustVcType::Map(key, value) => {
                    assert_eq!(*key, TrustVcType::Uint { width: 32 });
                    assert_eq!(*value, TrustVcType::Int { width: 32 });
                }
                other => panic!("expected Map<_, _> result type, got {:?}", other),
            }
        }
        other => panic!("expected MapMapEntries CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_map_map_entries_rejects_wrong_signature() {
    let expr: syn::Expr = syn::parse_str("m.map_entries(SpecFn::new(|k: i32, v: i32| v))").unwrap();
    let env = env_with(&[("m", "Map<u32, i32>")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("Map::map_entries must reject mismatched key/value signature");
    let msg = err.to_string();
    assert!(
        msg.contains("Map::map_entries requires SpecFn<(u32, i32), Ret>"),
        "error should mention Map::map_entries signature, got: {msg}",
    );
}

#[test]
fn lower_map_filter_keys_with_spec_fn_arg() {
    let expr: syn::Expr = syn::parse_str("m.filter_keys(SpecFn::new(|k: u32| k > 0))").unwrap();
    let env = env_with(&[("m", "Map<u32, i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Map::filter_keys should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::MapFilterKeys);
            assert_eq!(
                ty,
                TrustVcType::Map(
                    Box::new(TrustVcType::Uint { width: 32 }),
                    Box::new(TrustVcType::Int { width: 32 })
                )
            );
        }
        other => panic!("expected MapFilterKeys CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_map_filter_keys_rejects_wrong_predicate_signature() {
    let expr: syn::Expr = syn::parse_str("m.filter_keys(SpecFn::new(|k: i32| k > 0))").unwrap();
    let env = env_with(&[("m", "Map<u32, i32>")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("Map::filter_keys must reject mismatched key predicate types");
    let msg = err.to_string();
    assert!(
        msg.contains("Map::filter_keys requires SpecFn<u32, bool>"),
        "error should mention Map::filter_keys predicate signature, got: {msg}",
    );
}

#[test]
fn lower_set_fold_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("s.fold(0, SpecFn::new(|acc: i32, x: i32| acc + x))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Set::fold should lower");
    match result {
        TrustVcExpr::CollectionOp { op, args, ty, .. } => {
            assert_eq!(op, CollectionOp::SetFold);
            assert_eq!(ty, TrustVcType::Int { width: 32 });
            assert_eq!(args.len(), 2);
            assert!(matches!(args[1], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SetFold CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_set_fold_rejects_wrong_signature() {
    let expr: syn::Expr =
        syn::parse_str("s.fold(0, SpecFn::new(|x: i32, acc: u32| x as u32 + acc))").unwrap();
    let env = env_with(&[("s", "Set<i32>")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("Set::fold must reject mismatched accumulator/element signatures");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::fold requires initial accumulator plus SpecFn<(i32, i32), i32>"),
        "error should mention Set::fold signature, got: {msg}",
    );
}

#[test]
fn lower_seq_map_with_spec_fn_arg() {
    let expr: syn::Expr =
        syn::parse_str("s.map(SpecFn::new(|(i, x): (usize, i32)| x + (i as i32)))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("Seq::map should lower");
    match result {
        TrustVcExpr::CollectionOp { op, ty, .. } => {
            assert_eq!(op, CollectionOp::SeqMap);
            assert_eq!(
                ty,
                TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
            );
        }
        other => panic!("expected SeqMap CollectionOp, got {:?}", other),
    }
}

#[test]
fn lower_seq_map_rejects_wrong_signature() {
    let expr: syn::Expr = syn::parse_str("s.map(SpecFn::new(|x: i32| x + 1))").unwrap();
    let env = env_with(&[("s", "Seq<i32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("Seq::map must reject single-param closure");
    let msg = err.to_string();
    assert!(
        msg.contains("Seq::map requires SpecFn<(usize, i32), Ret>"),
        "error should mention Seq::map signature, got: {msg}",
    );
}

#[test]
fn lower_set_new_comprehension_with_explicit_type() {
    // `Set::<int>::new(|i| pred)` lowers to the SET_NEW_BUILTIN FnCall.
    let expr: syn::Expr = syn::parse_str("Set::<int>::new(SpecFn::new(|i: int| i >= 0))").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Set::new should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, SET_NEW_BUILTIN);
            assert_eq!(return_ty, TrustVcType::Set(Box::new(TrustVcType::MathInt)));
            assert_eq!(args.len(), 1);
            assert!(matches!(args[0], TrustVcExpr::SpecClosure { .. }));
        }
        other => panic!("expected SET_NEW_BUILTIN FnCall, got {:?}", other),
    }
}

#[test]
fn lower_set_new_comprehension_infers_element_from_closure() {
    // No explicit `Set::<T>` — element type comes from the closure parameter.
    let expr: syn::Expr = syn::parse_str("Set::new(SpecFn::new(|i: int| i >= 0))").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Set::new should lower");
    match result {
        TrustVcExpr::FnCall {
            name, return_ty, ..
        } => {
            assert_eq!(name, SET_NEW_BUILTIN);
            assert_eq!(return_ty, TrustVcType::Set(Box::new(TrustVcType::MathInt)));
        }
        other => panic!("expected SET_NEW_BUILTIN FnCall, got {:?}", other),
    }
}

#[test]
fn lower_set_new_rejects_non_bool_predicate() {
    let expr: syn::Expr = syn::parse_str("Set::<int>::new(SpecFn::new(|i: int| i + 1))").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("Set::new must reject non-bool predicates");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::new requires SpecFn<int, bool>"),
        "error should mention Set::new predicate signature, got: {msg}",
    );
}

#[test]
fn lower_set_new_rejects_element_type_mismatch() {
    // Explicit `Set::<i32>` but closure param is `int` — fail closed.
    let expr: syn::Expr = syn::parse_str("Set::<i32>::new(SpecFn::new(|i: int| i >= 0))").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("Set::new must reject element type mismatch");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::new closure parameter has type 'int'")
            && msg.contains("explicit Set element type is 'i32'"),
        "error should mention element type mismatch, got: {msg}",
    );
}
