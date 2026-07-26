// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier (forall/exists) and choose/choose! macro lowering tests.

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

// === Quantifier closure param typing (#2078) ===

#[test]
fn lower_forall_untyped_closure_param_rejected() {
    let expr: syn::Expr = syn::parse_str("forall(|x| x > 0)").unwrap();
    let env = TypeEnv::new();
    let err = lower_syn_expr(&expr, &env).expect_err("untyped param must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("requires an explicit type annotation"),
        "error should mention type annotation, got: {msg}",
    );
    assert!(
        msg.contains("'x'"),
        "error should name the parameter, got: {msg}",
    );
}

#[test]
fn lower_exists_untyped_closure_param_rejected() {
    let expr: syn::Expr = syn::parse_str("exists(|y| y != 0)").unwrap();
    let env = TypeEnv::new();
    let err = lower_syn_expr(&expr, &env).expect_err("untyped param must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("requires an explicit type annotation"),
        "error should mention type annotation, got: {msg}",
    );
    assert!(
        msg.contains("'y'"),
        "error should name the parameter, got: {msg}",
    );
}

#[test]
fn lower_forall_typed_closure_param_accepted() {
    let expr: syn::Expr = syn::parse_str("forall(|x: u32| x > 0)").unwrap();
    let env = TypeEnv::new();
    let result = lower_syn_expr(&expr, &env);
    assert!(
        result.is_ok(),
        "typed quantifier param should succeed, got: {:?}",
        result.err(),
    );
}

// === Quantifier empty-bound rejection (#2083) ===

#[test]
fn test_forall_empty_closure_rejected() {
    let expr: syn::Expr = syn::parse_str("forall(|| true)").unwrap();
    let env = env_with(&[]);
    match lower_syn_expr(&expr, &env) {
        Err(LoweringError::UnsupportedExpr(msg)) => {
            assert!(
                msg.contains("at least one bound variable"),
                "expected 'at least one bound variable' in error, got: {msg}"
            );
        }
        Err(other) => panic!("expected UnsupportedExpr, got: {other:?}"),
        Ok(result) => panic!("expected error for forall(|| true), got: {result:?}"),
    }
}

#[test]
fn test_exists_empty_closure_rejected() {
    let expr: syn::Expr = syn::parse_str("exists(|| false)").unwrap();
    let env = env_with(&[]);
    match lower_syn_expr(&expr, &env) {
        Err(LoweringError::UnsupportedExpr(msg)) => {
            assert!(
                msg.contains("at least one bound variable"),
                "expected 'at least one bound variable' in error, got: {msg}"
            );
        }
        Err(other) => panic!("expected UnsupportedExpr, got: {other:?}"),
        Ok(result) => panic!("expected error for exists(|| false), got: {result:?}"),
    }
}

#[test]
fn test_forall_with_typed_param_accepted() {
    let expr: syn::Expr = syn::parse_str("forall(|x: u32| x > 0)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env);
    assert!(
        result.is_ok(),
        "forall with typed param should succeed: {result:?}"
    );
    match result.unwrap() {
        TrustVcExpr::Quantifier {
            kind, bound_vars, ..
        } => {
            assert_eq!(kind, QuantifierKind::Forall);
            assert_eq!(bound_vars.len(), 1);
            assert_eq!(bound_vars[0].0, "x");
        }
        other => panic!("expected Quantifier, got: {other:?}"),
    }
}

#[test]
fn lower_forall_verus_source_syntax_int_param_accepted() {
    let expr = crate::parse_expr_str_with_chains("forall|i: int| i >= 0").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Verus-style forall should lower");
    match result {
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(kind, QuantifierKind::Forall);
            assert_eq!(bound_vars, vec![("i".to_string(), TrustVcType::MathInt)]);
            assert!(
                matches!(
                    *body,
                    TrustVcExpr::Compare {
                        op: CompareOp::Ge,
                        ..
                    }
                ),
                "expected comparison body, got: {body:?}",
            );
        }
        other => panic!("expected Quantifier, got: {other:?}"),
    }
}

#[test]
fn lower_exists_verus_source_syntax_nat_param_accepted() {
    let expr = crate::parse_expr_str_with_chains("exists|i: nat| i == 0").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Verus-style exists should lower");
    match result {
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(kind, QuantifierKind::Exists);
            assert_eq!(bound_vars, vec![("i".to_string(), TrustVcType::Nat)]);
            assert!(
                matches!(
                    *body,
                    TrustVcExpr::Compare {
                        op: CompareOp::Eq,
                        ..
                    }
                ),
                "expected comparison body, got: {body:?}",
            );
        }
        other => panic!("expected Quantifier, got: {other:?}"),
    }
}

#[test]
fn lower_forall_verus_source_syntax_multiple_params_accepted() {
    let expr = crate::parse_expr_str_with_chains("forall|i: int, j: nat| i <= j").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("multi-param Verus-style forall should lower");
    match result {
        TrustVcExpr::Quantifier {
            kind, bound_vars, ..
        } => {
            assert_eq!(kind, QuantifierKind::Forall);
            assert_eq!(
                bound_vars,
                vec![
                    ("i".to_string(), TrustVcType::MathInt),
                    ("j".to_string(), TrustVcType::Nat),
                ]
            );
        }
        other => panic!("expected Quantifier, got: {other:?}"),
    }
}

#[test]
fn lower_nested_verus_source_quantifiers_accepted() {
    let expr = crate::parse_expr_str_with_chains("forall|i: int| exists|j: int| i <= j")
        .expect("nested Verus-style quantifiers should parse");
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("nested Verus-style quantifiers should lower");
    match result {
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            ..
        } => {
            assert_eq!(kind, QuantifierKind::Forall);
            assert_eq!(bound_vars, vec![("i".to_string(), TrustVcType::MathInt)]);
            match *body {
                TrustVcExpr::Quantifier {
                    kind, bound_vars, ..
                } => {
                    assert_eq!(kind, QuantifierKind::Exists);
                    assert_eq!(bound_vars, vec![("j".to_string(), TrustVcType::MathInt)]);
                }
                other => panic!("expected nested exists body, got: {other:?}"),
            }
        }
        other => panic!("expected outer Quantifier, got: {other:?}"),
    }
}

#[test]
fn lower_forall_verus_trigger_attr_on_body_expr_sets_singleton_trigger() {
    let expr = crate::parse_expr_str_with_chains("forall|i: int| #[trigger] f(i) && i >= 0")
        .expect("Verus-style forall with trigger attr should parse");
    let mut env = env_with(&[]);
    env.insert_fn("f".to_string(), TrustVcType::Bool);
    env.insert_fn_params("f".to_string(), vec![TrustVcType::MathInt]);

    let result = lower_syn_expr(&expr, &env).expect("trigger attr should not block lowering");
    match result {
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            ..
        } => {
            assert_eq!(kind, QuantifierKind::Forall);
            assert_eq!(bound_vars, vec![("i".to_string(), TrustVcType::MathInt)]);
            assert!(
                matches!(
                    *body,
                    TrustVcExpr::Logic {
                        op: LogicOp::And,
                        ..
                    }
                ),
                "trigger attr should not change lowered body, got: {body:?}",
            );
            let triggers = triggers.expect("trigger attr should be preserved in IR trigger field");
            assert_eq!(triggers.len(), 1);
            assert_eq!(triggers[0].len(), 1);
            match &triggers[0][0] {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert_eq!(name, "f");
                    assert_eq!(args.len(), 1);
                    assert_eq!(*return_ty, TrustVcType::Bool);
                }
                other => panic!("expected lowered f(i) trigger, got: {other:?}"),
            }
        }
        other => panic!("expected Quantifier, got: {other:?}"),
    }
}

// === Choose expression lowering (#2143) ===

#[test]
fn lower_choose_basic_typed_binder() {
    let expr: syn::Expr = syn::parse_str("choose(|x: i32| x >= 0)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            key,
            ..
        } => {
            assert_eq!(var_name, "x");
            assert_eq!(var_ty, TrustVcType::Int { width: 32 });
            assert!(!key.is_empty(), "key should be non-empty canonical string");
            assert!(
                matches!(*condition, TrustVcExpr::Compare { .. }),
                "condition should be a Compare, got: {:?}",
                condition
            );
        }
        other => panic!("expected Choose, got {:?}", other),
    }
}

#[test]
fn lower_choose_verus_source_syntax_nested_rhs_accepted() {
    let expr = crate::parse_expr_str_with_chains("w == choose|x: i32| x >= 0i32 && x < 10i32")
        .expect("nested Verus-style choose should parse");
    let env = env_with(&[("w", "i32")]);
    let result = lower_syn_expr(&expr, &env).expect("nested Verus-style choose should lower");
    match result {
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            right,
            ..
        } => match *right {
            TrustVcExpr::Choose {
                var_name,
                var_ty,
                condition,
                ..
            } => {
                assert_eq!(var_name, "x");
                assert_eq!(var_ty, TrustVcType::Int { width: 32 });
                assert!(
                    matches!(
                        *condition,
                        TrustVcExpr::Logic {
                            op: LogicOp::And,
                            ..
                        }
                    ),
                    "expected choose condition conjunction, got: {condition:?}",
                );
            }
            other => panic!("expected Choose on comparison rhs, got: {other:?}"),
        },
        other => panic!("expected equality comparison, got: {other:?}"),
    }
}

#[test]
fn lower_choose_verus_source_syntax_nat_param_accepted() {
    let expr = crate::parse_expr_str_with_chains("choose|n: nat| n >= 0")
        .expect("Verus-style nat choose should parse");
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Verus-style nat choose should lower");
    match result {
        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            ..
        } => {
            assert_eq!(var_name, "n");
            assert_eq!(var_ty, TrustVcType::Nat);
            assert!(
                matches!(
                    *condition,
                    TrustVcExpr::Compare {
                        op: CompareOp::Ge,
                        ..
                    }
                ),
                "expected nat choose comparison condition, got: {condition:?}",
            );
        }
        other => panic!("expected Choose, got {other:?}"),
    }
}

#[test]
fn lower_choose_rejects_untyped_binder() {
    let expr: syn::Expr = syn::parse_str("choose(|x| x > 0)").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("untyped choose binder must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("requires an explicit type annotation"),
        "error should mention type annotation, got: {msg}",
    );
}

#[test]
fn lower_choose_infers_untyped_binder_from_suffixed_literal() {
    let expr: syn::Expr = syn::parse_str("choose(|x| x >= 5i32)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            ..
        } => {
            assert_eq!(var_name, "x");
            assert_eq!(var_ty, TrustVcType::Int { width: 32 });
            match *condition {
                TrustVcExpr::Compare { left, .. } => match *left {
                    TrustVcExpr::Var { name, ty } => {
                        assert_eq!(name, "x");
                        assert_eq!(ty, TrustVcType::Int { width: 32 });
                    }
                    other => panic!("expected typed choose var on lhs, got: {other:?}"),
                },
                other => panic!("expected Compare condition, got: {other:?}"),
            }
        }
        other => panic!("expected Choose, got {:?}", other),
    }
}

#[test]
fn lower_choose_infers_untyped_binder_from_typed_capture() {
    let expr: syn::Expr = syn::parse_str("choose(|x| x > y)").unwrap();
    let env = env_with(&[("y", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name, var_ty, ..
        } => {
            assert_eq!(var_name, "x");
            assert_eq!(var_ty, TrustVcType::Uint { width: 32 });
        }
        other => panic!("expected Choose, got {:?}", other),
    }
}

#[test]
fn lower_choose_multiple_binders_returns_tuple_constructor() {
    let expr: syn::Expr = syn::parse_str("choose(|x: i32, y: i32| x + y == 0)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("multi-binder choose should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "i32_i32_Tuple");
            assert_eq!(args.len(), 2);
            match return_ty {
                TrustVcType::Datatype { name, variants } => {
                    assert_eq!(name, "(i32, i32)");
                    assert_eq!(variants.len(), 1);
                    assert_eq!(variants[0].name, "Tuple");
                    assert_eq!(
                        variants[0].fields,
                        vec![
                            ("0".to_string(), TrustVcType::Int { width: 32 }),
                            ("1".to_string(), TrustVcType::Int { width: 32 }),
                        ]
                    );
                }
                other => panic!("expected tuple datatype return type, got: {other:?}"),
            }
            for arg in args {
                assert!(
                    matches!(arg, TrustVcExpr::Choose { .. }),
                    "tuple fields should be backed by single-binder choose expressions, got: {arg:?}"
                );
            }
        }
        other => panic!("expected tuple constructor FnCall, got: {other:?}"),
    }
}

#[test]
fn lower_choose_multiple_binders_builds_witness_chain() {
    let expr: syn::Expr = syn::parse_str("choose(|x: i32, y: i32| x <= y)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("multi-binder choose should lower");
    let TrustVcExpr::FnCall { args, .. } = result else {
        panic!("expected tuple constructor");
    };
    let [first, second] = args.as_slice() else {
        panic!("expected two tuple fields");
    };
    match first {
        TrustVcExpr::Choose {
            var_name,
            condition,
            ..
        } => {
            assert_eq!(var_name, "x");
            assert!(
                matches!(
                    condition.as_ref(),
                    TrustVcExpr::Quantifier {
                        kind: QuantifierKind::Exists,
                        ..
                    }
                ),
                "first component should choose an x admitting a y witness, got: {condition:?}",
            );
        }
        other => panic!("expected first field Choose, got: {other:?}"),
    }
    match second {
        TrustVcExpr::Choose {
            var_name,
            condition,
            ..
        } => {
            assert_eq!(var_name, "y");
            match condition.as_ref() {
                TrustVcExpr::Compare { left, .. } => assert!(
                    matches!(left.as_ref(), TrustVcExpr::Choose { var_name, .. } if var_name == "x"),
                    "second component condition should capture the chosen x, got: {left:?}",
                ),
                other => panic!("expected comparison condition for second field, got: {other:?}"),
            }
        }
        other => panic!("expected second field Choose, got: {other:?}"),
    }
}

#[test]
fn lower_verus_choose_multiple_binders_returns_tuple_constructor() {
    let expr = crate::parse_expr_str_with_chains("choose|x: i32, y: i32| x <= y")
        .expect("Verus-style multi-binder choose should parse");
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("Verus-style multi-binder choose should lower");
    assert!(
        matches!(&result, TrustVcExpr::FnCall { args, .. } if args.len() == 2),
        "expected tuple constructor with two chosen fields, got: {result:?}",
    );
}

#[test]
fn lower_choose_tuple_call_returns_tuple_constructor() {
    let expr =
        crate::parse_expr_str_with_chains("choose_tuple::<(nat, nat), _>(|m: nat, n: nat| m <= n)")
            .expect("choose_tuple call should normalize to choose call");
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("choose_tuple normalized call should lower");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(args.len(), 2);
            match return_ty {
                TrustVcType::Datatype { name, variants } => {
                    assert_eq!(name, "(nat, nat)");
                    assert_eq!(variants[0].fields[0].1, TrustVcType::Nat);
                    assert_eq!(variants[0].fields[1].1, TrustVcType::Nat);
                }
                other => panic!("expected tuple datatype return type, got: {other:?}"),
            }
        }
        other => panic!("expected tuple constructor FnCall, got: {other:?}"),
    }
}

#[test]
fn lower_tuple_expression_to_datatype_constructor() {
    let expr: syn::Expr = syn::parse_str("(1i32, y)").unwrap();
    let env = env_with(&[("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).expect("tuple expression should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "i32_i32_Tuple");
            assert_eq!(args.len(), 2);
            assert_eq!(infer_expr_type(&args[0]), TrustVcType::Int { width: 32 });
            assert_eq!(infer_expr_type(&args[1]), TrustVcType::Int { width: 32 });
            match return_ty {
                TrustVcType::Datatype { name, variants } => {
                    assert_eq!(name, "(i32, i32)");
                    assert_eq!(variants[0].name, "Tuple");
                }
                other => panic!("expected tuple datatype return type, got: {other:?}"),
            }
        }
        other => panic!("expected tuple constructor FnCall, got: {other:?}"),
    }
}

#[test]
fn lower_choose_rejects_non_closure_arg() {
    let expr: syn::Expr = syn::parse_str("choose(42)").unwrap();
    let env = env_with(&[]);
    let err =
        lower_syn_expr(&expr, &env).expect_err("choose with non-closure arg must be rejected");
    let msg = err.to_string();
    assert!(
        msg.contains("closure"),
        "error should mention closure, got: {msg}",
    );
}

#[test]
fn lower_choose_captures_outer_variable() {
    let expr: syn::Expr = syn::parse_str("choose(|x: i32| x > y)").unwrap();
    let env = env_with(&[("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name,
            condition,
            ..
        } => {
            assert_eq!(var_name, "x");
            assert!(
                matches!(*condition, TrustVcExpr::Compare { .. }),
                "condition should be a Compare, got: {:?}",
                condition
            );
        }
        other => panic!("expected Choose, got {:?}", other),
    }
}

// === Choose macro-form lowering (#2486) ===

#[test]
fn lower_choose_macro_basic_typed_binder() {
    let expr: syn::Expr = syn::parse_str("choose!(|x: i32| x >= 0)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name,
            var_ty,
            condition,
            key,
            ..
        } => {
            assert_eq!(var_name, "x");
            assert_eq!(var_ty, TrustVcType::Int { width: 32 });
            assert!(!key.is_empty(), "key should be non-empty canonical string");
            assert!(
                matches!(*condition, TrustVcExpr::Compare { .. }),
                "condition should be a Compare, got: {:?}",
                condition
            );
        }
        other => panic!("expected Choose from macro form, got {:?}", other),
    }
}

#[test]
fn lower_choose_macro_infers_untyped_binder_from_suffixed_literal() {
    let expr: syn::Expr = syn::parse_str("choose!(|x| x >= 10u32)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name, var_ty, ..
        } => {
            assert_eq!(var_name, "x");
            assert_eq!(var_ty, TrustVcType::Uint { width: 32 });
        }
        other => panic!("expected Choose from macro form, got {:?}", other),
    }
}

#[test]
fn lower_choose_macro_path_qualified() {
    let expr: syn::Expr = syn::parse_str("trust_vc::choose!(|x: u64| x > 5u64)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name, var_ty, ..
        } => {
            assert_eq!(var_name, "x");
            assert_eq!(var_ty, TrustVcType::Uint { width: 64 });
        }
        other => panic!("expected Choose from path-qualified macro, got {:?}", other),
    }
}

// === Finite Seq literal lowering (#2779) ===

fn seq_push_depth(expr: &TrustVcExpr) -> usize {
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver,
            ..
        } => 1 + seq_push_depth(receiver),
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } if args.is_empty() && matches!(return_ty, TrustVcType::Seq(_)) => 0,
        other => panic!("expected seq literal push chain, got: {other:?}"),
    }
}

fn map_insert_depth(expr: &TrustVcExpr) -> usize {
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ..
        } if args.len() == 2 => 1 + map_insert_depth(receiver),
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } if args.is_empty() && matches!(return_ty, TrustVcType::Map(_, _)) => 0,
        other => panic!("expected map literal insert chain, got: {other:?}"),
    }
}

fn set_insert_depth(expr: &TrustVcExpr) -> usize {
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ..
        } if args.len() == 1 => 1 + set_insert_depth(receiver),
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } if args.is_empty() && matches!(return_ty, TrustVcType::Set(_)) => 0,
        other => panic!("expected set literal insert chain, got: {other:?}"),
    }
}

#[test]
fn lower_seq_macro_literal_to_push_chain() {
    let expr: syn::Expr = syn::parse_str("seq![1i32, 2, 3]").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(seq_push_depth(&result), 3);
    assert_eq!(
        infer_expr_type(&result),
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
}

#[test]
fn lower_seq_macro_repeat_literal_to_push_chain() {
    let expr: syn::Expr = syn::parse_str("trust_vc_types::seq![5i32; 10]").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(seq_push_depth(&result), 10);
    assert_eq!(
        infer_expr_type(&result),
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
}

#[test]
fn lower_vec_macro_literal_view_len_to_seq_model() {
    let expr: syn::Expr = syn::parse_str("vec![7u8, 8u8, 9u8].view().len()").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("vec! literal view len should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            receiver,
            args,
            ty,
            ..
        } => {
            assert!(args.is_empty());
            assert_eq!(
                ty,
                TrustVcType::Uint {
                    width: crate::ir::pointer_width()
                }
            );
            match *receiver {
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::View,
                    receiver,
                    ..
                } => {
                    assert_eq!(seq_push_depth(&receiver), 3);
                    assert_eq!(
                        infer_expr_type(&receiver),
                        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
                    );
                }
                other => panic!("expected view receiver, got: {other:?}"),
            }
        }
        other => panic!("expected len collection op, got: {other:?}"),
    }
}

#[test]
fn lower_vec_macro_literal_view_index_to_seq_get() {
    let expr: syn::Expr = syn::parse_str("vec![7u8, 8u8, 9u8].view().index(1usize)").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).expect("vec! literal view index should lower");
    match result {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Get,
            receiver,
            args,
            ty,
            ..
        } => {
            assert_eq!(args.len(), 1);
            assert_eq!(ty, TrustVcType::Uint { width: 8 });
            match *receiver {
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::View,
                    receiver,
                    ..
                } => {
                    assert_eq!(seq_push_depth(&receiver), 3);
                    assert_eq!(
                        infer_expr_type(&receiver),
                        TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 8 }))
                    );
                }
                other => panic!("expected view receiver, got: {other:?}"),
            }
        }
        other => panic!("expected index/get collection op, got: {other:?}"),
    }
}

#[test]
fn lower_vec_macro_empty_and_repeat_stay_fail_closed() {
    for (src, expected) in [
        ("vec![]", "empty Vec literals are not modeled in this slice"),
        (
            "vec![7u8; 3]",
            "repeat literals are not modeled in this slice",
        ),
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let err = lower_syn_expr(&expr, &env_with(&[]))
            .expect_err(&format!("{src} should remain fail-closed"));
        let msg = err.to_string();
        assert!(
            msg.contains(expected),
            "{src} error should contain {expected:?}, got: {msg}"
        );
    }
}

#[test]
fn lower_map_macro_literal_to_insert_chain() {
    let expr: syn::Expr = syn::parse_str("trust_vc_types::map![1i32 => 2i32, 3 => 4]").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(map_insert_depth(&result), 2);
    assert_eq!(
        infer_expr_type(&result),
        TrustVcType::Map(
            Box::new(TrustVcType::Int { width: 32 }),
            Box::new(TrustVcType::Int { width: 32 })
        )
    );
}

#[test]
fn lower_set_macro_literal_to_insert_chain_with_trailing_comma() {
    let expr: syn::Expr = syn::parse_str("trust_vc_types::set![1i32, 2, 3,]").unwrap();
    let env = env_with(&[]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(set_insert_depth(&result), 3);
    assert_eq!(
        infer_expr_type(&result),
        TrustVcType::Set(Box::new(TrustVcType::Int { width: 32 }))
    );
}

#[test]
fn lower_map_macro_empty_requires_type_context() {
    let expr: syn::Expr = syn::parse_str("map![]").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("empty map! must fail closed");
    let msg = err.to_string();
    assert!(
        msg.contains("Map::<K, V>::empty"),
        "error should point to typed empty constructor, got: {msg}"
    );
}

#[test]
fn lower_set_macro_empty_requires_type_context() {
    let expr: syn::Expr = syn::parse_str("set![]").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("empty set! must fail closed");
    let msg = err.to_string();
    assert!(
        msg.contains("Set::<T>::empty"),
        "error should point to typed empty constructor, got: {msg}"
    );
}

#[test]
fn lower_seq_macro_empty_requires_type_context() {
    let expr: syn::Expr = syn::parse_str("seq![]").unwrap();
    let env = env_with(&[]);
    let err = lower_syn_expr(&expr, &env).expect_err("empty seq! must fail closed");
    let msg = err.to_string();
    assert!(
        msg.contains("Seq::<T>::empty"),
        "error should point to typed empty constructor, got: {msg}"
    );
}

#[test]
fn lower_choose_macro_captures_outer_variable() {
    let expr: syn::Expr = syn::parse_str("choose!(|x: i32| x > y)").unwrap();
    let env = env_with(&[("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Choose {
            var_name,
            condition,
            ..
        } => {
            assert_eq!(var_name, "x");
            assert!(
                matches!(*condition, TrustVcExpr::Compare { .. }),
                "condition should be a Compare, got: {:?}",
                condition
            );
        }
        other => panic!("expected Choose from macro with capture, got {:?}", other),
    }
}

// === Verus implication `==>` lowering (#2777 real_nonlinear surface) ===

#[test]
fn lower_implies_source_syntax_builds_implies_node() {
    // `P ==> Q` from direct source lowers to a real `TrustVcExpr::Implies`
    // (premise/conclusion), not a desugared `!P || Q`.
    let expr = crate::parse_expr_str_with_chains("a >= 0 ==> b >= 0").unwrap();
    let env = env_with(&[("a", "int"), ("b", "int")]);
    let result = lower_syn_expr(&expr, &env).expect("implication should lower");
    match result {
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            assert!(
                matches!(
                    *premise,
                    TrustVcExpr::Compare {
                        op: CompareOp::Ge,
                        ..
                    }
                ),
                "premise should be `a >= 0`, got: {premise:?}"
            );
            assert!(
                matches!(
                    *conclusion,
                    TrustVcExpr::Compare {
                        op: CompareOp::Ge,
                        ..
                    }
                ),
                "conclusion should be `b >= 0`, got: {conclusion:?}"
            );
        }
        other => panic!("expected Implies, got: {other:?}"),
    }
}

#[test]
fn lower_implies_is_right_associative() {
    // `a ==> b ==> c` parses/lowers as `a ==> (b ==> c)`.
    let expr = crate::parse_expr_str_with_chains("a ==> b ==> c").unwrap();
    let env = env_with(&[("a", "bool"), ("b", "bool"), ("c", "bool")]);
    let result = lower_syn_expr(&expr, &env).expect("nested implication should lower");
    match result {
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            assert!(
                matches!(*premise, TrustVcExpr::Var { .. }),
                "outer premise should be the bare `a`, got: {premise:?}"
            );
            assert!(
                matches!(*conclusion, TrustVcExpr::Implies { .. }),
                "outer conclusion should itself be `b ==> c`, got: {conclusion:?}"
            );
        }
        other => panic!("expected right-associated Implies, got: {other:?}"),
    }
}

#[test]
fn lower_implies_binds_looser_than_conjunction() {
    // `p && q ==> r` is `(p && q) ==> r`, so the premise is the conjunction.
    let expr = crate::parse_expr_str_with_chains("p && q ==> r").unwrap();
    let env = env_with(&[("p", "bool"), ("q", "bool"), ("r", "bool")]);
    let result = lower_syn_expr(&expr, &env).expect("implication should lower");
    match result {
        TrustVcExpr::Implies { premise, .. } => {
            assert!(
                matches!(
                    *premise,
                    TrustVcExpr::Logic {
                        op: LogicOp::And,
                        ..
                    }
                ),
                "premise should be the conjunction `p && q`, got: {premise:?}"
            );
        }
        other => panic!("expected Implies with conjunction premise, got: {other:?}"),
    }
}

#[test]
fn lower_implies_premise_chain_is_normalized() {
    // A comparison chain in the premise (`0 <= i < n`) must be normalized to a
    // conjunction of pairwise comparisons inside the implication premise.
    let expr = crate::parse_expr_str_with_chains("0 <= i < n ==> q").unwrap();
    let env = env_with(&[("i", "int"), ("n", "int"), ("q", "bool")]);
    let result = lower_syn_expr(&expr, &env).expect("chained-premise implication should lower");
    match result {
        TrustVcExpr::Implies { premise, .. } => {
            assert!(
                matches!(
                    *premise,
                    TrustVcExpr::Logic {
                        op: LogicOp::And,
                        ..
                    }
                ),
                "chained premise should normalize to a conjunction, got: {premise:?}"
            );
        }
        other => panic!("expected Implies with normalized chain premise, got: {other:?}"),
    }
}
