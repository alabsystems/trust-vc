// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Method call, struct literal, and wrapping/checked/saturating arithmetic tests.

use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::*;
use crate::ir_lowering::tests_support::env_with;
use crate::ir_lowering::*;

use super::support::counter_ty;

#[test]
fn lower_registered_method_call_to_fn_call() {
    let expr: syn::Expr = syn::parse_str("counter.bump(1)").unwrap();
    let mut env = TypeEnv::new();
    env.insert("counter".to_string(), counter_ty());
    env.insert_method_metadata(
        "Counter".to_string(),
        "bump".to_string(),
        MethodMeta {
            uf_name: "CounterSpec__bump".to_string(),
            return_type: counter_ty(),
            param_types: vec![TrustVcType::Uint { width: 32 }],
            box_receiver: None,
        },
    );

    let lowered = lower_syn_expr(&expr, &env).expect("registered method should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "CounterSpec__bump");
            assert_eq!(return_ty, counter_ty());
            assert_eq!(
                args,
                vec![
                    TrustVcExpr::Var {
                        name: "counter".to_string(),
                        ty: counter_ty(),
                    },
                    TrustVcExpr::IntLit {
                        value: 1,
                        ty: TrustVcType::Uint { width: 32 },
                    },
                ]
            );
        }
        other => panic!("expected method FnCall, got {:?}", other),
    }
}

#[test]
fn lower_collection_method_keeps_collection_path_before_manual_metadata() {
    let expr: syn::Expr = syn::parse_str("s.len()").unwrap();
    let mut env = env_with(&[("s", "Seq<i32>")]);
    env.insert_method_metadata(
        "Seq<i32>".to_string(),
        "len".to_string(),
        MethodMeta {
            uf_name: "SeqSpec__len".to_string(),
            return_type: TrustVcType::Bool,
            param_types: vec![],
            box_receiver: None,
        },
    );

    let lowered = lower_syn_expr(&expr, &env).expect("collection path should still work");
    assert!(matches!(
        lowered,
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Len,
            ..
        }
    ));
}

#[test]
fn lower_real_floor_method_to_math_int_cast() {
    let expr: syn::Expr = syn::parse_str("x.floor()").unwrap();
    let env = env_with(&[("x", "real")]);
    let lowered = lower_syn_expr(&expr, &env).expect("real floor should lower");
    match lowered {
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => {
            assert_eq!(from_ty, TrustVcType::Real);
            assert_eq!(to_ty, TrustVcType::MathInt);
            assert!(matches!(
                expr.as_ref(),
                TrustVcExpr::Var {
                    name,
                    ty: TrustVcType::Real,
                } if name == "x"
            ));
        }
        other => panic!("expected real floor Cast, got {other:?}"),
    }
}

#[test]
fn lower_u8_partial_ord_lt_method_to_comparison() {
    let expr: syn::Expr = syn::parse_str("x.lt(&y)").unwrap();
    let env = env_with(&[("x", "u8"), ("y", "u8")]);
    let lowered = lower_syn_expr(&expr, &env).expect("u8 lt method should lower");
    match lowered {
        TrustVcExpr::Compare { op, left, right } => {
            assert_eq!(op, CompareOp::Lt);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
            assert_eq!(
                *right,
                TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
        }
        other => panic!("expected u8 lt Compare, got {other:?}"),
    }
}

#[test]
fn lower_i32_partial_ord_gt_method_to_comparison() {
    let expr: syn::Expr = syn::parse_str("x.gt(&y)").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i32 gt method should lower");
    match lowered {
        TrustVcExpr::Compare { op, left, right } => {
            assert_eq!(op, CompareOp::Gt);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }
            );
            assert_eq!(
                *right,
                TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }
            );
        }
        other => panic!("expected i32 gt Compare, got {other:?}"),
    }
}

#[test]
fn lower_u8_partial_ord_le_method_to_comparison() {
    let expr: syn::Expr = syn::parse_str("x.le(&y)").unwrap();
    let env = env_with(&[("x", "u8"), ("y", "u8")]);
    let lowered = lower_syn_expr(&expr, &env).expect("u8 le method should lower");
    match lowered {
        TrustVcExpr::Compare { op, left, right } => {
            assert_eq!(op, CompareOp::Le);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
            assert_eq!(
                *right,
                TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
        }
        other => panic!("expected u8 le Compare, got {other:?}"),
    }
}

#[test]
fn lower_i32_partial_ord_ge_method_to_comparison() {
    let expr: syn::Expr = syn::parse_str("x.ge(&y)").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i32 ge method should lower");
    match lowered {
        TrustVcExpr::Compare { op, left, right } => {
            assert_eq!(op, CompareOp::Ge);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }
            );
            assert_eq!(
                *right,
                TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }
            );
        }
        other => panic!("expected i32 ge Compare, got {other:?}"),
    }
}

#[test]
fn lower_option_u8_partial_ord_le_method_to_lt_or_eq() {
    // Option<int> is totally ordered, so `a <= b` lowers to `a < b || a == b`:
    // the strict-order `Ite` OR'd with the structural-equality `Logic`.
    let expr: syn::Expr = syn::parse_str("left.le(&right)").unwrap();
    let env = env_with(&[("left", "Option<u8>"), ("right", "Option<u8>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("Option<u8> le method should lower");
    match lowered {
        TrustVcExpr::Logic {
            op: LogicOp::Or,
            left,
            right,
        } => {
            assert!(
                matches!(*left, TrustVcExpr::Ite { .. }),
                "le should OR the strict-less-than Ite as its left operand"
            );
            assert!(
                matches!(
                    *right,
                    TrustVcExpr::Logic {
                        op: LogicOp::Or,
                        ..
                    }
                ),
                "le should OR the structural-equality predicate as its right operand"
            );
        }
        other => panic!("expected Option le `lt || eq`, got {other:?}"),
    }
}

#[test]
fn lower_option_u8_partial_ord_ge_method_to_not_lt() {
    // `a >= b` iff `!(a < b)` (total order): the negated strict-less-than Ite.
    let expr: syn::Expr = syn::parse_str("left.ge(&right)").unwrap();
    let env = env_with(&[("left", "Option<u8>"), ("right", "Option<u8>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("Option<u8> ge method should lower");
    match lowered {
        TrustVcExpr::Not(inner) => {
            assert!(
                matches!(*inner, TrustVcExpr::Ite { .. }),
                "ge should negate the strict-less-than Ite"
            );
        }
        other => panic!("expected Option ge `!(a < b)`, got {other:?}"),
    }
}

#[test]
fn lower_option_u8_partial_ord_lt_method_to_lexicographic_comparison() {
    let expr: syn::Expr = syn::parse_str("left.lt(&right)").unwrap();
    let env = env_with(&[("left", "Option<u8>"), ("right", "Option<u8>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("Option<u8> lt method should lower");
    match lowered {
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            assert_eq!(ty, TrustVcType::Bool);
            assert!(matches!(*cond, TrustVcExpr::FnCall { ref name, .. } if name.contains("None")));
            assert!(
                matches!(*then_branch, TrustVcExpr::FnCall { ref name, .. } if name.contains("Some")),
                "None < Some(_) branch should test right Some"
            );
            assert!(
                matches!(*else_branch, TrustVcExpr::Ite { .. }),
                "Some/Some comparison should live in the else branch"
            );
        }
        other => panic!("expected Option lt lexicographic Ite, got {other:?}"),
    }
}

#[test]
fn lower_option_u8_partial_ord_gt_method_to_lexicographic_comparison() {
    let expr: syn::Expr = syn::parse_str("left.gt(&right)").unwrap();
    let env = env_with(&[("left", "Option<u8>"), ("right", "Option<u8>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("Option<u8> gt method should lower");
    match lowered {
        TrustVcExpr::Logic {
            op: LogicOp::And,
            left,
            right,
        } => {
            assert!(matches!(*left, TrustVcExpr::Not(_)));
            assert!(
                matches!(*right, TrustVcExpr::Not(_)),
                "Option gt should use total-order complement against structural equality"
            );
        }
        other => panic!("expected Option gt lexicographic Ite, got {other:?}"),
    }
}

#[test]
fn lower_option_partial_ord_rejects_mismatched_option_types() {
    let expr: syn::Expr = syn::parse_str("left.lt(&right)").unwrap();
    let env = env_with(&[("left", "Option<u8>"), ("right", "Option<u16>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("mismatched Option types must fail");
    assert!(
        err.to_string()
            .contains("requires an argument of the same Option type"),
        "unexpected error: {err}"
    );
}

#[test]
fn lower_option_partial_ord_rejects_non_integer_payload() {
    let expr: syn::Expr = syn::parse_str("left.lt(&right)").unwrap();
    let env = env_with(&[("left", "Option<bool>"), ("right", "Option<bool>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("Option<bool> ordering must fail");
    assert!(
        err.to_string()
            .contains("supports only Option<T> with a finite-width integer T"),
        "unexpected error: {err}"
    );
}

#[test]
fn lower_partial_ord_lt_method_coerces_unsuffixed_literal_argument() {
    let expr: syn::Expr = syn::parse_str("x.lt(&7)").unwrap();
    let env = env_with(&[("x", "u8")]);
    let lowered = lower_syn_expr(&expr, &env).expect("lt literal method should lower");
    match lowered {
        TrustVcExpr::Compare { op, right, .. } => {
            assert_eq!(op, CompareOp::Lt);
            assert_eq!(
                *right,
                TrustVcExpr::IntLit {
                    value: 7,
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
        }
        other => panic!("expected coerced literal Compare, got {other:?}"),
    }
}

#[test]
fn lower_partial_ord_integer_method_rejects_wrong_arity() {
    let expr: syn::Expr = syn::parse_str("x.lt(&y, &z)").unwrap();
    let env = env_with(&[("x", "u8"), ("y", "u8"), ("z", "u8")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong arity must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("lt expects 1 arg, got 2"),
        "error should mention arity, got: {err}",
    );
}

#[test]
fn lower_partial_ord_integer_method_rejects_noninteger_receiver() {
    let expr: syn::Expr = syn::parse_str("flag.gt(&other)").unwrap();
    let env = env_with(&[("flag", "bool"), ("other", "bool")]);
    let err = lower_syn_expr(&expr, &env).expect_err("noninteger receiver must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string()
            .contains("PartialOrd integer methods require a finite-width integer receiver"),
        "error should mention primitive integer receiver requirement, got: {err}",
    );
}

#[test]
fn lower_verus_result_is_ok_to_tester_call() {
    let expr = crate::parse_expr_str_with_chains("res is Ok").unwrap();
    let env = env_with(&[("res", "Result<u64, bool>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("Result variant test should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "is-Result_u64_bool_Ok");
            assert_eq!(return_ty, TrustVcType::Bool);
            assert_eq!(
                args,
                vec![TrustVcExpr::Var {
                    name: "res".to_string(),
                    ty: TrustVcType::from_str("Result<u64, bool>").unwrap(),
                }]
            );
        }
        other => panic!("expected Result tester FnCall, got {other:?}"),
    }
}

#[test]
fn lower_verus_result_is_err_on_direct_err_to_true() {
    let expr = crate::parse_expr_str_with_chains("Result::<u64, bool>::Err(false) is Err").unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new())
        .expect("direct Result::Err variant test should lower");
    assert_eq!(lowered, TrustVcExpr::BoolLit(true));
}

#[test]
fn lower_verus_result_wrong_variant_tests_on_direct_constructors_to_false() {
    let ok_is_err = crate::parse_expr_str_with_chains("Result::<u64, bool>::Ok(7u64) is Err")
        .expect("direct Result::Ok wrong variant test should parse");
    let lowered = lower_syn_expr(&ok_is_err, &TypeEnv::new())
        .expect("direct Result::Ok wrong variant test should lower");
    assert_eq!(lowered, TrustVcExpr::BoolLit(false));

    let err_is_ok = crate::parse_expr_str_with_chains("Result::<u64, bool>::Err(false) is Ok")
        .expect("direct Result::Err wrong variant test should parse");
    let lowered = lower_syn_expr(&err_is_ok, &TypeEnv::new())
        .expect("direct Result::Err wrong variant test should lower");
    assert_eq!(lowered, TrustVcExpr::BoolLit(false));
}

#[test]
fn lower_extracted_result_wrong_variant_tests_on_direct_constructors_to_false() {
    let ok_is_err: syn::Expr =
        syn::parse_str("(Result :: < i32, CustomErr > :: Ok(1i32)).is_err()")
            .expect("extracted direct Result::Ok wrong variant test should parse");
    let lowered = lower_syn_expr(&ok_is_err, &TypeEnv::new())
        .expect("extracted direct Result::Ok wrong variant test should lower");
    assert_eq!(lowered, TrustVcExpr::BoolLit(false));

    let err_is_ok: syn::Expr = syn::parse_str(
        "(Result :: < i32, CustomErr > :: Err(CustomErr { error_code: -1i32 })).is_ok()",
    )
    .expect("extracted direct Result::Err wrong variant test should parse");
    let mut env = TypeEnv::new();
    env.register_type_metadata_only(&TrustVcType::Datatype {
        name: "CustomErr".to_string(),
        variants: vec![DatatypeVariant::new(
            "CustomErr",
            vec![("error_code".to_string(), TrustVcType::Int { width: 32 })],
        )],
    });
    let lowered = lower_syn_expr(&err_is_ok, &env)
        .expect("extracted direct Result::Err wrong variant test should lower");
    assert_eq!(lowered, TrustVcExpr::BoolLit(false));
}

#[test]
fn lower_result_methods_do_not_treat_suffix_named_functions_as_constructors() {
    let result_ty = TrustVcType::from_str("Result<u64, bool>").unwrap();
    let mut env = TypeEnv::new();
    env.insert_fn("foo_Ok".to_string(), result_ty.clone());
    env.insert_fn_params("foo_Ok".to_string(), vec![TrustVcType::Uint { width: 64 }]);

    let is_err: syn::Expr = syn::parse_str("foo_Ok(7u64).is_err()").unwrap();
    let lowered = lower_syn_expr(&is_err, &env)
        .expect("suffix-named helper returning Result should lower as an unknown Result value");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "is-Result_u64_bool_Err");
            assert_eq!(return_ty, TrustVcType::Bool);
            assert_eq!(
                args,
                vec![TrustVcExpr::FnCall {
                    name: "foo_Ok".to_string(),
                    args: vec![TrustVcExpr::IntLit {
                        value: 7,
                        ty: TrustVcType::Uint { width: 64 },
                    }],
                    return_ty: result_ty,
                }]
            );
        }
        other => panic!("expected Result tester call for unknown helper result, got {other:?}"),
    }

    let unwrap: syn::Expr = syn::parse_str("foo_Ok(7u64).unwrap()").unwrap();
    let err = lower_syn_expr(&unwrap, &env)
        .expect_err("suffix-named helper returning Result must not expose an Ok payload");
    assert!(
        err.to_string().contains("known to be Ok"),
        "error should mention known-Ok requirement, got: {err}",
    );
}

#[test]
fn lower_verus_result_err_projection_to_selector_call() {
    let expr = crate::parse_expr_str_with_chains("res->Err_0").unwrap();
    let env = env_with(&[("res", "Result<u64, bool>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("Result Err_0 projection should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "Result_u64_bool_Err_0");
            assert_eq!(return_ty, TrustVcType::Bool);
            assert_eq!(
                args,
                vec![TrustVcExpr::Var {
                    name: "res".to_string(),
                    ty: TrustVcType::from_str("Result<u64, bool>").unwrap(),
                }]
            );
        }
        other => panic!("expected Result selector FnCall, got {other:?}"),
    }
}

#[test]
fn lower_verus_result_direct_variant_projections_to_payloads() {
    let ok_projection = crate::parse_expr_str_with_chains("Result::<u64, bool>::Ok(7u64)->Ok_0")
        .expect("direct Result::Ok projection should parse");
    let lowered = lower_syn_expr(&ok_projection, &TypeEnv::new())
        .expect("direct Result::Ok projection should lower");
    assert_eq!(
        lowered,
        TrustVcExpr::IntLit {
            value: 7,
            ty: TrustVcType::Uint { width: 64 },
        }
    );

    let err_projection =
        crate::parse_expr_str_with_chains("Result::<u64, bool>::Err(false)->Err_0")
            .expect("direct Result::Err projection should parse");
    let lowered = lower_syn_expr(&err_projection, &TypeEnv::new())
        .expect("direct Result::Err projection should lower");
    assert_eq!(lowered, TrustVcExpr::BoolLit(false));
}

#[test]
fn lower_registered_struct_literal_to_constructor_call() {
    let expr: syn::Expr = syn::parse_str("Counter { count: 1, max: 10 }").unwrap();
    let mut env = TypeEnv::new();
    env.insert("counter".to_string(), counter_ty());

    let lowered = lower_syn_expr(&expr, &env).expect("registered struct literal should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "Counter_Counter");
            assert_eq!(
                args,
                vec![
                    TrustVcExpr::IntLit {
                        value: 1,
                        ty: TrustVcType::Uint { width: 32 },
                    },
                    TrustVcExpr::IntLit {
                        value: 10,
                        ty: TrustVcType::Uint { width: 32 },
                    },
                ]
            );
            assert_eq!(
                return_ty,
                TrustVcType::Datatype {
                    name: "Counter".to_string(),
                    variants: vec![DatatypeVariant::new(
                        "Counter",
                        vec![
                            ("count".to_string(), TrustVcType::Uint { width: 32 }),
                            ("max".to_string(), TrustVcType::Uint { width: 32 }),
                        ],
                    )],
                }
            );
        }
        other => panic!("expected constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_registered_struct_literal_uses_declared_field_order() {
    let expr: syn::Expr = syn::parse_str("Counter { max: 10, count: 1 }").unwrap();
    let mut env = TypeEnv::new();
    env.insert("counter".to_string(), counter_ty());

    let lowered = lower_syn_expr(&expr, &env).expect("registered struct literal should lower");
    match lowered {
        TrustVcExpr::FnCall { args, .. } => assert_eq!(
            args,
            vec![
                TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Uint { width: 32 },
                },
                TrustVcExpr::IntLit {
                    value: 10,
                    ty: TrustVcType::Uint { width: 32 },
                },
            ]
        ),
        other => panic!("expected constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_unknown_struct_literal_reports_type() {
    let expr: syn::Expr = syn::parse_str("Missing { count: 1u32 }").unwrap();
    let err = lower_syn_expr(&expr, &TypeEnv::new()).expect_err("unknown struct literal must fail");
    assert!(matches!(err, LoweringError::UnsupportedExpr(_)));
    assert!(
        err.to_string()
            .contains("struct literal for unknown type 'Missing'"),
        "error should mention unknown type, got: {err}",
    );
}

#[test]
fn lower_wrapping_add() {
    let expr: syn::Expr = syn::parse_str("x.wrapping_add(y)").unwrap();
    let env = env_with(&[("x", "u32"), ("y", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::WrappingArith {
            mode: WrappingMode::Wrapping,
            op: ArithOp::Add,
            ..
        }
    ));
}

#[test]
fn lower_checked_add_propagates_receiver_type() {
    let expr: syn::Expr = syn::parse_str("x.checked_add(1)").unwrap();
    let env = env_with(&[("x", "u8")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::WrappingArith {
            mode,
            op,
            right,
            ty,
            ..
        } => {
            assert_eq!(mode, WrappingMode::Checked);
            assert_eq!(op, ArithOp::Add);
            assert_eq!(ty, TrustVcType::Uint { width: 8 });
            assert_eq!(
                *right,
                TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Uint { width: 8 }
                }
            );
        }
        other => panic!("expected WrappingArith, got {:?}", other),
    }
}

#[test]
fn lower_saturating_add_produces_wrapping_arith() {
    let expr: syn::Expr = syn::parse_str("x.saturating_add(y)").unwrap();
    let env = env_with(&[("x", "u32"), ("y", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::WrappingArith {
            mode: WrappingMode::Saturating,
            op: ArithOp::Add,
            ..
        }
    ));
}

#[test]
fn lower_saturating_sub_produces_wrapping_arith() {
    let expr: syn::Expr = syn::parse_str("x.saturating_sub(y)").unwrap();
    let env = env_with(&[("x", "u32"), ("y", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::WrappingArith {
            mode: WrappingMode::Saturating,
            op: ArithOp::Sub,
            ..
        }
    ));
}

#[test]
fn lower_saturating_mul_produces_wrapping_arith() {
    let expr: syn::Expr = syn::parse_str("x.saturating_mul(y)").unwrap();
    let env = env_with(&[("x", "u32"), ("y", "u32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(
        result,
        TrustVcExpr::WrappingArith {
            mode: WrappingMode::Saturating,
            op: ArithOp::Mul,
            ..
        }
    ));
}

#[test]
fn lower_integer_max_to_ge_ite() {
    // a.max(b) === if a >= b { a } else { b }.
    let expr: syn::Expr = syn::parse_str("x.max(0)").unwrap();
    let env = env_with(&[("x", "i128")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i128 max should lower");
    let i128_ty = TrustVcType::Int { width: 128 };
    match lowered {
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            assert_eq!(ty, i128_ty);
            assert!(matches!(
                *cond,
                TrustVcExpr::Compare {
                    op: CompareOp::Ge,
                    ..
                }
            ));
            assert_eq!(
                *then_branch,
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: i128_ty.clone(),
                }
            );
            assert_eq!(
                *else_branch,
                TrustVcExpr::IntLit {
                    value: 0,
                    ty: i128_ty,
                }
            );
        }
        other => panic!("expected max Ite, got {other:?}"),
    }
}

#[test]
fn lower_integer_min_to_le_ite() {
    // a.min(b) === if a <= b { a } else { b }.
    let expr: syn::Expr = syn::parse_str("x.min(y)").unwrap();
    let env = env_with(&[("x", "i64"), ("y", "i64")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i64 min should lower");
    match lowered {
        TrustVcExpr::Ite { cond, ty, .. } => {
            assert_eq!(ty, TrustVcType::Int { width: 64 });
            assert!(matches!(
                *cond,
                TrustVcExpr::Compare {
                    op: CompareOp::Le,
                    ..
                }
            ));
        }
        other => panic!("expected min Ite, got {other:?}"),
    }
}

#[test]
fn lower_integer_abs_to_sign_ite() {
    // x.abs() === if x < 0 { 0 - x } else { x }.
    let expr: syn::Expr = syn::parse_str("x.abs()").unwrap();
    let env = env_with(&[("x", "i32")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i32 abs should lower");
    match lowered {
        TrustVcExpr::Ite {
            cond,
            then_branch,
            ty,
            ..
        } => {
            assert_eq!(ty, TrustVcType::Int { width: 32 });
            assert!(matches!(
                *cond,
                TrustVcExpr::Compare {
                    op: CompareOp::Lt,
                    ..
                }
            ));
            assert!(matches!(
                *then_branch,
                TrustVcExpr::Arith {
                    op: ArithOp::Sub,
                    ..
                }
            ));
        }
        other => panic!("expected abs Ite, got {other:?}"),
    }
}

#[test]
fn lower_integer_saturating_abs_models_min_corner() {
    // x.saturating_abs() === if x == MIN { MAX } else { abs(x) }.
    let expr: syn::Expr = syn::parse_str("x.saturating_abs()").unwrap();
    let env = env_with(&[("x", "i128")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i128 saturating_abs should lower");
    let i128_ty = TrustVcType::Int { width: 128 };
    match lowered {
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            assert_eq!(ty, i128_ty);
            // Outer guard tests x == i128::MIN.
            match *cond {
                TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    right,
                    ..
                } => assert_eq!(
                    *right,
                    TrustVcExpr::IntLit {
                        value: i128::MIN,
                        ty: i128_ty.clone(),
                    }
                ),
                other => panic!("expected MIN equality guard, got {other:?}"),
            }
            // Saturated branch yields i128::MAX.
            assert_eq!(
                *then_branch,
                TrustVcExpr::IntLit {
                    value: i128::MAX,
                    ty: i128_ty,
                }
            );
            // Else branch is the abs sign-Ite.
            assert!(matches!(*else_branch, TrustVcExpr::Ite { .. }));
        }
        other => panic!("expected saturating_abs Ite, got {other:?}"),
    }
}

#[test]
fn lower_unsigned_abs_falls_through_to_unsupported() {
    // `abs`/`saturating_abs` are signed methods; an unsigned receiver must not be
    // claimed by the min/max/abs path (fails closed with the standard diagnostic).
    let expr: syn::Expr = syn::parse_str("x.saturating_abs()").unwrap();
    let env = env_with(&[("x", "u32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("unsigned saturating_abs must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
}

#[test]
fn lower_integer_max_rejects_mismatched_argument_type() {
    let expr: syn::Expr = syn::parse_str("x.max(flag)").unwrap();
    let env = env_with(&[("x", "i32"), ("flag", "bool")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong argument type must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string()
            .contains("requires an argument of the same finite integer type"),
        "error should mention argument type requirement, got: {err}",
    );
}

/// `env` where the source imports `std::ops::{Add, Shl, Shr}` at every call of
/// their methods, as the extractor records it.
fn with_std_operators(mut env: TypeEnv) -> TypeEnv {
    for method in ["add", "shl", "shr"] {
        env.register_std_operator_method(method);
    }
    env
}

#[test]
fn lower_primitive_integer_operator_method_needs_the_std_trait_in_scope() {
    // Without the std trait in scope the call resolves to another trait's
    // method of that name, so the lowering refuses it.
    for (src, vars) in [
        ("x.add(y)", [("x", "u64"), ("y", "u64")]),
        ("x.shl(y)", [("x", "u64"), ("y", "u32")]),
        ("x.shr(y)", [("x", "i8"), ("y", "u32")]),
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let err = lower_syn_expr(&expr, &env_with(&vars)).expect_err(src);
        assert!(matches!(err, LoweringError::UnsupportedMethod(_)), "{src}");
        assert!(err.to_string().contains("std::ops::"), "{src}: {err}");
    }
    // One method in scope does not bring in another.
    let mut env = env_with(&[("x", "u64"), ("y", "u32")]);
    env.register_std_operator_method("add");
    let expr: syn::Expr = syn::parse_str("x.shl(y)").unwrap();
    assert!(lower_syn_expr(&expr, &env).is_err());
    // A non-integer receiver keeps its own `add` (a `Seq` append).
    let expr: syn::Expr = syn::parse_str("s.add(t)").unwrap();
    let env = env_with(&[("s", "Seq<i32>"), ("t", "Seq<i32>")]);
    assert!(lower_syn_expr(&expr, &env).is_ok());
}

#[test]
fn lower_primitive_integer_add_trait_method_to_arithmetic() {
    let expr: syn::Expr = syn::parse_str("x.add(y)").unwrap();
    let env = with_std_operators(env_with(&[("x", "usize"), ("y", "usize")]));
    let lowered = lower_syn_expr(&expr, &env).expect("usize add method should lower");
    let usize_ty = TrustVcType::Uint { width: usize::BITS };
    match lowered {
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => {
            assert_eq!(op, ArithOp::Add);
            assert_eq!(ty, usize_ty);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: usize_ty.clone(),
                }
            );
            assert_eq!(
                *right,
                TrustVcExpr::Var {
                    name: "y".to_string(),
                    ty: usize_ty,
                }
            );
        }
        other => panic!("expected primitive add Arith, got {other:?}"),
    }
}

#[test]
fn lower_primitive_integer_add_trait_method_coerces_unsuffixed_literal() {
    let expr: syn::Expr = syn::parse_str("x.add(1)").unwrap();
    let env = with_std_operators(env_with(&[("x", "u8")]));
    let lowered = lower_syn_expr(&expr, &env).expect("u8 add literal method should lower");
    match lowered {
        TrustVcExpr::Arith { op, right, ty, .. } => {
            assert_eq!(op, ArithOp::Add);
            assert_eq!(ty, TrustVcType::Uint { width: 8 });
            assert_eq!(
                *right,
                TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Uint { width: 8 },
                }
            );
        }
        other => panic!("expected coerced primitive add Arith, got {other:?}"),
    }
}

#[test]
fn lower_primitive_integer_add_trait_method_rejects_mismatched_argument_type() {
    let expr: syn::Expr = syn::parse_str("x.add(flag)").unwrap();
    let env = with_std_operators(env_with(&[("x", "u32"), ("flag", "bool")]));
    let err = lower_syn_expr(&expr, &env).expect_err("wrong argument type must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string()
            .contains("requires an argument of the same finite integer type"),
        "error should mention argument type requirement, got: {err}",
    );
}

#[test]
fn lower_primitive_integer_shl_trait_method_to_special_arith() {
    // `core::ops::Shl::shl` method-call form lowers to the same
    // `SpecialArith { op: Shl, .. }` IR as the binary `<<` operator (#2779).
    let expr: syn::Expr = syn::parse_str("u.shl(amt)").unwrap();
    let env = with_std_operators(env_with(&[("u", "u16"), ("amt", "u16")]));
    let lowered = lower_syn_expr(&expr, &env).expect("u16 shl method should lower");
    let u16_ty = TrustVcType::Uint { width: 16 };
    match lowered {
        TrustVcExpr::SpecialArith {
            op,
            left,
            right,
            ty,
        } => {
            assert_eq!(op, SpecialArithOp::Shl);
            assert_eq!(ty, u16_ty);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "u".to_string(),
                    ty: u16_ty.clone(),
                }
            );
            assert_eq!(
                *right,
                TrustVcExpr::Var {
                    name: "amt".to_string(),
                    ty: u16_ty,
                }
            );
        }
        other => panic!("expected primitive shl SpecialArith, got {other:?}"),
    }
}

#[test]
fn lower_primitive_integer_shr_trait_method_to_special_arith() {
    // `core::ops::Shr::shr` method-call form lowers to `SpecialArith { op: Shr }`.
    let expr: syn::Expr = syn::parse_str("u.shr(amt)").unwrap();
    let env = with_std_operators(env_with(&[("u", "i16"), ("amt", "i16")]));
    let lowered = lower_syn_expr(&expr, &env).expect("i16 shr method should lower");
    let i16_ty = TrustVcType::Int { width: 16 };
    match lowered {
        TrustVcExpr::SpecialArith { op, left, ty, .. } => {
            assert_eq!(op, SpecialArithOp::Shr);
            assert_eq!(ty, i16_ty);
            assert_eq!(
                *left,
                TrustVcExpr::Var {
                    name: "u".to_string(),
                    ty: i16_ty,
                }
            );
        }
        other => panic!("expected primitive shr SpecialArith, got {other:?}"),
    }
}

#[test]
fn lower_primitive_integer_shl_trait_method_coerces_unsuffixed_literal() {
    // An unsuffixed literal shift amount is coerced to the receiver's integer
    // type so it carries a known width (mirrors the binary `<<` literal path).
    let expr: syn::Expr = syn::parse_str("u.shl(15)").unwrap();
    let env = with_std_operators(env_with(&[("u", "u16")]));
    let lowered = lower_syn_expr(&expr, &env).expect("u16 shl literal method should lower");
    let u16_ty = TrustVcType::Uint { width: 16 };
    match lowered {
        TrustVcExpr::SpecialArith { op, right, ty, .. } => {
            assert_eq!(op, SpecialArithOp::Shl);
            assert_eq!(ty, u16_ty);
            assert_eq!(
                *right,
                TrustVcExpr::IntLit {
                    value: 15,
                    ty: u16_ty,
                }
            );
        }
        other => panic!("expected coerced primitive shl SpecialArith, got {other:?}"),
    }
}

#[test]
fn lower_primitive_integer_shl_trait_method_rejects_non_integer_amount() {
    // A non-integer shift amount must fail closed (more-or-equally conservative
    // than Verus, which type-checks the `Shl` impl's RHS).
    let expr: syn::Expr = syn::parse_str("u.shl(flag)").unwrap();
    let env = with_std_operators(env_with(&[("u", "u16"), ("flag", "bool")]));
    let err = lower_syn_expr(&expr, &env).expect_err("non-integer shift amount must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("integer shift amount"),
        "error should mention the integer shift amount requirement, got: {err}",
    );
}

#[test]
fn lower_signed_finite_div_euclid_to_conditional_truncating_div() {
    let expr: syn::Expr = syn::parse_str("x.div_euclid(y)").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32")]);
    let lowered = lower_syn_expr(&expr, &env).expect("signed div_euclid should lower");
    assert_euclidean_ite_shape(&lowered, ArithOp::Div, TrustVcType::Int { width: 32 });
}

#[test]
fn lower_signed_finite_rem_euclid_to_conditional_truncating_rem() {
    let expr: syn::Expr = syn::parse_str("x.rem_euclid(y)").unwrap();
    let env = env_with(&[("x", "i64"), ("y", "i64")]);
    let lowered = lower_syn_expr(&expr, &env).expect("signed rem_euclid should lower");
    assert_euclidean_ite_shape(&lowered, ArithOp::Rem, TrustVcType::Int { width: 64 });
}

#[test]
fn lower_unsigned_div_euclid_to_plain_division() {
    let expr: syn::Expr = syn::parse_str("x.div_euclid(y)").unwrap();
    let env = env_with(&[("x", "u32"), ("y", "u32")]);
    let lowered = lower_syn_expr(&expr, &env).expect("unsigned div_euclid should lower");
    assert!(matches!(
        lowered,
        TrustVcExpr::Arith {
            op: ArithOp::Div,
            ty: TrustVcType::Uint { width: 32 },
            ..
        }
    ));
}

#[test]
fn lower_unsigned_rem_euclid_to_plain_remainder() {
    let expr: syn::Expr = syn::parse_str("x.rem_euclid(y)").unwrap();
    let env = env_with(&[("x", "u16"), ("y", "u16")]);
    let lowered = lower_syn_expr(&expr, &env).expect("unsigned rem_euclid should lower");
    assert!(matches!(
        lowered,
        TrustVcExpr::Arith {
            op: ArithOp::Rem,
            ty: TrustVcType::Uint { width: 16 },
            ..
        }
    ));
}

#[test]
fn lower_mathint_div_euclid_to_euclidean_division() {
    // Verus `int`: `div_euclid` routes to `ArithOp::Div` on `MathInt`, which the
    // encoder emits as SMT-LIB Euclidean `Int.div` (no finite-width sign wrapper).
    // Mirrors the `/` operator on `int` (already Euclidean) and lets the ay-pb
    // cutting-planes `ceil_div` (refutation_check.rs:206-217) be specified over ℤ.
    let expr: syn::Expr = syn::parse_str("x.div_euclid(y)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "int")]);
    let lowered = lower_syn_expr(&expr, &env).expect("int div_euclid should lower");
    assert!(matches!(
        lowered,
        TrustVcExpr::Arith {
            op: ArithOp::Div,
            ty: TrustVcType::MathInt,
            ..
        }
    ));
}

#[test]
fn lower_mathint_rem_euclid_to_euclidean_remainder() {
    let expr: syn::Expr = syn::parse_str("x.rem_euclid(y)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "int")]);
    let lowered = lower_syn_expr(&expr, &env).expect("int rem_euclid should lower");
    assert!(matches!(
        lowered,
        TrustVcExpr::Arith {
            op: ArithOp::Rem,
            ty: TrustVcType::MathInt,
            ..
        }
    ));
}

#[test]
fn lower_nat_div_euclid_to_euclidean_division() {
    let expr: syn::Expr = syn::parse_str("x.div_euclid(y)").unwrap();
    let env = env_with(&[("x", "nat"), ("y", "nat")]);
    let lowered = lower_syn_expr(&expr, &env).expect("nat div_euclid should lower");
    assert!(matches!(
        lowered,
        TrustVcExpr::Arith {
            op: ArithOp::Div,
            ty: TrustVcType::Nat,
            ..
        }
    ));
}

#[test]
fn lower_signed_finite_euclid_method_rejects_wrong_arity() {
    let expr: syn::Expr = syn::parse_str("x.div_euclid(y, z)").unwrap();
    let env = env_with(&[("x", "i32"), ("y", "i32"), ("z", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong arity must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("div_euclid expects 1 arg, got 2"),
        "error should mention arity, got: {err}",
    );
}

#[test]
fn lower_math_int_rem_euclid_rejects_mismatched_argument_type() {
    // `int`/`nat` Euclidean methods are now SUPPORTED (routed to Euclidean
    // `Int.div`/`mod`; see `lower_mathint_*_to_euclidean_*`). The argument must be
    // an `int`/`nat` too — a finite-width arg against a math-int receiver is
    // rejected by the new MathInt/Nat branch's argument-type guard.
    let expr: syn::Expr = syn::parse_str("x.rem_euclid(y)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("mismatched math-int arg must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("requires an `int`/`nat` argument"),
        "error should mention the int/nat argument requirement, got: {err}",
    );
}

#[test]
fn lower_signed_finite_euclid_method_rejects_mismatched_argument_type() {
    let expr: syn::Expr = syn::parse_str("x.rem_euclid(flag)").unwrap();
    let env = env_with(&[("x", "i32"), ("flag", "bool")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong argument type must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string()
            .contains("requires an argument of the same finite integer type"),
        "error should mention argument type requirement, got: {err}",
    );
}

#[test]
fn lower_mathint_min_to_conditional() {
    // Verus `int`: `a.min(b)` lowers to `if a <= b { a } else { b }` (an `Ite`
    // over the SMT `Int` sort). Unblocks the ay-pb cutting-planes
    // `impliedGe_saturate` step (refutation_check.rs:176, `c.min(self.rhs)`).
    let expr: syn::Expr = syn::parse_str("x.min(y)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "int")]);
    let lowered = lower_syn_expr(&expr, &env).expect("int min should lower");
    assert_minmax_ite_shape(&lowered, CompareOp::Le, TrustVcType::MathInt);
}

#[test]
fn lower_mathint_max_to_conditional() {
    let expr: syn::Expr = syn::parse_str("x.max(y)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "int")]);
    let lowered = lower_syn_expr(&expr, &env).expect("int max should lower");
    assert_minmax_ite_shape(&lowered, CompareOp::Ge, TrustVcType::MathInt);
}

#[test]
fn lower_i128_min_to_conditional() {
    // The real `c.min(self.rhs)` receiver type is i128: `a.min(b)` lowers to the
    // signed-128 comparison `Ite` (min/max never overflow, so no sign wrapper).
    let expr: syn::Expr = syn::parse_str("x.min(y)").unwrap();
    let env = env_with(&[("x", "i128"), ("y", "i128")]);
    let lowered = lower_syn_expr(&expr, &env).expect("i128 min should lower");
    assert_minmax_ite_shape(&lowered, CompareOp::Le, TrustVcType::Int { width: 128 });
}

#[test]
fn lower_nat_max_to_conditional() {
    let expr: syn::Expr = syn::parse_str("x.max(y)").unwrap();
    let env = env_with(&[("x", "nat"), ("y", "nat")]);
    let lowered = lower_syn_expr(&expr, &env).expect("nat max should lower");
    assert_minmax_ite_shape(&lowered, CompareOp::Ge, TrustVcType::Nat);
}

#[test]
fn lower_minmax_method_rejects_wrong_arity() {
    let expr: syn::Expr = syn::parse_str("x.min(y, z)").unwrap();
    let env = env_with(&[("x", "int"), ("y", "int"), ("z", "int")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong arity must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("min expects 1 arg, got 2"),
        "error should mention arity, got: {err}",
    );
}

#[test]
fn lower_minmax_method_rejects_mismatched_argument_type() {
    let expr: syn::Expr = syn::parse_str("x.min(flag)").unwrap();
    let env = env_with(&[("x", "i32"), ("flag", "bool")]);
    let err = lower_syn_expr(&expr, &env).expect_err("wrong argument type must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    // A finite-width receiver (`i32`) is now claimed by the upstream
    // `lower_minmax_abs_integer_method_call` dispatch (which also adds
    // `abs`/`saturating_abs`); the math-int/`nat` path stays with
    // `lower_minmax_integer_method_call`. Both reject a mismatched (non-integer)
    // argument as `UnsupportedMethod` with a "requires an argument of the same
    // [finite] integer type" diagnostic, so assert the wording common to both.
    let msg = err.to_string();
    assert!(
        msg.contains("requires an argument of the same") && msg.contains("integer type"),
        "error should mention argument type requirement, got: {err}",
    );
}

fn assert_minmax_ite_shape(expr: &TrustVcExpr, expected_cmp: CompareOp, expected_ty: TrustVcType) {
    let TrustVcExpr::Ite {
        cond,
        then_branch,
        else_branch,
        ty,
    } = expr
    else {
        panic!("expected min/max Ite, got: {expr:?}");
    };
    assert_eq!(*ty, expected_ty);
    assert!(
        matches!(cond.as_ref(), TrustVcExpr::Compare { op, .. } if *op == expected_cmp),
        "min/max condition should compare with {expected_cmp:?}, got: {cond:?}",
    );
    // then_branch is the receiver, else_branch is the argument (both the operand
    // type); the picked operand is one of them, so neither is a nested Ite here.
    assert!(
        !matches!(then_branch.as_ref(), TrustVcExpr::Ite { .. }),
        "min/max then-branch should be the receiver operand, got: {then_branch:?}",
    );
    assert!(
        !matches!(else_branch.as_ref(), TrustVcExpr::Ite { .. }),
        "min/max else-branch should be the argument operand, got: {else_branch:?}",
    );
}

fn assert_euclidean_ite_shape(
    expr: &TrustVcExpr,
    expected_inner_op: ArithOp,
    expected_ty: TrustVcType,
) {
    let TrustVcExpr::Ite {
        cond,
        then_branch,
        else_branch,
        ty,
    } = expr
    else {
        panic!("expected outer Ite, got: {expr:?}");
    };
    assert_eq!(*ty, expected_ty);
    assert!(matches!(
        cond.as_ref(),
        TrustVcExpr::Compare {
            op: CompareOp::Lt,
            ..
        }
    ));
    assert!(matches!(
        then_branch.as_ref(),
        TrustVcExpr::Ite {
            ty,
            ..
        } if *ty == expected_ty
    ));
    assert!(matches!(
        else_branch.as_ref(),
        TrustVcExpr::Arith {
            op,
            ty,
            ..
        } if *op == expected_inner_op && *ty == expected_ty
    ));
}

fn option_u32_ty() -> TrustVcType {
    TrustVcType::from_str("Option<u32>").unwrap()
}

fn result_u32_u32_ty() -> TrustVcType {
    TrustVcType::from_str("Result<u32, u32>").unwrap()
}

#[test]
fn lower_option_is_some_to_tester_call() {
    let expr: syn::Expr = syn::parse_str("opt.is_some()").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let result = lower_syn_expr(&expr, &env).expect("is_some should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(name.contains("Some"), "tester should mention Some: {name}");
            assert_eq!(args.len(), 1);
            assert_eq!(return_ty, TrustVcType::Bool);
        }
        other => panic!("expected tester FnCall, got {:?}", other),
    }
}

#[test]
fn lower_f32_clone_to_receiver_identity() {
    let expr: syn::Expr = syn::parse_str("value.clone()").unwrap();
    let env = env_with(&[("value", "f32")]);
    let result = lower_syn_expr(&expr, &env).expect("f32 clone should lower");
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "value".to_string(),
            ty: TrustVcType::Float { width: 32 },
        }
    );
}

#[test]
fn lower_option_is_none_to_tester_call() {
    let expr: syn::Expr = syn::parse_str("opt.is_none()").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let result = lower_syn_expr(&expr, &env).expect("is_none should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(name.contains("None"), "tester should mention None: {name}");
            assert_eq!(args.len(), 1);
            assert_eq!(return_ty, TrustVcType::Bool);
        }
        other => panic!("expected tester FnCall, got {:?}", other),
    }
}

#[test]
fn lower_option_unwrap_known_some_local_returns_payload() {
    let expr: syn::Expr =
        syn::parse_str("{ let ok = Option::<i8>::Some(1); ok.unwrap() }").unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new()).expect("known Some unwrap should lower");
    match lowered {
        TrustVcExpr::Let { body, .. } => assert_eq!(
            *body,
            TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 8 }
            }
        ),
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_option_expect_known_some_ignores_message_literal() {
    let expr: syn::Expr =
        syn::parse_str("{ let ok = Option::<u32>::Some(7); ok.expect(\"built with Some\") }")
            .unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new()).expect("known Some expect should lower");
    match lowered {
        TrustVcExpr::Let { body, .. } => assert_eq!(
            *body,
            TrustVcExpr::IntLit {
                value: 7,
                ty: TrustVcType::Uint { width: 32 }
            }
        ),
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_result_unwrap_direct_ok_returns_payload() {
    let expr: syn::Expr = syn::parse_str("Result::<i8, i32>::Ok(1i8).unwrap()").unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new()).expect("known Ok unwrap should lower");
    assert_eq!(
        lowered,
        TrustVcExpr::IntLit {
            value: 1,
            ty: TrustVcType::Int { width: 8 }
        }
    );
}

#[test]
fn lower_result_expect_known_ok_local_returns_payload() {
    let expr: syn::Expr =
        syn::parse_str("{ let ok = Result::<u32, i32>::Ok(7); ok.expect(\"built with Ok\") }")
            .unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new()).expect("known Ok expect should lower");
    match lowered {
        TrustVcExpr::Let { body, .. } => assert_eq!(
            *body,
            TrustVcExpr::IntLit {
                value: 7,
                ty: TrustVcType::Uint { width: 32 }
            }
        ),
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_result_unwrap_unknown_fails_closed() {
    let expr: syn::Expr = syn::parse_str("res.unwrap()").unwrap();
    let env = env_with(&[("res", "Result<u32, u32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("unknown unwrap must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("known to be Ok"),
        "error should mention known-Ok requirement, got: {err}",
    );
}

#[test]
fn lower_result_expect_direct_err_fails_closed() {
    let expr: syn::Expr = syn::parse_str("Result::<u32, i32>::Err(-1).expect(\"ok\")").unwrap();
    let err = lower_syn_expr(&expr, &TypeEnv::new()).expect_err("known Err expect must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("known to be Ok"),
        "error should mention known-Ok requirement, got: {err}",
    );
}

#[test]
fn lower_result_expect_rejects_wrong_arity() {
    let expr: syn::Expr = syn::parse_str("Result::<u32, i32>::Ok(7).expect()").unwrap();
    let err = lower_syn_expr(&expr, &TypeEnv::new()).expect_err("wrong arity must fail");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("expect expects 1 arg"),
        "error should mention arity, got: {err}",
    );
}

#[test]
fn lower_option_unwrap_unknown_fails_closed() {
    let expr: syn::Expr = syn::parse_str("opt.unwrap()").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("unknown unwrap must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("known to be Some"),
        "error should mention known-Some requirement, got: {err}",
    );
}

#[test]
fn lower_typed_option_local_some_coerces_constructor_payload() {
    let expr: syn::Expr =
        syn::parse_str("{ let opt: Option<u32> = Some(42); opt.unwrap_or_default() }").unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new()).expect("typed Some local should lower");
    match lowered {
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            assert_eq!(ty, option_u32_ty());
            match *value {
                TrustVcExpr::FnCall {
                    args, return_ty, ..
                } => {
                    assert_eq!(return_ty, option_u32_ty());
                    assert_eq!(
                        args,
                        vec![TrustVcExpr::IntLit {
                            value: 42,
                            ty: TrustVcType::Uint { width: 32 }
                        }]
                    );
                }
                other => panic!("expected Some constructor, got {:?}", other),
            }
            assert_eq!(
                *body,
                TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Uint { width: 32 }
                }
            );
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_typed_option_local_some_ignores_unrelated_option_metadata() {
    let expr: syn::Expr =
        syn::parse_str("{ let opt: Option<u32> = Some(42); opt.unwrap_or_default() }").unwrap();
    let env = env_with(&[("other", "Option<u64>")]);
    let lowered = lower_syn_expr(&expr, &env)
        .expect("typed Some local should use the annotation, not unrelated metadata");
    match lowered {
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            assert_eq!(ty, option_u32_ty());
            assert_eq!(infer_expr_type(&value), option_u32_ty());
            assert_eq!(
                *body,
                TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Uint { width: 32 }
                }
            );
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_option_unwrap_or_default_none_returns_zero() {
    let expr: syn::Expr =
        syn::parse_str("{ let opt: Option<u32> = None; opt.unwrap_or_default() }").unwrap();
    let lowered = lower_syn_expr(&expr, &TypeEnv::new()).expect("typed None local should lower");
    match lowered {
        TrustVcExpr::Let { body, .. } => assert_eq!(
            *body,
            TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 32 }
            }
        ),
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_typed_option_local_none_uses_annotation_when_other_option_registered() {
    let expr: syn::Expr =
        syn::parse_str("{ let opt: Option<u32> = None; opt.unwrap_or_default() }").unwrap();
    let env = env_with(&[("other", "Option<u64>")]);
    let lowered = lower_syn_expr(&expr, &env)
        .expect("typed None local should use the annotation, not unrelated metadata");
    match lowered {
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            assert_eq!(ty, option_u32_ty());
            assert_eq!(infer_expr_type(&value), option_u32_ty());
            assert_eq!(
                *body,
                TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::Uint { width: 32 }
                }
            );
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_option_unwrap_or_else_unknown_to_match() {
    let expr: syn::Expr = syn::parse_str("opt.unwrap_or_else(|| 99)").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("unwrap_or_else should lower");
    match lowered {
        TrustVcExpr::Match { arms, ty, .. } => {
            assert_eq!(arms.len(), 2);
            assert_eq!(ty, TrustVcType::Uint { width: 32 });
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn lower_option_unwrap_or_else_accepts_trust_vc_closure_ensures_clause() {
    let expr: syn::Expr = syn::parse_str(
        "opt.unwrap_or_else(trust_vc::closure!(|| -> u32 ensures(|res: u32| res == 99u32) 99u32))",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered =
        lower_syn_expr(&expr, &env).expect("unwrap_or_else trust_vc::closure! should lower");
    match lowered {
        TrustVcExpr::Match { ty, arms, .. } => {
            assert_eq!(ty, TrustVcType::Uint { width: 32 });
            assert_eq!(arms.len(), 2);
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn lower_option_ok_or_else_typed_let_coerces_err_type() {
    let expr: syn::Expr =
        syn::parse_str("{ let res: Result<u32, u32> = opt.ok_or_else(|| 0); res }").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ok_or_else typed let should lower");
    match lowered {
        TrustVcExpr::Let { ty, value, .. } => {
            assert_eq!(ty, result_u32_u32_ty());
            match *value {
                TrustVcExpr::Match { ty, arms, .. } => {
                    assert_eq!(ty, result_u32_u32_ty());
                    assert_eq!(arms.len(), 2);
                    match &arms[1].body {
                        TrustVcExpr::FnCall {
                            args, return_ty, ..
                        } => {
                            assert_eq!(*return_ty, result_u32_u32_ty());
                            assert_eq!(
                                args,
                                &vec![TrustVcExpr::IntLit {
                                    value: 0,
                                    ty: TrustVcType::Uint { width: 32 }
                                }]
                            );
                        }
                        other => panic!("expected Err constructor, got {:?}", other),
                    }
                }
                other => panic!("expected Match value, got {:?}", other),
            }
        }
        other => panic!("expected Let, got {:?}", other),
    }
}

#[test]
fn lower_option_ok_or_else_accepts_trust_vc_closure_ensures_clause() {
    let expr: syn::Expr = syn::parse_str(
        "opt.ok_or_else(trust_vc::closure!(|| -> u32 ensures(|err: u32| err == 99u32) 99u32))",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("ok_or_else trust_vc::closure! should lower");
    match lowered {
        TrustVcExpr::Match { ty, arms, .. } => {
            assert_eq!(ty, result_u32_u32_ty());
            assert_eq!(arms.len(), 2);
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn lower_option_ok_or_else_contract_equivalent_match_shape() {
    let expr: syn::Expr = syn::parse_str(
        "{ let res: Result<u32, u32> = opt.ok_or_else(|| -> u32 { 99u32 }); \
           match opt { Some(x) => res == Ok::<u32, u32>(x), None => res == Err::<u32, u32>(99u32) } }",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("contract-equivalent ok_or_else should lower");
    match lowered {
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            assert_eq!(ty, result_u32_u32_ty());
            assert!(matches!(
                *value,
                TrustVcExpr::Match { ty, .. } if ty == result_u32_u32_ty()
            ));
            assert!(matches!(
                *body,
                TrustVcExpr::Match {
                    ty: TrustVcType::Bool,
                    ..
                }
            ));
        }
        other => panic!("expected Let with match value/body, got {:?}", other),
    }
}

#[test]
fn lower_option_and_then_unknown_to_match() {
    let expr: syn::Expr = syn::parse_str("opt.and_then(|x: u32| Some(x + 1))").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("and_then should lower");
    match lowered {
        TrustVcExpr::Match { ty, arms, .. } => {
            assert_eq!(ty, option_u32_ty());
            assert_eq!(arms.len(), 2);
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn lower_option_and_then_accepts_trust_vc_closure_requires_clause() {
    let expr: syn::Expr = syn::parse_str(
        "opt.and_then(trust_vc::closure!(|x: u32| -> Option<u32> requires(x < 1000u32) Some(x + 1u32)))",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("and_then trust_vc::closure! should lower");
    match lowered {
        TrustVcExpr::Match { ty, arms, .. } => {
            assert_eq!(ty, option_u32_ty());
            assert_eq!(arms.len(), 2);
        }
        other => panic!("expected Match, got {:?}", other),
    }
}

#[test]
fn lower_option_and_then_contract_equivalent_match_shape() {
    let expr: syn::Expr = syn::parse_str(
        "{ let res: Option<u32> = opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) }); \
           match opt { Some(x) => res == Some(x + 1u32), None => res == Option::<u32>::None } }",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("contract-equivalent and_then should lower");
    match lowered {
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            assert_eq!(ty, option_u32_ty());
            assert!(matches!(
                *value,
                TrustVcExpr::Match { ty, .. } if ty == option_u32_ty()
            ));
            assert!(matches!(
                *body,
                TrustVcExpr::Match {
                    ty: TrustVcType::Bool,
                    ..
                }
            ));
        }
        other => panic!("expected Let with match value/body, got {:?}", other),
    }
}

#[test]
fn lower_option_unwrap_or_else_contract_equivalent_match_shape() {
    let expr: syn::Expr = syn::parse_str(
        "{ let val: u32 = opt.unwrap_or_else(|| -> u32 { 99u32 }); \
           match opt { Some(x) => val == x, None => val == 99u32 } }",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered =
        lower_syn_expr(&expr, &env).expect("contract-equivalent unwrap_or_else should lower");
    match lowered {
        TrustVcExpr::Let {
            ty, value, body, ..
        } => {
            assert_eq!(ty, TrustVcType::Uint { width: 32 });
            assert!(matches!(
                *value,
                TrustVcExpr::Match {
                    ty: TrustVcType::Uint { width: 32 },
                    ..
                }
            ));
            assert!(matches!(
                *body,
                TrustVcExpr::Match {
                    ty: TrustVcType::Bool,
                    ..
                }
            ));
        }
        other => panic!("expected Let with match value/body, got {:?}", other),
    }
}

#[test]
fn lower_option_unwrap_or_else_rejects_non_closure() {
    let expr: syn::Expr = syn::parse_str("opt.unwrap_or_else(fallback)").unwrap();
    let env = env_with(&[("opt", "Option<u32>"), ("fallback", "u32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("non-closure fallback must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("expects a closure argument"),
        "error should mention closure requirement, got: {err}",
    );
}

#[test]
fn lower_option_unwrap_or_else_rejects_unqualified_closure_macro() {
    let expr: syn::Expr = syn::parse_str(
        "opt.unwrap_or_else(closure!(|| -> u32 ensures(|res: u32| res == 99u32) 99u32))",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("unqualified closure! macro must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("expects a closure argument"),
        "error should mention closure requirement, got: {err}",
    );
}

#[test]
fn lower_option_unwrap_or_else_rejects_non_trust_vc_closure_macro_path() {
    let expr: syn::Expr = syn::parse_str(
        "opt.unwrap_or_else(foo::closure!(|| -> u32 ensures(|res: u32| res == 99u32) 99u32))",
    )
    .unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let err =
        lower_syn_expr(&expr, &env).expect_err("non-trust_vc closure! macro path must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("expects a closure argument"),
        "error should mention closure requirement, got: {err}",
    );
}

#[test]
fn lower_option_unwrap_or_else_rejects_trust_vc_closure_without_contract() {
    let expr: syn::Expr =
        syn::parse_str("opt.unwrap_or_else(trust_vc::closure!(|| 99u32))").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let err = lower_syn_expr(&expr, &env)
        .expect_err("trust_vc::closure! without requires/ensures must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string()
            .contains("requires at least a requires(...) or ensures(...) clause"),
        "error should mention the missing contract clause, got: {err}",
    );
}

#[test]
fn lower_option_ok_or_else_rejects_closure_with_state_parameter() {
    let expr: syn::Expr = syn::parse_str("opt.ok_or_else(|state: u32| state)").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("non-zero-arg fallback must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedMethod(_)));
    assert!(
        err.to_string().contains("expects 0 parameters"),
        "error should mention zero-arg closure requirement, got: {err}",
    );
}

#[test]
fn lower_option_and_then_rejects_untyped_closure_parameter() {
    let expr: syn::Expr = syn::parse_str("opt.and_then(|x| Some(x + 1u32))").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("untyped and_then closure must fail closed");
    assert!(matches!(err, LoweringError::InvalidType(_)));
    assert!(
        err.to_string()
            .contains("requires an explicit type annotation"),
        "error should mention explicit type requirement, got: {err}",
    );
}

#[test]
fn lower_option_cloned_uses_erased_reference_value_model() {
    let expr: syn::Expr = syn::parse_str("opt.cloned()").unwrap();
    let env = env_with(&[("opt", "Option<u32>")]);
    let lowered = lower_syn_expr(&expr, &env).expect("cloned should lower");
    assert_eq!(
        lowered,
        TrustVcExpr::Var {
            name: "opt".to_string(),
            ty: option_u32_ty()
        }
    );
}

fn num_wrapper_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "NumWrapper".to_string(),
        variants: vec![DatatypeVariant::new(
            "NumWrapper",
            vec![("x".to_string(), TrustVcType::Uint { width: 64 })],
        )],
    }
}

#[test]
fn lower_direct_cow_owned_single_field_struct_view_to_field_projection() {
    let expr: syn::Expr = syn::parse_str("Cow::Owned(NumWrapper { x }).view()").unwrap();
    let mut env = env_with(&[("x", "u64")]);
    env.register_type_metadata_only(&num_wrapper_ty());
    let lowered = lower_syn_expr(&expr, &env).expect("direct Cow::Owned view should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(
                name.contains("NumWrapper"),
                "selector should mention type: {name}"
            );
            assert!(name.contains('x'), "selector should mention field: {name}");
            assert_eq!(args.len(), 1);
            assert_eq!(return_ty, TrustVcType::Uint { width: 64 });
        }
        other => panic!("expected field selector FnCall, got {:?}", other),
    }
}

#[test]
fn lower_direct_cow_borrowed_str_view_to_collection_view() {
    let expr: syn::Expr = syn::parse_str("Cow::Borrowed(s).view() == s.view()").unwrap();
    let env = env_with(&[("s", "str")]);
    let lowered = lower_syn_expr(&expr, &env).expect("direct Cow::Borrowed str view should lower");
    match lowered {
        TrustVcExpr::Compare { left, right, .. } => {
            assert!(matches!(
                *left,
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::View,
                    ty: TrustVcType::Seq(_),
                    ..
                }
            ));
            assert!(matches!(
                *right,
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::View,
                    ty: TrustVcType::Seq(_),
                    ..
                }
            ));
        }
        other => panic!("expected comparison, got {:?}", other),
    }
}

#[test]
fn lower_cow_view_on_unknown_variable_fails_closed() {
    let expr: syn::Expr = syn::parse_str("c.view()").unwrap();
    let env = env_with(&[("c", "Cow<str>")]);
    let err = lower_syn_expr(&expr, &env).expect_err("unknown Cow receiver must fail closed");
    assert!(
        err.to_string().contains("direct Cow::Owned") && err.to_string().contains("Cow::Borrowed"),
        "error should document direct-constructor requirement, got: {err}",
    );
}

#[test]
fn lower_direct_cow_owned_scalar_view_fails_closed() {
    let expr: syn::Expr = syn::parse_str("Cow::Owned(x).view()").unwrap();
    let env = env_with(&[("x", "u64")]);
    let err = lower_syn_expr(&expr, &env).expect_err("scalar Cow view must fail closed");
    assert!(
        err.to_string().contains("Cow::view for 'u64'"),
        "error should mention unsupported inner type, got: {err}",
    );
}
