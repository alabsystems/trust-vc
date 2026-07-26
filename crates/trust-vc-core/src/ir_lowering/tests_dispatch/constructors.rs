// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Datatype constructor lowering tests.

use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::*;
use crate::ir_lowering::*;

use super::support::{counter_ty, generic_choice_template_ty, option_u64_ty, outer_counter_ty};

#[test]
fn lower_nullary_datatype_constructor_path() {
    let expr: syn::Expr = syn::parse_str("None").unwrap();
    let mut env = TypeEnv::new();
    env.insert("opt".to_string(), option_u64_ty());
    let result = lower_syn_expr(&expr, &env).expect("None should lower as constructor");
    match result {
        TrustVcExpr::FnCall {
            ref name,
            ref args,
            ref return_ty,
        } => {
            assert!(
                name.contains("None"),
                "UF name should contain 'None', got: {name}"
            );
            assert!(args.is_empty(), "None is nullary, got {} args", args.len());
            assert_eq!(
                return_ty,
                &option_u64_ty(),
                "return type should be Option<u64>"
            );
        }
        other => panic!("expected FnCall for None, got: {:?}", other),
    }
}

#[test]
fn lower_datatype_constructor_call() {
    let expr: syn::Expr = syn::parse_str("Some(42u64)").unwrap();
    let mut env = TypeEnv::new();
    env.insert("opt".to_string(), option_u64_ty());
    let result = lower_syn_expr(&expr, &env).expect("Some(42u64) should lower as constructor");
    match result {
        TrustVcExpr::FnCall {
            ref name,
            ref args,
            ref return_ty,
        } => {
            assert!(
                name.contains("Some"),
                "UF name should contain 'Some', got: {name}"
            );
            assert_eq!(args.len(), 1, "Some takes 1 argument");
            assert_eq!(
                return_ty,
                &option_u64_ty(),
                "return type should be Option<u64>"
            );
        }
        other => panic!("expected FnCall for Some(42u64), got: {:?}", other),
    }
}

#[test]
fn lower_unqualified_some_infers_payload_type_despite_other_option_metadata() {
    let expr: syn::Expr = syn::parse_str("Some(42u32)").unwrap();
    let mut env = TypeEnv::new();
    env.insert("other".to_string(), option_u64_ty());
    let result = lower_syn_expr(&expr, &env)
        .expect("bare Some should infer from payload instead of using unrelated Option metadata");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(return_ty, TrustVcType::from_str("Option<u32>").unwrap());
            assert_eq!(
                args,
                vec![TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Uint { width: 32 }
                }]
            );
        }
        other => panic!("expected inferred Some constructor, got {:?}", other),
    }
}

#[test]
fn duplicate_option_metadata_does_not_make_none_ambiguous() {
    let expr: syn::Expr = syn::parse_str("None").unwrap();
    let mut env = TypeEnv::new();
    env.insert("first".to_string(), option_u64_ty());
    env.insert("second".to_string(), option_u64_ty());
    let result = lower_syn_expr(&expr, &env)
        .expect("duplicate registration of same Option type should be idempotent");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert!(args.is_empty());
            assert_eq!(return_ty, option_u64_ty());
        }
        other => panic!("expected None constructor, got {:?}", other),
    }
}

#[test]
fn custom_some_constructor_is_not_preempted_by_builtin_option_path() {
    let expr: syn::Expr = syn::parse_str("Some()").unwrap();
    let custom = TrustVcType::Datatype {
        name: "CustomSome".to_string(),
        variants: vec![DatatypeVariant::new("Some", vec![])],
    };
    let mut env = TypeEnv::new();
    env.insert("custom".to_string(), custom.clone());
    let result = lower_syn_expr(&expr, &env).expect("custom zero-field Some should lower");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert!(args.is_empty());
            assert_eq!(return_ty, custom);
        }
        other => panic!("expected custom Some constructor, got {:?}", other),
    }
}

#[test]
fn lower_qualified_datatype_constructor_call() {
    let expr: syn::Expr = syn::parse_str("Option::Some(42u64)").unwrap();
    let mut env = TypeEnv::new();
    env.insert("opt".to_string(), option_u64_ty());
    let result =
        lower_syn_expr(&expr, &env).expect("Option::Some(42u64) should lower as constructor");
    match result {
        TrustVcExpr::FnCall {
            ref name, ref args, ..
        } => {
            assert!(
                name.contains("Some"),
                "UF name should contain 'Some', got: {name}"
            );
            assert_eq!(args.len(), 1, "Some takes 1 argument");
        }
        other => panic!("expected FnCall for Option::Some(42u64), got: {:?}", other),
    }
}

#[test]
fn lower_enum_record_variant_struct_literal() {
    let expr: syn::Expr = syn::parse_str("EnumRecord::A { a: 12 }").unwrap();
    let enum_ty = TrustVcType::Datatype {
        name: "EnumRecord".to_string(),
        variants: vec![
            DatatypeVariant::new(
                "A",
                vec![("a".to_string(), TrustVcType::Uint { width: 64 })],
            ),
            DatatypeVariant::new(
                "B",
                vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
            ),
        ],
    };
    let mut env = TypeEnv::new();
    env.insert("e".to_string(), enum_ty.clone());

    let result = lower_syn_expr(&expr, &env).expect("record variant literal should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(name.contains("EnumRecord"), "got constructor UF {name}");
            assert!(name.contains("A"), "got constructor UF {name}");
            assert_eq!(
                args,
                vec![TrustVcExpr::IntLit {
                    value: 12,
                    ty: TrustVcType::Uint { width: 64 }
                }]
            );
            assert_eq!(return_ty, enum_ty);
        }
        other => panic!("expected enum record variant constructor call, got {other:?}"),
    }
}

#[test]
fn lower_explicit_option_some_constructor_without_env_metadata() {
    let expr: syn::Expr = syn::parse_str("Option::<i8>::Some(1)").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new())
        .expect("explicit Option::<T>::Some should lower without pre-registered metadata");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(return_ty, TrustVcType::from_str("Option<i8>").unwrap());
            assert_eq!(
                args,
                vec![TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Int { width: 8 }
                }]
            );
        }
        other => panic!("expected Some constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_explicit_option_none_constructor_without_env_metadata() {
    let expr: syn::Expr = syn::parse_str("Option::<u32>::None").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new())
        .expect("explicit Option::<T>::None should lower without pre-registered metadata");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(return_ty, TrustVcType::from_str("Option<u32>").unwrap());
            assert!(args.is_empty());
        }
        other => panic!("expected None constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_explicit_result_ok_constructor_without_env_metadata() {
    let expr: syn::Expr = syn::parse_str("Ok::<u32, u32>(42)").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new())
        .expect("explicit Ok::<T, E> should lower without pre-registered metadata");
    match result {
        TrustVcExpr::FnCall {
            args, return_ty, ..
        } => {
            assert_eq!(
                return_ty,
                TrustVcType::from_str("Result<u32, u32>").unwrap()
            );
            assert_eq!(
                args,
                vec![TrustVcExpr::IntLit {
                    value: 42,
                    ty: TrustVcType::Uint { width: 32 }
                }]
            );
        }
        other => panic!("expected Ok constructor FnCall, got {:?}", other),
    }
}

#[test]
fn lower_explicit_generic_enum_constructor_substitutes_payload_type() {
    let expr: syn::Expr = syn::parse_str("Choice::<u64>::First(11)").unwrap();
    let mut env = TypeEnv::new();
    env.insert("choice_template".to_string(), generic_choice_template_ty());

    let result =
        lower_syn_expr(&expr, &env).expect("explicit generic enum constructor should lower");
    let expected_ty = TrustVcType::Datatype {
        name: "Choice<u64>".to_string(),
        variants: vec![
            DatatypeVariant::new(
                "First",
                vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
            ),
            DatatypeVariant::new("Empty", vec![]),
        ],
    };
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert!(
                name.contains("Choice") && name.contains("First"),
                "constructor UF should mention concrete enum and variant, got {name}",
            );
            assert_eq!(return_ty, expected_ty);
            assert_eq!(
                args,
                vec![TrustVcExpr::IntLit {
                    value: 11,
                    ty: TrustVcType::Uint { width: 64 },
                }]
            );
        }
        other => panic!("expected generic enum constructor FnCall, got {:?}", other),
    }
}

#[test]
fn reject_non_nullary_constructor_without_call() {
    let expr: syn::Expr = syn::parse_str("Some").unwrap();
    let mut env = TypeEnv::new();
    env.insert("opt".to_string(), option_u64_ty());
    let err = lower_syn_expr(&expr, &env).expect_err("Some without args should be an error");
    let msg = err.to_string();
    assert!(
        msg.contains("expects 1 argument"),
        "error should mention expected argument count, got: {msg}"
    );
}

#[test]
fn variable_shadows_constructor() {
    let expr: syn::Expr = syn::parse_str("None").unwrap();
    let mut env = TypeEnv::new();
    env.insert("opt".to_string(), option_u64_ty());
    env.insert("None".to_string(), TrustVcType::Bool);
    let result = lower_syn_expr(&expr, &env).expect("None as variable should work");
    match result {
        TrustVcExpr::Var { ref name, ref ty } => {
            assert_eq!(name, "None");
            assert_eq!(ty, &TrustVcType::Bool);
        }
        other => panic!("expected Var for shadowed None, got: {:?}", other),
    }
}

#[test]
fn lower_struct_update_syntax_copies_omitted_fields_from_rest() {
    let expr: syn::Expr = syn::parse_str("Counter { max: 10, ..base }").unwrap();
    let mut env = TypeEnv::new();
    env.insert("base".to_string(), counter_ty());

    let result = lower_syn_expr(&expr, &env).expect("struct update syntax should lower");
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = result
    else {
        panic!("expected lowered struct update constructor call");
    };

    assert!(
        name.contains("Counter"),
        "constructor UF should mention Counter, got {name}"
    );
    assert_eq!(return_ty, counter_ty());
    assert_eq!(args.len(), 2);
    assert!(matches!(
        &args[0],
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty: TrustVcType::Uint { width: 32 },
        } if name.contains("count")
            && args == &vec![TrustVcExpr::Var {
                name: "base".to_string(),
                ty: counter_ty(),
            }]
    ));
    assert_eq!(
        args[1],
        TrustVcExpr::IntLit {
            value: 10,
            ty: TrustVcType::Uint { width: 32 },
        }
    );
}

#[test]
fn lower_struct_update_rejects_mismatched_rest_type() {
    let expr: syn::Expr = syn::parse_str("Counter { max: 10, ..other }").unwrap();
    let mut env = TypeEnv::new();
    env.insert("other".to_string(), outer_counter_ty());

    let err = lower_syn_expr(&expr, &env).expect_err("mismatched struct update rest must fail");
    let msg = err.to_string();
    assert!(
        msg.contains("struct update rest for 'Counter'"),
        "error should mention struct update rest type mismatch, got: {msg}",
    );
}
