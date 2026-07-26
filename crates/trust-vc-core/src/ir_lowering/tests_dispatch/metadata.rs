// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TypeEnv metadata and field-access lowering tests.

use crate::ir::TrustVcType;
use crate::ir_expr::*;
use crate::ir_lowering::*;

use super::support::{counter_ty, outer_counter_ty};

#[test]
fn type_env_auto_registers_recursive_datatype_metadata() {
    let mut env = TypeEnv::new();
    env.insert("outer".to_string(), outer_counter_ty());

    let outer_inner = env
        .lookup_field("OuterCounter", "inner")
        .expect("outer datatype should register selector metadata");
    assert_eq!(outer_inner.uf_name, "OuterCounter_OuterCounter_inner");
    assert_eq!(outer_inner.field_type, counter_ty());

    let nested_count = env
        .lookup_field("Counter", "count")
        .expect("nested datatype fields should be registered recursively");
    assert_eq!(nested_count.uf_name, "Counter_Counter_count");
    assert_eq!(nested_count.field_type, TrustVcType::Uint { width: 32 });

    let ctor = env
        .lookup_constructor("Counter")
        .expect("single-variant datatype should register constructor metadata");
    assert_eq!(ctor.uf_name, "Counter_Counter");
    assert_eq!(
        ctor.fields,
        vec![
            ("count".to_string(), TrustVcType::Uint { width: 32 }),
            ("max".to_string(), TrustVcType::Uint { width: 32 }),
        ]
    );
}

#[test]
fn type_env_extend_preserves_manual_method_metadata() {
    let mut env = TypeEnv::new();
    env.insert("counter".to_string(), counter_ty());
    env.insert_method_metadata(
        "Counter".to_string(),
        "bump".to_string(),
        MethodMeta {
            uf_name: "Counter__bump".to_string(),
            return_type: counter_ty(),
            param_types: vec![TrustVcType::Uint { width: 32 }],
            box_receiver: None,
        },
    );

    let child = env.extend(&[("fresh".to_string(), outer_counter_ty())]);

    let meta = child
        .lookup_method("Counter", "bump")
        .expect("extend() should preserve method metadata");
    assert_eq!(meta.uf_name, "Counter__bump");
    assert_eq!(meta.return_type, counter_ty());
    assert_eq!(meta.param_types, vec![TrustVcType::Uint { width: 32 }]);
    assert!(
        child.lookup_field("OuterCounter", "inner").is_some(),
        "extend() should register metadata for newly bound datatype variables"
    );
}

#[test]
fn type_env_manual_field_and_constructor_registration_round_trips() {
    let mut env = TypeEnv::new();
    env.insert_field_metadata(
        "ManualCounter".to_string(),
        "count".to_string(),
        "ManualCounter_ManualCounter_count".to_string(),
        TrustVcType::Uint { width: 16 },
    );
    env.insert_constructor_metadata(
        "ManualCounter".to_string(),
        ConstructorMeta {
            uf_name: "ManualCounter_ManualCounter".to_string(),
            fields: vec![("count".to_string(), TrustVcType::Uint { width: 16 })],
        },
    );

    let field = env
        .lookup_field("ManualCounter", "count")
        .expect("manual field registration should be visible");
    assert_eq!(field.uf_name, "ManualCounter_ManualCounter_count");
    assert_eq!(field.field_type, TrustVcType::Uint { width: 16 });

    let constructor = env
        .lookup_constructor("ManualCounter")
        .expect("manual constructor registration should be visible");
    assert_eq!(constructor.uf_name, "ManualCounter_ManualCounter");
    assert_eq!(
        constructor.fields,
        vec![("count".to_string(), TrustVcType::Uint { width: 16 })]
    );
}

#[test]
fn lower_registered_field_access_to_selector_call() {
    let expr: syn::Expr = syn::parse_str("counter.count").unwrap();
    let mut env = TypeEnv::new();
    env.insert("counter".to_string(), counter_ty());

    let lowered = lower_syn_expr(&expr, &env).expect("registered field access should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "Counter_Counter_count");
            assert_eq!(return_ty, TrustVcType::Uint { width: 32 });
            assert_eq!(
                args,
                vec![TrustVcExpr::Var {
                    name: "counter".to_string(),
                    ty: counter_ty(),
                }]
            );
        }
        other => panic!("expected selector FnCall, got {:?}", other),
    }
}

#[test]
fn lower_nested_registered_field_access_recurses() {
    let expr: syn::Expr = syn::parse_str("outer.inner.count").unwrap();
    let mut env = TypeEnv::new();
    env.insert("outer".to_string(), outer_counter_ty());

    let lowered = lower_syn_expr(&expr, &env).expect("nested field access should lower");
    match lowered {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, "Counter_Counter_count");
            assert_eq!(return_ty, TrustVcType::Uint { width: 32 });
            assert_eq!(args.len(), 1);
            match &args[0] {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } => {
                    assert_eq!(name, "OuterCounter_OuterCounter_inner");
                    assert_eq!(*return_ty, counter_ty());
                    assert_eq!(
                        args,
                        &vec![TrustVcExpr::Var {
                            name: "outer".to_string(),
                            ty: outer_counter_ty(),
                        }]
                    );
                }
                other => panic!("expected nested selector FnCall, got {:?}", other),
            }
        }
        other => panic!("expected selector FnCall, got {:?}", other),
    }
}

#[test]
fn lower_unknown_field_access_reports_field_and_type() {
    let expr: syn::Expr = syn::parse_str("counter.missing").unwrap();
    let mut env = TypeEnv::new();
    env.insert("counter".to_string(), counter_ty());

    let err = lower_syn_expr(&expr, &env).expect_err("unknown field must fail closed");
    assert!(matches!(err, LoweringError::UnsupportedExpr(_)));
    let msg = err.to_string();
    assert!(
        msg.contains("field 'missing' on type 'Counter'"),
        "error should include missing field + receiver type, got: {msg}",
    );
}
