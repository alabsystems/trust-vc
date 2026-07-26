//! Type-environment tests for prepared_context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::ir::{DatatypeVariant, TraitBound, TraitDecl, TraitMethodDecl, TrustVcType};
use crate::ir_expr::{MatchPattern, TrustVcExpr};
use crate::vc::ProofObligation;

fn contains_fn_call(expr: &TrustVcExpr, needle: &str) -> bool {
    expr_contains(
        expr,
        &|node| matches!(node, TrustVcExpr::FnCall { name, .. } if name == needle),
    )
}

fn contains_var(expr: &TrustVcExpr, needle: &str) -> bool {
    expr_contains(
        expr,
        &|node| matches!(node, TrustVcExpr::Var { name, .. } if name == needle),
    )
}

fn contains_int_lit(expr: &TrustVcExpr, expected: i128) -> bool {
    expr_contains(
        expr,
        &|node| matches!(node, TrustVcExpr::IntLit { value, .. } if *value == expected),
    )
}

fn expr_contains(expr: &TrustVcExpr, predicate: &impl Fn(&TrustVcExpr) -> bool) -> bool {
    if predicate(expr) {
        return true;
    }

    match expr {
        TrustVcExpr::UnitLit
        | TrustVcExpr::BoolLit(_)
        | TrustVcExpr::StringLit(_)
        | TrustVcExpr::IntLit { .. }
        | TrustVcExpr::Var { .. }
        | TrustVcExpr::IntConst { .. }
        | TrustVcExpr::ReadPlace { .. }
        | TrustVcExpr::PlaceDisjoint { .. }
        | TrustVcExpr::ProphecyNew { .. } => false,
        TrustVcExpr::Compare { left, right, .. } | TrustVcExpr::Logic { left, right, .. } => {
            expr_contains(left, predicate) || expr_contains(right, predicate)
        }
        TrustVcExpr::Not(inner)
        | TrustVcExpr::Neg(inner)
        | TrustVcExpr::Cast { expr: inner, .. }
        | TrustVcExpr::SpecClosure { body: inner, .. }
        | TrustVcExpr::Choose {
            condition: inner, ..
        }
        | TrustVcExpr::ProphecyResolve { value: inner, .. } => expr_contains(inner, predicate),
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => expr_contains(premise, predicate) || expr_contains(conclusion, predicate),
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_contains(cond, predicate)
                || expr_contains(then_branch, predicate)
                || expr_contains(else_branch, predicate)
        }
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::SpecialArith { left, right, .. }
        | TrustVcExpr::WrappingArith { left, right, .. } => {
            expr_contains(left, predicate) || expr_contains(right, predicate)
        }
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => {
            expr_contains(scrutinee, predicate)
                || arms.iter().any(|arm| {
                    pattern_contains(&arm.pattern, predicate) || expr_contains(&arm.body, predicate)
                })
        }
        TrustVcExpr::Let { value, body, .. } => {
            expr_contains(value, predicate) || expr_contains(body, predicate)
        }
        TrustVcExpr::CollectionOp { receiver, args, .. } => {
            expr_contains(receiver, predicate)
                || args.iter().any(|arg| expr_contains(arg, predicate))
        }
        TrustVcExpr::Index {
            receiver, index, ..
        } => expr_contains(receiver, predicate) || expr_contains(index, predicate),
        TrustVcExpr::Quantifier { body, triggers, .. } => {
            expr_contains(body, predicate)
                || triggers.as_ref().is_some_and(|groups| {
                    groups
                        .iter()
                        .flat_map(|group| group.iter())
                        .any(|trigger| expr_contains(trigger, predicate))
                })
        }
        TrustVcExpr::FnCall { args, .. } => args.iter().any(|arg| expr_contains(arg, predicate)),
    }
}

fn pattern_contains(pattern: &MatchPattern, predicate: &impl Fn(&TrustVcExpr) -> bool) -> bool {
    match pattern {
        MatchPattern::Lit(expr) => expr_contains(expr, predicate),
        MatchPattern::Or(patterns) => patterns
            .iter()
            .any(|pattern| pattern_contains(pattern, predicate)),
        MatchPattern::Ident(_)
        | MatchPattern::Constructor { .. }
        | MatchPattern::Struct { .. }
        | MatchPattern::Wildcard => false,
    }
}

#[test]
fn test_build_type_env_registers_datatype_metadata_from_context() {
    let counter_ty = TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![DatatypeVariant::new(
            "Counter",
            vec![
                ("count".to_string(), TrustVcType::Uint { width: 32 }),
                ("max".to_string(), TrustVcType::Uint { width: 32 }),
            ],
        )],
    };
    let wrapped_ty = TrustVcType::Datatype {
        name: "WrappedCounter".to_string(),
        variants: vec![DatatypeVariant::new(
            "WrappedCounter",
            vec![("inner".to_string(), counter_ty.clone())],
        )],
    };

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counter", counter_ty.clone());
    ctx.declare_helper_function_typed("wrap", wrapped_ty.clone(), vec![]);

    let env = build_type_env(&ctx).expect("type env should build");

    let count_meta = env
        .lookup_field("Counter", "count")
        .expect("context datatypes should register field metadata");
    assert_eq!(count_meta.uf_name, "Counter_Counter_count");
    assert_eq!(count_meta.field_type, TrustVcType::Uint { width: 32 });

    let wrapped_ctor = env
        .lookup_constructor("WrappedCounter")
        .expect("helper-return datatypes should register constructor metadata");
    assert_eq!(wrapped_ctor.uf_name, "WrappedCounter_WrappedCounter");
    assert_eq!(
        wrapped_ctor.fields,
        vec![("inner".to_string(), counter_ty.clone())]
    );

    let nested_meta = env
        .lookup_field("Counter", "max")
        .expect("nested datatype metadata should be registered recursively");
    assert_eq!(nested_meta.uf_name, "Counter_Counter_max");
}

#[test]
fn test_prepare_context_lowers_registered_field_access() {
    let counter_ty = TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![DatatypeVariant::new(
            "Counter",
            vec![
                ("count".to_string(), TrustVcType::Uint { width: 32 }),
                ("max".to_string(), TrustVcType::Uint { width: 32 }),
            ],
        )],
    };
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counter", counter_ty.clone());
    ctx.push_obligation(ProofObligation::assert(
        "field_access",
        "counter.count > 0u32",
    ));

    let prepared =
        prepare_context(&ctx).expect("field access should lower through prepare_context");
    let expr = &prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "field_access")
        .expect("added assertion should be preserved")
        .expr;
    match expr {
        crate::ir_expr::TrustVcExpr::Compare { left, .. } => match left.as_ref() {
            crate::ir_expr::TrustVcExpr::FnCall {
                name,
                return_ty,
                args,
            } => {
                assert_eq!(name, "Counter_Counter_count");
                assert_eq!(*return_ty, TrustVcType::Uint { width: 32 });
                assert_eq!(
                    args,
                    &vec![crate::ir_expr::TrustVcExpr::Var {
                        name: "counter".to_string(),
                        ty: counter_ty,
                    }]
                );
            }
            other => panic!("expected selector FnCall on left side, got {:?}", other),
        },
        other => panic!("expected comparison expression, got {:?}", other),
    }
}

#[test]
fn test_prepare_context_lowers_prophecy_view_with_registered_binding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", TrustVcType::Uint { width: 64 });
    ctx.declare_var_typed("v", TrustVcType::Uint { width: 64 });
    ctx.register_prophecy_binding("p", TrustVcType::Uint { width: 64 });
    ctx.push_obligation(ProofObligation::assume("prophecy_view", "v == p.view()"));

    let prepared = prepare_context(&ctx)
        .expect("registered prophecy locals should lower through prepare_context");
    let expr = &prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "prophecy_view")
        .expect("added assumption should be preserved")
        .expr;
    match expr {
        crate::ir_expr::TrustVcExpr::Compare { left, right, .. } => {
            assert!(
                matches!(
                    left.as_ref(),
                    crate::ir_expr::TrustVcExpr::Var { name, ty }
                        if name == "v" && *ty == TrustVcType::Uint { width: 64 }
                ),
                "left-hand side should stay as the local variable: {expr:?}"
            );
            assert!(
                matches!(
                    right.as_ref(),
                    crate::ir_expr::TrustVcExpr::ProphecyNew { name, ty }
                        if name == "p" && *ty == TrustVcType::Uint { width: 64 }
                ),
                "right-hand side should lower to a prophecy term: {expr:?}"
            );
        }
        other => panic!("expected comparison expression, got {:?}", other),
    }
}

#[test]
fn test_prepare_context_lowers_struct_literal_to_constructor_call() {
    let counter_ty = TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![DatatypeVariant::new(
            "Counter",
            vec![
                ("count".to_string(), TrustVcType::Uint { width: 32 }),
                ("max".to_string(), TrustVcType::Uint { width: 32 }),
            ],
        )],
    };
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counter", counter_ty);
    ctx.push_obligation(ProofObligation::assert(
        "struct_literal",
        "counter.count == Counter { count: 0u32, max: 10u32 }.count",
    ));

    let prepared =
        prepare_context(&ctx).expect("struct literal should lower through prepare_context");
    let expr = &prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "struct_literal")
        .expect("added assertion should be preserved")
        .expr;
    match expr {
        crate::ir_expr::TrustVcExpr::Compare { right, .. } => match right.as_ref() {
            crate::ir_expr::TrustVcExpr::FnCall {
                name,
                return_ty,
                args,
            } => {
                assert_eq!(
                    name, "Counter_Counter_count",
                    "outer .count selector should be a FnCall"
                );
                assert_eq!(*return_ty, TrustVcType::Uint { width: 32 });
                assert_eq!(
                    args.len(),
                    1,
                    "selector takes one argument (the constructor call)"
                );
                match &args[0] {
                    crate::ir_expr::TrustVcExpr::FnCall { name, args, .. } => {
                        assert_eq!(name, "Counter_Counter", "inner should be constructor UF");
                        assert_eq!(args.len(), 2, "constructor takes two fields");
                    }
                    other => panic!("expected constructor FnCall, got {:?}", other),
                }
            }
            other => panic!("expected selector FnCall on right side, got {:?}", other),
        },
        other => panic!("expected comparison expression, got {:?}", other),
    }
}

#[test]
fn test_prepare_context_lowers_trait_bound_method_call() {
    let mut ctx = VerificationContext::new();
    let type_param = TrustVcType::TypeParam("T".to_string());
    ctx.declare_var_typed("counter", type_param.clone());
    ctx.function_context = Some(FunctionContext {
        name: "lemma".to_string(),
        params: vec![("counter".to_string(), type_param.clone())],
        return_type: TrustVcType::Bool,
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![TraitBound {
            type_param: "T".to_string(),
            trait_name: "CounterSpec".to_string(),
        }],
    });
    ctx.register_trait_decl(TraitDecl {
        name: "CounterSpec".to_string(),
        methods: vec![TraitMethodDecl {
            name: "grant".to_string(),
            params: vec![("token".to_string(), TrustVcType::Bool)],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.push_obligation(ProofObligation::assert(
        "trait_method",
        "counter.grant(true)",
    ));

    let prepared = prepare_context(&ctx)
        .expect("trait-bound method call should lower through prepare_context");
    let expr = &prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "trait_method")
        .expect("added assertion should be preserved")
        .expr;
    match expr {
        crate::ir_expr::TrustVcExpr::FnCall {
            name,
            return_ty,
            args,
        } => {
            assert_eq!(name, "CounterSpec__grant");
            assert_eq!(*return_ty, TrustVcType::Bool);
            assert_eq!(
                args,
                &vec![
                    crate::ir_expr::TrustVcExpr::Var {
                        name: "counter".to_string(),
                        ty: type_param,
                    },
                    crate::ir_expr::TrustVcExpr::BoolLit(true),
                ]
            );
        }
        other => panic!("expected method FnCall, got {:?}", other),
    }
}

#[test]
fn test_prepare_context_lowers_helper_trait_bound_body_axiom() {
    let mut ctx = VerificationContext::new();
    let type_param = TrustVcType::TypeParam("T".to_string());
    ctx.declare_var_typed("x", type_param.clone());
    ctx.declare_var_typed("flag", TrustVcType::Bool);
    ctx.function_context = Some(FunctionContext {
        name: "wrapper".to_string(),
        params: vec![("flag".to_string(), TrustVcType::Bool)],
        return_type: TrustVcType::Bool,
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.declare_helper_function_typed_with_bounds(
        "generic_get",
        TrustVcType::Bool,
        vec![("x".to_string(), type_param.clone())],
        vec![TraitBound {
            type_param: "T".to_string(),
            trait_name: "Valued".to_string(),
        }],
    );
    ctx.register_trait_decl(TraitDecl {
        name: "Valued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.push_obligation(
        crate::vc::ProofObligation::broadcast_assume(
            "__body_axiom_generic_get",
            "generic_get(x) == x.get_value()",
        )
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["generic_get(x)".to_string()]]),
    );

    let prepared = prepare_context(&ctx)
        .expect("helper trait-bound body axiom should lower through prepare_context");
    let expr = &prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "__body_axiom_generic_get")
        .expect("helper body axiom should be preserved")
        .expr;
    match expr {
        crate::ir_expr::TrustVcExpr::Compare { left, right, .. } => {
            match left.as_ref() {
                crate::ir_expr::TrustVcExpr::FnCall { name, args, .. } => {
                    assert_eq!(name, "generic_get");
                    assert_eq!(args.len(), 1);
                }
                other => panic!("expected helper call on left side, got {:?}", other),
            }
            match right.as_ref() {
                crate::ir_expr::TrustVcExpr::FnCall {
                    name,
                    return_ty,
                    args,
                } => {
                    assert_eq!(name, "Valued__get_value");
                    assert_eq!(*return_ty, TrustVcType::Bool);
                    assert_eq!(
                        args,
                        &vec![crate::ir_expr::TrustVcExpr::Var {
                            name: "x".to_string(),
                            ty: type_param,
                        }]
                    );
                }
                other => panic!("expected trait UF call on right side, got {:?}", other),
            }
        }
        other => panic!("expected helper body axiom equality, got {:?}", other),
    }
}

#[test]
fn test_typeenv_variable_function_name_collision() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("foo", TrustVcType::Uint { width: 32 });
    ctx.declare_helper_function_typed("foo", TrustVcType::Bool, vec![]);
    ctx.push_obligation(ProofObligation::assert("check", "foo > 0"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    match &prepared.obligations[0].expr {
        TrustVcExpr::Compare { left, .. } => match left.as_ref() {
            TrustVcExpr::Var { name, ty } => {
                assert_eq!(name, "foo");
                assert_eq!(
                    *ty,
                    TrustVcType::Uint { width: 32 },
                    "variable 'foo' must resolve as Uint{{32}}, not Bool from helper function"
                );
            }
            other => panic!("expected Var for 'foo', got {:?}", other),
        },
        other => panic!("expected Compare, got {:?}", other),
    }
}

#[test]
fn test_typeenv_function_call_resolves_from_fn_namespace() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f", TrustVcType::Uint { width: 64 });
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed("f", TrustVcType::Int { width: 32 }, vec![]);
    ctx.push_obligation(ProofObligation::assert("check", "f(x) > 0"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    match &prepared.obligations[0].expr {
        TrustVcExpr::Compare { left, .. } => match left.as_ref() {
            TrustVcExpr::FnCall {
                name, return_ty, ..
            } => {
                assert_eq!(name, "f");
                assert_eq!(
                    *return_ty,
                    TrustVcType::Int { width: 32 },
                    "function call 'f(x)' should use fn return type Int{{32}}, not var type Uint{{64}}"
                );
            }
            other => panic!("expected FnCall for 'f(x)', got {:?}", other),
        },
        other => panic!("expected Compare, got {:?}", other),
    }
}

// --- Datatype constructor string-lowering regression (#2487) ---

#[test]
fn test_prepare_context_lowers_option_none_constructor() {
    let option_u64 = TrustVcType::Datatype {
        name: "Option<u64>".to_string(),
        variants: vec![
            DatatypeVariant::new("None", vec![]),
            DatatypeVariant::new(
                "Some",
                vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
            ),
        ],
    };

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", option_u64.clone());
    ctx.push_obligation(ProofObligation::assert("none_eq", "opt == None"));

    let prepared =
        prepare_context(&ctx).expect("prepare_context should succeed with None constructor");
    assert_eq!(prepared.obligations.len(), 1);
    let expr = &prepared.obligations[0].expr;
    assert!(
        contains_fn_call(expr, "Option_u64_None")
            && contains_fn_call(expr, "is-Option_u64_None")
            && contains_fn_call(expr, "is-Option_u64_Some")
            && contains_var(expr, "opt"),
        "Option None equality should compare opt with structural Option equality, got: {expr:?}"
    );
}

#[test]
fn test_prepare_context_lowers_option_some_constructor() {
    let option_u64 = TrustVcType::Datatype {
        name: "Option<u64>".to_string(),
        variants: vec![
            DatatypeVariant::new("None", vec![]),
            DatatypeVariant::new(
                "Some",
                vec![("0".to_string(), TrustVcType::Uint { width: 64 })],
            ),
        ],
    };

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", option_u64.clone());
    ctx.push_obligation(ProofObligation::assert("some_eq", "opt == Some(42u64)"));

    let prepared =
        prepare_context(&ctx).expect("prepare_context should succeed with Some constructor");
    assert_eq!(prepared.obligations.len(), 1);
    let expr = &prepared.obligations[0].expr;
    assert!(
        contains_fn_call(expr, "Option_u64_Some")
            && contains_fn_call(expr, "is-Option_u64_None")
            && contains_fn_call(expr, "is-Option_u64_Some")
            && contains_fn_call(expr, "Option_u64_Some_0")
            && contains_var(expr, "opt")
            && contains_int_lit(expr, 42),
        "Option Some equality should compare opt and payload 42 with structural Option equality, got: {expr:?}"
    );
}
