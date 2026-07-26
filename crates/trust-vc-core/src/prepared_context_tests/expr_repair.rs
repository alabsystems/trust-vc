//! Expression-repair tests for prepared_context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, QuantifierKind, TrustVcExpr};
use crate::ir_lowering::TypeEnv;

#[test]
fn test_fix_fn_call_return_types_corrects_wrong_type() {
    let mut env = TypeEnv::new();
    env.insert_fn("helper".to_string(), TrustVcType::Uint { width: 32 });

    let expr = TrustVcExpr::FnCall {
        name: "helper".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }],
        return_ty: TrustVcType::Bool,
    };

    let fixed = fix_fn_call_return_types(expr, &env);
    match fixed {
        TrustVcExpr::FnCall { return_ty, .. } => {
            assert_eq!(
                return_ty,
                TrustVcType::Uint { width: 32 },
                "return_ty must be corrected from Bool to Uint{{32}}"
            );
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

#[test]
fn test_fix_fn_call_return_types_preserves_unknown_functions() {
    let env = TypeEnv::new();

    let expr = TrustVcExpr::FnCall {
        name: "unknown_fn".to_string(),
        args: vec![],
        return_ty: TrustVcType::Int { width: 32 },
    };

    let fixed = fix_fn_call_return_types(expr, &env);
    match fixed {
        TrustVcExpr::FnCall { return_ty, .. } => {
            assert_eq!(
                return_ty,
                TrustVcType::Int { width: 32 },
                "return_ty must be preserved when function is not in TypeEnv"
            );
        }
        other => panic!("expected FnCall, got {:?}", other),
    }
}

#[test]
fn test_fix_fn_call_return_types_recurses_through_compare() {
    let mut env = TypeEnv::new();
    env.insert_fn("square".to_string(), TrustVcType::Int { width: 32 });

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(TrustVcExpr::FnCall {
            name: "square".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty: TrustVcType::Bool,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let fixed = fix_fn_call_return_types(expr, &env);
    match fixed {
        TrustVcExpr::Compare { left, .. } => match *left {
            TrustVcExpr::FnCall { return_ty, .. } => {
                assert_eq!(
                    return_ty,
                    TrustVcType::Int { width: 32 },
                    "nested FnCall return_ty must be corrected"
                );
            }
            other => panic!("expected FnCall in left, got {:?}", other),
        },
        other => panic!("expected Compare, got {:?}", other),
    }
}

#[test]
fn test_fix_fn_call_return_types_recurses_through_arith() {
    let mut env = TypeEnv::new();
    env.insert_fn("len".to_string(), TrustVcType::Uint { width: 64 });

    let expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(TrustVcExpr::FnCall {
            name: "len".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "s".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty: TrustVcType::Bool,
        }),
        right: Box::new(TrustVcExpr::FnCall {
            name: "len".to_string(),
            args: vec![TrustVcExpr::Var {
                name: "t".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }],
            return_ty: TrustVcType::Bool,
        }),
        ty: TrustVcType::Int { width: 32 },
    };

    let fixed = fix_fn_call_return_types(expr, &env);
    match fixed {
        TrustVcExpr::Arith { left, right, .. } => {
            match *left {
                TrustVcExpr::FnCall { return_ty, .. } => {
                    assert_eq!(return_ty, TrustVcType::Uint { width: 64 });
                }
                other => panic!("expected FnCall in left, got {:?}", other),
            }
            match *right {
                TrustVcExpr::FnCall { return_ty, .. } => {
                    assert_eq!(return_ty, TrustVcType::Uint { width: 64 });
                }
                other => panic!("expected FnCall in right, got {:?}", other),
            }
        }
        other => panic!("expected Arith, got {:?}", other),
    }
}

#[test]
fn test_fix_fn_call_return_types_leaves_non_fncall_unchanged() {
    let env = TypeEnv::new();

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let original = expr.clone();
    let fixed = fix_fn_call_return_types(expr, &env);
    assert_eq!(fixed, original, "non-FnCall expression must be unchanged");
}

#[test]
fn test_fix_fn_call_return_types_nested_fn_call_chain() {
    let mut env = TypeEnv::new();
    env.insert_fn("outer".to_string(), TrustVcType::Int { width: 32 });
    env.insert_fn("inner".to_string(), TrustVcType::Uint { width: 64 });

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(TrustVcExpr::FnCall {
            name: "outer".to_string(),
            args: vec![TrustVcExpr::FnCall {
                name: "inner".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "x".to_string(),
                    ty: TrustVcType::Int { width: 32 },
                }],
                return_ty: TrustVcType::Bool,
            }],
            return_ty: TrustVcType::Bool,
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let fixed = fix_fn_call_return_types(expr, &env);
    match &fixed {
        TrustVcExpr::Compare { left, .. } => match left.as_ref() {
            TrustVcExpr::FnCall {
                name,
                return_ty,
                args,
                ..
            } => {
                assert_eq!(name, "outer");
                assert_eq!(
                    *return_ty,
                    TrustVcType::Int { width: 32 },
                    "outer FnCall return_ty must be corrected"
                );
                match &args[0] {
                    TrustVcExpr::FnCall {
                        name, return_ty, ..
                    } => {
                        assert_eq!(name, "inner");
                        assert_eq!(
                            *return_ty,
                            TrustVcType::Uint { width: 64 },
                            "inner FnCall return_ty must be corrected"
                        );
                    }
                    other => panic!("expected inner FnCall, got {:?}", other),
                }
            }
            other => panic!("expected outer FnCall, got {:?}", other),
        },
        other => panic!("expected Compare, got {:?}", other),
    }
}

#[test]
fn test_fix_fn_call_return_types_quantifier_trigger_bodies() {
    let mut env = TypeEnv::new();
    env.insert_fn("f".to_string(), TrustVcType::Int { width: 32 });

    let f_call = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }],
        return_ty: TrustVcType::Bool,
    };

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(f_call.clone()),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        triggers: Some(vec![vec![f_call]]),
        trigger_inference_mode: None,
    };

    let fixed = fix_fn_call_return_types(expr, &env);
    match &fixed {
        TrustVcExpr::Quantifier { body, triggers, .. } => {
            match body.as_ref() {
                TrustVcExpr::Compare { left, .. } => match left.as_ref() {
                    TrustVcExpr::FnCall { return_ty, .. } => {
                        assert_eq!(
                            *return_ty,
                            TrustVcType::Int { width: 32 },
                            "body FnCall return_ty must be corrected"
                        );
                    }
                    other => panic!("expected FnCall in body, got {:?}", other),
                },
                other => panic!("expected Compare in body, got {:?}", other),
            }

            let trigger_groups = triggers.as_ref().expect("triggers must be present");
            assert_eq!(trigger_groups.len(), 1);
            assert_eq!(trigger_groups[0].len(), 1);
            match &trigger_groups[0][0] {
                TrustVcExpr::FnCall { return_ty, .. } => {
                    assert_eq!(
                        *return_ty,
                        TrustVcType::Int { width: 32 },
                        "trigger FnCall return_ty must be corrected"
                    );
                }
                other => panic!("expected FnCall in trigger, got {:?}", other),
            }
        }
        other => panic!("expected Quantifier, got {:?}", other),
    }
}
