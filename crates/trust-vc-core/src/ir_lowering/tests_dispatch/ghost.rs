// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ghost wrapper view lowering tests.

use crate::encoder::datatype::selector_symbol_name;
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::ir_expr::{MatchPattern, TrustVcExpr};
use crate::ir_lowering::*;
use crate::vc::{TypedProofObligation, VerificationContext};

use super::support::option_u64_ty;

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
fn lower_ghost_option_view_erases_to_receiver() {
    let expr: syn::Expr = syn::parse_str("t.view()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("t".to_string(), option_u64_ty());
    env.insert_erased_ghost_var("t".to_string());

    let result = lower_syn_expr(&expr, &env).expect("Ghost<Option<T>>::view should lower");
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "t".to_string(),
            ty: option_u64_ty(),
        }
    );
}

#[test]
fn lower_ghost_option_view_projection_keeps_option_methods_available() {
    let expr: syn::Expr = syn::parse_str("t.view().is_some() || t.view().is_none()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("t".to_string(), option_u64_ty());
    env.insert_erased_ghost_var("t".to_string());

    let result = lower_syn_expr(&expr, &env).expect("view-projected Option methods should lower");
    assert_eq!(infer_expr_type(&result), TrustVcType::Bool);
}

#[test]
fn lower_generic_ghost_option_view_unwrap_projects_payload_selector() {
    let expr: syn::Expr = syn::parse_str("t.view().unwrap()").unwrap();
    let option_t_ty = TrustVcType::from_str("Option<T>").unwrap();
    let mut env = TypeEnv::new();
    env.insert("t".to_string(), option_t_ty.clone());
    env.insert_erased_ghost_var("t".to_string());

    let result =
        lower_syn_expr(&expr, &env).expect("Ghost<Option<T>> payload projection should lower");
    match result {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            assert_eq!(name, selector_symbol_name("Option<T>", "Some", "0", 0));
            assert_eq!(
                args,
                vec![TrustVcExpr::Var {
                    name: "t".to_string(),
                    ty: option_t_ty,
                }]
            );
            assert_eq!(return_ty, TrustVcType::TypeParam("T".to_string()));
        }
        other => panic!("expected Some.0 selector projection, got {other:?}"),
    }
}

#[test]
fn lower_erased_ghost_option_unwrap_without_view_still_fails_closed() {
    let expr: syn::Expr = syn::parse_str("t.unwrap()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("t".to_string(), option_u64_ty());
    env.insert_erased_ghost_var("t".to_string());

    let err = lower_syn_expr(&expr, &env).expect_err("projection requires the Ghost view surface");
    assert!(
        err.to_string()
            .contains("requires a receiver known to be Some"),
        "error should preserve ordinary Option::unwrap behavior, got {err}"
    );
}

#[test]
fn encode_generic_ghost_option_view_unwrap_projection_reflexive() {
    let expr: syn::Expr = syn::parse_str("t.view().unwrap() == t.view().unwrap()").unwrap();
    let option_t_ty = TrustVcType::from_str("Option<T>").unwrap();
    let mut env = TypeEnv::new();
    env.insert("t".to_string(), option_t_ty.clone());
    env.insert_erased_ghost_var("t".to_string());

    let lowered =
        lower_syn_expr(&expr, &env).expect("generic Ghost<Option<T>> projection should lower");
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t", option_t_ty);
    ctx.mark_erased_ghost_var("t");
    ctx.push_typed_obligation(TypedProofObligation::assert(
        "generic_ghost_option_projection_reflexive",
        lowered,
    ));

    let result = AYEncoder::verify(&ctx);
    assert!(
        result.is_verified(),
        "generic Ghost<Option<T>> selector equality should encode and verify, got {result:?}"
    );
}

#[test]
fn lower_ghost_option_view_equality_uses_erased_option_value() {
    let expr: syn::Expr = syn::parse_str("t.view() == t.view()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("t".to_string(), option_u64_ty());
    env.insert_erased_ghost_var("t".to_string());

    let result = lower_syn_expr(&expr, &env).expect("view equality should lower");
    assert_eq!(infer_expr_type(&result), TrustVcType::Bool);
    assert!(
        contains_fn_call(&result, "is-Option_u64_None")
            && contains_fn_call(&result, "is-Option_u64_Some")
            && contains_fn_call(&result, "Option_u64_Some_0")
            && contains_var(&result, "t"),
        "erased Option equality should compare the ghost variable with structural Option equality, got {result:?}"
    );
}

#[test]
fn lower_non_option_view_still_fails_closed() {
    let expr: syn::Expr = syn::parse_str("x.view()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("x".to_string(), TrustVcType::Uint { width: 64 });

    let err = lower_syn_expr(&expr, &env).expect_err("non-Option view should fail closed");
    assert!(
        err.to_string().contains("view"),
        "error should mention rejected view() call, got {err}"
    );
}

#[test]
fn lower_plain_option_view_fails_closed() {
    let expr: syn::Expr = syn::parse_str("opt.view()").unwrap();
    let mut env = TypeEnv::new();
    env.insert("opt".to_string(), option_u64_ty());

    let err = lower_syn_expr(&expr, &env).expect_err("plain Option::view should not erase");
    assert!(
        err.to_string().contains("view"),
        "error should mention rejected view() call, got {err}"
    );
}
