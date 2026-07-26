// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{ArithOp, CompareOp, LogicOp, QuantifierKind, TrustVcExpr};
use crate::ir::TrustVcType;
use proptest::prelude::*;

const MAX_DEPTH: u32 = 3;
const FREE_INT_VARS: [&str; 3] = ["x", "y", "z"];
const FREE_BOOL_VARS: [&str; 3] = ["p", "q", "r"];

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn bool_ty() -> TrustVcType {
    TrustVcType::Bool
}

fn int_lit_expr(value: u8) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value: i128::from(value),
        ty: i32_ty(),
    }
}

fn int_var_expr(name: String) -> TrustVcExpr {
    TrustVcExpr::Var { name, ty: i32_ty() }
}

fn bool_var_expr(name: String) -> TrustVcExpr {
    TrustVcExpr::Var {
        name,
        ty: bool_ty(),
    }
}

fn arith_op_strategy() -> impl Strategy<Value = ArithOp> {
    prop_oneof![
        Just(ArithOp::Add),
        Just(ArithOp::Sub),
        Just(ArithOp::Mul),
        Just(ArithOp::Div),
        Just(ArithOp::Rem),
    ]
}

fn compare_op_strategy() -> impl Strategy<Value = CompareOp> {
    prop_oneof![
        Just(CompareOp::Eq),
        Just(CompareOp::Ne),
        Just(CompareOp::Lt),
        Just(CompareOp::Le),
        Just(CompareOp::Gt),
        Just(CompareOp::Ge),
    ]
}

fn logic_op_strategy() -> impl Strategy<Value = LogicOp> {
    prop_oneof![Just(LogicOp::And), Just(LogicOp::Or),]
}

fn quantifier_kind_strategy() -> impl Strategy<Value = QuantifierKind> {
    prop_oneof![Just(QuantifierKind::Forall), Just(QuantifierKind::Exists),]
}

fn int_leaf_strategy(int_vars: &[String]) -> BoxedStrategy<TrustVcExpr> {
    prop_oneof![
        (0u8..=7).prop_map(int_lit_expr),
        prop::sample::select(int_vars.to_vec()).prop_map(int_var_expr),
    ]
    .boxed()
}

fn bool_leaf_strategy(int_vars: &[String], bool_vars: &[String]) -> BoxedStrategy<TrustVcExpr> {
    prop_oneof![
        Just(TrustVcExpr::BoolLit(true)),
        Just(TrustVcExpr::BoolLit(false)),
        prop::sample::select(bool_vars.to_vec()).prop_map(bool_var_expr),
        (
            compare_op_strategy(),
            int_leaf_strategy(int_vars),
            int_leaf_strategy(int_vars),
        )
            .prop_map(|(op, left, right)| TrustVcExpr::Compare {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
    ]
    .boxed()
}

fn arb_int_expr_with_env(depth: u32, int_vars: Vec<String>) -> BoxedStrategy<TrustVcExpr> {
    if depth == 0 {
        return int_leaf_strategy(&int_vars);
    }

    prop_oneof![
        4 => int_leaf_strategy(&int_vars),
        3 => (
            arith_op_strategy(),
            arb_int_expr_with_env(depth - 1, int_vars.clone()),
            arb_int_expr_with_env(depth - 1, int_vars.clone()),
        )
            .prop_map(|(op, left, right)| TrustVcExpr::Arith {
                op,
                left: Box::new(left),
                right: Box::new(right),
                ty: i32_ty(),
            }),
        1 => arb_int_expr_with_env(depth - 1, int_vars)
            .prop_map(|expr| TrustVcExpr::Neg(Box::new(expr))),
    ]
    .boxed()
}

fn quantifier_expr_strategy(
    depth: u32,
    int_vars: Vec<String>,
    bool_vars: Vec<String>,
    allow_quantifiers: bool,
) -> BoxedStrategy<TrustVcExpr> {
    let single_bound = quantifier_kind_strategy().prop_flat_map({
        let int_vars = int_vars.clone();
        let bool_vars = bool_vars.clone();
        move |kind| {
            let bound_name = format!("i{depth}");
            let mut extended_int_vars = int_vars.clone();
            extended_int_vars.push(bound_name.clone());
            arb_bool_expr_with_env(
                depth - 1,
                extended_int_vars,
                bool_vars.clone(),
                allow_quantifiers,
            )
            .prop_map(move |body| TrustVcExpr::Quantifier {
                kind,
                bound_vars: vec![(bound_name.clone(), i32_ty())],
                body: Box::new(body),
                triggers: None,
                trigger_inference_mode: None,
            })
        }
    });

    let double_bound = quantifier_kind_strategy().prop_flat_map(move |kind| {
        let left_name = format!("i{depth}");
        let right_name = format!("j{depth}");
        let mut extended_int_vars = int_vars.clone();
        extended_int_vars.push(left_name.clone());
        extended_int_vars.push(right_name.clone());
        arb_bool_expr_with_env(
            depth - 1,
            extended_int_vars,
            bool_vars.clone(),
            allow_quantifiers,
        )
        .prop_map(move |body| TrustVcExpr::Quantifier {
            kind,
            bound_vars: vec![
                (left_name.clone(), i32_ty()),
                (right_name.clone(), i32_ty()),
            ],
            body: Box::new(body),
            triggers: None,
            trigger_inference_mode: None,
        })
    });

    prop_oneof![2 => single_bound, 1 => double_bound,].boxed()
}

fn arb_bool_expr_with_env(
    depth: u32,
    int_vars: Vec<String>,
    bool_vars: Vec<String>,
    allow_quantifiers: bool,
) -> BoxedStrategy<TrustVcExpr> {
    if depth == 0 {
        return bool_leaf_strategy(&int_vars, &bool_vars);
    }

    let compare = (
        compare_op_strategy(),
        arb_int_expr_with_env(depth - 1, int_vars.clone()),
        arb_int_expr_with_env(depth - 1, int_vars.clone()),
    )
        .prop_map(|(op, left, right)| TrustVcExpr::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        });

    let logic = (
        logic_op_strategy(),
        arb_bool_expr_with_env(
            depth - 1,
            int_vars.clone(),
            bool_vars.clone(),
            allow_quantifiers,
        ),
        arb_bool_expr_with_env(
            depth - 1,
            int_vars.clone(),
            bool_vars.clone(),
            allow_quantifiers,
        ),
    )
        .prop_map(|(op, left, right)| TrustVcExpr::Logic {
            op,
            left: Box::new(left),
            right: Box::new(right),
        });

    let not = arb_bool_expr_with_env(
        depth - 1,
        int_vars.clone(),
        bool_vars.clone(),
        allow_quantifiers,
    )
    .prop_map(|expr| TrustVcExpr::Not(Box::new(expr)));

    if allow_quantifiers {
        prop_oneof![
            4 => bool_leaf_strategy(&int_vars, &bool_vars),
            3 => compare,
            2 => logic,
            1 => not,
            1 => quantifier_expr_strategy(depth, int_vars, bool_vars, allow_quantifiers),
        ]
        .boxed()
    } else {
        prop_oneof![
            4 => bool_leaf_strategy(&int_vars, &bool_vars),
            3 => compare,
            2 => logic,
            1 => not,
        ]
        .boxed()
    }
}

pub(crate) fn arb_int_expr() -> BoxedStrategy<TrustVcExpr> {
    arb_int_expr_with_env(
        MAX_DEPTH,
        FREE_INT_VARS.iter().map(ToString::to_string).collect(),
    )
}

pub(crate) fn arb_bool_expr() -> BoxedStrategy<TrustVcExpr> {
    arb_bool_expr_with_env(
        MAX_DEPTH,
        FREE_INT_VARS.iter().map(ToString::to_string).collect(),
        FREE_BOOL_VARS.iter().map(ToString::to_string).collect(),
        true,
    )
}

pub(crate) fn arb_bool_expr_no_quantifiers() -> BoxedStrategy<TrustVcExpr> {
    arb_bool_expr_with_env(
        MAX_DEPTH,
        FREE_INT_VARS.iter().map(ToString::to_string).collect(),
        FREE_BOOL_VARS.iter().map(ToString::to_string).collect(),
        false,
    )
}

pub(crate) fn arb_non_quantified_expr() -> BoxedStrategy<TrustVcExpr> {
    prop_oneof![arb_int_expr(), arb_bool_expr_no_quantifiers(),].boxed()
}

pub(crate) fn arb_quantifier_expr() -> BoxedStrategy<TrustVcExpr> {
    quantifier_expr_strategy(
        MAX_DEPTH,
        FREE_INT_VARS.iter().map(ToString::to_string).collect(),
        FREE_BOOL_VARS.iter().map(ToString::to_string).collect(),
        false,
    )
}

pub(crate) fn arb_expr() -> BoxedStrategy<TrustVcExpr> {
    prop_oneof![arb_int_expr(), arb_bool_expr(),].boxed()
}

impl Arbitrary for TrustVcExpr {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        arb_expr()
    }
}
