// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::error::TrustVcResult;
use crate::expr_codegen::runtime::lower_expr_codegen_runtime;
use crate::expr_codegen::{closure_to_quantifier_tokens, expr_to_builder_tokens};
use crate::ir::TrustVcType;
use crate::ir_expr::arbitrary::{
    arb_bool_expr_no_quantifiers, arb_int_expr, arb_non_quantified_expr, arb_quantifier_expr,
};
use crate::ir_expr::{ArithOp, CompareOp, LogicOp, QuantifierKind, TrustVcExpr};
use crate::ir_lowering::{lower_syn_expr, TypeEnv};
use crate::vc::VariableDecl;
use ay_dpll::api::Term;
use proptest::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

const MAX_SAFE_DEPTH: u32 = 3;

fn safe_int_expr_strategy(depth: u32) -> BoxedStrategy<TrustVcExpr> {
    let leaf = prop_oneof![
        (0u8..=7).prop_map(|value| TrustVcExpr::IntLit {
            value: i128::from(value),
            ty: i32_ty(),
        }),
        prop::sample::select(vec!["x".to_string(), "y".to_string(), "z".to_string()])
            .prop_map(|name| TrustVcExpr::Var { name, ty: i32_ty() },),
    ];
    if depth == 0 {
        return leaf.boxed();
    }
    prop_oneof![
        4 => leaf,
        3 => (
            prop_oneof![
                Just(ArithOp::Add),
                Just(ArithOp::Sub),
                Just(ArithOp::Mul),
            ],
            safe_int_expr_strategy(depth - 1),
            safe_int_expr_strategy(depth - 1),
        )
            .prop_map(|(op, left, right)| TrustVcExpr::Arith {
                op,
                left: Box::new(left),
                right: Box::new(right),
                ty: i32_ty(),
            }),
        1 => safe_int_expr_strategy(depth - 1).prop_map(|expr| TrustVcExpr::Neg(Box::new(expr))),
    ]
    .boxed()
}

fn safe_bool_expr_strategy(depth: u32) -> BoxedStrategy<TrustVcExpr> {
    let leaf = prop_oneof![
        Just(TrustVcExpr::BoolLit(true)),
        Just(TrustVcExpr::BoolLit(false)),
        prop::sample::select(vec!["p".to_string(), "q".to_string(), "r".to_string()]).prop_map(
            |name| TrustVcExpr::Var {
                name,
                ty: TrustVcType::Bool,
            },
        ),
        (
            prop_oneof![
                Just(CompareOp::Eq),
                Just(CompareOp::Ne),
                Just(CompareOp::Lt),
                Just(CompareOp::Le),
                Just(CompareOp::Gt),
                Just(CompareOp::Ge),
            ],
            safe_int_expr_strategy(0),
            safe_int_expr_strategy(0),
        )
            .prop_map(|(op, left, right)| TrustVcExpr::Compare {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
    ];
    if depth == 0 {
        return leaf.boxed();
    }
    prop_oneof![
        4 => leaf,
        3 => (
            prop_oneof![Just(LogicOp::And), Just(LogicOp::Or),],
            safe_bool_expr_strategy(depth - 1),
            safe_bool_expr_strategy(depth - 1),
        )
            .prop_map(|(op, left, right)| TrustVcExpr::Logic {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }),
        1 => safe_bool_expr_strategy(depth - 1).prop_map(|expr| TrustVcExpr::Not(Box::new(expr))),
    ]
    .boxed()
}

fn collect_free_vars(
    expr: &TrustVcExpr,
    bound: &mut BTreeSet<String>,
    free: &mut BTreeMap<String, TrustVcType>,
) {
    match expr {
        TrustVcExpr::BoolLit(_) | TrustVcExpr::IntLit { .. } => {}
        TrustVcExpr::Var { name, ty } => {
            if !bound.contains(name) {
                if let Some(previous) = free.insert(name.clone(), ty.clone()) {
                    assert_eq!(previous, *ty, "free variable '{name}' changed type");
                }
            }
        }
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. } => {
            collect_free_vars(left, bound, free);
            collect_free_vars(right, bound, free);
        }
        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => {
            collect_free_vars(inner, bound, free);
        }
        TrustVcExpr::Quantifier {
            bound_vars, body, ..
        } => {
            let names: Vec<String> = bound_vars.iter().map(|(name, _)| name.clone()).collect();
            for name in &names {
                bound.insert(name.clone());
            }
            collect_free_vars(body, bound, free);
            for name in names {
                bound.remove(&name);
            }
        }
        other => panic!("unexpected generator variant in property test: {other:?}"),
    }
}

fn free_var_types(exprs: &[&TrustVcExpr]) -> BTreeMap<String, TrustVcType> {
    let mut free = BTreeMap::new();
    let mut bound = BTreeSet::new();
    for expr in exprs {
        collect_free_vars(expr, &mut bound, &mut free);
    }
    free
}

fn type_env_for_expr(expr: &TrustVcExpr) -> TypeEnv {
    let mut env = TypeEnv::new();
    for (name, ty) in free_var_types(&[expr]) {
        env.insert(name, ty);
    }
    env
}

fn encoder_for_exprs(exprs: &[&TrustVcExpr]) -> AYEncoder {
    let mut encoder = AYEncoder::new();
    for (name, ty) in free_var_types(exprs) {
        encoder
            .declare_variable(&VariableDecl {
                bounded_len: false,
                name,
                ty,
            })
            .expect("generated free variable declarations should succeed");
    }
    encoder
}

fn encode_expr(expr: &TrustVcExpr) -> TrustVcResult<Term> {
    let mut encoder = encoder_for_exprs(&[expr]);
    encoder.resolve_condition_typed(expr)
}

fn encode_fingerprint(expr: &TrustVcExpr) -> String {
    match encode_expr(expr) {
        Ok(term) => format!("ok:{term:?}"),
        Err(err) => format!("err:{err:?}"),
    }
}

fn terms_are_equivalent(left: &TrustVcExpr, right: &TrustVcExpr) -> TrustVcResult<bool> {
    let mut encoder = encoder_for_exprs(&[left, right]);
    let left_term = encoder.resolve_condition_typed(left)?;
    let right_term = encoder.resolve_condition_typed(right)?;
    let eq = encoder.solver.try_eq(left_term, right_term).unwrap();
    let neq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(neq).unwrap();
    Ok(encoder.solver.try_check_sat().unwrap().is_unsat())
}

fn expr_to_source(expr: &TrustVcExpr) -> String {
    match expr {
        TrustVcExpr::BoolLit(value) => value.to_string(),
        // A bare `Int { width: 32 }` literal is the unsuffixed placeholder; a
        // source `5i32` is the `i32` literal, pinned by an identity cast
        // (`ir_lowering::atoms::typed_int_literal`).
        TrustVcExpr::IntLit { value, ty } => match ty {
            TrustVcType::Int { width: 32 } => format!("{value}"),
            other => panic!("unexpected literal type in property source printer: {other:?}"),
        },
        TrustVcExpr::Var { name, .. } => name.clone(),
        TrustVcExpr::Arith {
            op, left, right, ..
        } => {
            format!(
                "({} {} {})",
                expr_to_source(left),
                op,
                expr_to_source(right)
            )
        }
        TrustVcExpr::Neg(inner) => format!("-({})", expr_to_source(inner)),
        TrustVcExpr::Compare { op, left, right } => {
            format!(
                "({} {} {})",
                expr_to_source(left),
                op,
                expr_to_source(right)
            )
        }
        TrustVcExpr::Logic { op, left, right } => {
            format!(
                "({} {} {})",
                expr_to_source(left),
                op,
                expr_to_source(right)
            )
        }
        TrustVcExpr::Not(inner) => format!("!({})", expr_to_source(inner)),
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            ..
        } => {
            let func = match kind {
                QuantifierKind::Forall => "forall",
                QuantifierKind::Exists => "exists",
            };
            let vars = bound_vars
                .iter()
                .map(|(name, ty)| format!("{name}: {}", type_to_source(ty)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{func}(|{vars}| {})", expr_to_source(body))
        }
        other => panic!("unexpected generator variant in source printer: {other:?}"),
    }
}

fn type_to_source(ty: &TrustVcType) -> &'static str {
    match ty {
        TrustVcType::Bool => "bool",
        TrustVcType::Int { width: 32 } => "i32",
        TrustVcType::Uint { width: 32 } => "u32",
        other => panic!("unexpected quantifier type in source printer: {other:?}"),
    }
}

fn extract_quantifier_codegen_input(expr: &syn::Expr) -> Option<(&'static str, &syn::ExprClosure)> {
    let call = match expr {
        syn::Expr::Call(call) => call,
        _ => return None,
    };
    if call.args.len() != 1 {
        return None;
    }
    let closure = match call.args.first()? {
        syn::Expr::Closure(closure) => closure,
        _ => return None,
    };
    let func = match call.func.as_ref() {
        syn::Expr::Path(path) if path.qself.is_none() => {
            path.path.segments.last()?.ident.to_string()
        }
        _ => return None,
    };
    let kind = match func.as_str() {
        "forall" => "Forall",
        "exists" => "Exists",
        _ => return None,
    };
    Some((kind, closure))
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_resolve_condition_typed_never_panics(expr in any::<TrustVcExpr>()) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| encode_expr(&expr)));
        prop_assert!(result.is_ok(), "resolve_condition_typed panicked for {expr:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_encoding_is_deterministic(expr in any::<TrustVcExpr>()) {
        prop_assert_eq!(
            encode_fingerprint(&expr),
            encode_fingerprint(&expr),
            "typed encoding should be deterministic for {:?}",
            expr,
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_eq_symmetry_produces_equivalent_terms(
        left in safe_int_expr_strategy(MAX_SAFE_DEPTH),
        right in safe_int_expr_strategy(MAX_SAFE_DEPTH),
    ) {
        let forward = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        };
        let reverse = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(right),
            right: Box::new(left),
        };
        let equivalent = terms_are_equivalent(&forward, &reverse)
            .expect("symmetric equality expressions should encode");
        prop_assert!(equivalent, "equality symmetry terms should be equivalent");
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_logic_and_symmetry_produces_equivalent_terms(
        left in safe_bool_expr_strategy(MAX_SAFE_DEPTH),
        right in safe_bool_expr_strategy(MAX_SAFE_DEPTH),
    ) {
        let forward = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        };
        let reverse = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(right),
            right: Box::new(left),
        };
        let equivalent = terms_are_equivalent(&forward, &reverse)
            .expect("symmetric conjunction expressions should encode");
        prop_assert!(equivalent, "conjunction symmetry terms should be equivalent");
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_logic_or_symmetry_produces_equivalent_terms(
        left in safe_bool_expr_strategy(MAX_SAFE_DEPTH),
        right in safe_bool_expr_strategy(MAX_SAFE_DEPTH),
    ) {
        let forward = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        };
        let reverse = TrustVcExpr::Logic {
            op: LogicOp::Or,
            left: Box::new(right),
            right: Box::new(left),
        };
        let equivalent = terms_are_equivalent(&forward, &reverse)
            .expect("symmetric disjunction expressions should encode");
        prop_assert!(equivalent, "disjunction symmetry terms should be equivalent");
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_ir_lowering_matches_expr_codegen_for_non_quantified_exprs(
        expr in arb_non_quantified_expr(),
    ) {
        let source = expr_to_source(&expr);
        let parsed: syn::Expr = syn::parse_str(&source).expect("generated source should parse");
        let env = type_env_for_expr(&expr);

        prop_assert!(
            expr_to_builder_tokens(&parsed).is_some(),
            "expr_codegen should support generated source: {source}",
        );

        let lowered = lower_syn_expr(&parsed, &env).expect("ir_lowering should succeed");
        let codegen = lower_expr_codegen_runtime(&parsed, &env)
            .expect("runtime expr_codegen mirror should succeed");

        prop_assert_eq!(&lowered, &expr, "ir_lowering should reconstruct generated expr");
        prop_assert_eq!(&codegen, &expr, "expr_codegen mirror should reconstruct generated expr");
        prop_assert_eq!(&lowered, &codegen, "lowering paths should agree for {}", source);
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_ir_lowering_matches_expr_codegen_for_quantifiers(
        expr in arb_quantifier_expr(),
    ) {
        let source = expr_to_source(&expr);
        let parsed: syn::Expr = syn::parse_str(&source).expect("generated quantifier source should parse");
        let env = type_env_for_expr(&expr);

        let (kind, closure) = extract_quantifier_codegen_input(&parsed)
            .expect("generated quantifier source should have a closure");
        prop_assert!(
            closure_to_quantifier_tokens(closure, kind).is_some(),
            "closure_to_quantifier_tokens should support generated source: {source}",
        );

        let lowered = lower_syn_expr(&parsed, &env).expect("ir_lowering should succeed");
        let codegen = lower_expr_codegen_runtime(&parsed, &env)
            .expect("runtime expr_codegen mirror should succeed");

        prop_assert_eq!(&lowered, &expr, "ir_lowering should reconstruct generated quantifier");
        prop_assert_eq!(&codegen, &expr, "expr_codegen mirror should reconstruct generated quantifier");
        prop_assert_eq!(&lowered, &codegen, "lowering paths should agree for {}", source);
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 10_000, ..ProptestConfig::default() })]

    #[test]
    fn prop_arbitrary_subset_is_printable_and_parses(
        expr in prop_oneof![arb_int_expr(), arb_bool_expr_no_quantifiers(), arb_quantifier_expr(),],
    ) {
        let source = expr_to_source(&expr);
        let parsed: syn::Expr = syn::parse_str(&source).expect("generated source should parse");
        let env = type_env_for_expr(&expr);
        let lowered = lower_syn_expr(&parsed, &env).expect("generated source should lower");
        prop_assert_eq!(lowered, expr, "generated printable subset should round-trip through syn");
    }
}
