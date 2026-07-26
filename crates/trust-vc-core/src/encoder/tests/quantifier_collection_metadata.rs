//! Direct regressions for quantifier-bound collection metadata.

use super::*;
use crate::encoder::types::sort_for_type;
use crate::ir::{CollectionOp, CompareOp, LogicOp, QuantifierKind, TrustVcExpr, TrustVcType};

fn u32_ty() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

fn i64_ty() -> TrustVcType {
    TrustVcType::Int { width: 64 }
}

fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

fn collection_len(receiver_name: &str, receiver_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(var(receiver_name, receiver_ty)),
        receiver_name: Some(receiver_name.to_string()),
        args: Vec::new(),
        ty: TrustVcType::Uint {
            width: crate::ir::pointer_width(),
        },
    }
}

fn contains_key(receiver_name: &str, receiver_ty: TrustVcType, key_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::CollectionOp {
        op: CollectionOp::ContainsKey,
        receiver: Box::new(var(receiver_name, receiver_ty)),
        receiver_name: Some(receiver_name.to_string()),
        args: vec![TrustVcExpr::IntLit {
            value: 1,
            ty: key_ty,
        }],
        ty: TrustVcType::Bool,
    }
}

fn fn_call(name: &str, arg_name: &str, arg_ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args: vec![var(arg_name, arg_ty)],
        return_ty: TrustVcType::Bool,
    }
}

fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn tautology(expr: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::Or,
        left: Box::new(expr.clone()),
        right: Box::new(TrustVcExpr::Not(Box::new(expr))),
    }
}

fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn forall(name: &str, ty: TrustVcType, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![(name.to_string(), ty)],
        body: Box::new(body),
        triggers: None,
        trigger_inference_mode: None,
    }
}

#[test]
fn test_quantifier_bound_seq_registers_length_metadata() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let seq_ty = TrustVcType::Seq(Box::new(i32_ty()));
    let body = eq(
        collection_len("s", seq_ty.clone()),
        collection_len("s", seq_ty.clone()),
    );
    let result = parser.encode_trust_vc_expr(&forall("s", seq_ty, body));

    assert!(
        result.is_ok(),
        "Seq bound variable length metadata should be registered before body encoding: {:?}",
        result.err()
    );
}

#[test]
fn test_quantifier_bound_set_helper_arg_sort_and_length_metadata() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let set_ty = TrustVcType::Set(Box::new(u32_ty()));
    let helper = solver
        .try_declare_fun("set_helper", &[sort_for_type(&set_ty)], Sort::Bool)
        .unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::from([("set_helper".to_string(), helper)]);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let helper_ok = tautology(fn_call("set_helper", "s", set_ty.clone()));
    let len_ok = eq(
        collection_len("s", set_ty.clone()),
        collection_len("s", set_ty.clone()),
    );
    let result = parser.encode_trust_vc_expr(&forall("s", set_ty, and(helper_ok, len_ok)));

    assert!(
        result.is_ok(),
        "Set bound variable should keep helper-compatible sort and registered length metadata: {:?}",
        result.err()
    );
}

#[test]
fn test_quantifier_bound_map_helper_arg_sort_and_domain_metadata() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let map_ty = TrustVcType::Map(Box::new(u32_ty()), Box::new(i64_ty()));
    let helper = solver
        .try_declare_fun("map_helper", &[sort_for_type(&map_ty)], Sort::Bool)
        .unwrap();
    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::from([("map_helper".to_string(), helper)]);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let helper_ok = tautology(fn_call("map_helper", "m", map_ty.clone()));
    let dom_ok = tautology(contains_key("m", map_ty.clone(), u32_ty()));
    let result = parser.encode_trust_vc_expr(&forall("m", map_ty, and(helper_ok, dom_ok)));

    assert!(
        result.is_ok(),
        "Map bound variable should keep helper-compatible sort and registered domain metadata: {:?}",
        result.err()
    );
}
