// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;

pub(super) fn u32_ty() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

pub(super) fn bool_ty() -> TrustVcType {
    TrustVcType::Bool
}

pub(super) fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: u32_ty(),
    }
}

pub(super) fn fn_call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: u32_ty(),
    }
}

pub(super) fn fn_call_bool(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: bool_ty(),
    }
}

pub(super) fn int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: u32_ty(),
    }
}

pub(super) fn compare_gt(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Gt,
        left: Box::new(left),
        right: Box::new(right),
    }
}

pub(super) fn compare_eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

pub(super) fn arith_add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: crate::ir::ArithOp::Add,
        left: Box::new(left),
        right: Box::new(right),
        ty: u32_ty(),
    }
}

pub(super) fn logic_and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: crate::ir::LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

pub(super) fn index_expr(receiver: TrustVcExpr, index: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(index),
        receiver_name: None,
        elem_ty: u32_ty(),
    }
}

pub(super) fn bound_vars(names: &[&str]) -> Vec<(String, TrustVcType)> {
    names.iter().map(|n| (n.to_string(), u32_ty())).collect()
}

pub(super) fn let_expr(name: &str, value: TrustVcExpr, body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Let {
        name: name.to_string(),
        ty: u32_ty(),
        value: Box::new(value),
        body: Box::new(body),
    }
}

pub(super) fn choose_expr(var_name: &str, condition: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Choose {
        var_name: var_name.to_string(),
        var_ty: u32_ty(),
        condition: Box::new(condition),
        key: "test_choose".to_string(),
        also_assert: None,
    }
}

pub(super) fn spec_closure(params: &[&str], body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::SpecClosure {
        params: params.iter().map(|n| (n.to_string(), u32_ty())).collect(),
        body: Box::new(body),
        ty: u32_ty(),
    }
}

pub(super) fn quantifier_expr(bvars: &[&str], body: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Quantifier {
        kind: crate::ir::QuantifierKind::Forall,
        bound_vars: bvars.iter().map(|n| (n.to_string(), u32_ty())).collect(),
        body: Box::new(body),
        triggers: None,
        trigger_inference_mode: None,
    }
}
