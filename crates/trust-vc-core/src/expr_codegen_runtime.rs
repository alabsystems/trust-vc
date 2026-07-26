// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::ir::TrustVcType;
use crate::ir_builder;
use crate::ir_expr::{ArithOp, TrustVcExpr};
use crate::ir_lowering::{type_from_int_suffix, TypeEnv};

pub(crate) fn lower_expr_codegen_runtime(expr: &syn::Expr, env: &TypeEnv) -> Option<TrustVcExpr> {
    match expr {
        syn::Expr::Lit(lit) => lower_lit(lit),
        syn::Expr::Path(path) => lower_path(path, env),
        syn::Expr::Binary(bin) => lower_binary(bin, env),
        syn::Expr::Unary(unary) => lower_unary(unary, env),
        syn::Expr::Paren(paren) => lower_expr_codegen_runtime(&paren.expr, env),
        syn::Expr::Group(group) => lower_expr_codegen_runtime(&group.expr, env),
        syn::Expr::Call(call) => lower_call(call, env),
        syn::Expr::Tuple(tuple) if tuple.elems.is_empty() => Some(ir_builder::unit_lit()),
        _ => None,
    }
}

fn lower_lit(lit: &syn::ExprLit) -> Option<TrustVcExpr> {
    match &lit.lit {
        syn::Lit::Bool(value) => Some(ir_builder::bool_lit(value.value())),
        syn::Lit::Int(value) => {
            let parsed = value.base10_parse::<i128>().ok()?;
            let ty = if value.suffix().is_empty() {
                TrustVcType::Int { width: 32 }
            } else {
                type_from_int_suffix(value.suffix()).ok()?
            };
            Some(ir_builder::int_lit(parsed, ty))
        }
        _ => None,
    }
}

fn lower_path(path: &syn::ExprPath, env: &TypeEnv) -> Option<TrustVcExpr> {
    if path.qself.is_some() {
        return None;
    }

    let segments = path.path.segments.iter().collect::<Vec<_>>();
    let [segment] = segments.as_slice() else {
        return None;
    };
    let name = segment.ident.to_string();
    match name.as_str() {
        "true" => Some(ir_builder::bool_lit(true)),
        "false" => Some(ir_builder::bool_lit(false)),
        _ => env
            .lookup(&name)
            .cloned()
            .map(|ty| ir_builder::var(&name, ty)),
    }
}

fn lower_binary(bin: &syn::ExprBinary, env: &TypeEnv) -> Option<TrustVcExpr> {
    let left = lower_expr_codegen_runtime(&bin.left, env)?;
    let right = lower_expr_codegen_runtime(&bin.right, env)?;
    match &bin.op {
        syn::BinOp::Eq(_) => Some(ir_builder::eq(left, right)),
        syn::BinOp::Ne(_) => Some(ir_builder::ne(left, right)),
        syn::BinOp::Lt(_) => Some(ir_builder::lt(left, right)),
        syn::BinOp::Le(_) => Some(ir_builder::le(left, right)),
        syn::BinOp::Gt(_) => Some(ir_builder::gt(left, right)),
        syn::BinOp::Ge(_) => Some(ir_builder::ge(left, right)),
        syn::BinOp::And(_) => Some(ir_builder::and(left, right)),
        syn::BinOp::Or(_) => Some(ir_builder::or(left, right)),
        syn::BinOp::Add(_) => Some(ir_builder::arith_inferred(ArithOp::Add, left, right)),
        syn::BinOp::Sub(_) => Some(ir_builder::arith_inferred(ArithOp::Sub, left, right)),
        syn::BinOp::Mul(_) => Some(ir_builder::arith_inferred(ArithOp::Mul, left, right)),
        syn::BinOp::Div(_) => Some(ir_builder::arith_inferred(ArithOp::Div, left, right)),
        syn::BinOp::Rem(_) => Some(ir_builder::arith_inferred(ArithOp::Rem, left, right)),
        _ => None,
    }
}

fn lower_unary(unary: &syn::ExprUnary, env: &TypeEnv) -> Option<TrustVcExpr> {
    let inner = lower_expr_codegen_runtime(&unary.expr, env)?;
    match unary.op {
        syn::UnOp::Not(_) => Some(ir_builder::not(inner)),
        syn::UnOp::Neg(_) => Some(ir_builder::neg(inner)),
        _ => None,
    }
}

fn lower_call(call: &syn::ExprCall, env: &TypeEnv) -> Option<TrustVcExpr> {
    let func = match &*call.func {
        syn::Expr::Path(path) if path.qself.is_none() => {
            path.path.segments.last()?.ident.to_string()
        }
        _ => return None,
    };
    if call.args.len() != 1 {
        return None;
    }

    let closure = match call.args.first()? {
        syn::Expr::Closure(closure) => closure,
        _ => return None,
    };

    let mut scoped_env = env.clone();
    let mut bound_vars = Vec::new();
    for input in &closure.inputs {
        let pat_type = match input {
            syn::Pat::Type(pat_type) => pat_type,
            _ => return None,
        };
        let name = match pat_type.pat.as_ref() {
            syn::Pat::Ident(ident) => ident.ident.to_string(),
            _ => return None,
        };
        let ty = lower_type(&pat_type.ty)?;
        scoped_env.insert(name.clone(), ty.clone());
        bound_vars.push((name, ty));
    }

    let body = lower_expr_codegen_runtime(&closure.body, &scoped_env)?;
    match func.as_str() {
        "forall" => Some(ir_builder::forall(bound_vars, body, None)),
        "exists" => Some(ir_builder::exists(bound_vars, body, None)),
        _ => None,
    }
}

fn lower_type(ty: &syn::Type) -> Option<TrustVcType> {
    if matches!(ty, syn::Type::Tuple(tuple) if tuple.elems.is_empty()) {
        return Some(TrustVcType::Unit);
    }

    let path = match ty {
        syn::Type::Path(path) if path.qself.is_none() => path,
        _ => return None,
    };
    let segments = path.path.segments.iter().collect::<Vec<_>>();
    let [segment] = segments.as_slice() else {
        return None;
    };
    match segment.ident.to_string().as_str() {
        "bool" => Some(TrustVcType::Bool),
        "i8" => Some(TrustVcType::Int { width: 8 }),
        "i16" => Some(TrustVcType::Int { width: 16 }),
        "i32" => Some(TrustVcType::Int { width: 32 }),
        "i64" => Some(TrustVcType::Int { width: 64 }),
        "i128" => Some(TrustVcType::Int { width: 128 }),
        "u8" => Some(TrustVcType::Uint { width: 8 }),
        "u16" => Some(TrustVcType::Uint { width: 16 }),
        "u32" => Some(TrustVcType::Uint { width: 32 }),
        "u64" => Some(TrustVcType::Uint { width: 64 }),
        "u128" => Some(TrustVcType::Uint { width: 128 }),
        _ => None,
    }
}
