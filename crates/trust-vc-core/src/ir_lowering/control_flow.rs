//! Control-flow and block-expression lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::env::{OptionBindingMeta, OptionBindingState, ResultBindingMeta, ResultBindingState};
use super::{
    infer_expr_type, lower_syn_expr_with_depth, next_lowering_depth,
    operators::coerce_unsuffixed_literal, LoweringError, TypeEnv, COLLECTION_CONSTRUCTOR_PREFIX,
};
use crate::encoder::datatype::variant_symbol_name;
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CollectionOp, SpecialArithOp, TrustVcExpr};

pub(super) fn lower_if(
    if_expr: &syn::ExprIf,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    // Desugar `if let PAT = E { T } else { F }` to `match E { PAT => T, _ => F }`
    // so the expression-value if-let inherits the proven-sound match encoder
    // (nested-ITE with a wildcard-seeded default) — the `_ => F` arm ensures the
    // not-matched continuation is fully lowered, so the match is NEVER assumed to
    // succeed. Fire ONLY when the condition, after stripping Paren/Group, is
    // DIRECTLY `syn::Expr::Let`: a let-chain (`if let P = a && b`) wraps the
    // `Expr::Let` in an `Expr::Binary`, whose inner `Expr::Let` still reaches the
    // fail-closed backstop; `while let` / `let ... else` are separate syn nodes
    // and are untouched. Unsupported PAT shapes fail closed via `lower_pattern`.
    if let Some(expr_let) = if_cond_as_direct_let(&if_expr.cond) {
        return desugar_if_let(if_expr, expr_let, env, depth);
    }
    let cond = Box::new(lower_syn_expr_with_depth(&if_expr.cond, env, depth)?);
    let then_raw = lower_block_expr(&if_expr.then_branch, env, depth)?;
    let else_raw = match &if_expr.else_branch {
        Some((_, expr)) => lower_syn_expr_with_depth(expr, env, depth)?,
        None => return Err(LoweringError::MissingElseBranch),
    };
    // Cross-coerce unsuffixed literals between branches so that
    // `if c { 0 } else { x }` where `x: u8` coerces the `0` to Uint{8}
    // instead of leaving it at default Int{32}. Part of #1560.
    let then_ty = infer_expr_type(&then_raw);
    let else_ty = infer_expr_type(&else_raw);
    let then_branch = Box::new(coerce_unsuffixed_literal(then_raw, &else_ty));
    let else_branch = Box::new(coerce_unsuffixed_literal(else_raw, &then_ty));
    let ty = infer_expr_type(&then_branch);
    Ok(TrustVcExpr::Ite {
        cond,
        then_branch,
        else_branch,
        ty,
    })
}

/// The condition of an `if let`, only when it is DIRECTLY an `Expr::Let` (after
/// stripping parentheses/groups). Returns `None` for a let-chain (`Expr::Binary`
/// wrapping a let) so its inner `Expr::Let` still fails closed downstream.
fn if_cond_as_direct_let(cond: &syn::Expr) -> Option<&syn::ExprLet> {
    let mut current = cond;
    loop {
        match current {
            syn::Expr::Paren(paren) => current = &paren.expr,
            syn::Expr::Group(group) => current = &group.expr,
            syn::Expr::Let(expr_let) => return Some(expr_let),
            _ => return None,
        }
    }
}

/// Desugar `if let PAT = E { T } else { F }` to `match E { PAT => T, _ => F }`
/// and delegate to `lower_match`, which extends the arm environment with PAT's
/// bindings (so `T` resolves them) and emits the sound wildcard-seeded match. An
/// absent `else` becomes a unit `()` arm (the else-less statement form). A `guard`
/// is impossible on an `if let` condition, so none is synthesized.
fn desugar_if_let(
    if_expr: &syn::ExprIf,
    expr_let: &syn::ExprLet,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let then_body = syn::Expr::Block(syn::ExprBlock {
        attrs: Vec::new(),
        label: None,
        block: if_expr.then_branch.clone(),
    });
    let else_body = match &if_expr.else_branch {
        Some((_, expr)) => (**expr).clone(),
        None => syn::Expr::Tuple(syn::ExprTuple {
            attrs: Vec::new(),
            paren_token: Default::default(),
            elems: syn::punctuated::Punctuated::new(),
        }),
    };
    let arm_matched = syn::Arm {
        attrs: Vec::new(),
        pat: (*expr_let.pat).clone(),
        guard: None,
        fat_arrow_token: Default::default(),
        body: Box::new(then_body),
        comma: Some(Default::default()),
    };
    let arm_default = syn::Arm {
        attrs: Vec::new(),
        pat: syn::Pat::Wild(syn::PatWild {
            attrs: Vec::new(),
            underscore_token: Default::default(),
        }),
        guard: None,
        fat_arrow_token: Default::default(),
        body: Box::new(else_body),
        comma: Some(Default::default()),
    };
    let synth_match = syn::ExprMatch {
        attrs: Vec::new(),
        match_token: Default::default(),
        expr: expr_let.expr.clone(),
        brace_token: Default::default(),
        arms: vec![arm_matched, arm_default],
    };
    super::match_lowering::lower_match(&synth_match, env, depth)
}

pub(super) fn lower_block_expr(
    block: &syn::Block,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if block.stmts.is_empty() {
        return Ok(TrustVcExpr::UnitLit);
    }
    let mut local_env = env.clone();
    let mut stmts = block.stmts.iter().peekable();
    let mut result: Option<TrustVcExpr> = None;

    while let Some(stmt) = stmts.next() {
        let is_last = stmts.peek().is_none();
        match stmt {
            syn::Stmt::Local(local) => {
                let let_depth = next_lowering_depth(depth)?;
                let (name, ty) = extract_let_binding(local, &local_env, let_depth)?;
                let mut init_env = local_env.clone();
                init_env.register_type_metadata_only(&ty);
                let init = local
                    .init
                    .as_ref()
                    .ok_or_else(|| LoweringError::UnsupportedExpr("let without init".into()))?;
                let value = lower_let_initializer(
                    &init.expr,
                    &init_env,
                    let_depth,
                    let_binding_has_annotation(local).then_some(&ty),
                )?;
                let value = coerce_expr_to_type(value, &ty);
                let (value, is_prophecy) = bind_prophecy_local(value, &name);
                local_env.insert(name.clone(), ty.clone());
                if is_prophecy {
                    local_env.insert_prophecy_binding(name.clone(), ty.clone());
                }
                if let Some(option_meta) = option_binding_from_value(&value) {
                    local_env.insert_option_binding(name.clone(), option_meta);
                }
                if let Some(result_meta) = result_binding_from_value(&value) {
                    local_env.insert_result_binding(name.clone(), result_meta);
                }
                if is_last {
                    return Err(LoweringError::UnsupportedExpr(
                        "unit-valued block ending in let statement".into(),
                    ));
                }

                let remaining: Vec<_> = stmts.collect();
                let body = lower_stmts(&remaining, &local_env, let_depth)?;
                return Ok(TrustVcExpr::Let {
                    name,
                    ty,
                    value: Box::new(value),
                    body: Box::new(body),
                });
            }
            syn::Stmt::Expr(expr, semi) => {
                if let syn::Expr::Assign(assign) = expr {
                    let assign_depth = next_lowering_depth(depth)?;
                    let (name, ty, value) =
                        lower_assignment_statement(assign, &local_env, assign_depth)?;
                    local_env.insert(name.clone(), ty.clone());
                    if let Some(option_meta) = option_binding_from_value(&value) {
                        local_env.insert_option_binding(name.clone(), option_meta);
                    }
                    if let Some(result_meta) = result_binding_from_value(&value) {
                        local_env.insert_result_binding(name.clone(), result_meta);
                    }
                    let remaining: Vec<_> = stmts.collect();
                    let body = if is_last {
                        TrustVcExpr::UnitLit
                    } else {
                        lower_stmts(&remaining, &local_env, assign_depth)?
                    };
                    return Ok(TrustVcExpr::Let {
                        name,
                        ty,
                        value: Box::new(value),
                        body: Box::new(body),
                    });
                }
                if let syn::Expr::Binary(binary) = expr {
                    if is_compound_assignment_op(&binary.op) {
                        let assign_depth = next_lowering_depth(depth)?;
                        let (name, ty, value) =
                            lower_compound_assignment_statement(binary, &local_env, assign_depth)?;
                        local_env.insert(name.clone(), ty.clone());
                        let remaining: Vec<_> = stmts.collect();
                        let body = if is_last {
                            TrustVcExpr::UnitLit
                        } else {
                            lower_stmts(&remaining, &local_env, assign_depth)?
                        };
                        return Ok(TrustVcExpr::Let {
                            name,
                            ty,
                            value: Box::new(value),
                            body: Box::new(body),
                        });
                    }
                }
                let lowered = lower_syn_expr_with_depth(expr, &local_env, depth)?;
                if is_last {
                    if semi.is_some() {
                        result = Some(TrustVcExpr::UnitLit);
                    } else {
                        result = Some(lowered);
                    }
                }
            }
            syn::Stmt::Item(_) => {
                return Err(LoweringError::UnsupportedExpr("item in block".into()));
            }
            syn::Stmt::Macro(_) => {
                return Err(LoweringError::UnsupportedExpr("macro in block".into()));
            }
        }
    }

    result.ok_or(LoweringError::EmptyBlock)
}

fn lower_stmts(
    stmts: &[&syn::Stmt],
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    if stmts.is_empty() {
        return Ok(TrustVcExpr::UnitLit);
    }
    let mut local_env = env.clone();
    let mut iter = stmts.iter().peekable();

    while let Some(stmt) = iter.next() {
        let is_last = iter.peek().is_none();
        match stmt {
            syn::Stmt::Local(local) => {
                let let_depth = next_lowering_depth(depth)?;
                let (name, ty) = extract_let_binding(local, &local_env, let_depth)?;
                let mut init_env = local_env.clone();
                init_env.register_type_metadata_only(&ty);
                let init = local
                    .init
                    .as_ref()
                    .ok_or_else(|| LoweringError::UnsupportedExpr("let without init".into()))?;
                let value = lower_let_initializer(
                    &init.expr,
                    &init_env,
                    let_depth,
                    let_binding_has_annotation(local).then_some(&ty),
                )?;
                let value = coerce_expr_to_type(value, &ty);
                let (value, is_prophecy) = bind_prophecy_local(value, &name);
                local_env.insert(name.clone(), ty.clone());
                if is_prophecy {
                    local_env.insert_prophecy_binding(name.clone(), ty.clone());
                }
                if let Some(option_meta) = option_binding_from_value(&value) {
                    local_env.insert_option_binding(name.clone(), option_meta);
                }
                if let Some(result_meta) = result_binding_from_value(&value) {
                    local_env.insert_result_binding(name.clone(), result_meta);
                }
                if is_last {
                    return Err(LoweringError::UnsupportedExpr(
                        "unit-valued block ending in let statement".into(),
                    ));
                }

                let remaining: Vec<_> = iter.copied().collect();
                let body = lower_stmts(&remaining, &local_env, let_depth)?;
                return Ok(TrustVcExpr::Let {
                    name,
                    ty,
                    value: Box::new(value),
                    body: Box::new(body),
                });
            }
            syn::Stmt::Expr(expr, semi) => {
                if let syn::Expr::Assign(assign) = expr {
                    let assign_depth = next_lowering_depth(depth)?;
                    let (name, ty, value) =
                        lower_assignment_statement(assign, &local_env, assign_depth)?;
                    local_env.insert(name.clone(), ty.clone());
                    if let Some(option_meta) = option_binding_from_value(&value) {
                        local_env.insert_option_binding(name.clone(), option_meta);
                    }
                    if let Some(result_meta) = result_binding_from_value(&value) {
                        local_env.insert_result_binding(name.clone(), result_meta);
                    }
                    let remaining: Vec<_> = iter.copied().collect();
                    let body = if is_last {
                        TrustVcExpr::UnitLit
                    } else {
                        lower_stmts(&remaining, &local_env, assign_depth)?
                    };
                    return Ok(TrustVcExpr::Let {
                        name,
                        ty,
                        value: Box::new(value),
                        body: Box::new(body),
                    });
                }
                if let syn::Expr::Binary(binary) = expr {
                    if is_compound_assignment_op(&binary.op) {
                        let assign_depth = next_lowering_depth(depth)?;
                        let (name, ty, value) =
                            lower_compound_assignment_statement(binary, &local_env, assign_depth)?;
                        local_env.insert(name.clone(), ty.clone());
                        let remaining: Vec<_> = iter.copied().collect();
                        let body = if is_last {
                            TrustVcExpr::UnitLit
                        } else {
                            lower_stmts(&remaining, &local_env, assign_depth)?
                        };
                        return Ok(TrustVcExpr::Let {
                            name,
                            ty,
                            value: Box::new(value),
                            body: Box::new(body),
                        });
                    }
                }
                let lowered = lower_syn_expr_with_depth(expr, &local_env, depth)?;
                if is_last {
                    if semi.is_some() {
                        return Ok(TrustVcExpr::UnitLit);
                    }
                    return Ok(lowered);
                }
            }
            syn::Stmt::Item(_) => {
                return Err(LoweringError::UnsupportedExpr("item in block".into()));
            }
            syn::Stmt::Macro(_) => {
                return Err(LoweringError::UnsupportedExpr("macro in block".into()));
            }
        }
    }

    Err(LoweringError::EmptyBlock)
}

fn lower_assignment_statement(
    assign: &syn::ExprAssign,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType, TrustVcExpr), LoweringError> {
    let target = strip_assignment_target_wrappers(assign.left.as_ref());
    if let Some(name) = assignment_target_ident(target) {
        let ty = env.lookup(&name).cloned().ok_or_else(|| {
            LoweringError::TypeInference(format!(
                "assignment target '{}' has no known type in specification context",
                name
            ))
        })?;
        let value = lower_syn_expr_with_depth(&assign.right, env, depth)?;
        return Ok((name, ty.clone(), coerce_expr_to_type(value, &ty)));
    }

    if let syn::Expr::Index(index_target) = target {
        return lower_index_assignment_statement(index_target, &assign.right, env, depth);
    }

    Err(LoweringError::UnsupportedExpr(
        "assignment target other than a local variable or indexed collection element".into(),
    ))
}

fn lower_compound_assignment_statement(
    binary: &syn::ExprBinary,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType, TrustVcExpr), LoweringError> {
    let target = strip_assignment_target_wrappers(binary.left.as_ref());
    if let syn::Expr::Index(index_target) = target {
        return lower_index_compound_assignment_statement(
            index_target,
            &binary.op,
            &binary.right,
            env,
            depth,
        );
    }

    Err(LoweringError::UnsupportedBinOp(
        "compound assignment not supported in verification".into(),
    ))
}

fn assignment_target_ident(expr: &syn::Expr) -> Option<String> {
    let syn::Expr::Path(path) = strip_assignment_target_wrappers(expr) else {
        return None;
    };
    if path.qself.is_none() && path.path.segments.len() == 1 {
        path.path
            .segments
            .first()
            .map(|segment| segment.ident.to_string())
    } else {
        None
    }
}

fn strip_assignment_target_wrappers(mut expr: &syn::Expr) -> &syn::Expr {
    loop {
        match expr {
            syn::Expr::Paren(paren) => expr = &paren.expr,
            syn::Expr::Group(group) => expr = &group.expr,
            _ => return expr,
        }
    }
}

fn lower_index_assignment_statement(
    target: &syn::ExprIndex,
    value_expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType, TrustVcExpr), LoweringError> {
    if let Some((name, outer_index_expr, inner_index_expr)) = nested_index_target(target) {
        return lower_nested_index_assignment_statement(
            &name,
            outer_index_expr,
            inner_index_expr,
            value_expr,
            env,
            depth,
        );
    }
    let name = assignment_target_ident(strip_assignment_target_wrappers(&target.expr)).ok_or_else(
        || {
            LoweringError::UnsupportedExpr(
                "indexed assignment target must be a directly indexed local variable".into(),
            )
        },
    )?;
    let receiver_ty = env.lookup(&name).cloned().ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "indexed assignment target '{}' has no known type in specification context",
            name
        ))
    })?;
    let elem_ty = match &receiver_ty {
        TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => *elem.clone(),
        other => {
            return Err(LoweringError::TypeInference(format!(
                "indexed assignment requires Seq/array receiver, got '{}'",
                other.to_type_string()
            )));
        }
    };
    let index = lower_syn_expr_with_depth(&target.index, env, depth)?;
    let value = lower_syn_expr_with_depth(value_expr, env, depth)?;
    let value = coerce_expr_to_type(value, &elem_ty);
    let receiver = TrustVcExpr::Var {
        name: name.clone(),
        ty: receiver_ty.clone(),
    };
    Ok((
        name.clone(),
        receiver_ty.clone(),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Update,
            receiver: Box::new(receiver),
            receiver_name: Some(name),
            args: vec![index, value],
            ty: receiver_ty,
        },
    ))
}

fn lower_index_compound_assignment_statement(
    target: &syn::ExprIndex,
    op: &syn::BinOp,
    rhs_expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType, TrustVcExpr), LoweringError> {
    if let Some((name, outer_index_expr, inner_index_expr)) = nested_index_target(target) {
        return lower_nested_index_compound_assignment_statement(
            &name,
            outer_index_expr,
            inner_index_expr,
            op,
            rhs_expr,
            env,
            depth,
        );
    }
    let name = assignment_target_ident(strip_assignment_target_wrappers(&target.expr)).ok_or_else(
        || {
            LoweringError::UnsupportedExpr(
                "indexed compound assignment target must be a directly indexed local variable"
                    .into(),
            )
        },
    )?;
    let receiver_ty = env.lookup(&name).cloned().ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "indexed compound assignment target '{}' has no known type in specification context",
            name
        ))
    })?;
    let elem_ty = match &receiver_ty {
        TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => *elem.clone(),
        other => {
            return Err(LoweringError::TypeInference(format!(
                "indexed compound assignment requires Seq/array receiver, got '{}'",
                other.to_type_string()
            )));
        }
    };
    let index = lower_syn_expr_with_depth(&target.index, env, depth)?;
    let rhs = lower_syn_expr_with_depth(rhs_expr, env, depth)?;
    let rhs = coerce_expr_to_type(rhs, &elem_ty);
    let receiver = TrustVcExpr::Var {
        name: name.clone(),
        ty: receiver_ty.clone(),
    };
    let old_element = TrustVcExpr::Index {
        receiver: Box::new(receiver.clone()),
        index: Box::new(index.clone()),
        receiver_name: Some(name.clone()),
        elem_ty: elem_ty.clone(),
    };
    let value = lower_compound_assignment_value(op, old_element, rhs, &elem_ty)?;
    Ok((
        name.clone(),
        receiver_ty.clone(),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Update,
            receiver: Box::new(receiver),
            receiver_name: Some(name),
            args: vec![index, value],
            ty: receiver_ty,
        },
    ))
}

fn nested_index_target(target: &syn::ExprIndex) -> Option<(String, &syn::Expr, &syn::Expr)> {
    let syn::Expr::Index(inner) = strip_assignment_target_wrappers(&target.expr) else {
        return None;
    };
    let name = assignment_target_ident(strip_assignment_target_wrappers(&inner.expr))?;
    Some((name, &inner.index, &target.index))
}

fn collection_elem_ty(ty: &TrustVcType, context: &str) -> Result<TrustVcType, LoweringError> {
    match ty {
        TrustVcType::Seq(elem) | TrustVcType::Array(elem, _) => Ok(*elem.clone()),
        other => Err(LoweringError::TypeInference(format!(
            "{context} requires Seq/array receiver, got '{}'",
            other.to_type_string()
        ))),
    }
}

fn nested_index_receiver_expr(
    name: &str,
    receiver_ty: &TrustVcType,
    outer_index: TrustVcExpr,
    inner_ty: &TrustVcType,
) -> TrustVcExpr {
    TrustVcExpr::Index {
        receiver: Box::new(TrustVcExpr::Var {
            name: name.to_string(),
            ty: receiver_ty.clone(),
        }),
        index: Box::new(outer_index),
        receiver_name: Some(name.to_string()),
        elem_ty: inner_ty.clone(),
    }
}

fn nested_index_update_expr(
    name: &str,
    receiver_ty: TrustVcType,
    outer_index: TrustVcExpr,
    inner_index: TrustVcExpr,
    inner_value: TrustVcExpr,
) -> Result<TrustVcExpr, LoweringError> {
    let inner_ty = collection_elem_ty(&receiver_ty, "nested indexed assignment")?;
    let inner_receiver =
        nested_index_receiver_expr(name, &receiver_ty, outer_index.clone(), &inner_ty);
    let updated_inner = TrustVcExpr::CollectionOp {
        op: CollectionOp::Update,
        receiver: Box::new(inner_receiver),
        receiver_name: None,
        args: vec![inner_index, inner_value],
        ty: inner_ty,
    };
    Ok(TrustVcExpr::CollectionOp {
        op: CollectionOp::Update,
        receiver: Box::new(TrustVcExpr::Var {
            name: name.to_string(),
            ty: receiver_ty.clone(),
        }),
        receiver_name: Some(name.to_string()),
        args: vec![outer_index, updated_inner],
        ty: receiver_ty,
    })
}

fn lower_nested_index_assignment_statement(
    name: &str,
    outer_index_expr: &syn::Expr,
    inner_index_expr: &syn::Expr,
    value_expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType, TrustVcExpr), LoweringError> {
    let receiver_ty = env.lookup(name).cloned().ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "nested indexed assignment target '{}' has no known type in specification context",
            name
        ))
    })?;
    let inner_ty = collection_elem_ty(&receiver_ty, "nested indexed assignment")?;
    let elem_ty = collection_elem_ty(&inner_ty, "nested indexed assignment")?;
    let outer_index = lower_syn_expr_with_depth(outer_index_expr, env, depth)?;
    let inner_index = lower_syn_expr_with_depth(inner_index_expr, env, depth)?;
    let value = lower_syn_expr_with_depth(value_expr, env, depth)?;
    let value = coerce_expr_to_type(value, &elem_ty);
    let updated =
        nested_index_update_expr(name, receiver_ty.clone(), outer_index, inner_index, value)?;
    Ok((name.to_string(), receiver_ty, updated))
}

fn lower_nested_index_compound_assignment_statement(
    name: &str,
    outer_index_expr: &syn::Expr,
    inner_index_expr: &syn::Expr,
    op: &syn::BinOp,
    rhs_expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType, TrustVcExpr), LoweringError> {
    let receiver_ty = env.lookup(name).cloned().ok_or_else(|| {
        LoweringError::TypeInference(format!(
            "nested indexed compound assignment target '{}' has no known type in specification context",
            name
        ))
    })?;
    let inner_ty = collection_elem_ty(&receiver_ty, "nested indexed compound assignment")?;
    let elem_ty = collection_elem_ty(&inner_ty, "nested indexed compound assignment")?;
    let outer_index = lower_syn_expr_with_depth(outer_index_expr, env, depth)?;
    let inner_index = lower_syn_expr_with_depth(inner_index_expr, env, depth)?;
    let rhs = lower_syn_expr_with_depth(rhs_expr, env, depth)?;
    let rhs = coerce_expr_to_type(rhs, &elem_ty);
    let inner_receiver =
        nested_index_receiver_expr(name, &receiver_ty, outer_index.clone(), &inner_ty);
    let old_element = TrustVcExpr::Index {
        receiver: Box::new(inner_receiver),
        index: Box::new(inner_index.clone()),
        receiver_name: None,
        elem_ty: elem_ty.clone(),
    };
    let value = lower_compound_assignment_value(op, old_element, rhs, &elem_ty)?;
    let updated =
        nested_index_update_expr(name, receiver_ty.clone(), outer_index, inner_index, value)?;
    Ok((name.to_string(), receiver_ty, updated))
}

fn lower_compound_assignment_value(
    op: &syn::BinOp,
    left: TrustVcExpr,
    right: TrustVcExpr,
    elem_ty: &TrustVcType,
) -> Result<TrustVcExpr, LoweringError> {
    let left = Box::new(coerce_expr_to_type(left, elem_ty));
    let right = Box::new(coerce_expr_to_type(right, elem_ty));
    match op {
        syn::BinOp::AddAssign(_) => Ok(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::SubAssign(_) => Ok(TrustVcExpr::Arith {
            op: ArithOp::Sub,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::MulAssign(_) => Ok(TrustVcExpr::Arith {
            op: ArithOp::Mul,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::DivAssign(_) => Ok(TrustVcExpr::Arith {
            op: ArithOp::Div,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::RemAssign(_) => Ok(TrustVcExpr::Arith {
            op: ArithOp::Rem,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::BitAndAssign(_) => Ok(TrustVcExpr::SpecialArith {
            op: SpecialArithOp::BitAnd,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::BitOrAssign(_) => Ok(TrustVcExpr::SpecialArith {
            op: SpecialArithOp::BitOr,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::BitXorAssign(_) => Ok(TrustVcExpr::SpecialArith {
            op: SpecialArithOp::BitXor,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::ShlAssign(_) => Ok(TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        syn::BinOp::ShrAssign(_) => Ok(TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shr,
            left,
            right,
            ty: elem_ty.clone(),
        }),
        _ => Err(LoweringError::UnsupportedBinOp(
            "unknown compound assignment operator".into(),
        )),
    }
}

fn is_compound_assignment_op(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

fn bind_prophecy_local(value: TrustVcExpr, name: &str) -> (TrustVcExpr, bool) {
    match value {
        TrustVcExpr::ProphecyNew {
            name: prophecy_name,
            ty,
        } if prophecy_name == "__trust_vc_prophecy_unbound__" => (
            TrustVcExpr::ProphecyNew {
                name: name.to_string(),
                ty,
            },
            true,
        ),
        other => (other, false),
    }
}

fn lower_let_initializer(
    expr: &syn::Expr,
    env: &TypeEnv,
    depth: usize,
    target_ty: Option<&TrustVcType>,
) -> Result<TrustVcExpr, LoweringError> {
    if let Some(target_ty) = target_ty {
        if let Some(constructor) = lower_targeted_empty_std_collection_initializer(expr, target_ty)
        {
            return Ok(constructor);
        }
        if let Some(constructor) = lower_targeted_none_initializer(expr, target_ty)? {
            return Ok(constructor);
        }
    }
    lower_syn_expr_with_depth(expr, env, depth)
}

fn lower_targeted_empty_std_collection_initializer(
    expr: &syn::Expr,
    target_ty: &TrustVcType,
) -> Option<TrustVcExpr> {
    let source_kind = empty_std_collection_call_kind(expr)?;
    let expected_kind = match target_ty {
        TrustVcType::Seq(_) => "Vec",
        TrustVcType::Set(_) => "HashSet",
        TrustVcType::Map(_, _) => "HashMap",
        _ => return None,
    };
    if source_kind != expected_kind {
        return None;
    }

    Some(TrustVcExpr::FnCall {
        name: targeted_empty_collection_constructor_name(source_kind, target_ty),
        args: vec![],
        return_ty: target_ty.clone(),
    })
}

fn empty_std_collection_call_kind(expr: &syn::Expr) -> Option<&'static str> {
    let syn::Expr::Call(call) = expr else {
        return None;
    };
    if !call.args.is_empty() {
        return None;
    }
    let syn::Expr::Path(path) = call.func.as_ref() else {
        return None;
    };
    if path.qself.is_some() {
        return None;
    }
    let mut segments = path.path.segments.iter().rev();
    let method = segments.next()?;
    if method.ident != "new" && method.ident != "default" {
        return None;
    }
    let receiver = segments.next()?;
    match receiver.ident.to_string().as_str() {
        "Vec" => Some("Vec"),
        "HashMap" => Some("HashMap"),
        "HashSet" => Some("HashSet"),
        _ => None,
    }
}

fn targeted_empty_collection_constructor_name(kind: &str, target_ty: &TrustVcType) -> String {
    let raw = format!("{}_{}_new", kind, target_ty.to_type_string());
    let mut sanitized = String::with_capacity(raw.len());
    let mut last_was_underscore = false;
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() {
            sanitized.push(ch);
            last_was_underscore = false;
        } else if !last_was_underscore {
            sanitized.push('_');
            last_was_underscore = true;
        }
    }
    while sanitized.ends_with('_') {
        sanitized.pop();
    }
    format!("{COLLECTION_CONSTRUCTOR_PREFIX}{sanitized}")
}

fn lower_targeted_none_initializer(
    expr: &syn::Expr,
    target_ty: &TrustVcType,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    let syn::Expr::Path(path) = expr else {
        return Ok(None);
    };
    if path.path.segments.len() != 1
        || path.path.segments[0].ident != "None"
        || !matches!(&path.path.segments[0].arguments, syn::PathArguments::None)
    {
        return Ok(None);
    }
    let TrustVcType::Datatype { name, variants } = target_ty else {
        return Ok(None);
    };
    if !name.starts_with("Option<")
        || !variants
            .iter()
            .any(|variant| variant.name == "None" && variant.fields.is_empty())
    {
        return Ok(None);
    }
    Ok(Some(TrustVcExpr::FnCall {
        name: variant_symbol_name(name, "None"),
        args: vec![],
        return_ty: target_ty.clone(),
    }))
}

fn let_binding_has_annotation(local: &syn::Local) -> bool {
    matches!(local.pat, syn::Pat::Type(_))
}

fn coerce_expr_to_type(expr: TrustVcExpr, target_ty: &TrustVcType) -> TrustVcExpr {
    match expr {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if same_datatype_family(&return_ty, target_ty) => {
            if let Some(variant) = matching_datatype_variant(&return_ty, &name) {
                let Some(field_types) = datatype_variant_field_types(target_ty, &variant) else {
                    return TrustVcExpr::FnCall {
                        name,
                        args,
                        return_ty,
                    };
                };
                if field_types.len() != args.len() {
                    return TrustVcExpr::FnCall {
                        name,
                        args,
                        return_ty,
                    };
                }
                let coerced_args = args
                    .into_iter()
                    .zip(field_types)
                    .map(|(arg, field_ty)| coerce_expr_to_type(arg, &field_ty))
                    .collect();
                let TrustVcType::Datatype {
                    name: target_name, ..
                } = target_ty
                else {
                    return TrustVcExpr::FnCall {
                        name: variant_symbol_name(&return_ty.to_type_string(), variant.as_str()),
                        args: coerced_args,
                        return_ty,
                    };
                };
                TrustVcExpr::FnCall {
                    name: variant_symbol_name(target_name, &variant),
                    args: coerced_args,
                    return_ty: target_ty.clone(),
                }
            } else {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                }
            }
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => TrustVcExpr::Ite {
            cond,
            then_branch: Box::new(coerce_expr_to_type(*then_branch, target_ty)),
            else_branch: Box::new(coerce_expr_to_type(*else_branch, target_ty)),
            ty: target_ty.clone(),
        },
        TrustVcExpr::Match {
            scrutinee, arms, ..
        } => TrustVcExpr::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| crate::ir_expr::MatchArm {
                    pattern: arm.pattern,
                    body: coerce_expr_to_type(arm.body, target_ty),
                    // The guard is a boolean, not the match's value type — carry it
                    // verbatim (coercing it to `target_ty` would corrupt it).
                    guard: arm.guard,
                })
                .collect(),
            ty: target_ty.clone(),
        },
        other => coerce_unsuffixed_literal(other, target_ty),
    }
}

fn same_datatype_family(left: &TrustVcType, right: &TrustVcType) -> bool {
    let (
        TrustVcType::Datatype {
            name: left_name, ..
        },
        TrustVcType::Datatype {
            name: right_name, ..
        },
    ) = (left, right)
    else {
        return false;
    };
    left_name.split('<').next() == right_name.split('<').next()
}

fn matching_datatype_variant(ty: &TrustVcType, constructor_name: &str) -> Option<String> {
    let TrustVcType::Datatype { name, variants } = ty else {
        return None;
    };
    variants
        .iter()
        .find(|variant| variant_symbol_name(name, &variant.name) == constructor_name)
        .map(|variant| variant.name.clone())
}

fn datatype_variant_field_types(ty: &TrustVcType, variant_name: &str) -> Option<Vec<TrustVcType>> {
    let TrustVcType::Datatype { variants, .. } = ty else {
        return None;
    };
    variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .map(|variant| {
            variant
                .fields
                .iter()
                .map(|(_, field_ty)| field_ty.clone())
                .collect()
        })
}

fn option_binding_from_value(value: &TrustVcExpr) -> Option<OptionBindingMeta> {
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = value
    else {
        return None;
    };
    let TrustVcType::Datatype { name: ty_name, .. } = return_ty else {
        return None;
    };
    if !ty_name.starts_with("Option<") {
        return None;
    }
    if name == &variant_symbol_name(ty_name, "None") && args.is_empty() {
        return Some(OptionBindingMeta {
            ty: return_ty.clone(),
            state: OptionBindingState::None,
        });
    }
    if name == &variant_symbol_name(ty_name, "Some") && args.len() == 1 {
        return Some(OptionBindingMeta {
            ty: return_ty.clone(),
            state: OptionBindingState::Some {
                value: args.first().cloned(),
            },
        });
    }
    None
}

fn result_binding_from_value(value: &TrustVcExpr) -> Option<ResultBindingMeta> {
    let TrustVcExpr::FnCall {
        name,
        args,
        return_ty,
    } = value
    else {
        return None;
    };
    let TrustVcType::Datatype { name: ty_name, .. } = return_ty else {
        return None;
    };
    if !ty_name.starts_with("Result<") {
        return None;
    }
    if name == &variant_symbol_name(ty_name, "Ok") && args.len() == 1 {
        return Some(ResultBindingMeta {
            ty: return_ty.clone(),
            state: ResultBindingState::Ok {
                value: args.first().cloned(),
            },
        });
    }
    if name == &variant_symbol_name(ty_name, "Err") && args.len() == 1 {
        return Some(ResultBindingMeta {
            ty: return_ty.clone(),
            state: ResultBindingState::Err {
                error: args.first().cloned(),
            },
        });
    }
    None
}

/// Names a `let _ = ..;` binding.
///
/// A wildcard discards the value but NOT the evaluation: the initializer is
/// still lowered by the caller, so any obligation it carries (a callee's
/// `requires`, an overflow check) is still emitted. Binding to a fresh name that
/// nothing can reference is therefore exactly `let _`, whereas SKIPPING the
/// statement would silently drop those obligations — the unsound direction.
fn fresh_wildcard_binding_name() -> String {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    format!(
        "__trust_vc_wildcard_{}",
        NEXT.fetch_add(1, Ordering::Relaxed)
    )
}

fn extract_let_binding(
    local: &syn::Local,
    env: &TypeEnv,
    depth: usize,
) -> Result<(String, TrustVcType), LoweringError> {
    match &local.pat {
        // `let _ = expr;` — type comes from the initializer, same as an ident.
        syn::Pat::Wild(_) => {
            let name = fresh_wildcard_binding_name();
            if let Some(init) = &local.init {
                let expr = lower_syn_expr_with_depth(&init.expr, env, depth).map_err(|err| {
                    LoweringError::TypeInference(format!(
                        "cannot infer type for `let _` binding without explicit annotation: \
                             failed to lower initializer ({})",
                        err
                    ))
                })?;
                return Ok((name, infer_expr_type(&expr)));
            }
            Err(LoweringError::TypeInference(
                "cannot infer type for `let _` binding without a lowerable initializer".into(),
            ))
        }
        syn::Pat::Ident(pattern) => {
            let name = pattern.ident.to_string();
            if let Some(init) = &local.init {
                let expr = lower_syn_expr_with_depth(&init.expr, env, depth).map_err(|err| {
                    LoweringError::TypeInference(format!(
                        "cannot infer type for let-binding '{}' without explicit annotation: \
                             failed to lower initializer ({})",
                        name, err
                    ))
                })?;
                return Ok((name, infer_expr_type(&expr)));
            }
            Err(LoweringError::TypeInference(format!(
                "cannot infer type for let-binding '{}' without explicit annotation or lowerable initializer",
                name
            )))
        }
        syn::Pat::Type(pattern) => match &*pattern.pat {
            syn::Pat::Ident(pattern_ident) => {
                let name = pattern_ident.ident.to_string();
                let ty = env.resolve_syn_type(&pattern.ty)?;
                Ok((name, ty))
            }
            // `let _: T = expr;`
            syn::Pat::Wild(_) => {
                let ty = env.resolve_syn_type(&pattern.ty)?;
                Ok((fresh_wildcard_binding_name(), ty))
            }
            _ => Err(LoweringError::UnsupportedPattern(
                "complex let pattern".into(),
            )),
        },
        _ => Err(LoweringError::UnsupportedPattern(
            "unsupported let pattern".into(),
        )),
    }
}
