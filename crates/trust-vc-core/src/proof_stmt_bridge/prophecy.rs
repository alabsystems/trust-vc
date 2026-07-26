// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prophecy rewriting: new, view, resolve operations.

use super::helpers::{
    is_proph_wrapper_type, is_prophecy_new_expr, placeholder_expr, prophecy_view_receiver,
    receiver_ident_name, typed_local_binding,
};
use super::rewrite::BridgeState;
use crate::expr_codegen::expr_to_try_builder_tokens;
use crate::local_vars::extract_type_string;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::spanned::Spanned;
use syn::{parse_quote, Expr, Local, Stmt};

pub(super) fn try_rewrite_prophecy_new(
    local: &Local,
    state: &mut BridgeState,
) -> syn::Result<Option<Vec<Stmt>>> {
    let Some((binding_ident, binding_ty)) = typed_local_binding(local) else {
        return Ok(None);
    };
    if !is_proph_wrapper_type(binding_ty) {
        return Ok(None);
    }
    let Some(init) = &local.init else {
        return Ok(None);
    };
    if !is_prophecy_new_expr(init.expr.as_ref()) {
        return Ok(None);
    }

    let support_root = crate::macro_support_root();
    let binding_name = binding_ident.to_string();
    let inner_ty = extract_type_string(binding_ty);

    state.shadow_local_name(&binding_name);
    state
        .prophecy_locals
        .insert(binding_name.clone(), inner_ty.clone());

    let helper_stmt: Stmt = parse_quote! {
        #support_root::register_prophecy_local(
            #binding_name.to_string(),
            #inner_ty.to_string(),
        );
    };

    Ok(Some(vec![Stmt::Local(local.clone()), helper_stmt]))
}

pub(super) fn try_rewrite_prophecy_view(
    local: &Local,
    state: &mut BridgeState,
) -> syn::Result<Option<Vec<Stmt>>> {
    let Some((binding_ident, binding_ty)) = typed_local_binding(local) else {
        return Ok(None);
    };
    let Some(init) = &local.init else {
        return Ok(None);
    };
    let Some((receiver_name, receiver_expr)) = prophecy_view_receiver(init.expr.as_ref()) else {
        return Ok(None);
    };
    let Some(prophecy_inner_ty) = state.prophecy_locals.get(&receiver_name).cloned() else {
        return Ok(None);
    };

    let binding_name = binding_ident.to_string();
    if binding_name == receiver_name {
        return Err(syn::Error::new(
            local.span(),
            "proof ghost-statement bridge does not support shadowing a prophecy local with \
             its own `.view()` result",
        ));
    }

    let placeholder = placeholder_expr(binding_ty)?;
    let support_root = crate::macro_support_root();
    let bridge_id = state.next_bridge_id();
    let obligation_name = format!("ghost_stmt_view_{}_{}", binding_name, bridge_id);
    let condition_display = format!("{} == {}.view()", binding_name, receiver_name);
    let binding_ty_str = extract_type_string(binding_ty);
    let view_expr = view_equivalence_expr(
        &binding_name,
        &binding_ty_str,
        &receiver_name,
        &prophecy_inner_ty,
    );

    state.shadow_local_name(&binding_name);
    state.bridged_locals.insert(binding_name.clone());

    let typecheck_guard: Stmt = parse_quote! {
        if false {
            let _: #binding_ty = #receiver_expr.view();
        }
    };
    let mut decl = local.clone();
    decl.init = None;
    let assign_stmt: Stmt = parse_quote! {
        #binding_ident = #placeholder;
    };
    let helper_stmt: Stmt = parse_quote! {
        #support_root::collect_symbolic_let_binding_expr(
            #obligation_name.to_string(),
            #condition_display.to_string(),
            #view_expr,
        );
    };

    Ok(Some(vec![
        typecheck_guard,
        Stmt::Local(decl),
        assign_stmt,
        helper_stmt,
    ]))
}

fn view_equivalence_expr(
    binding_name: &str,
    binding_ty: &str,
    prophecy_name: &str,
    prophecy_inner_ty: &str,
) -> TokenStream {
    let support_root = crate::macro_support_root();
    quote! {
        #support_root::ir_builder::eq(
            #support_root::ir_builder::var(
                #binding_name,
                #support_root::ir::TrustVcType::parse_or_opaque(#binding_ty),
            ),
            #support_root::ir::TrustVcExpr::ProphecyNew {
                name: #prophecy_name.to_string(),
                ty: #support_root::ir::TrustVcType::parse_or_opaque(#prophecy_inner_ty),
            },
        )
    }
}

pub(super) fn try_rewrite_prophecy_resolve(
    expr: &Expr,
    state: &mut BridgeState,
) -> syn::Result<Option<Vec<Stmt>>> {
    let Expr::MethodCall(method_call) = expr else {
        return Ok(None);
    };
    if method_call.method != "resolve" || method_call.args.len() != 1 {
        return Ok(None);
    }
    let Some(receiver_name) = receiver_ident_name(method_call.receiver.as_ref()) else {
        return Ok(None);
    };
    let Some(prophecy_inner_ty) = state.prophecy_locals.get(&receiver_name).cloned() else {
        return Ok(None);
    };

    let Some(resolve_arg) = method_call.args.first() else {
        return Ok(None);
    };

    // A prophecy may be resolved at most once on a control-flow path. A second resolve
    // would assume a second equality over the same prophecy symbol, contradicting the
    // first and vacuously verifying everything downstream (false-verify). Reject it.
    // resolved_prophecies is branch-scoped (see BridgeState), so same-symbol resolves
    // in disjoint branches are still allowed.
    if !state.resolved_prophecies.insert(receiver_name.clone()) {
        return Err(syn::Error::new(
            expr.span(),
            format!(
                "prophecy `{receiver_name}` is resolved more than once on this path; \
                 a prophecy may be resolved at most once"
            ),
        ));
    }

    let support_root = crate::macro_support_root();
    let bridge_id = state.next_bridge_id();
    let obligation_name = format!("ghost_stmt_resolve_{}_{}", receiver_name, bridge_id);
    let arg_display = resolve_arg.to_token_stream().to_string();
    let condition_display = format!("{}.view() == {}", receiver_name, arg_display);

    let typecheck_guard: Stmt = parse_quote! {
        if false {
            #method_call;
        }
    };

    let helper_stmt = if let Some(rhs_builder) = expr_to_try_builder_tokens(resolve_arg) {
        let lhs_expr = prophecy_new_expr(&receiver_name, &prophecy_inner_ty);
        parse_quote! {
            match #rhs_builder {
                Some(rhs_expr) => #support_root::collect_symbolic_assume_expr(
                    #obligation_name.to_string(),
                    #condition_display.to_string(),
                    #support_root::ir_builder::eq(#lhs_expr, rhs_expr),
                ),
                None => #support_root::verify_macro::collect_obligation(
                    #support_root::vc::ObligationKind::Assume,
                    #obligation_name.to_string(),
                    #condition_display.to_string(),
                    None,
                ),
            };
        }
    } else {
        parse_quote! {
            #support_root::verify_macro::collect_obligation(
                #support_root::vc::ObligationKind::Assume,
                #obligation_name.to_string(),
                #condition_display.to_string(),
                None,
            );
        }
    };

    Ok(Some(vec![typecheck_guard, helper_stmt]))
}

fn prophecy_new_expr(prophecy_name: &str, prophecy_inner_ty: &str) -> TokenStream {
    let support_root = crate::macro_support_root();
    quote! {
        #support_root::ir::TrustVcExpr::ProphecyNew {
            name: #prophecy_name.to_string(),
            ty: #support_root::ir::TrustVcType::parse_or_opaque(#prophecy_inner_ty),
        }
    }
}
