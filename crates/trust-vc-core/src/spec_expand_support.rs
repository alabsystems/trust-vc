// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Signature/type helpers for spec function expansion.
//!
//! Extracted from `spec_expand.rs` to keep files under 500 lines (#2599).

use crate::expr_codegen;
use crate::local_vars::extract_type_string;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashSet;

pub(super) fn support_root() -> syn::Path {
    crate::macro_support_root()
}

pub(super) fn ir_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::ir }
}

pub(super) fn ir_builder_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::ir_builder }
}

pub(super) fn verify_macro_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::verify_macro }
}

pub(super) fn vc_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::vc }
}

pub(super) fn mode_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::mode }
}

/// Extracted function parameter (name, type string).
pub(super) struct FnParam {
    pub(super) name: String,
    pub(super) ty: String,
}

/// Extracts typed parameters from a function signature, skipping receivers.
pub(super) fn extract_fn_params(sig: &syn::Signature) -> Vec<FnParam> {
    sig.inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => {
                if let syn::Pat::Ident(pat_ident) = &*pat_type.pat {
                    Some(FnParam {
                        name: pat_ident.ident.to_string(),
                        ty: extract_type_string(&pat_type.ty),
                    })
                } else {
                    None
                }
            }
            syn::FnArg::Receiver(_) => None,
        })
        .collect()
}

/// Collects generic type parameter names from the function signature.
pub(super) fn extract_type_params(sig: &syn::Signature) -> HashSet<String> {
    sig.generics
        .type_params()
        .map(|param| param.ident.to_string())
        .collect()
}

/// Collects trait bounds from generic parameters and where clauses.
fn extract_trait_bounds(sig: &syn::Signature) -> Vec<(String, String)> {
    let mut bounds = Vec::new();

    for param in sig.generics.type_params() {
        append_trait_bounds(&mut bounds, &param.ident.to_string(), &param.bounds);
    }

    if let Some(where_clause) = &sig.generics.where_clause {
        for predicate in &where_clause.predicates {
            if let syn::WherePredicate::Type(predicate) = predicate {
                if let syn::Type::Path(type_path) = &predicate.bounded_ty {
                    if let Some(type_param) = type_path.path.get_ident() {
                        append_trait_bounds(
                            &mut bounds,
                            &type_param.to_string(),
                            &predicate.bounds,
                        );
                    }
                }
            }
        }
    }

    bounds
}

fn append_trait_bounds(
    bounds: &mut Vec<(String, String)>,
    type_param: &str,
    predicates: &syn::punctuated::Punctuated<syn::TypeParamBound, syn::token::Plus>,
) {
    for bound in predicates {
        let syn::TypeParamBound::Trait(trait_bound) = bound else {
            continue;
        };
        if !matches!(trait_bound.modifier, syn::TraitBoundModifier::None) {
            continue;
        }
        let Some(trait_name) = trait_bound
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
        else {
            continue;
        };
        let bound_entry = (type_param.to_string(), trait_name);
        if !bounds.contains(&bound_entry) {
            bounds.push(bound_entry);
        }
    }
}

pub(super) fn trait_bound_tokens(sig: &syn::Signature) -> Vec<TokenStream> {
    let ir_path = ir_path();
    extract_trait_bounds(sig)
        .into_iter()
        .map(|(type_param, trait_name)| {
            quote! {
                #ir_path::TraitBound::new(#type_param, #trait_name)
            }
        })
        .collect()
}

/// Generates the ghost-code block that panics at runtime.
///
/// Used for both `#[cfg(all(test, not(trust_mc)))]` non-proof path and
/// `#[cfg(all(not(test), not(trust_mc)))]` production path.
pub(super) fn ghost_unreachable_block(fn_name: &syn::Ident, block: &syn::Block) -> TokenStream {
    quote! {
        #[allow(unreachable_code)]
        if false {
            return { #block };
        }
        loop {
            unreachable!(concat!(
                "spec function `",
                stringify!(#fn_name),
                "` called at runtime - spec functions are ghost code"
            ));
        }
    }
}

/// Builds token lists for parameter registration, context params, and bound vars.
pub(super) fn param_tokens(
    params: &[FnParam],
    type_params: &HashSet<String>,
) -> (Vec<TokenStream>, Vec<TokenStream>, Vec<TokenStream>) {
    let ir_path = ir_path();
    let registration = params
        .iter()
        .map(|p| {
            let (name, ty) = (&p.name, &p.ty);
            if let Some(ty_tokens) = trust_vc_type_tokens(ty, type_params) {
                quote! {
                    if __trust_vc_ctx.get_variable_type(#name).is_none() {
                        __trust_vc_ctx.declare_var_typed(#name, #ty_tokens);
                    }
                }
            } else {
                quote! {
                    if __trust_vc_ctx.get_variable_type(#name).is_none() {
                        __trust_vc_ctx.declare_var_typed(#name, #ir_path::TrustVcType::Opaque(#ty.to_string()));
                    }
                }
            }
        })
        .collect();
    let ctx_params = params
        .iter()
        .map(|p| {
            let (name, ty) = (&p.name, &p.ty);
            let ty_tokens = trust_vc_type_tokens(ty, type_params).unwrap_or_else(|| {
                quote! {
                    #ir_path::TrustVcType::Opaque(#ty.to_string())
                }
            });
            quote! { (#name.to_string(), #ty_tokens) }
        })
        .collect();
    let bound_vars = params
        .iter()
        .map(|p| {
            let name = &p.name;
            quote! { #name.to_string() }
        })
        .collect();
    (registration, ctx_params, bound_vars)
}

/// Maps a Rust type name to TrustVcType constructor tokens for body axioms.
///
/// Covers primitive types used in spec function signatures. Returns `None`
/// for unknown types, causing the caller to fall back to the string path.
pub(super) fn trust_vc_type_tokens(
    name: &str,
    type_params: &HashSet<String>,
) -> Option<TokenStream> {
    let ir_path = ir_path();
    if type_params.contains(name) {
        return Some(quote! {
            #ir_path::TrustVcType::TypeParam(#name.to_string())
        });
    }

    match name {
        "()" => Some(quote! { #ir_path::TrustVcType::Unit }),
        "bool" => Some(quote! { #ir_path::TrustVcType::Bool }),
        "i8" => Some(quote! { #ir_path::TrustVcType::Int { width: 8 } }),
        "i16" => Some(quote! { #ir_path::TrustVcType::Int { width: 16 } }),
        "i32" => Some(quote! { #ir_path::TrustVcType::Int { width: 32 } }),
        "i64" => Some(quote! { #ir_path::TrustVcType::Int { width: 64 } }),
        "u8" => Some(quote! { #ir_path::TrustVcType::Uint { width: 8 } }),
        "u16" => Some(quote! { #ir_path::TrustVcType::Uint { width: 16 } }),
        "u32" => Some(quote! { #ir_path::TrustVcType::Uint { width: 32 } }),
        "u64" => Some(quote! { #ir_path::TrustVcType::Uint { width: 64 } }),
        "usize" => Some(quote! { #ir_path::TrustVcType::Uint { width: 64 } }),
        "isize" => Some(quote! { #ir_path::TrustVcType::Int { width: 64 } }),
        "int" => Some(quote! { #ir_path::TrustVcType::MathInt }),
        "nat" => Some(quote! { #ir_path::TrustVcType::Nat }),
        _ => None,
    }
}

/// Attempts to build TrustVcExpr tokens for the body axiom equality:
/// `fn_name(params) == body`.
///
/// Returns `Some(TokenStream)` if the body expression is supported by
/// `expr_to_builder_tokens`. Falls back to `None` for multi-statement blocks,
/// let bindings, unsupported expression types, or unknown parameter types.
///
/// Part of #2217: migrate body axioms from string concatenation to TrustVcExpr.
pub(super) fn build_body_axiom_expr_tokens(
    params: &[FnParam],
    type_params: &HashSet<String>,
    fn_name_str: &str,
    return_type: &str,
    block: &syn::Block,
) -> Option<TokenStream> {
    let ir_builder_path = ir_builder_path();
    // Extract single trailing expression from block
    let body_expr = match block.stmts.as_slice() {
        [syn::Stmt::Expr(expr, _)] => expr,
        _ => return None,
    };

    // Convert body expression to TrustVcExpr builder tokens
    let body_tokens = expr_codegen::expr_to_builder_tokens(body_expr)?;

    // Build return type TrustVcType tokens (fall back to string path if unknown)
    let ret_ty_tokens = trust_vc_type_tokens(return_type, type_params)?;

    // Build parameter variable TrustVcExpr tokens with known types from signature.
    // Returns None (fall back to string path) if any param has an unsupported type
    // (e.g., Seq<i32>) to avoid caching TrustVcExpr with incorrect variable sorts.
    let param_var_tokens: Option<Vec<TokenStream>> = params
        .iter()
        .map(|p| {
            let name = &p.name;
            let ty_tokens = trust_vc_type_tokens(&p.ty, type_params)?;
            Some(quote! { #ir_builder_path::var(#name, #ty_tokens) })
        })
        .collect();
    let param_var_tokens = param_var_tokens?;

    // Build fn_call TrustVcExpr: fn_name(param1, param2, ...) with correct return type
    let fn_call_tokens = quote! {
        #ir_builder_path::fn_call(
            #fn_name_str,
            vec![#(#param_var_tokens),*],
            #ret_ty_tokens,
        )
    };

    // Build equality: fn_call == body
    Some(quote! {
        #ir_builder_path::eq(#fn_call_tokens, #body_tokens)
    })
}
