// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Utility functions for proof statement bridge.

use crate::local_vars::extract_type_string;
use syn::spanned::Spanned;
use syn::{parse_quote, Expr, ExprPath, Local, Pat, Type};

pub(super) fn typed_local_binding(local: &Local) -> Option<(&syn::Ident, &Type)> {
    match &local.pat {
        Pat::Type(pat_type) => match pat_type.pat.as_ref() {
            Pat::Ident(pat_ident) => Some((&pat_ident.ident, pat_type.ty.as_ref())),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn local_binding_name(local: &Local) -> Option<String> {
    match &local.pat {
        Pat::Type(pat_type) => match pat_type.pat.as_ref() {
            Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
            _ => None,
        },
        Pat::Ident(pat_ident) => Some(pat_ident.ident.to_string()),
        _ => None,
    }
}

pub(super) fn is_proph_wrapper_type(ty: &Type) -> bool {
    match ty {
        Type::Path(type_path) => type_path
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "Proph"),
        Type::Reference(type_ref) => is_proph_wrapper_type(type_ref.elem.as_ref()),
        _ => false,
    }
}

pub(super) fn is_prophecy_new_expr(expr: &Expr) -> bool {
    let Expr::Call(call) = expr else {
        return false;
    };
    if !call.args.is_empty() {
        return false;
    }
    let Expr::Path(path) = call.func.as_ref() else {
        return false;
    };
    path_matches_suffix(&path.path, &["Proph", "new"])
}

pub(super) fn prophecy_view_receiver(expr: &Expr) -> Option<(String, ExprPath)> {
    let Expr::MethodCall(method_call) = expr else {
        return None;
    };
    if method_call.method != "view" || !method_call.args.is_empty() {
        return None;
    }
    let Expr::Path(path) = method_call.receiver.as_ref() else {
        return None;
    };
    let name = receiver_ident_name(method_call.receiver.as_ref())?;
    Some((name, path.clone()))
}

pub(super) fn receiver_ident_name(expr: &Expr) -> Option<String> {
    let Expr::Path(path) = expr else {
        return None;
    };
    if path.qself.is_some() || path.path.segments.len() != 1 {
        return None;
    }
    Some(path.path.segments.first()?.ident.to_string())
}

pub(super) fn path_matches_suffix(path: &syn::Path, suffix: &[&str]) -> bool {
    let segments: Vec<_> = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    let suffix: Vec<_> = suffix.iter().map(|segment| segment.to_string()).collect();
    segments.ends_with(&suffix)
}

pub(super) fn placeholder_expr(ty: &Type) -> syn::Result<Expr> {
    let ty_name = extract_type_string(ty);
    match ty_name.as_str() {
        "bool" => Ok(parse_quote!(false)),
        "i8" => Ok(parse_quote!(0i8)),
        "i16" => Ok(parse_quote!(0i16)),
        "i32" => Ok(parse_quote!(0i32)),
        "i64" => Ok(parse_quote!(0i64)),
        "i128" => Ok(parse_quote!(0i128)),
        "isize" => Ok(parse_quote!(0isize)),
        "u8" => Ok(parse_quote!(0u8)),
        "u16" => Ok(parse_quote!(0u16)),
        "u32" => Ok(parse_quote!(0u32)),
        "u64" => Ok(parse_quote!(0u64)),
        "u128" => Ok(parse_quote!(0u128)),
        "usize" => Ok(parse_quote!(0usize)),
        _ => Err(syn::Error::new(
            ty.span(),
            "proof ghost-statement bridge currently supports only bool and primitive integer \
             placeholder types",
        )),
    }
}
