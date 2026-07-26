// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Free helper functions for mut-ref proof rewriting.

use crate::ir::TrustVcType;
use crate::ir_place::{PlaceProjection, TrustVcPlace};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{BinOp, ExprPath, Ident, Macro};

/// String-based key for `TrustVcPlace` in ordered maps.
///
/// `TrustVcPlace` contains `TrustVcExpr` (via `PlaceProjection::Index`) which
/// does not implement `Ord`/`Hash`. This key provides a deterministic
/// ordering for version tracking and used-place iteration.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct PlaceKey(pub(super) String);

pub(super) fn place_key(place: &TrustVcPlace) -> PlaceKey {
    let mut key = place.root_name.clone();
    for proj in &place.projections {
        match proj {
            PlaceProjection::Field { field_name, .. } => {
                key.push('.');
                key.push_str(field_name);
            }
            PlaceProjection::Index { .. } => {
                key.push_str("[idx]");
            }
        }
    }
    PlaceKey(key)
}

pub(super) fn opaque_ty() -> TrustVcType {
    TrustVcType::Opaque("unknown".to_string())
}

pub(super) fn macro_name(mac: &Macro) -> Option<String> {
    mac.path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
}

pub(super) fn simple_path_ident(expr_path: &ExprPath) -> Option<String> {
    if expr_path.qself.is_none() && expr_path.path.segments.len() == 1 {
        expr_path
            .path
            .segments
            .first()
            .map(|seg| seg.ident.to_string())
    } else {
        None
    }
}

pub(super) fn member_name(member: &syn::Member) -> String {
    match member {
        syn::Member::Named(ident) => ident.to_string(),
        syn::Member::Unnamed(index) => index.index.to_string(),
    }
}

pub(super) fn place_expr_tokens(place: &TrustVcPlace, param_ident: &Ident) -> TokenStream {
    let mut expr = quote!(*#param_ident);
    for proj in &place.projections {
        match proj {
            PlaceProjection::Field { field_name, .. } => {
                if let Ok(index) = field_name.parse::<usize>() {
                    let index = syn::Index::from(index);
                    expr = quote!((#expr).#index);
                } else {
                    let ident = format_ident!("{}", field_name);
                    expr = quote!((#expr).#ident);
                }
            }
            PlaceProjection::Index { .. } => {
                // Index projection token generation not yet supported (Slice 4+).
            }
        }
    }
    expr
}

pub(super) fn place_display(place: &TrustVcPlace) -> String {
    if place.projections.is_empty() {
        return format!("*{}", place.root_name);
    }

    let mut display = place.root_name.clone();
    for proj in &place.projections {
        match proj {
            PlaceProjection::Field { field_name, .. } => {
                display.push('.');
                display.push_str(field_name);
            }
            PlaceProjection::Index { .. } => {
                display.push_str("[?]");
            }
        }
    }
    display
}

pub(super) fn shadow_ident(place: &TrustVcPlace, version: usize) -> Ident {
    let mut parts = vec![place.root_name.clone()];
    for proj in &place.projections {
        match proj {
            PlaceProjection::Field { field_name, .. } => {
                if field_name.chars().all(|ch| ch.is_ascii_digit()) {
                    parts.push(format!("field_{}", field_name));
                } else {
                    parts.push(field_name.replace(|ch: char| !ch.is_ascii_alphanumeric(), "_"));
                }
            }
            PlaceProjection::Index { .. } => {
                parts.push("idx".to_string());
            }
        }
    }
    format_ident!("__trust_vc_mutref_{}_{}", parts.join("_"), version)
}

pub(super) fn is_supported_referent_type(ty: &str) -> bool {
    matches!(
        ty,
        "bool"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
    )
}

pub(super) fn is_assign_binop(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
            | BinOp::BitAndAssign(_)
            | BinOp::BitOrAssign(_)
            | BinOp::BitXorAssign(_)
            | BinOp::ShlAssign(_)
            | BinOp::ShrAssign(_)
    )
}
