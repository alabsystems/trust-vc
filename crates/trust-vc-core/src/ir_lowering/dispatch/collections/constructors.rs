//! Collection constructor and coercion helpers for IR lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2526.

use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;
use crate::ir_lowering::{LoweringError, TypeEnv, COLLECTION_CONSTRUCTOR_PREFIX};

/// Type an unsuffixed integer literal argument by the receiver type — only
/// where that never changes its value.
///
/// In Rust, `x.checked_add(100)` where `x: u8` means `100` is `u8`. IR
/// lowering defaults unsuffixed literals to `Int{32}`; the literal (for `-v`,
/// the literal `-v`) takes the receiver's type exactly when it is a value of
/// that type (`ir_lowering::untyped_literal_at_peer`). This used to retype any
/// `Int{32}` literal by shape: `x.wrapping_add(300)` made a `u8` literal of
/// 300. A literal the receiver type cannot hold keeps its own type, and the
/// encoder refuses the mixed-type wrapping operation.
pub(in crate::ir_lowering::dispatch) fn coerce_literal_to_receiver_type(
    expr: TrustVcExpr,
    receiver_ty: &TrustVcType,
) -> TrustVcExpr {
    let literal = match &expr {
        TrustVcExpr::IntLit { .. } => true,
        TrustVcExpr::Neg(inner) => matches!(inner.as_ref(), TrustVcExpr::IntLit { .. }),
        _ => false,
    };
    if !literal {
        return expr;
    }
    crate::ir_lowering::untyped_literal_at_peer(&expr, receiver_ty).unwrap_or(expr)
}

pub(in crate::ir_lowering::dispatch) fn lower_collection_constructor(
    path: &syn::ExprPath,
    env: &TypeEnv,
) -> Result<Option<TrustVcExpr>, LoweringError> {
    if path.qself.is_some() {
        return Ok(None);
    }

    let Some(method_segment) = path.path.segments.last() else {
        return Ok(None);
    };
    let constructor_name = method_segment.ident.to_string();
    if !matches!(constructor_name.as_str(), "empty" | "new") {
        return Ok(None);
    }

    let Some(type_segment) = path.path.segments.iter().rev().nth(1) else {
        return Ok(None);
    };
    if constructor_name == "new" && type_segment.ident == "Multiset" {
        return Ok(None);
    }
    let return_ty = match collection_type_from_segment(type_segment, &constructor_name, env)? {
        Some(return_ty) => return_ty,
        None => return Ok(None),
    };

    Ok(Some(TrustVcExpr::FnCall {
        name: collection_constructor_symbol_name(&path.path),
        args: vec![],
        return_ty,
    }))
}

fn collection_type_from_segment(
    segment: &syn::PathSegment,
    constructor_name: &str,
    env: &TypeEnv,
) -> Result<Option<TrustVcType>, LoweringError> {
    let parse_generic = |index: usize| -> Result<TrustVcType, LoweringError> {
        let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
            return Err(LoweringError::TypeInference(format!(
                "collection constructor '{}::{}()' requires explicit type arguments",
                segment.ident, constructor_name
            )));
        };
        let ty = args
            .args
            .iter()
            .filter_map(|arg| match arg {
                syn::GenericArgument::Type(ty) => Some(ty),
                _ => None,
            })
            .nth(index)
            .ok_or_else(|| {
                LoweringError::TypeInference(format!(
                    "collection constructor '{}::{}()' is missing type argument {}",
                    segment.ident,
                    constructor_name,
                    index + 1
                ))
            })?;
        collection_element_type_from_syn_type(ty, constructor_name, env)
    };

    match segment.ident.to_string().as_str() {
        // `String::new()` is the empty string: a zero-arity constructor whose
        // tracked length the encoder registers as the literal 0 (the same lane
        // `Vec::<T>::new()` uses), so `s.view().len() == 0` is decidable on it.
        // `String` has no type arguments and no `empty` spelling.
        "String"
            if constructor_name == "new"
                && matches!(segment.arguments, syn::PathArguments::None) =>
        {
            Ok(Some(TrustVcType::String))
        }
        // `VecDeque<T>` views as the same `Seq<T>` a `Vec<T>` does (vstd
        // `VecDeque::view`), so its empty constructor is the empty sequence.
        "Seq" | "Vec" | "VecDeque" => Ok(Some(TrustVcType::Seq(Box::new(parse_generic(0)?)))),
        "Set" | "HashSet" => Ok(Some(TrustVcType::Set(Box::new(parse_generic(0)?)))),
        "Multiset" => Ok(Some(TrustVcType::Multiset(Box::new(parse_generic(0)?)))),
        "Map" | "HashMap" => Ok(Some(TrustVcType::Map(
            Box::new(parse_generic(0)?),
            Box::new(parse_generic(1)?),
        ))),
        _ => Ok(None),
    }
}

fn collection_element_type_from_syn_type(
    ty: &syn::Type,
    constructor_name: &str,
    env: &TypeEnv,
) -> Result<TrustVcType, LoweringError> {
    match ty {
        syn::Type::Path(type_path) if type_path.qself.is_none() => {
            let Some(last_segment) = type_path.path.segments.last() else {
                return Err(LoweringError::InvalidType("empty type path".to_string()));
            };

            match last_segment.ident.to_string().as_str() {
                "bool" => Ok(TrustVcType::Bool),
                "char" => Ok(TrustVcType::Char),
                "str" => Ok(TrustVcType::StrSlice),
                "String" => Ok(TrustVcType::String),
                "i8" => Ok(TrustVcType::Int { width: 8 }),
                "i16" => Ok(TrustVcType::Int { width: 16 }),
                "i32" => Ok(TrustVcType::Int { width: 32 }),
                "i64" => Ok(TrustVcType::Int { width: 64 }),
                "i128" => Ok(TrustVcType::Int { width: 128 }),
                "isize" => Ok(TrustVcType::Int {
                    width: crate::ir::pointer_width(),
                }),
                "u8" => Ok(TrustVcType::Uint { width: 8 }),
                "u16" => Ok(TrustVcType::Uint { width: 16 }),
                "u32" => Ok(TrustVcType::Uint { width: 32 }),
                "u64" => Ok(TrustVcType::Uint { width: 64 }),
                "u128" => Ok(TrustVcType::Uint { width: 128 }),
                "usize" => Ok(TrustVcType::Uint {
                    width: crate::ir::pointer_width(),
                }),
                "Seq" | "Set" | "Multiset" | "Map" => {
                    collection_type_from_segment(last_segment, constructor_name, env)?.ok_or_else(
                        || {
                            LoweringError::InvalidType(format!(
                                "unsupported collection type '{}'",
                                quote::quote!(#ty).to_string().replace(' ', "")
                            ))
                        },
                    )
                }
                _ => Ok(env.resolve_syn_type(ty)?),
            }
        }
        // A TUPLE element type (`Seq<(u32, u32)>`) is not a `Type::Path`; route it
        // through the same general resolver the unknown-`Path` arm above uses, so
        // it resolves to the tuple's modeled sort (or an opaque one). Consistent
        // and sound-by-construction: a resolvable tuple encodes like any other
        // element sort, and an unresolvable one becomes opaque → fail-closed
        // downstream, never a false-verify.
        syn::Type::Tuple(_) => Ok(env.resolve_syn_type(ty)?),
        _ => Err(LoweringError::InvalidType(format!(
            "unsupported collection constructor type '{}'",
            quote::quote!(#ty).to_string().replace(' ', "")
        ))),
    }
}

fn collection_constructor_symbol_name(path: &syn::Path) -> String {
    let raw = quote::quote!(#path).to_string().replace(' ', "");
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
