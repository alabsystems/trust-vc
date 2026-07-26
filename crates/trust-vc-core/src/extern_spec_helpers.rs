// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Helper utilities for `extern_spec!` macro expansion.
//!
//! Extracted from `extern_spec.rs` to keep file size under 500 lines.

use std::fmt::Write as _;

use proc_macro2::Span;
use quote::{format_ident, ToTokens};
use syn::{
    fold::Fold, punctuated::Punctuated, token::Comma, Attribute, FnArg, Ident, Pat, PatType,
    PathArguments, Signature, Type, TypePath,
};

use crate::error::{TrustVcError, TrustVcResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractAttrKind {
    Requires,
    Ensures,
    Returns,
    /// `default_ensures` — an extra postcondition a trait DEFAULT BODY must
    /// establish. Legal ONLY on a defaulted trait-method declaration; rejected
    /// everywhere else (`forbid_default_ensures`).
    DefaultEnsures,
}

/// Extract the path string from a Type for lookup purposes.
///
/// Returns `None` for unsupported type forms (qualified paths like `<T as Trait>::Assoc`,
/// references, tuples, etc.). The caller should handle this case appropriately.
pub(crate) fn type_to_path_string(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(TypePath { qself: None, path }) => {
            let segments: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
            Some(segments.join("::"))
        }
        _ => None,
    }
}

/// Extract the full path string from a Type, preserving generic arguments.
///
/// Unlike `type_to_path_string` which erases generics (e.g., `Vec::<u8>` → `Vec`),
/// this function preserves angle-bracketed arguments (e.g., `Vec::<u8>` → `Vec::<u8>`).
/// Used for exact-match lookups where distinct concrete specializations must remain
/// distinguishable (#2305).
pub(crate) fn type_to_full_path_string(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(TypePath { qself: None, path }) => {
            let mut result = String::new();
            for (i, segment) in path.segments.iter().enumerate() {
                if i > 0 {
                    result.push_str("::");
                }
                result.push_str(&segment.ident.to_string());
                match &segment.arguments {
                    PathArguments::None => {}
                    PathArguments::AngleBracketed(args) => {
                        let rendered: Vec<String> = args
                            .args
                            .iter()
                            .map(|a| {
                                a.to_token_stream()
                                    .to_string()
                                    .split_whitespace()
                                    .collect::<Vec<_>>()
                                    .join(" ")
                            })
                            .collect();
                        let _ = write!(result, "::<{}>", rendered.join(", "));
                    }
                    PathArguments::Parenthesized(_) => return None,
                }
            }
            Some(result)
        }
        _ => None,
    }
}

/// Extract requires/ensures attributes from the method's attributes.
///
/// Accepts both bare and qualified forms (`#[requires(...)]`,
/// `#[trust_vc::requires(...)]`, and the corresponding `ensures` forms).
/// Returns an error if a contract attribute uses a form other than the list
/// form, which would otherwise be silently dropped (#810).
pub(crate) fn extract_contracts(
    attrs: &[Attribute],
    surface: &'static str,
) -> TrustVcResult<(Vec<String>, Vec<String>)> {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();

    for attr in attrs {
        let Some(kind) = contract_attr_kind(attr) else {
            continue;
        };

        let meta_list = if let syn::Meta::List(meta_list) = &attr.meta {
            meta_list
        } else {
            let attr_name = match kind {
                ContractAttrKind::Requires => "requires",
                ContractAttrKind::Ensures => "ensures",
                ContractAttrKind::Returns | ContractAttrKind::DefaultEnsures => continue,
            };
            let message = format!(
                "{surface}: #[{attr_name}] must use parenthesized form: #[{attr_name}(expr)]"
            );
            return Err(invalid_contract_attribute_error(attr, surface, &message));
        };

        match kind {
            ContractAttrKind::Requires => requires.push(meta_list.tokens.to_string()),
            ContractAttrKind::Ensures => ensures.push(meta_list.tokens.to_string()),
            // `Returns` is folded in by `normalize_trait_returns_contracts`;
            // `DefaultEnsures` is harvested separately at the trait-decl site
            // (`parse_trait_method_decl`). Both must be a NO-OP here — neither may
            // silently become a regular `ensures`, and neither may error, because
            // the legitimate trait-decl path also calls `extract_contracts`.
            ContractAttrKind::Returns | ContractAttrKind::DefaultEnsures => {}
        }
    }

    Ok((requires, ensures))
}

pub(crate) fn extract_param_names(
    sig: &Signature,
    surface: &'static str,
) -> TrustVcResult<Vec<String>> {
    let mut names = Vec::new();

    for input in &sig.inputs {
        let FnArg::Typed(pat_ty) = input else {
            continue;
        };

        if let Pat::Ident(pat_ident) = pat_ty.pat.as_ref() {
            names.push(pat_ident.ident.to_string());
            continue;
        }

        return Err(TrustVcError::Parse {
            context: contract_attribute_context(surface),
            source: syn::Error::new_spanned(
                &pat_ty.pat,
                format!(
                    "{surface}: extern_spec parameters must use simple identifiers \
                     (for call-site binding); patterns are not supported here"
                ),
            ),
        });
    }

    Ok(names)
}

pub(crate) fn contract_attr_kind(attr: &Attribute) -> Option<ContractAttrKind> {
    let path = attr.path();
    let mut segments = path.segments.iter();
    let first = segments.next()?;
    let target = match segments.next() {
        Some(second) => {
            if segments.next().is_some() || first.ident != "trust_vc" {
                return None;
            }
            &second.ident
        }
        None => &first.ident,
    };

    if target == "requires" {
        Some(ContractAttrKind::Requires)
    } else if target == "ensures" {
        Some(ContractAttrKind::Ensures)
    } else if target == "returns" {
        Some(ContractAttrKind::Returns)
    } else if target == "default_ensures" {
        Some(ContractAttrKind::DefaultEnsures)
    } else {
        None
    }
}

/// Rejects `default_ensures` anywhere it is not a defaulted trait-method
/// declaration. `default_ensures` is legal ONLY on a trait method that carries a
/// default body (harvested + gated in `parse_trait_method_decl`); on impl
/// methods, free functions, and extern/foreign specs it is ill-formed and must
/// fail the file CLOSED rather than be silently dropped by `extract_contracts`.
///
/// Returns the `"default_ensures not allowed here"` Parse error on the first
/// `default_ensures` attribute found.
pub(crate) fn forbid_default_ensures(attrs: &[Attribute]) -> TrustVcResult<()> {
    for attr in attrs {
        if contract_attr_kind(attr) == Some(ContractAttrKind::DefaultEnsures) {
            return Err(TrustVcError::Parse {
                context: "parse trait_spec contract attribute",
                source: syn::Error::new_spanned(attr, "default_ensures not allowed here"),
            });
        }
    }
    Ok(())
}

fn invalid_contract_attribute_error(
    attr: &Attribute,
    surface: &'static str,
    message: &str,
) -> TrustVcError {
    TrustVcError::Parse {
        context: contract_attribute_context(surface),
        source: syn::Error::new_spanned(attr, message),
    }
}

fn contract_attribute_context(surface: &'static str) -> &'static str {
    match surface {
        "extern_spec" => "parse extern_spec contract attribute",
        "trait_spec" => "parse trait_spec contract attribute",
        "trait_impl" => "parse trait_impl contract attribute",
        _ => "parse contract attribute",
    }
}

/// Encode a type-name component into a valid Rust identifier fragment.
///
/// Uses injective encoding so that distinct type names always produce distinct
/// identifiers (#1461, #1435). For example, `foo::bar` and `foo_bar` remain
/// distinct because `::` maps to `_P__P_` while `_` maps to `__`.
pub(crate) fn encode_ident_component(name: &str) -> String {
    let mut encoded = String::with_capacity(name.len() + 16);
    for ch in name.chars() {
        match ch {
            '_' => encoded.push_str("__"),
            ch if ch.is_ascii_alphanumeric() => encoded.push(ch),
            '<' => encoded.push_str("_LT_"),
            '>' => encoded.push_str("_GT_"),
            ',' => encoded.push_str("_C_"),
            ':' => encoded.push_str("_P_"),
            ' ' => encoded.push_str("_S_"),
            '&' => encoded.push_str("_R_"),
            '*' => encoded.push_str("_D_"),
            '(' => encoded.push_str("_LP_"),
            ')' => encoded.push_str("_RP_"),
            '[' => encoded.push_str("_LB_"),
            ']' => encoded.push_str("_RB_"),
            _ => {
                use std::fmt::Write;
                let _ = write!(encoded, "_x{:02X}_", ch as u32);
            }
        }
    }
    if encoded.is_empty() {
        encoded.push('_');
    }
    encoded
}

/// Generate a unique identifier for the extern spec stub function.
///
/// The type component uses injective encoding so names like `foo::bar` and
/// `foo_bar` remain distinct (#1461, #1435).
pub(crate) fn generate_stub_ident(type_name: &str, method_name: &str, span: Span) -> Ident {
    let clean_type = encode_ident_component(type_name);
    format_ident!(
        "__trust_vc_extern_spec_{}_{}",
        clean_type,
        method_name,
        span = span
    )
}

/// Convert a Signature's inputs to call arguments.
/// Handles both `self` receivers and typed parameters.
pub(crate) fn sig_to_call_args(sig: &Signature) -> Punctuated<syn::Expr, Comma> {
    let mut args = Punctuated::new();

    for (idx, input) in sig.inputs.iter().enumerate() {
        let expr: syn::Expr = match input {
            FnArg::Receiver(_) => syn::parse_quote!(self_),
            FnArg::Typed(PatType { pat, .. }) => {
                if let Pat::Ident(pat_ident) = pat.as_ref() {
                    let ident = &pat_ident.ident;
                    syn::parse_quote!(#ident)
                } else {
                    let placeholder = format_ident!("__unsupported_pattern_{}", idx);
                    syn::parse_quote!(#placeholder)
                }
            }
        };
        args.push(expr);
    }

    args
}

/// Syn fold that replaces bare `Self` type references with a concrete type.
///
/// Extern spec stubs are standalone functions (not inside an `impl` block),
/// so `Self` is not in scope. This folder rewrites `Self` occurrences in
/// parameter types, return types, and where-clause predicates.
struct ReplaceSelf<'a> {
    self_ty: &'a Type,
}

impl Fold for ReplaceSelf<'_> {
    fn fold_type(&mut self, ty: Type) -> Type {
        match &ty {
            Type::Path(TypePath { qself: None, path }) if path.is_ident("Self") => {
                self.self_ty.clone()
            }
            _ => syn::fold::fold_type(self, ty),
        }
    }
}

/// Transform signature to replace `self` with `self_: SelfType` and `Self`
/// with the concrete type everywhere (parameters, return type, where clauses).
///
/// Preserves lifetimes from the receiver (e.g., `&'a self` -> `self_: &'a Type`).
pub(crate) fn transform_sig_for_stub(sig: &Signature, self_ty: &Type) -> Signature {
    let mut folder = ReplaceSelf { self_ty };
    let mut new_sig = sig.clone();
    new_sig.inputs = sig
        .inputs
        .iter()
        .map(|input| match input {
            FnArg::Receiver(recv) => {
                let ty: Type = if let Some((_, lifetime)) = &recv.reference {
                    if recv.mutability.is_some() {
                        syn::parse_quote!(&#lifetime mut #self_ty)
                    } else {
                        syn::parse_quote!(&#lifetime #self_ty)
                    }
                } else {
                    self_ty.clone()
                };
                FnArg::Typed(PatType {
                    attrs: recv.attrs.clone(),
                    pat: Box::new(syn::parse_quote!(self_)),
                    colon_token: Default::default(),
                    ty: Box::new(ty),
                })
            }
            FnArg::Typed(pat_ty) => {
                let folded_ty = folder.fold_type((*pat_ty.ty).clone());
                FnArg::Typed(PatType {
                    attrs: pat_ty.attrs.clone(),
                    pat: pat_ty.pat.clone(),
                    colon_token: pat_ty.colon_token,
                    ty: Box::new(folded_ty),
                })
            }
        })
        .collect();
    new_sig.output = folder.fold_return_type(new_sig.output);
    if let Some(ref mut where_clause) = new_sig.generics.where_clause {
        where_clause.predicates = where_clause
            .predicates
            .iter()
            .map(|p| folder.fold_where_predicate(p.clone()))
            .collect();
    }
    new_sig
}

#[cfg(test)]
#[path = "extern_spec_helpers_tests.rs"]
mod tests;
