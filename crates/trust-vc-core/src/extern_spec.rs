// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `extern_spec!` macro for specifying contracts on external functions.
//!
//! This macro allows users to attach specifications to functions they don't own
//! (e.g., standard library functions). The specs are registered at compile time
//! and discovered by trust_mc during verification.
//!
//! # Syntax
//!
//! Generic types require turbofish syntax (`Type::<T>`). This is a Rust
//! language constraint: the compiler's parser interprets `<` as a comparison
//! operator in proc-macro input, so `Option<T>` is rejected before the macro
//! runs. Turbofish (`Option::<T>`) disambiguates. Part of #945.
//!
//! ```text
//! use trust_vc::extern_spec;
//!
//! extern_spec! {
//!     impl<T> core::option::Option::<T> {
//!         #[requires(self.is_some())]
//!         #[ensures(Some(result) == old(self))]
//!         fn unwrap(self) -> T;
//!     }
//! }
//! ```
//!
//! # Design
//!
//! Specs are parsed from the `extern_spec!` body, normalized against the target
//! signature, and registered so the verification engine can attach them at the
//! call site without owning the external function's source.

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    braced,
    parse::{Parse, ParseStream},
    spanned::Spanned,
    Attribute, Generics, Path, PathArguments, Result, Signature, Token, Type, TypePath,
};

use crate::error::{TrustVcError, TrustVcResult};
use crate::extern_spec_helpers::{
    extract_contracts, extract_param_names, forbid_default_ensures, generate_stub_ident,
    sig_to_call_args, transform_sig_for_stub, type_to_path_string,
};

/// Parsed extern_spec! input containing one or more impl blocks.
pub struct ExternSpecInput {
    items: Vec<ExternImplBlock>,
}

/// Projected extern_spec data reused by the runtime registry bridge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParsedExternSpecEntry {
    pub(crate) target_path: String,
    pub(crate) param_names: Vec<String>,
    pub(crate) requires: Vec<String>,
    pub(crate) ensures: Vec<String>,
}

/// An impl block within extern_spec! containing methods with contracts.
struct ExternImplBlock {
    generics: Generics,
    self_ty: Type,
    methods: Vec<ExternMethod>,
}

/// A single method declaration with contracts.
struct ExternMethod {
    attrs: Vec<Attribute>,
    sig: Signature,
}

impl Parse for ExternSpecInput {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(ExternSpecInput { items })
    }
}

impl Parse for ExternImplBlock {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let _impl_token: Token![impl] = input.parse()?;

        // Parse optional generics: impl<T> Type<T> { ... }
        let generics: Generics = input.parse()?;

        // Parse the type being implemented
        let self_ty: Type = input.parse()?;

        // Parse the brace-delimited method list
        let content;
        let _brace = braced!(content in input);

        let mut methods = Vec::new();
        while !content.is_empty() {
            methods.push(content.parse()?);
        }

        Ok(ExternImplBlock {
            generics,
            self_ty,
            methods,
        })
    }
}

impl Parse for ExternMethod {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let sig: Signature = input.parse()?;
        let _semi: Token![;] = input.parse()?;
        Ok(ExternMethod { attrs, sig })
    }
}

fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn render_metadata_path_arguments(arguments: &PathArguments) -> Option<String> {
    match arguments {
        PathArguments::None => Some(String::new()),
        PathArguments::AngleBracketed(arguments) => {
            let args = arguments
                .args
                .iter()
                .map(|arg| collapse_whitespace(&arg.to_token_stream().to_string()))
                .collect::<Vec<_>>();
            Some(format!("::<{}>", args.join(", ")))
        }
        PathArguments::Parenthesized(_) => None,
    }
}

fn render_metadata_type_path(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(TypePath { qself: None, path }) => render_metadata_path(path),
        _ => None,
    }
}

fn render_metadata_path(path: &Path) -> Option<String> {
    let mut rendered = String::new();
    if path.leading_colon.is_some() {
        rendered.push_str("::");
    }

    for (index, segment) in path.segments.iter().enumerate() {
        if index > 0 {
            rendered.push_str("::");
        }
        rendered.push_str(&segment.ident.to_string());
        rendered.push_str(&render_metadata_path_arguments(&segment.arguments)?);
    }

    Some(rendered)
}

fn trust_vc_error_into_syn_error(err: TrustVcError) -> syn::Error {
    match err {
        TrustVcError::Parse { source, .. } => source,
        other => syn::Error::new(Span::call_site(), other.to_string()),
    }
}

fn unsupported_target_type_error(self_ty: &Type) -> TrustVcError {
    TrustVcError::Parse {
        context: "parse extern_spec target type",
        source: syn::Error::new_spanned(
            self_ty,
            "extern_spec! requires a simple type path (e.g., `Option::<T>`, `std::vec::Vec::<T>`). \
             Qualified paths like `<T as Trait>::Assoc` are not supported.",
        ),
    }
}

fn build_target_path(self_ty: &Type, method_name: &str) -> TrustVcResult<String> {
    match render_metadata_type_path(self_ty) {
        Some(type_name) => Ok(format!("{type_name}::{method_name}")),
        None => Err(unsupported_target_type_error(self_ty)),
    }
}

pub(crate) fn try_project_extern_spec_entries(
    input: ExternSpecInput,
) -> TrustVcResult<Vec<ParsedExternSpecEntry>> {
    let mut entries = Vec::new();

    for impl_block in input.items {
        for method in impl_block.methods {
            let target_path =
                build_target_path(&impl_block.self_ty, &method.sig.ident.to_string())?;
            // Foreign default bodies are Phase B; `default_ensures` on an
            // extern/foreign spec is rejected for now (fail closed).
            forbid_default_ensures(&method.attrs)?;
            let param_names = extract_param_names(&method.sig, "extern_spec")?;
            let (requires, ensures) = extract_contracts(&method.attrs, "extern_spec")?;
            entries.push(ParsedExternSpecEntry {
                target_path,
                param_names,
                requires,
                ensures,
            });
        }
    }

    Ok(entries)
}

fn build_stub_signature(
    impl_generics: &Generics,
    method: &ExternMethod,
    self_ty: &Type,
    stub_ident: syn::Ident,
) -> Signature {
    let mut stub_sig = transform_sig_for_stub(&method.sig, self_ty);
    stub_sig.ident = stub_ident;

    let mut merged_generics = impl_generics.clone();
    for param in &method.sig.generics.params {
        merged_generics.params.push(param.clone());
    }
    if let Some(where_clause) = method.sig.generics.where_clause.as_ref() {
        if let Some(existing_where) = merged_generics.where_clause.as_mut() {
            existing_where
                .predicates
                .extend(where_clause.predicates.clone());
        } else {
            merged_generics.where_clause = Some(where_clause.clone());
        }
    }
    stub_sig.generics = merged_generics;
    stub_sig
}

fn expand_method_stub(
    impl_generics: &Generics,
    self_ty: &Type,
    type_name: &str,
    method: &ExternMethod,
) -> TrustVcResult<TokenStream> {
    let span = method.sig.span();
    let method_name = method.sig.ident.to_string();
    let target_path = build_target_path(self_ty, &method_name)?;
    // Foreign default bodies are Phase B; reject `default_ensures` on an
    // extern/foreign spec for now (fail closed) rather than silently drop it.
    forbid_default_ensures(&method.attrs)?;
    let (requires, ensures) = extract_contracts(&method.attrs, "extern_spec")?;
    let stub_ident = generate_stub_ident(type_name, &method_name, span);
    let stub_sig = build_stub_signature(impl_generics, method, self_ty, stub_ident);
    let call_args = sig_to_call_args(&method.sig);
    let method_ident = &method.sig.ident;
    let call_expr = quote_spanned! {span=> #self_ty :: #method_ident(#call_args) };
    let target_doc = format!("trust_vc:extern_spec:target={}", target_path);
    let requires_doc = format!("trust_vc:extern_spec:requires={}", requires.join("; "));
    let ensures_doc = format!("trust_vc:extern_spec:ensures={}", ensures.join("; "));
    let other_attrs: Vec<_> = method
        .attrs
        .iter()
        .filter(|attr| {
            attr.path()
                .get_ident()
                .is_none_or(|id| id != "requires" && id != "ensures")
        })
        .collect();

    Ok(quote_spanned! {span=>
        #[doc(hidden)]
        #[doc = #target_doc]
        #[doc = #requires_doc]
        #[doc = #ensures_doc]
        #[allow(dead_code, non_snake_case, unused_variables)]
        #(#other_attrs)*
        #stub_sig {
            #call_expr
        }
    })
}

/// Generate the expansion for one impl block.
fn try_expand_impl_block(impl_block: ExternImplBlock) -> TrustVcResult<TokenStream> {
    let type_name = type_to_path_string(&impl_block.self_ty)
        .ok_or_else(|| unsupported_target_type_error(&impl_block.self_ty))?;

    let mut output = TokenStream::new();
    for method in &impl_block.methods {
        output.extend(expand_method_stub(
            &impl_block.generics,
            &impl_block.self_ty,
            &type_name,
            method,
        )?);
    }

    Ok(output)
}

fn expand_impl_block(impl_block: ExternImplBlock) -> Result<TokenStream> {
    try_expand_impl_block(impl_block).map_err(trust_vc_error_into_syn_error)
}

/// Main entry point for extern_spec! macro expansion.
pub fn expand_extern_spec(input: ExternSpecInput) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    for impl_block in input.items {
        output.extend(expand_impl_block(impl_block)?);
    }

    // Wrap in a const block to avoid polluting the namespace
    Ok(quote! {
        const _: () = {
            #output
        };
    })
}

#[cfg(test)]
mod tests;
