// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Expansion logic for trust_vc core function-like proc macros.
//!
//! Handles: assume, assert, requires, ensures, proof_block, old, track_let,
//! assert_by (single-arg and Verus-style two-arg), assume_by, assert_by_contradiction.
//! Solver-mode and quantifier expansions are in `macro_expand_ext.rs`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;

use trust_vc_core::{expr_to_try_builder_tokens, parse_expr_tokens_with_chains};

mod assert_by;
mod invariant;
mod obligations;

#[cfg(test)]
mod tests;

pub(crate) use assert_by::{
    expand_assert_by, expand_assert_by_contradiction, expand_assert_by_with_proof_block,
    expand_assert_forall_by, expand_assume_by_with_block, expand_calc,
};
pub(crate) use invariant::expand_open_local_invariant;
pub(crate) use obligations::{
    expand_assert, expand_assert_seqs_equal, expand_assume, expand_cite, expand_cite_tokens,
    expand_ensures, expand_ghost_ensures, expand_ghost_requires, expand_old, expand_proof_block,
    expand_recommends, expand_requires, expand_track_let,
};

/// Extracts the citation reference text from a `cite` clause / `cite!` second
/// argument. Accepts a string literal (`"lemma 4.2"`) or a path to an external
/// proof/lemma/source (`proofs::seq::len_nonneg`).
pub(crate) fn cite_reference_string(expr: &syn::Expr) -> syn::Result<String> {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(lit_str),
            ..
        }) => Ok(lit_str.value()),
        syn::Expr::Path(path) => Ok(quote!(#path).to_string()),
        other => Err(syn::Error::new_spanned(
            other,
            "cite citation reference must be a string literal or a path to an \
             external proof/lemma/source",
        )),
    }
}

/// Converts expression tokens into a canonicalized AST string at macro expansion
/// time, avoiding runtime `stringify!` collection paths.
pub(crate) fn canonical_expr_ast_string(expr: &proc_macro2::TokenStream) -> String {
    parse_expr_with_chains(expr)
        .map(|parsed| quote!(#parsed).to_string())
        .unwrap_or_else(|_| expr.to_string())
}

pub(crate) fn parse_expr_with_chains(expr: &proc_macro2::TokenStream) -> syn::Result<syn::Expr> {
    parse_expr_tokens_with_chains(expr.clone())
}

pub(crate) fn normalize_expr_tokens(
    expr: &proc_macro2::TokenStream,
) -> syn::Result<proc_macro2::TokenStream> {
    parse_expr_with_chains(expr).map(|parsed| quote!(#parsed))
}

#[allow(clippy::indexing_slicing)] // invariant: `trees[..index]`/`trees[index+1..]` bounded by `position()` return within `trees.len()`
fn split_macro_expr_and_tail(
    tokens: proc_macro2::TokenStream,
) -> (proc_macro2::TokenStream, Option<proc_macro2::TokenStream>) {
    let trees: Vec<proc_macro2::TokenTree> = tokens.into_iter().collect();
    let split = trees.iter().position(|tree| {
        matches!(
            tree,
            proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ','
        )
    });

    match split {
        Some(index) => (
            trees[..index].iter().cloned().collect(),
            Some(trees[index + 1..].iter().cloned().collect()),
        ),
        None => (trees.into_iter().collect(), None),
    }
}

/// Generates the obligation collection call for a given expression.
///
/// Tries the typed `TrustVcExpr` path first (Phase 5 Step 3b). Falls back to
/// string-based `collect_typed_obligation` for unsupported expression forms.
/// The `kind_tokens` parameter is the `ObligationKind` variant tokens.
/// The `name_prefix` is used to generate unique obligation names.
pub(crate) fn generate_obligation_collection(
    expr_tokens: &proc_macro2::TokenStream,
    ast_string: &str,
    kind_tokens: proc_macro2::TokenStream,
    name_prefix: &str,
) -> proc_macro2::TokenStream {
    let support_root = trust_vc_core::macro_support_root();
    let parsed = parse_expr_with_chains(expr_tokens).ok();
    let try_builder = parsed.as_ref().and_then(expr_to_try_builder_tokens);

    if let Some(builder) = try_builder {
        // Generated tokens produce Option<TrustVcExpr>. If variable type lookup
        // fails at runtime, falls back to string path. Fixes #2233.
        // Keys use line+column for uniqueness on same-line obligations. Part of #2652.
        quote! {
            if let Some(__trust_vc_expr) = { #builder } {
                #support_root::verify_macro::collect_obligation_expr(
                    #kind_tokens,
                    format!("{}{}_col_{}", #name_prefix, line!(), column!()),
                    #ast_string.to_string(),
                    __trust_vc_expr,
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            } else {
                #support_root::verify_macro::collect_typed_obligation(
                    #kind_tokens,
                    format!("{}{}_col_{}", #name_prefix, line!(), column!()),
                    #ast_string.to_string(),
                    Some(format!("{}:{}:{}", file!(), line!(), column!())),
                );
            }
        }
    } else {
        quote! {
            #support_root::verify_macro::collect_typed_obligation(
                #kind_tokens,
                format!("{}{}_col_{}", #name_prefix, line!(), column!()),
                #ast_string.to_string(),
                Some(format!("{}:{}:{}", file!(), line!(), column!())),
            );
        }
    }
}
