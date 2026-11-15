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
    let parsed = parse_expr_with_chains(expr)?;
    let tokens = quote!(#parsed);
    reject_mut_ref_final_marker(expr, &tokens)?;
    Ok(tokens)
}

/// Refuse the parse-time marker for the reserved-keyword spec op `final(..)`
/// BEFORE it can be emitted into a runtime `assert!`.
///
/// `final(..)` SURVIVES the parse: `trust_vc_core` rewrites the
/// reserved keyword to `MUT_REF_FINAL_MARKER` so the clause is parseable at all.
/// That marker is resolved, with clause context, by the file-check path's
/// two-state resolver; there is no runtime function behind it. Emitting it into
/// a runtime obligation compiles to `error[E0425]: cannot find function
/// `__trust_vc_mut_ref_final``, which names a symbol the author never wrote —
/// strictly worse than the pre-rewrite "expected an expression".
///
/// `normalize_expr_tokens` above is the SHARED token path (`requires!`,
/// `assume!`, `invariant!`, `recommends!`, `assert_by`/`calc` operands, …);
/// `postcondition_lowering::normalize_expr_tokens` (the `ensures` path) and
/// `proof_entrypoints::assert` (which parses its own tokens and never reaches
/// either normalizer) call this helper directly. Every surface is pinned in
/// `tests/compile-fail/mut_ref_final_*.rs`.
pub(crate) fn reject_mut_ref_final_marker(
    source: &proc_macro2::TokenStream,
    normalized: &proc_macro2::TokenStream,
) -> syn::Result<()> {
    if !normalized
        .to_string()
        .contains(trust_vc_core::MUT_REF_FINAL_MARKER)
    {
        return Ok(());
    }
    let span = source
        .clone()
        .into_iter()
        .next()
        .map_or_else(proc_macro2::Span::call_site, |tt| tt.span());
    Err(syn::Error::new(
        span,
        "`final(..)` is a `&mut` two-state contract op resolved by the \
         verification path (`cargo trust-vc check`), and has no runtime \
         meaning to expand into an obligation. It is supported in a function \
         contract clause over a supported scalar `&mut` parameter \
         (`final`/`mut_ref_future` in `ensures`; `mut_ref_current`/`old` in \
         either). Write the postcondition over the bare `&mut` parameter \
         (which already denotes its final value there), or verify this \
         function through the verification path",
    ))
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
