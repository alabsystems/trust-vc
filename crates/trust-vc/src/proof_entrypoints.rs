// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-family proc-macro entrypoint helpers.

use proc_macro::TokenStream;
use quote::quote;

use crate::macro_expand;

pub(crate) fn assume(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_assume(expr))
}

pub(crate) fn assert(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input.clone());

    let parsed_expr: syn::Expr = match trust_vc_core::parse_expr_tokens_with_chains(expr.clone()) {
        Ok(expr) => expr,
        Err(err) => {
            let err_msg = format!("Failed to parse assertion: {}", err);
            return TokenStream::from(quote! {
                compile_error!(#err_msg);
            });
        }
    };

    TokenStream::from(macro_expand::expand_assert(expr, &parsed_expr))
}

pub(crate) fn requires(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_requires(expr))
}

pub(crate) fn recommends(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_recommends(expr))
}

pub(crate) fn cite(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_cite_tokens(tokens))
}

pub(crate) fn ghost_requires(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_ghost_requires(expr))
}

pub(crate) fn ghost_ensures(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_ghost_ensures(expr))
}

pub(crate) fn ensures(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_ensures(expr))
}

pub(crate) fn proof_block(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_proof_block(tokens))
}

pub(crate) fn old(input: TokenStream) -> TokenStream {
    let expr = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_old(expr))
}

pub(crate) fn track_let(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_track_let(tokens))
}

pub(crate) fn reveal(input: TokenStream) -> TokenStream {
    let name: syn::Ident = match syn::parse(input) {
        Ok(ident) => ident,
        Err(err) => {
            let err_msg = format!("reveal! expects a function name: {}", err);
            return TokenStream::from(quote! {
                compile_error!(#err_msg);
            });
        }
    };
    let name_str = name.to_string();
    let support_root = trust_vc_core::macro_support_root();

    TokenStream::from(quote! {
        #support_root::push_reveal_or_group(#name_str);
    })
}

pub(crate) fn hide(input: TokenStream) -> TokenStream {
    let name: syn::Ident = match syn::parse(input) {
        Ok(ident) => ident,
        Err(err) => {
            let err_msg = format!("hide! expects a function name: {}", err);
            return TokenStream::from(quote! {
                compile_error!(#err_msg);
            });
        }
    };
    let name_str = name.to_string();
    let support_root = trust_vc_core::macro_support_root();

    TokenStream::from(quote! {
        #support_root::push_hide(#name_str);
    })
}

pub(crate) fn broadcast_use(input: TokenStream) -> TokenStream {
    let group_name: syn::Ident = match syn::parse(input) {
        Ok(ident) => ident,
        Err(err) => {
            let err_msg = format!("broadcast_use! expects a group name: {}", err);
            return TokenStream::from(quote! {
                compile_error!(#err_msg);
            });
        }
    };
    let group_name_str = group_name.to_string();
    let support_root = trust_vc_core::macro_support_root();

    TokenStream::from(quote! {
        #support_root::register_broadcast_use_or_group(#group_name_str);
    })
}

/// Reveals or defines a named group of opaque functions.
///
/// Two syntaxes:
/// - **Named definition:** `reveal_group!(group_name { fn1, fn2, fn3 })` — emits
///   a manifest entry at module scope for later runtime lookup.
/// - **Inline reveal (legacy):** `reveal_group!(fn1, fn2, fn3)` — desugars to
///   individual `push_reveal()` calls (backward compatible).
///
/// Disambiguated by checking whether the first ident is followed by `{`.
/// Part of #2495.
pub(crate) fn reveal_group_impl(input: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    use proc_macro2::Delimiter;
    use syn::punctuated::Punctuated;
    let support_root = trust_vc_core::macro_support_root();

    // Try the named-definition syntax first: `name { fn1, fn2, ... }`
    let mut iter = input.clone().into_iter().peekable();

    if let Some(proc_macro2::TokenTree::Ident(group_ident)) = iter.peek() {
        let group_name = group_ident.to_string();
        let _ident = iter.next(); // consume the ident
        if let Some(proc_macro2::TokenTree::Group(group)) = iter.next() {
            if group.delimiter() == Delimiter::Brace {
                if iter.next().is_some() {
                    let err_msg = "reveal_group! named definition does not accept trailing tokens after the member list";
                    return quote! {
                        compile_error!(#err_msg);
                    };
                }

                // Named definition: parse the braced member list.
                let inner = group.stream();
                let members: Punctuated<syn::Ident, syn::Token![,]> =
                    match syn::parse::Parser::parse2(Punctuated::parse_terminated, inner) {
                        Ok(names) => names,
                        Err(err) => {
                            let err_msg = format!(
                                "reveal_group! named definition expects {{ fn1, fn2, ... }}: {}",
                                err,
                            );
                            return quote! {
                                compile_error!(#err_msg);
                            };
                        }
                    };

                let member_names: Vec<String> = members.iter().map(|id| id.to_string()).collect();

                return quote! {
                    #support_root::inventory::submit! {
                        #support_root::NamedRevealGroupDef {
                            name: #group_name,
                            members: &[#(#member_names),*],
                        }
                    }
                };
            }
        }
    }

    // Fall through to inline reveal syntax: `reveal_group!(fn1, fn2, fn3)`
    let fn_names: Punctuated<syn::Ident, syn::Token![,]> =
        match syn::parse::Parser::parse2(Punctuated::parse_terminated, input) {
            Ok(names) => names,
            Err(err) => {
                let err_msg = format!(
                    "reveal_group! expects comma-separated function names: {}",
                    err
                );
                return quote! {
                    compile_error!(#err_msg);
                };
            }
        };

    if fn_names.is_empty() {
        return quote! {
            compile_error!("reveal_group! requires at least one function name");
        };
    }

    let reveals: Vec<_> = fn_names
        .iter()
        .map(|name| {
            let name_str = name.to_string();
            quote! {
                #support_root::verify_macro::push_reveal(#name_str);
            }
        })
        .collect();

    quote! { #(#reveals)* }
}

pub(crate) fn reveal_group(input: TokenStream) -> TokenStream {
    TokenStream::from(reveal_group_impl(input.into()))
}

pub(crate) fn assume_by(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);

    // Two-argument form: assume_by!(condition, { block })
    // Single-argument form: assume_by!(condition) — equivalent to assume!()
    match trust_vc_core::parse_assert_by(tokens) {
        trust_vc_core::AssertByParsed::WithProofBlock {
            condition,
            proof_block,
        } => TokenStream::from(macro_expand::expand_assume_by_with_block(
            condition,
            proof_block,
        )),
        trust_vc_core::AssertByParsed::Single {
            tokens: _,
            condition,
        } => {
            // Single-arg: desugar to assume!(condition)
            TokenStream::from(macro_expand::expand_assume(condition))
        }
        _ => TokenStream::from(quote! {
            compile_error!("unsupported assume_by! form returned by trust_vc_core::parse_assert_by");
        }),
    }
}

pub(crate) fn assert_by(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);

    // Detect Verus-style two-argument form: assert_by!(condition, { proof_block })
    match trust_vc_core::parse_assert_by(tokens) {
        trust_vc_core::AssertByParsed::WithProofBlock {
            condition,
            proof_block,
        } => TokenStream::from(macro_expand::expand_assert_by_with_proof_block(
            condition,
            proof_block,
        )),
        trust_vc_core::AssertByParsed::Single { tokens, condition } => {
            TokenStream::from(macro_expand::expand_assert_by(tokens, condition))
        }
        _ => TokenStream::from(quote! {
            compile_error!("unsupported assert_by! form returned by trust_vc_core::parse_assert_by");
        }),
    }
}

pub(crate) fn assert_forall_by(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);

    match trust_vc_core::parse_assert_forall_by(tokens) {
        Ok(parsed) => TokenStream::from(macro_expand::expand_assert_forall_by(parsed)),
        Err(err) => TokenStream::from(err.to_compile_error()),
    }
}

pub(crate) fn assert_by_contradiction(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);

    match trust_vc_core::parse_assert_by(tokens) {
        trust_vc_core::AssertByParsed::WithProofBlock {
            condition,
            proof_block,
        } => TokenStream::from(macro_expand::expand_assert_by_contradiction(
            condition,
            proof_block,
        )),
        trust_vc_core::AssertByParsed::Single { .. } => TokenStream::from(quote! {
            compile_error!(
                "assert_by_contradiction! requires the form assert_by_contradiction!(condition, { proof_block })"
            );
        }),
        _ => TokenStream::from(quote! {
            compile_error!(
                "unsupported assert_by_contradiction! form returned by trust_vc_core::parse_assert_by"
            );
        }),
    }
}

pub(crate) fn calc(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_calc(tokens))
}

pub(crate) fn open_local_invariant(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(macro_expand::expand_open_local_invariant(tokens))
}

#[cfg(test)]
mod tests {
    use super::reveal_group_impl;
    use quote::quote;

    #[test]
    fn test_reveal_group_named_definition_rejects_trailing_tokens() {
        let expanded = reveal_group_impl(quote!(bundle { alpha } trailing)).to_string();
        assert!(
            expanded.contains("compile_error !"),
            "named reveal_group definitions must fail closed on trailing tokens, got: {expanded}"
        );
        assert!(
            expanded.contains("does not accept trailing tokens"),
            "named reveal_group trailing-token diagnostic should explain the failure, got: {expanded}"
        );
    }

    #[test]
    fn test_reveal_group_inline_syntax_still_expands_to_member_reveals() {
        let expanded = reveal_group_impl(quote!(alpha, beta)).to_string();
        assert!(
            expanded.contains("push_reveal"),
            "inline reveal_group syntax should still emit reveal registrations, got: {expanded}"
        );
        assert!(
            !expanded.contains("compile_error !"),
            "inline reveal_group syntax must remain valid, got: {expanded}"
        );
    }
}
