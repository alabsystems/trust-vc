//! Broadcast lemmas and trigger pattern support.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Handles `#[broadcast]` lemma expansion, `#[trigger]` pattern annotation,
//! `#[auto_trigger]`, and `#[all_triggers]` attribute expansion.

use crate::local_vars::extract_type_string;
use crate::{mode, mode_scan};
use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{Expr, ItemFn, Token};

/// Parses trigger attribute arguments into `(group, pattern)`.
///
/// Accepted forms:
/// - `trigger(pattern)` -> `(0, "pattern")`
/// - `trigger(group, pattern)` -> `(group, "pattern")`
/// - `trigger(pattern, group = group)` -> `(group, "pattern")`
///
/// If parsing does not match `group, pattern`, the entire token stream is
/// treated as the pattern with group 0 for backward compatibility.
fn parse_trigger_group_and_pattern(attr_tokens: &TokenStream) -> (u32, String) {
    let fallback = || (0, attr_tokens.to_string());
    let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
    let Ok(parts) = parser.parse2(attr_tokens.clone()) else {
        return fallback();
    };

    if parts.len() != 2 {
        return fallback();
    }

    let mut parts = parts.iter();
    let Some(first) = parts.next() else {
        return fallback();
    };
    let Some(second) = parts.next() else {
        return fallback();
    };

    if let Some(group) = parse_trigger_group_literal(first) {
        return (group, quote!(#second).to_string());
    }

    if let Some(group) = parse_named_trigger_group(second) {
        return (group, quote!(#first).to_string());
    }

    fallback()
}

fn parse_trigger_group_literal(expr: &Expr) -> Option<u32> {
    let Expr::Lit(expr_lit) = expr else {
        return None;
    };
    let syn::Lit::Int(int_lit) = &expr_lit.lit else {
        return None;
    };
    int_lit.base10_parse::<u32>().ok()
}

fn parse_named_trigger_group(expr: &Expr) -> Option<u32> {
    let Expr::Assign(assign) = expr else {
        return None;
    };
    let Expr::Path(path) = &*assign.left else {
        return None;
    };
    if !path.path.is_ident("group") {
        return None;
    }
    parse_trigger_group_literal(&assign.right)
}

/// Expands a `#[broadcast]` lemma.
///
/// Registers the lemma for automatic instantiation by the SMT solver.
/// Broadcast lemmas are universally quantified over their parameters and
/// are automatically applied when their triggers match.
///
/// # ay Encoding
///
/// For a broadcast lemma:
/// ```text
/// #[trust_vc::broadcast]
/// #[trust_vc::trigger(sum(n))]
/// fn lemma_sum_nonneg(n: u64) {
///     trust_vc::ensures!(sum(n) >= 0);
/// }
/// ```
///
/// Generates:
/// ```text
/// (assert (forall ((n Int))
///   (!  ; trigger annotation
///     (>= (sum n) 0)
///     :pattern ((sum n)))))
/// ```
///
/// # Postcondition
///
/// Output contains __trust_vc_broadcast_lemma marker for trust_mc detection.
fn expand_broadcast_params(sig: &syn::Signature) -> (Vec<TokenStream>, Vec<TokenStream>) {
    let support_root = crate::macro_support_root();
    let mut param_errors = Vec::new();
    let param_declarations = sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => match &*pat_type.pat {
                syn::Pat::Ident(pat_ident) => {
                    let param_name = pat_ident.ident.to_string();
                    let param_type = extract_type_string(&pat_type.ty);
                    Some(quote! {
                        #support_root::verify_macro::collect_variable(
                            #param_name.to_string(),
                            #param_type.to_string()
                        );
                    })
                }
                _ => {
                    let err = syn::LitStr::new(
                        &format!(
                            "trust_vc::broadcast does not support complex parameter patterns. Use simple named parameters instead of: {}",
                            quote!(#pat_type)
                        ),
                        proc_macro2::Span::call_site(),
                    );
                    param_errors.push(quote! {
                        compile_error!(#err);
                    });
                    None
                }
            },
            syn::FnArg::Receiver(_) => {
                let err = syn::LitStr::new(
                    "trust_vc::broadcast does not support self parameters. Use a free function with an explicit parameter instead.",
                    proc_macro2::Span::call_site(),
                );
                param_errors.push(quote! {
                    compile_error!(#err);
                });
                None
            }
        })
        .collect();
    (param_errors, param_declarations)
}

pub fn expand_broadcast(input: ItemFn) -> TokenStream {
    expand_broadcast_with_group(input, None)
}

pub fn expand_broadcast_with_group(input: ItemFn, group_name: Option<String>) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;
    let fn_name_str = fn_name.to_string();

    // Broadcast lemmas are proof-mode ghost code: they can call proof/spec
    // siblings and proof code may call them. Validate them through the same
    // mode checker used by #[proof].
    mode::register_compile_time_function_mode(&fn_name_str, mode::FunctionMode::Proof);
    let (_scan, mode_errors) = mode_scan::validate_mode(&input, mode::FunctionMode::Proof, block);
    if !mode_errors.is_empty() {
        return quote! { #(#mode_errors)* };
    }

    let (param_errors, param_declarations) = expand_broadcast_params(sig);
    let broadcast_marker_doc = crate::attr_doc_metadata::broadcast_marker_doc_attr();
    let broadcast_group_docs: Vec<_> = group_name
        .as_ref()
        .map(|name| {
            let value = crate::attr_doc_metadata::broadcast_group_doc_attr(name);
            quote! { #[doc = #value] }
        })
        .into_iter()
        .collect();
    let group_name_tokens = if let Some(group_name) = group_name.clone() {
        quote! { Some(#group_name.to_string()) }
    } else {
        quote! { None }
    };
    let support_root = crate::macro_support_root();

    quote! {
        #(#attrs)*
        /// Broadcast lemma - auto-applied by SMT solver
        #[doc(hidden)]
        #[doc = #broadcast_marker_doc]
        #(#broadcast_group_docs)*
        #[allow(dead_code, unused_variables)]
        #vis #sig {
            #support_root::mode::register_function_mode(
                stringify!(#fn_name),
                #support_root::mode::FunctionMode::Proof
            );

            #(#param_errors)*
            #[cfg(trust_mc)]
            {
                let __trust_vc_broadcast_lemma = stringify!(#fn_name);
                #block
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                let _broadcast_guard = #support_root::verify_macro::BroadcastGuard::enter();

                #(#param_declarations)*

                let result = { #block };

                #support_root::register_broadcast_lemma_with_group(
                    stringify!(#fn_name).to_string(),
                    #group_name_tokens,
                );

                result
            }
            #[cfg(not(any(trust_mc, test)))]
            {
                #[allow(unreachable_code)]
                if false {
                    return { #block };
                }
                loop {
                    unreachable!(concat!(
                        "broadcast lemma `",
                        stringify!(#fn_name),
                        "` called at runtime - lemmas are ghost code"
                    ));
                }
            }
        }
    }
}

/// Expands a trigger attribute with group support.
///
/// Parses the attribute to detect:
/// - trigger(pattern) - Single trigger (group 0)
/// - trigger(n, pattern) - Trigger in group n
///
/// Multiple triggers with the same group number form one trigger group.
/// A group fires only when all expressions in it match.
///
/// # Postcondition
///
/// Output contains __trust_vc_trigger_pattern with group number >= 0.
pub fn expand_trigger_with_group(input: ItemFn, attr_tokens: TokenStream) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;

    // Parse structurally instead of using string find(',') so nested commas in
    // trigger patterns are preserved (e.g. trigger(1, f(a, b))). Fixes #1838.
    let (group, pattern) = parse_trigger_group_and_pattern(&attr_tokens);
    let trigger_index = match crate::attr_doc_metadata::next_trigger_doc_index(attrs) {
        Ok(index) => index,
        Err(err) => {
            return syn::Error::new(
                sig.ident.span(),
                format!("failed to read trigger doc metadata before expansion: {err}"),
            )
            .to_compile_error();
        }
    };

    let pattern_str = &pattern;
    let trigger_group_doc =
        crate::attr_doc_metadata::trigger_group_doc_attr(trigger_index, group as usize);
    let trigger_pattern_doc =
        crate::attr_doc_metadata::trigger_pattern_doc_attr(trigger_index, pattern_str);
    let support_root = crate::macro_support_root();

    quote! {
        #(#attrs)*
        #[doc = #trigger_group_doc]
        #[doc = #trigger_pattern_doc]
        #[allow(unused_variables)]
        #vis #sig {
            #[cfg(trust_mc)]
            {
                let __trust_vc_trigger_group = #group;
                let __trust_vc_trigger_pattern = #pattern;
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #support_root::verify_macro::register_trigger(
                    #group,
                    #pattern_str.to_string(),
                );
            }
            #block
        }
    }
}

/// Expands a `#[auto_trigger]` annotation.
///
/// Marks the function for conservative automatic trigger selection.
pub fn expand_auto_trigger(input: ItemFn) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let support_root = crate::macro_support_root();
    let trigger_mode_doc = crate::attr_doc_metadata::trigger_mode_doc_attr(
        crate::attr_doc_metadata::TriggerModeDoc::Conservative,
    );

    quote! {
        #(#attrs)*
        #[doc = #trigger_mode_doc]
        #vis #sig {
            #[cfg(trust_mc)]
            {
                #[allow(unused_variables)]
                let __trust_vc_auto_trigger_marker = "trust_vc_runtime::__trigger::auto_conservative";
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #support_root::set_trigger_inference_mode(
                    #support_root::TriggerInferenceMode::Conservative,
                );
            }
            #block
        }
    }
}

/// Expands a `#[all_triggers]` annotation.
///
/// Marks the function for aggressive automatic trigger selection.
pub fn expand_all_triggers(input: ItemFn) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let support_root = crate::macro_support_root();
    let trigger_mode_doc = crate::attr_doc_metadata::trigger_mode_doc_attr(
        crate::attr_doc_metadata::TriggerModeDoc::Aggressive,
    );

    quote! {
        #(#attrs)*
        #[doc = #trigger_mode_doc]
        #vis #sig {
            #[cfg(trust_mc)]
            {
                #[allow(unused_variables)]
                let __trust_vc_all_triggers_marker = "trust_vc_runtime::__trigger::auto_aggressive";
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #support_root::set_trigger_inference_mode(
                    #support_root::TriggerInferenceMode::Aggressive,
                );
            }
            #block
        }
    }
}

#[cfg(test)]
#[path = "broadcast_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "broadcast_expansion_tests.rs"]
mod expansion_tests;
