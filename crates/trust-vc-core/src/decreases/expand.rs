//! Proc-macro expansion entrypoints for `#[decreases]` and `#[via_fn]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Contains the three public entrypoints that the `trust_vc` proc-macro crate
//! calls: `expand_decreases`, `expand_decreases_with_clauses`, `expand_via_fn`.

use crate::local_vars::extract_type_string;
use crate::mode_index;
use crate::recursion_graph;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse::Parser, spanned::Spanned, ItemFn};

use super::clause::parse_decreases_clauses;
use super::measure_shape::{
    analyze_measure_plan, render_unsupported_recursive_measure_condition, MeasurePlan,
};
use super::transform::transform_body_with_checks;

fn collect_param_declarations(sig: &syn::Signature) -> Vec<TokenStream> {
    let support_root = crate::macro_support_root();
    sig.inputs
        .iter()
        .filter_map(|arg| {
            let syn::FnArg::Typed(pat_type) = arg else {
                return None;
            };
            let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                return None;
            };

            let param_name = pat_ident.ident.to_string();
            let param_type = extract_type_string(&pat_type.ty);
            Some(quote! {
                #support_root::verify_macro::collect_variable(
                    #param_name.to_string(),
                    #param_type.to_string()
                );
            })
        })
        .collect()
}

fn collect_param_idents(sig: &syn::Signature) -> Vec<syn::Ident> {
    sig.inputs
        .iter()
        .filter_map(|arg| {
            let syn::FnArg::Typed(pat_type) = arg else {
                return None;
            };
            let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                return None;
            };

            Some(pat_ident.ident.clone())
        })
        .collect()
}

/// Expands a `#[decreases(measure)]` or `#[decreases(m1, m2, ...)]` function.
///
/// Note: This simpler API without when/via is currently unused - the proc macro
/// uses `expand_decreases_with_clauses` instead. Kept for potential future use.
///
/// # Termination Verification
///
/// For a recursive function with single measure `m`:
/// 1. At each call site, verify `m >= 0` (measure is non-negative)
/// 2. At each recursive call, verify `m_new < m_old` (measure decreases)
///
/// For lexicographic measures `(m1, m2, ...)`:
/// 1. At each call site, verify all measures are non-negative
/// 2. At each recursive call, verify lexicographic decrease:
///    - Either m1_new < m1_old, OR
///    - m1_new == m1_old AND m2_new < m2_old, OR
///    - m1_new == m1_old AND m2_new == m2_old AND m3_new < m3_old, etc.
///
/// # ay Encoding (Lexicographic)
///
/// For `#[decreases(m, n)]`:
/// ```text
/// ; Either first measure decreases
/// (assert (or (< m' m)
/// ; Or first stays same AND second decreases
///             (and (= m' m) (< n' n))))
/// ; All measures non-negative
/// (assert (and (>= m' 0) (>= n' 0)))
/// ```
///
/// # Precondition
///
/// measures must be non-empty (at least one measure expression).
pub fn expand_decreases(input: ItemFn, measures: TokenStream) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let _fn_name = &sig.ident;
    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    let parsed_measures = parser.parse2(measures.clone());
    let entry_expr = match parsed_measures {
        Ok(parsed) if parsed.is_empty() => {
            return syn::Error::new(
                proc_macro2::Span::call_site(),
                "#[trust_vc::decreases] requires at least one measure expression",
            )
            .to_compile_error();
        }
        Ok(parsed) if parsed.len() == 1 => match parsed.iter().next() {
            Some(measure) => quote!(#measure),
            None => {
                return syn::Error::new(
                    input.span(),
                    "internal error: parsed had len 1 but iter was empty",
                )
                .to_compile_error();
            }
        },
        Ok(parsed) => quote!((#parsed)),
        Err(err) => return err.to_compile_error(),
    };
    let entry_doc_attr =
        crate::attr_doc_metadata::decreases_entry_doc_attr(&quote!(#entry_expr).to_string());

    quote! {
        #(#attrs)*
        #[doc = #entry_doc_attr]
        /// Function with termination proof via decreasing measure(s)
        #[allow(dead_code, unused_variables)]
        #vis #sig {
            // Termination measure(s) for verification
            #[cfg(trust_mc)]
            {
                let __trust_vc_measures_entry = &(#entry_expr);
            }

            // Execute function body normally
            #block
        }
    }
}

/// Expands a `#[decreases(...)]` with support for when/via clauses.
///
/// # Extended Syntax
///
/// ```text
/// #[trust_vc::decreases(measure)]
/// #[trust_vc::decreases(m1, m2, ...)]
/// #[trust_vc::decreases(measure, when = condition)]
/// #[trust_vc::decreases(measure, via = proof_fn)]
/// #[trust_vc::decreases(measure, when = condition, via = proof_fn)]
/// ```
///
/// # Precondition
///
/// attr_tokens must contain at least one measure expression.
pub fn expand_decreases_with_clauses(input: ItemFn, attr_tokens: TokenStream) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;

    let clause = parse_decreases_clauses(attr_tokens);
    let measures = clause.measures;
    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    let parsed_measures = parser.parse2(measures.clone());
    let measure_plan = parsed_measures
        .as_ref()
        .ok()
        .map(|parsed| analyze_measure_plan(sig, parsed));
    let entry_expr = match parsed_measures {
        Ok(ref parsed) if parsed.is_empty() => {
            return syn::Error::new(
                proc_macro2::Span::call_site(),
                "#[trust_vc::decreases] requires at least one measure expression",
            )
            .to_compile_error();
        }
        Ok(ref parsed) if parsed.len() == 1 => match parsed.iter().next() {
            Some(measure) => quote!(#measure),
            None => {
                return syn::Error::new(
                    input.span(),
                    "internal error: parsed had len 1 but iter was empty",
                )
                .to_compile_error();
            }
        },
        Ok(ref parsed) if parsed.len() > 1 => {
            quote!((#parsed))
        }
        Ok(_) => quote!(#measures),
        Err(err) => return err.to_compile_error(),
    };

    // Generate MeasureNonNegative obligations for each measure component (#2361).
    // Without non-negativity, decrease over signed integers is not well-founded.
    // When a `when` condition is present, non-negativity is only required when
    // the condition holds — otherwise the function doesn't recurse (#1188).
    let when_condition_str = clause
        .when_condition
        .as_ref()
        .map(|cond| quote!(#cond).to_string());
    let support_root = crate::macro_support_root();
    let nonneg_obligations: Vec<TokenStream> = match &parsed_measures {
        Ok(parsed) => {
            let component_conditions: Vec<String> = match measure_plan.as_ref() {
                Some(MeasurePlan::RecursiveAware(components)) => components
                    .iter()
                    .map(|component| {
                        let entry_expr = if component.recursive_datatype {
                            format!("__trust_vc_dt_size({})", component.param_name)
                        } else {
                            component.param_name.clone()
                        };
                        if let Some(ref when_str) = when_condition_str {
                            format!("(!({})) || ({} >= 0)", when_str, entry_expr)
                        } else {
                            format!("{} >= 0", entry_expr)
                        }
                    })
                    .collect(),
                Some(MeasurePlan::UnsupportedRecursiveDatatype) => parsed
                    .iter()
                    .map(|_| {
                        render_unsupported_recursive_measure_condition(
                            when_condition_str.as_deref(),
                        )
                    })
                    .collect(),
                _ => parsed
                    .iter()
                    .map(|component| {
                        let raw_nonneg = format!("{} >= 0", quote!(#component));
                        if let Some(ref when_str) = when_condition_str {
                            format!("(!({})) || ({})", when_str, raw_nonneg)
                        } else {
                            raw_nonneg
                        }
                    })
                    .collect(),
            };

            component_conditions
                .into_iter()
                .enumerate()
                .map(|(i, nonneg_condition)| {
                    let fn_name_str_val = fn_name.to_string();
                    let try_builder = syn::parse_str::<syn::Expr>(&nonneg_condition)
                        .ok()
                        .as_ref()
                        .and_then(crate::expr_codegen::expr_to_try_builder_tokens);
                    if let Some(builder) = try_builder {
                        quote! {
                            if let Some(__trust_vc_nonneg_expr) = { #builder } {
                                #support_root::verify_macro::collect_obligation_expr(
                                    #support_root::vc::ObligationKind::MeasureNonNegative,
                                    format!("{}:measure_nonneg_{}", #fn_name_str_val, #i),
                                    #nonneg_condition.to_string(),
                                    __trust_vc_nonneg_expr,
                                    Some(format!("{}:{}", file!(), line!()))
                                );
                            } else {
                                #support_root::verify_macro::collect_obligation(
                                    #support_root::vc::ObligationKind::MeasureNonNegative,
                                    format!("{}:measure_nonneg_{}", #fn_name_str_val, #i),
                                    #nonneg_condition.to_string(),
                                    Some(format!("{}:{}", file!(), line!()))
                                );
                            }
                        }
                    } else {
                        quote! {
                            #support_root::verify_macro::collect_obligation(
                                #support_root::vc::ObligationKind::MeasureNonNegative,
                                format!("{}:measure_nonneg_{}", #fn_name_str_val, #i),
                                #nonneg_condition.to_string(),
                                Some(format!("{}:{}", file!(), line!()))
                            );
                        }
                    }
                })
                .collect()
        }
        Err(_) => vec![], // Parse error already handled above
    };

    let when_condition = clause.when_condition.clone();
    let via_fn = clause.via_fn.clone();

    // Generate when condition marker if present
    let when_marker = when_condition.as_ref().map(|cond| {
        quote! {
            let __trust_vc_decreases_when = || { #cond };
        }
    });

    // Generate via function marker if present
    let via_marker = via_fn.as_ref().map(|fn_tokens| {
        quote! {
            let __trust_vc_decreases_via = stringify!(#fn_tokens);
        }
    });

    // Extract parameter names and types for ay variable declaration (like #[proof] does)
    let param_declarations = collect_param_declarations(sig);
    let param_names = collect_param_idents(sig);

    let _fn_name_str = fn_name.to_string();

    // Query the crate-local recursion graph for automatic SCC peers (#2054).
    // This augments any explicit `mutual_with(...)` peers with automatically
    // discovered recursive partners from the call graph.
    let scc_summary = recursion_graph::summary_for_item_fn(&input, fn_name.span());
    let mut all_peers = clause.mutual_peers.clone();
    if let Some(ref summary) = scc_summary {
        for member in &summary.scc_members {
            if member != &summary.current {
                if let Some(tail) = member.0.last() {
                    if !all_peers.contains(tail) {
                        all_peers.push(tail.clone());
                    }
                }
            }
        }
    }

    // Build optional resolver context for qualified-path matching in the transform.
    let resolver_ctx = scc_summary.as_ref().and_then(|summary| {
        let source_file = fn_name.span().local_file()?;
        let crate_root = mode_index::discover_crate_root(&source_file)?;
        let index = mode_index::get_or_build_index(&crate_root)?;
        let caller_module = recursion_graph::caller_module_from_span(fn_name.span());
        Some(super::transform::ResolverContext {
            index,
            caller_module,
            scc_members: summary.scc_members.clone(),
            current: summary.current.clone(),
        })
    });

    // Transform the body to inject checks at recursion points (see #1337 and #1353)
    let transformed_body = transform_body_with_checks(
        block,
        fn_name,
        &entry_expr,
        measure_plan.as_ref(),
        when_condition.as_ref(),
        &all_peers,
        resolver_ctx.as_ref(),
    );
    let via_call = via_fn.as_ref().map(|via_tokens| {
        if let Some(condition) = when_condition.as_ref() {
            quote! {
                if #condition {
                    #via_tokens(#(#param_names),*);
                }
            }
        } else {
            quote! {
                #via_tokens(#(#param_names),*);
            }
        }
    });
    let measure_str = quote!(#entry_expr).to_string();
    let entry_doc_attr = crate::attr_doc_metadata::decreases_entry_doc_attr(&measure_str);
    let when_doc_attrs: Vec<_> = when_condition
        .as_ref()
        .map(|condition| {
            let value =
                crate::attr_doc_metadata::decreases_when_doc_attr(&quote!(#condition).to_string());
            quote! { #[doc = #value] }
        })
        .into_iter()
        .collect();
    let via_doc_attrs: Vec<_> = via_fn
        .as_ref()
        .map(|via_tokens| {
            let value =
                crate::attr_doc_metadata::decreases_via_doc_attr(&quote!(#via_tokens).to_string());
            quote! { #[doc = #value] }
        })
        .into_iter()
        .collect();

    // When a via_fn is present, it provides the complete termination proof
    // (including branch guards). Use the original body instead of the
    // transformed body which injects unguarded MeasureDecreases at recursive
    // call sites. Part of #2658 Category G1.
    let test_body = if via_fn.is_some() {
        quote! { #block }
    } else {
        transformed_body
    };

    quote! {
        #(#attrs)*
        #[doc = #entry_doc_attr]
        #(#when_doc_attrs)*
        #(#via_doc_attrs)*
        /// Function with termination proof via decreasing measure(s)
        #[allow(dead_code, unused_variables)]
        #vis #sig {
            // Termination measure(s) with optional when/via clauses
            #[cfg(trust_mc)]
            {
                let __trust_vc_measures_entry = &(#entry_expr);

                // Optional: when condition (decreases only checked when true)
                #when_marker

                // Optional: via function reference (provides termination proof)
                #via_marker
            }

            #[cfg(all(test, not(trust_mc)))]
            {
                // Verification at recursion points only (fixes #1337 and #1353)
                #(#param_declarations)*
                let __trust_vc_measures_entry = &(#entry_expr);
                // Non-negativity obligations for well-founded termination (#2361)
                #(#nonneg_obligations)*
                #via_call
                #test_body
            }

            #[cfg(not(any(trust_mc, test)))]
            {
                // In production mode, just execute the function
                #block
            }
        }
    }
}

/// Expands a `#[via_fn]` proof function.
///
/// Via functions prove that termination measures decrease at recursive call
/// sites. They have the same parameters as the function they prove.
///
/// # Generated Code
///
/// Via functions are treated similarly to proof functions - they are:
/// - Verified during compilation via trust_mc
/// - Erased at runtime
/// - Marked with a special marker for trust_mc to associate with decreases clauses
pub fn expand_via_fn(input: ItemFn) -> TokenStream {
    let attrs = &input.attrs;
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;
    let param_declarations = collect_param_declarations(sig);

    quote! {
        #(#attrs)*
        /// Via function - proves termination for decreases clause
        #[doc(hidden)]
        #[allow(dead_code, unused_variables, unused_mut)]
        #vis #sig {
            #[cfg(trust_mc)]
            {
                let __trust_vc_via_fn = stringify!(#fn_name);
                #block
            }
            #[cfg(all(test, not(trust_mc)))]
            {
                #(#param_declarations)*
                #block
            }
            #[cfg(not(any(trust_mc, test)))]
            {
                #[allow(unreachable_code)]
                if false {
                    return { #block };
                }
                loop {
                    unreachable!(concat!(
                        "via function `",
                        stringify!(#fn_name),
                        "` called at runtime - via functions are ghost code"
                    ));
                }
            }
        }
    }
}
