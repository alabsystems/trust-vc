//! Spec function macro expansion — `#[trust_vc::spec]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `lib.rs` to keep files under 500 lines (#1816).
//! Signature/type helpers live in `spec_expand_support.rs` (#2599).
//!
//! Spec functions are ghost code for verification only. They have no runtime
//! behavior. During proof mode, the body axiom is encoded as a BroadcastAssume
//! obligation: `∀params. f(params) == body(params)`, which the ay encoder
//! handles via the existing quantifier pipeline.

use crate::local_vars::extract_type_string;
use crate::mode;
use crate::mode_scan;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashSet;
use syn::ItemFn;

#[path = "spec_expand_support.rs"]
mod support;
use support::*;

const SPEC_RETURNS_ERROR: &str = "spec functions cannot have `returns` clause";

fn find_named_attr<'a>(attrs: &'a [syn::Attribute], name: &str) -> Option<&'a syn::Attribute> {
    attrs.iter().find(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == name)
    })
}

/// Generates the proof-mode body: registers params, function context, and
/// body axiom as a BroadcastAssume obligation.
///
/// When `body_axiom_expr_tokens` is `Some`, also caches the pre-built
/// TrustVcExpr in PRE_BUILT_EXPRS so `prepare_context` skips string
/// parse+lower for the body axiom. Part of #2217.
/// Whether a `#[trust_vc::spec]` function carries a decreases termination
/// measure, checked robustly against attribute-macro expansion order:
/// - if `#[trust_vc::decreases]` expanded first (the conventional outer
///   attribute) it left a `trust_vc:decreases:entry=` doc-metadata marker;
/// - if this `spec` attribute expanded first, the raw `#[trust_vc::decreases]`
///   (or bare `#[decreases]`) attribute is still present below it.
///
/// Gates admission of recursive defining axioms — see `proof_mode_block`'s
/// `suppress_recursive_body_axiom`.
fn spec_fn_has_decreases_measure(attrs: &[syn::Attribute]) -> bool {
    if matches!(
        crate::attr_doc_metadata::extract_decreases_doc_metadata(attrs),
        Ok(Some(_))
    ) {
        return true;
    }
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "decreases")
    })
}

#[allow(clippy::too_many_arguments)]
fn proof_mode_block(
    params: &[FnParam],
    type_params: &HashSet<String>,
    trait_bounds: &[TokenStream],
    fn_name_str: &str,
    return_type: &str,
    body_axiom_name: &str,
    body_axiom_condition: &str,
    call_expr: &str,
    block: &syn::Block,
    body_axiom_expr_tokens: Option<TokenStream>,
    is_recursive: bool,
    suppress_recursive_body_axiom: bool,
    is_external_trusted: bool,
    is_opaque: bool,
    is_inline: bool,
    rlimit_ms: Option<u64>,
) -> TokenStream {
    let ir_path = ir_path();
    let verify_macro_path = verify_macro_path();
    let vc_path = vc_path();
    let mode_path = mode_path();
    let (param_registration, ctx_params, bound_vars) = param_tokens(params, type_params);
    // Soundness gate (mirrors spec_function_catalog.rs): never assert the
    // defining axiom of a self-recursive spec function that has no decreases
    // measure — for a non-terminating body it has no model and entails `false`.
    // The helper declaration below still stands, so the function stays
    // uninterpreted (fail-closed) rather than admitting a contradiction.
    // SOUNDNESS-CRITICAL (H14, trust boundary; review round 2). The SIXTH
    // publisher of `__body_axiom_<f>` is this proc-macro lane, and it knew only
    // `opaque` and `inline`. A `#[trust_vc::spec] #[trust_vc::external_body] fn
    // sp() -> u32 { 100 }` — the uninterpreted-spec-function idiom — therefore
    // published `sp() == 100` HERE while the FILE lane
    // (`spec_function_catalog::SpecFunctionDef::from_item_fn`) declined the
    // identical source text: one program, two lanes, two answers. The braces of
    // a trusted declaration hold a PLACEHOLDER; the symbol is still declared
    // (`declare_helper_function_typed_with_bounds` below), so the function stays
    // an uninterpreted UF carrying only what it declares.
    let emit_body_axiom =
        return_type != "()" && !suppress_recursive_body_axiom && !is_external_trusted;

    // Emit set_rlimit call if #[trust_vc::rlimit(N)] was present. Part of #2489.
    let rlimit_setup = rlimit_ms.map(|ms| {
        quote! { __trust_vc_ctx.set_rlimit(#ms); }
    });

    // Generate TrustVcExpr cache call if builder tokens are available.
    // Placed after restore_context so lookup_var_type can access param types.
    // Wrapped in Option closure so `?` from variable lookups propagates (#2233).
    // The gate is applied at EXPANSION time, not as an `if false` in the emitted
    // code: a declined axiom must leave no `__body_axiom_<f>` behind at all, so
    // that "did this lane publish?" is answerable by reading the expansion.
    let cache_expr = match body_axiom_expr_tokens {
        Some(expr_tokens) if emit_body_axiom => quote! {
            {
                let __trust_vc_cache_name =
                    format!("{}_{}", #body_axiom_name, module_path!());
                if let Some(__trust_vc_body_expr) =
                    (|| -> Option<#ir_path::TrustVcExpr> { Some(#expr_tokens) })()
                {
                    #verify_macro_path::cache_pre_built_expr(
                        __trust_vc_cache_name,
                        #body_axiom_condition.to_string(),
                        __trust_vc_body_expr,
                    );
                }
            }
        },
        _ => quote! {},
    };

    let body_axiom_push = if emit_body_axiom {
        quote! {
            {
                let __trust_vc_axiom_name =
                    format!("{}_{}", #body_axiom_name, module_path!());
                if !__trust_vc_ctx
                    .obligations()
                    .iter()
                    .any(|obligation| obligation.name() == __trust_vc_axiom_name)
                {
                    __trust_vc_ctx.push_obligation(
                        #vc_path::ProofObligation::broadcast_assume(
                            __trust_vc_axiom_name,
                            #body_axiom_condition.to_string(),
                        )
                        .with_location(format!("{}:{}", file!(), line!()))
                        .with_bound_vars(vec![#(#bound_vars),*])
                        .with_trigger_patterns(vec![vec![#call_expr.to_string()]])
                        .with_opaque(#is_opaque)
                        .with_inline(#is_inline),
                    );
                }
            }
        }
    } else {
        quote! {}
    };

    let return_type_tokens = trust_vc_type_tokens(return_type, type_params).unwrap_or_else(|| {
        let rt = return_type;
        quote! { #ir_path::TrustVcType::Opaque(#rt.to_string()) }
    });

    quote! {
        if #verify_macro_path::is_in_proof_mode() {
            let mut __trust_vc_ctx = #verify_macro_path::take_context()
                .unwrap_or_else(#vc_path::VerificationContext::new);

            #(#param_registration)*

            // Register in typed helper function map so all called spec functions
            // are available in TypeEnv, not just the last one. Part of #2431.
            __trust_vc_ctx.declare_helper_function_typed_with_bounds(
                #fn_name_str,
                #return_type_tokens,
                vec![#(#ctx_params),*],
                vec![#(#trait_bounds),*],
            );

            __trust_vc_ctx.set_function_context(
                #vc_path::FunctionContext::new(
                    #fn_name_str,
                    vec![#(#ctx_params),*],
                    #return_type_tokens,
                    #mode_path::FunctionMode::Spec,
                )
                .with_recursive(#is_recursive)
                .with_trait_bounds(vec![#(#trait_bounds),*]),
            );

            #rlimit_setup

            #body_axiom_push

            #verify_macro_path::restore_context(Some(__trust_vc_ctx));

            #cache_expr

            return { #block };
        }
    }
}

/// Expands `#[trust_vc::spec]` attribute macro.
///
/// Note: Uses `loop { unreachable!(...) }` pattern to ensure compatibility
/// with non-unit return types (fixes #25).
pub fn expand_spec(input: ItemFn) -> TokenStream {
    let mode_path = mode_path();
    let vis = &input.vis;
    let sig = &input.sig;
    let block = &input.block;
    let fn_name = &sig.ident;
    let fn_name_str = fn_name.to_string();

    if let Some(attr) = find_named_attr(&input.attrs, "returns") {
        return syn::Error::new_spanned(attr, SPEC_RETURNS_ERROR).to_compile_error();
    }

    // Detect #[trust_vc::opaque] or #[opaque] marker. Part of #1901.
    let is_opaque = input.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|s| s.ident == "opaque")
    });

    // SOUNDNESS-CRITICAL (H14, trust boundary; review round 2). Detect
    // `#[trust_vc::external_body]` / `#[trust_vc::external]` — the trusted
    // boundary — right beside the `opaque` detection that this lane already had.
    // `has_external_trusted_attr` is the SAME predicate the file lane consults
    // (`spec_function_catalog.rs`, E6), matched by last path segment so a foreign
    // namespace spelling (`#[verifier::external_body]`) declines too. It
    // suppresses the defining axiom only; the symbol is still declared.
    let is_external_trusted =
        crate::vc_extraction::attr_extract::has_external_trusted_attr(&input.attrs);

    // Detect #[trust_vc::inline] or #[inline] marker. Part of #2488.
    let is_inline = input.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|s| s.ident == "inline")
    });

    // Inline + opaque is contradictory. Part of #2488.
    if is_inline && is_opaque {
        return quote! {
            compile_error!("#[trust_vc::inline] and #[trust_vc::opaque] are mutually exclusive");
        };
    }

    // Detect #[trust_vc::rlimit(N)] — per-function solver timeout in ms. Part of #2489.
    let rlimit_ms: Option<u64> = input.attrs.iter().find_map(|attr| {
        let last_seg = attr.path().segments.last()?;
        if last_seg.ident != "rlimit" {
            return None;
        }
        let tokens: proc_macro2::TokenStream = attr.parse_args().ok()?;
        let lit: syn::LitInt = syn::parse2(tokens).ok()?;
        lit.base10_parse::<u64>().ok()
    });

    // Strip opaque, inline, and rlimit attributes from output to avoid re-processing.
    let attrs: Vec<_> =
        input
            .attrs
            .iter()
            .filter(|attr| {
                !attr.path().segments.last().is_some_and(|s| {
                    s.ident == "opaque" || s.ident == "rlimit" || s.ident == "inline"
                })
            })
            .collect();

    let params = extract_fn_params(sig);
    let type_params = extract_type_params(sig);
    let trait_bounds = trait_bound_tokens(sig);
    let param_names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
    let return_type = match &sig.output {
        syn::ReturnType::Type(_, ty) => extract_type_string(ty),
        syn::ReturnType::Default => "()".to_string(),
    };

    let call_expr = format!("{}({})", fn_name_str, param_names.join(", "));
    let body_expr = quote!(#block).to_string();
    let body_axiom_name = format!("__body_axiom_{}", fn_name_str);
    let body_axiom_condition = format!("{} == {}", call_expr, body_expr);

    // Order-independent mode validation: outbound + inbound audit (#2300).
    mode::register_compile_time_function_mode(&fn_name_str, mode::FunctionMode::Spec);
    let (_scan, mode_errors) = mode_scan::validate_mode(&input, mode::FunctionMode::Spec, block);
    if !mode_errors.is_empty() {
        return quote! { #(#mode_errors)* };
    }

    // Detect recursion via SCC summary, falling back to self-call detection (#2054).
    // This makes spec functions correct for mutual recursion, not just self-calls.
    let is_recursive = crate::recursion_graph::summary_for_item_fn(&input, fn_name.span())
        .map_or_else(
            || crate::block_contains_self_call(&fn_name_str, block),
            |summary| summary.is_recursive,
        );

    // Inline + recursive is unsound (body substitution would loop). Part of #2488.
    if is_inline && is_recursive {
        return quote! {
            compile_error!("#[trust_vc::inline] cannot be used on recursive spec functions");
        };
    }

    // Soundness gate: a self-recursive spec function is well-defined only if it
    // terminates, which Verus requires a `#[trust_vc::decreases]` clause to
    // establish. The decreases macro (which by convention is the outer
    // attribute, expanded before this one) records itself via a
    // `trust_vc:decreases:entry=` doc-metadata marker; its absence means no
    // termination measure, so we must not assert the recursive defining axiom.
    let has_decreases = spec_fn_has_decreases_measure(&input.attrs);
    let suppress_recursive_body_axiom = is_recursive && !has_decreases;

    // H10 (macro lane): the helper this expansion registers is keyed by NAME and
    // ARGUMENTS — `declare_helper_function_typed_with_bounds` below — so a
    // generic parameter that no value parameter carries collapses every
    // instantiation into ONE uninterpreted application, exactly as in the file
    // lane. MEASURED liar on the untouched expansion: `#[spec] fn rsz<T>(n: u64)
    // -> u64 { if n == 0 { size_of::<T>() as u64 } else { rsz::<T>(n - 1) } }`
    // (recursive, no `decreases`, so its body axiom is suppressed and its body
    // is therefore never lowered) proved `rsz::<u8>(0) == rsz::<u64>(0)`, which
    // Rust refutes 1 != 8.
    //
    // The exemption is the file lane's: a body axiom published for EVERY use is
    // lowered in the erased environment, where an instantiation-dependent body
    // fails to lower and fails the query (measured on this lane too — the
    // `size_of::<T>()` body above fails `__body_axiom_*` preparation whenever
    // the axiom is emitted), so a body that does lower is T-uniform. An OPAQUE
    // definition is refused with the recursion-suppressed one: whether its
    // hidden axiom is lowered before it is gated out is not a property this
    // expansion controls.
    //
    // A refusal here is a compile error rather than a fail-closed verdict
    // because the expansion IS the declaration: there is no per-query
    // registration to decline. Verus likewise rejects a recursive spec function
    // with no `decreases` at compile time.
    let uncarried_generics: Vec<String> = sig
        .generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Const(const_param) => Some(const_param.ident.to_string()),
            syn::GenericParam::Type(type_param) => {
                let name = type_param.ident.to_string();
                // Carried exactly when a value parameter's registered type IS
                // the parameter (`x: T` → `TrustVcType::TypeParam("T")`, whose
                // argument the encoder wraps in the type-keyed `Box_T`). A
                // nested (`Option<T>`) or return-only occurrence carries
                // nothing.
                (!params.iter().any(|param| param.ty.trim() == name)).then_some(name)
            }
            syn::GenericParam::Lifetime(_) => None,
        })
        .collect();
    let definition_is_unconditional =
        !is_opaque && !suppress_recursive_body_axiom && return_type != "()";
    if !uncarried_generics.is_empty() && !definition_is_unconditional {
        let detail = format!(
            "generic instantiation not carried: spec function `{fn_name_str}` declares generic \
             parameter(s) {} that no value parameter carries into its solver term, and its body \
             axiom is not published for every use ({}), so calls at different instantiations \
             would collapse into one uninterpreted application; TrustVc fails closed",
            uncarried_generics
                .iter()
                .map(|param| format!("`{param}`"))
                .collect::<Vec<_>>()
                .join(", "),
            if is_opaque {
                "it is opaque"
            } else if suppress_recursive_body_axiom {
                "it is recursive with no `decreases` measure, so the axiom is suppressed"
            } else {
                "it returns `()`"
            }
        );
        return syn::Error::new_spanned(&input.sig, detail).to_compile_error();
    }

    // Try to build TrustVcExpr for body axiom (Phase 5: typed pipeline, #2217).
    // Falls back to None for unsupported expressions; string path handles those.
    let body_axiom_expr_tokens =
        build_body_axiom_expr_tokens(&params, &type_params, &fn_name_str, &return_type, block);

    let proof_block = proof_mode_block(
        &params,
        &type_params,
        &trait_bounds,
        &fn_name_str,
        &return_type,
        &body_axiom_name,
        &body_axiom_condition,
        &call_expr,
        block,
        body_axiom_expr_tokens,
        is_recursive,
        suppress_recursive_body_axiom,
        is_external_trusted,
        is_opaque,
        is_inline,
        rlimit_ms,
    );
    let ghost_block = ghost_unreachable_block(fn_name, block);

    quote! {
        #(#attrs)*
        #[doc(hidden)]
        #[allow(dead_code, unused_variables)]
        #vis #sig {
            // Gate the mode-registry call behind the verification cfgs, mirroring
            // `expand_proof`. `register_function_mode` is an `::trust_vc_core::`
            // path that only matters during verification (test / trust_mc). Leaving
            // it unconditional forced every crate that uses `#[trust_vc::spec]` in
            // *library* (non-test) code to carry a normal `trust_vc_core`
            // dependency just to resolve a call that never does anything outside a
            // verification build. Gating it lets the spec surface (e.g.
            // `trust-vc-std::arithmetic`) host `#[spec]` definitions with only a
            // dev-dependency on the engine — the body still expands to the ghost
            // `loop { unreachable!() }` in production.
            #[cfg(any(test, trust_mc))]
            #mode_path::register_function_mode(
                stringify!(#fn_name),
                #mode_path::FunctionMode::Spec
            );

            #[cfg(trust_mc)]
            { #block }
            #[cfg(all(test, not(trust_mc)))]
            {
                #proof_block
                #ghost_block
            }
            #[cfg(all(not(test), not(trust_mc)))]
            { #ghost_block }
        }
    }
}

#[cfg(test)]
#[path = "spec_expand_tests.rs"]
mod tests;
