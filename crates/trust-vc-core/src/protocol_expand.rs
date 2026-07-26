//! Protocol macro expansions for `#[protocol]`, `#[action]`, `#[safety]`, `#[liveness]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These expansion functions are NOT feature-gated — they generate TokenStreams
//! regardless of whether the `ty` feature is enabled. The generated code
//! registers protocol components in thread-local storage. Actual TY translation
//! and model checking only happens when the `ty` feature is active.

use proc_macro2::TokenStream;
use quote::quote;
use syn::ItemFn;

/// Expand `#[protocol]` on a struct.
///
/// Preserves the original struct and generates an `impl` method
/// `__trust_vc_register_protocol()` that registers state variables (field names +
/// types) for TY translation.
///
/// Users (or test harnesses) call `StructName::__trust_vc_register_protocol()`
/// before `VerificationPipeline::collect_from_macros()` to populate the
/// protocol state var registry. In tests, pair with `clear_registrations()`
/// for clean state between runs.
pub fn expand_protocol(input: syn::ItemStruct) -> TokenStream {
    let struct_name = &input.ident;
    let struct_name_str = struct_name.to_string();
    let support_root = crate::macro_support_root();

    let field_registrations: Vec<TokenStream> = match &input.fields {
        syn::Fields::Named(fields) => fields
            .named
            .iter()
            .filter_map(|f| {
                let field_name = f.ident.as_ref()?;
                let field_name_str = field_name.to_string();
                let ty = &f.ty;
                let field_type_str = quote!(#ty).to_string();
                Some(quote! {
                    #support_root::verification_bridge::register_protocol_state_var(
                        #struct_name_str,
                        #field_name_str,
                        #field_type_str,
                    );
                })
            })
            .collect(),
        _ => vec![],
    };

    quote! {
        #input

        #[cfg(any(test, trust_mc))]
        impl #struct_name {
            /// Register protocol state variables for TY verification.
            ///
            /// Call before `VerificationPipeline::collect_from_macros()` to
            /// populate the protocol state var registry. In tests, pair with
            /// `clear_registrations()` for clean state between runs.
            #[doc(hidden)]
            pub fn __trust_vc_register_protocol() {
                #(#field_registrations)*
            }
        }
    }
}

/// Expand `#[action(ProtocolName)]` on a function.
///
/// Preserves the original function body and injects registration code
/// that records the action name, protocol name, and body text for TY
/// Next generation.
pub fn expand_action(input: ItemFn, protocol_name: &str) -> TokenStream {
    let fn_name = &input.sig.ident;
    let fn_name_str = fn_name.to_string();
    let block = &input.block;
    let body_str = quote!(#block).to_string();
    let vis = &input.vis;
    let sig = &input.sig;
    let attrs = &input.attrs;
    let support_root = crate::macro_support_root();

    quote! {
        #(#attrs)*
        #vis #sig {
            #[cfg(any(test, trust_mc))]
            #support_root::verification_bridge::register_protocol_action(
                #protocol_name,
                #fn_name_str,
                #body_str,
            );
            #block
        }
    }
}

/// Expand `#[safety(ProtocolName)]` on a function.
///
/// Preserves the original function body and injects registration code
/// that records the safety invariant for TY INVARIANT checking.
pub fn expand_safety(input: ItemFn, protocol_name: &str) -> TokenStream {
    let fn_name = &input.sig.ident;
    let fn_name_str = fn_name.to_string();
    let block = &input.block;
    let body_str = quote!(#block).to_string();
    let vis = &input.vis;
    let sig = &input.sig;
    let attrs = &input.attrs;
    let support_root = crate::macro_support_root();

    quote! {
        #(#attrs)*
        #vis #sig {
            #[cfg(any(test, trust_mc))]
            #support_root::verification_bridge::register_protocol_invariant(
                #protocol_name,
                #fn_name_str,
                #body_str,
            );
            #block
        }
    }
}

/// Expand `#[liveness(ProtocolName, fairness = "weak")]` on a function.
///
/// Preserves the original function body and injects registration code
/// that records the liveness property and fairness specification.
pub fn expand_liveness(input: ItemFn, protocol_name: &str, fairness: &str) -> TokenStream {
    let fn_name = &input.sig.ident;
    let fn_name_str = fn_name.to_string();
    let block = &input.block;
    let body_str = quote!(#block).to_string();
    let vis = &input.vis;
    let sig = &input.sig;
    let attrs = &input.attrs;
    let support_root = crate::macro_support_root();

    quote! {
        #(#attrs)*
        #vis #sig {
            #[cfg(any(test, trust_mc))]
            #support_root::verification_bridge::register_protocol_liveness(
                #protocol_name,
                #fn_name_str,
                #body_str,
                #fairness,
            );
            #block
        }
    }
}
