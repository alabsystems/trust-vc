//! Protocol macro expansions for `#[protocol]`, `#[action]`, `#[safety]`, `#[liveness]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These expansion functions are NOT feature-gated — they generate TokenStreams
//! regardless of whether the `ty` feature is enabled. TY translation and model
//! checking only happen when the `ty` feature is active.
//!
//! The model is the Rust the attributes annotate, as Rust resolves it:
//! - a field's type is the type Rust resolves for it (through an alias), never
//!   how it is spelled;
//! - the initial state is the struct's `Default::default()`, as Rust runs it
//!   (a user `impl Default` included); a struct without `Default` has none,
//!   and is refused;
//! - a component is recorded where it is declared, in every build of the
//!   crate declaring it, so the model holds every component linked into the
//!   program, whether or not its function ever runs and whatever `cfg` the
//!   declaring crate was built with;
//! - a component is recorded for the protocol TYPE its attribute names, and a
//!   component with a receiver must be a method of that type, so its `self`
//!   is the protocol state the model reads;
//! - a component's body is read as written, so it may carry no attribute that
//!   could rewrite it afterwards (an attribute macro below this one).

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::ItemFn;

/// Expand `#[protocol]` on a struct.
///
/// Preserves the original struct and generates an `impl` method
/// `__trust_vc_register_protocol()` that registers the struct's fields, each
/// with its type as Rust resolves it and its value in the struct's
/// `Default::default()` (the model's initial state), and every component
/// declared for it for TY translation.
///
/// Users (or test harnesses) call `StructName::__trust_vc_register_protocol()`
/// before `VerificationPipeline::collect_from_macros()` to select the
/// protocol for verification. In tests, pair with `clear_registrations()` for
/// clean state between runs.
pub fn expand_protocol(input: syn::ItemStruct) -> TokenStream {
    let struct_name = &input.ident;
    let struct_name_str = struct_name.to_string();
    let support_root = crate::macro_support_root();
    let bridge = quote!(#support_root::verification_bridge);

    let field_registrations: Vec<TokenStream> = match &input.fields {
        syn::Fields::Named(fields) => fields
            .named
            .iter()
            .filter_map(|f| {
                let field_name = f.ident.as_ref()?;
                let field_name_str = field_name.to_string();
                let ty = &f.ty;
                let spelled = quote!(#ty).to_string();
                Some(quote! {
                    {
                        let __trust_vc_field = &#bridge::ProtocolFieldType::<#ty>(::core::marker::PhantomData);
                        #bridge::register_protocol_field(
                            #struct_name_str,
                            #field_name_str,
                            __trust_vc_field.protocol_type(),
                            #spelled,
                            __trust_vc_initial.as_ref().map(|[__trust_vc_first, __trust_vc_second]| {
                                [
                                    __trust_vc_field.protocol_value(&__trust_vc_first.#field_name),
                                    __trust_vc_field.protocol_value(&__trust_vc_second.#field_name),
                                ]
                            }),
                        );
                    }
                })
            })
            .collect(),
        _ => vec![],
    };

    quote! {
        #input

        #[cfg(any(test, trust_mc))]
        impl #struct_name {
            /// Register this protocol for TY verification: its fields, which
            /// start at `Default::default()`, and every `#[action]`,
            /// `#[safety]` and `#[liveness]` declared for it.
            ///
            /// Call before `VerificationPipeline::collect_from_macros()`. In
            /// tests, pair with `clear_registrations()` for clean state
            /// between runs.
            #[doc(hidden)]
            pub fn __trust_vc_register_protocol() {
                #[allow(unused_imports)]
                use #bridge::{
                    ProtocolDefaultState as _, ProtocolModelledField as _,
                    ProtocolNoDefaultState as _, ProtocolUnmodelledField as _,
                };
                // The initial state is what Rust builds: `Default::default()`
                // (twice), or none when the struct has no `Default`.
                #[allow(unused_variables)]
                let __trust_vc_initial: ::core::option::Option<[Self; 2]> =
                    (&#bridge::ProtocolInitialState::<Self>(::core::marker::PhantomData))
                        .protocol_initial_states();
                #(#field_registrations)*
                #bridge::register_declared_protocol_components(
                    #struct_name_str,
                    ::core::any::TypeId::of::<Self>(),
                );
            }
        }
    }
}

/// Expand `#[action(ProtocolName)]` on a function: a TY `Next` disjunct.
pub fn expand_action(input: ItemFn, protocol_name: &str) -> TokenStream {
    expand_component(input, protocol_name, quote!(Action), "")
}

/// Expand `#[safety(ProtocolName)]` on a function: a TY `INVARIANT`.
pub fn expand_safety(input: ItemFn, protocol_name: &str) -> TokenStream {
    expand_component(input, protocol_name, quote!(Safety), "")
}

/// Expand `#[liveness(ProtocolName, fairness = "weak")]` on a function: a TY
/// `PROPERTY` with its fairness specification.
pub fn expand_liveness(input: ItemFn, protocol_name: &str, fairness: &str) -> TokenStream {
    expand_component(input, protocol_name, quote!(Liveness), fairness)
}

/// Preserve the function and record it, where it is declared, as a component
/// of the protocol type `protocol_name` names.
fn expand_component(
    input: ItemFn,
    protocol_name: &str,
    kind: TokenStream,
    fairness: &str,
) -> TokenStream {
    let protocol: syn::Path = match syn::parse_str(protocol_name) {
        Ok(path) => path,
        Err(_) => {
            let message = format!(
                "protocol component: `{protocol_name}` is not the path of a \
                 #[trust_vc::protocol] struct"
            );
            return quote!(compile_error!(#message););
        }
    };
    let ItemFn {
        attrs,
        vis,
        sig,
        block,
    } = &input;
    let fn_name_str = sig.ident.to_string();
    // The model reads the body as written here; an attribute macro below
    // this one runs after, and what it makes of the body is what Rust runs.
    if let Some(attr) = attrs.iter().find(|attr| !is_inert(attr)) {
        let path = attr.path();
        let message = format!(
            "protocol component `{fn_name_str}`: `#[{}]` could change the body after the \
             protocol model read it; a component's attributes are limited to doc comments, \
             lint levels, `cfg`, `inline`, `cold`, `must_use`, `track_caller`, `deprecated` \
             and `rustfmt::`/`clippy::` tool attributes",
            quote!(#path).to_string().replace(' ', "")
        );
        return quote_spanned!(attr.span()=> compile_error!(#message););
    }
    let body_str = quote!(#block).to_string();
    let support_root = crate::macro_support_root();
    // The model reads `self.<field>` as the protocol's field: a component with
    // a receiver is a method of the protocol it names.
    let self_is_the_protocol = sig.receiver().map(|receiver| {
        quote_spanned! {receiver.span()=>
            let _: ::core::marker::PhantomData<Self> = ::core::marker::PhantomData::<#protocol>;
        }
    });

    quote! {
        #(#attrs)*
        #vis #sig {
            #self_is_the_protocol
            // Recorded in every build: a `cfg` here is the DECLARING crate's,
            // and a component compiled out of a crate built without `test` or
            // `trust_mc` would be silently missing from the model of a
            // protocol registered from another crate.
            #support_root::inventory::submit! {
                #support_root::verification_bridge::ProtocolComponentDef {
                    protocol: ::core::any::TypeId::of::<#protocol>,
                    kind: #support_root::verification_bridge::ProtocolComponentKind::#kind,
                    name: #fn_name_str,
                    body: #body_str,
                    fairness: #fairness,
                }
            }
            #block
        }
    }
}

/// An attribute that leaves the body the model reads as the body Rust runs:
/// a built-in attribute that does not rewrite code, or a `rustfmt`/`clippy`
/// tool attribute. `cfg` removes the whole function, its component included.
/// Anything else (an attribute macro, `cfg_attr`) is not inert.
fn is_inert(attr: &syn::Attribute) -> bool {
    let path = attr.path();
    if path.leading_colon.is_some() {
        return false;
    }
    let segments: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    match segments
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        [name] => matches!(
            *name,
            "doc"
                | "allow"
                | "warn"
                | "deny"
                | "forbid"
                | "expect"
                | "cfg"
                | "inline"
                | "cold"
                | "must_use"
                | "track_caller"
                | "deprecated"
        ),
        [tool, _] => matches!(*tool, "rustfmt" | "clippy"),
        _ => false,
    }
}
