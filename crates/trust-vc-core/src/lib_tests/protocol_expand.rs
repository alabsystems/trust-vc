// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for protocol_expand.rs: `expand_protocol`, `expand_action`,
//! `expand_safety`, `expand_liveness`.
//!
//! The end-to-end behaviour (the model holds every declared component, a field
//! has the type Rust resolves) is in `trust-vc/tests/protocol_macro_soundness.rs`;
//! these pin the shape of the expansion.

use super::*;

fn compact(tokens: proc_macro2::TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

// ──── expand_protocol ────────────────────────────────────────────────────

#[test]
fn test_expand_protocol_registers_fields_by_resolved_type_and_default_and_declared_components() {
    let input: syn::ItemStruct = syn::parse2(quote! {
        struct Counter {
            count: u64,
            enabled: bool,
        }
    })
    .expect("parse protocol struct");

    let expanded = compact(expand_protocol(input));

    assert!(
        expanded.contains("structCounter{count:u64,enabled:bool,}"),
        "the struct is preserved: {expanded}"
    );
    assert!(
        expanded.contains("pubfn__trust_vc_register_protocol()"),
        "{expanded}"
    );
    // The type is what method resolution on the field's type selects; the
    // spelling only names it in a refusal. The initial value is the field of
    // `Default::default()`, called twice, where the struct has `Default`.
    for piece in [
        "let__trust_vc_initial:::core::option::Option<[Self;2]>=(&::trust_vc_core::verification_bridge::ProtocolInitialState::<Self>(::core::marker::PhantomData)).protocol_initial_states();",
        "let__trust_vc_field=&::trust_vc_core::verification_bridge::ProtocolFieldType::<u64>(::core::marker::PhantomData);",
        "register_protocol_field(\"Counter\",\"count\",__trust_vc_field.protocol_type(),\"u64\",__trust_vc_initial.as_ref().map(|[__trust_vc_first,__trust_vc_second]|{[__trust_vc_field.protocol_value(&__trust_vc_first.count),__trust_vc_field.protocol_value(&__trust_vc_second.count),]}),)",
    ] {
        assert!(expanded.contains(piece), "{piece} missing from {expanded}");
    }
    assert!(
        expanded.contains(
            "register_declared_protocol_components(\"Counter\",::core::any::TypeId::of::<Self>(),)"
        ),
        "{expanded}"
    );
    assert!(
        !expanded.contains("register_protocol_state_var"),
        "no field is registered by its spelling: {expanded}"
    );
}

#[test]
fn test_expand_protocol_empty_struct_registers_no_field() {
    let input: syn::ItemStruct = syn::parse2(quote! {
        struct EmptyProtocol {}
    })
    .expect("parse empty struct");

    let expanded = compact(expand_protocol(input));

    assert!(
        expanded.contains("__trust_vc_register_protocol"),
        "{expanded}"
    );
    assert!(!expanded.contains("register_protocol_field"), "{expanded}");
}

// ──── expand_action / expand_safety / expand_liveness ────────────────────

/// A component is recorded where it is declared (an `inventory` entry), for
/// the protocol TYPE its attribute names, in every build of the crate
/// declaring it, and never registered when its function runs.
#[test]
fn test_components_are_declared_for_the_protocol_type_not_registered_by_running() {
    let method = || -> syn::ItemFn {
        syn::parse2(quote! {
            fn step(&mut self) {
                self.count = self.count + 1;
            }
        })
        .expect("parse component fn")
    };
    for (expanded, kind, fairness) in [
        (compact(expand_action(method(), "Counter")), "Action", ""),
        (compact(expand_safety(method(), "Counter")), "Safety", ""),
        (
            compact(expand_liveness(method(), "Counter", "weak")),
            "Liveness",
            "weak",
        ),
    ] {
        assert!(
            expanded.contains("fnstep(&mutself){"),
            "the function is preserved: {expanded}"
        );
        assert!(
            expanded.contains(&format!(
                "inventory::submit!{{::trust_vc_core::verification_bridge::ProtocolComponentDef{{protocol:::core::any::TypeId::of::<Counter>,kind:::trust_vc_core::verification_bridge::ProtocolComponentKind::{kind},name:\"step\","
            )),
            "{expanded}"
        );
        assert!(
            expanded.contains(&format!("fairness:\"{fairness}\",}}")),
            "{expanded}"
        );
        assert!(
            !expanded.contains("register_protocol_"),
            "nothing is registered when the function runs: {expanded}"
        );
        assert!(
            !expanded.contains("cfg"),
            "the entry is in every build of the declaring crate: {expanded}"
        );
        assert!(
            expanded.contains(
                "let_:::core::marker::PhantomData<Self>=::core::marker::PhantomData::<Counter>;"
            ),
            "a method is a method of the protocol it names: {expanded}"
        );
    }
}

/// A component without a receiver cannot read `self`; it is not tied to an
/// impl.
#[test]
fn test_a_component_without_a_receiver_has_no_self_check() {
    let input: syn::ItemFn = syn::parse2(quote! {
        fn always() -> bool {
            true
        }
    })
    .expect("parse safety fn");

    let expanded = compact(expand_safety(input, "a::Counter"));

    assert!(
        expanded.contains("TypeId::of::<a::Counter>"),
        "the protocol is named by its path: {expanded}"
    );
    assert!(!expanded.contains("PhantomData"), "{expanded}");
}

#[test]
fn test_a_protocol_argument_that_is_not_a_path_is_a_compile_error() {
    let input: syn::ItemFn = syn::parse2(quote! {
        fn step(&mut self) {}
    })
    .expect("parse action fn");

    let expanded = compact(expand_action(input, "Counter, extra"));

    assert!(expanded.starts_with("compile_error!"), "{expanded}");
}

/// The model reads the body as `#[action]` sees it; an attribute macro below
/// it runs after and can change what Rust runs (`#[trust_vc::contract]` adds
/// a runtime `assert!` in a non-test build). Only attributes that leave the
/// body as written are kept.
#[test]
fn test_a_component_under_a_body_changing_attribute_is_a_compile_error() {
    for attr in [
        quote!(#[trust_vc::contract(requires(self.x < 5))]),
        quote!(#[instrument]),
        quote!(#[cfg_attr(test, inline)]),
        quote!(#[::core::prelude::v1::test]),
    ] {
        let input: syn::ItemFn = syn::parse2(quote! {
            #attr
            fn bump(&mut self) {
                self.x = 1;
            }
        })
        .expect("parse action fn");
        let expanded = compact(expand_action(input, "Capped"));
        assert!(expanded.starts_with("compile_error!"), "{attr}: {expanded}");
    }
    let input: syn::ItemFn = syn::parse2(quote! {
        /// Doc.
        #[inline]
        #[allow(dead_code)]
        #[must_use]
        #[cfg(test)]
        #[track_caller]
        #[rustfmt::skip]
        #[clippy::cognitive_complexity = "1"]
        fn bump(&mut self) {
            self.x = 1;
        }
    })
    .expect("parse action fn");
    let expanded = compact(expand_action(input, "Capped"));
    assert!(expanded.contains("ProtocolComponentDef"), "{expanded}");
    assert!(expanded.starts_with("#[doc="), "{expanded}");
}
