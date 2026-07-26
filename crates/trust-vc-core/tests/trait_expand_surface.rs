// Integration coverage for trait-expansion Slice 1 (#2432).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;
use trust_vc_core::{expand_trait_impl, expand_trait_spec};

fn normalize(tokens: proc_macro2::TokenStream) -> String {
    tokens
        .to_string()
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

#[test]
fn trait_spec_expansion_strips_contract_attributes_and_emits_helper() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Sortable {
            #[requires(self.len() > 0)]
            #[trust_vc::ensures(result.len() == self.len())]
            fn sort(&self) -> Self;
        }
    })
    .expect("parse trait");

    let expanded = normalize(expand_trait_spec(input));
    assert!(expanded.contains("__trust_vc_trait_decl_Sortable"));
    assert!(expanded.contains("TraitDecl"));
    assert!(!expanded.contains("requires(self.len()>0)"));
    assert!(!expanded.contains("trust_vc::ensures"));
}

#[test]
fn trait_spec_expansion_strips_returns_attribute_and_rewrites_binder() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Counter {
            #[trust_vc::returns(ret)]
            #[trust_vc::ensures(ret >= 0)]
            fn value(&self) -> i32;
        }
    })
    .expect("parse trait");

    let expanded = normalize(expand_trait_spec(input));
    assert!(!expanded.contains("trust_vc::returns"));
    assert!(!expanded.contains("ret>=0"));
    assert!(
        expanded.contains("\"result>=0\".to_string()"),
        "returns binder should be normalized into result-based ensures: {expanded}"
    );
}

#[test]
fn trait_impl_expansion_strips_contract_attributes_and_emits_helper() {
    let input: syn::ItemImpl = syn::parse2(quote! {
        impl CounterSpec for Counter {
            #[trust_vc::ensures(result >= self.0)]
            fn value(&self) -> i32 {
                self.0
            }
        }
    })
    .expect("parse trait impl");

    let expanded = normalize(expand_trait_impl(input));
    assert!(expanded.contains("__trust_vc_trait_impl_decl_CounterSpec_Counter"));
    assert!(expanded.contains("TraitImplDecl"));
    assert!(!expanded.contains("trust_vc::ensures"));
}

#[test]
fn trait_impl_expansion_uses_injective_type_encoding() {
    let path_impl: syn::ItemImpl = syn::parse2(quote! {
        impl Demo for foo::Bar {
            fn value(&self) -> i32 {
                0
            }
        }
    })
    .expect("parse path impl");
    let underscore_impl: syn::ItemImpl = syn::parse2(quote! {
        impl Demo for foo_bar {
            fn value(&self) -> i32 {
                0
            }
        }
    })
    .expect("parse underscore impl");

    let path_expanded = normalize(expand_trait_impl(path_impl));
    let underscore_expanded = normalize(expand_trait_impl(underscore_impl));

    assert!(path_expanded.contains("__trust_vc_trait_impl_decl_Demo_foo_P__P_Bar"));
    assert!(underscore_expanded.contains("__trust_vc_trait_impl_decl_Demo_foo__bar"));
    assert!(path_expanded.contains("foo_P__P_Bar__value"));
    assert!(underscore_expanded.contains("foo__bar__value"));
}

#[test]
fn trait_spec_expansion_preserves_non_trust_vc_contract_like_attributes() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Sortable {
            #[other::requires(self.len() > 1)]
            #[trust_vc::requires(self.len() > 0)]
            fn sort(&self) -> Self;
        }
    })
    .expect("parse trait");

    let expanded = normalize(expand_trait_spec(input));
    assert!(expanded.contains("other::requires"));
    assert!(!expanded.contains("trust_vc::requires"));
    // The requires condition appears as a positional arg in TraitMethodDecl::new(...)
    assert!(
        expanded.contains("vec![\"self.len()>0\".to_string()]"),
        "requires condition should be passed to TraitMethodDecl: {expanded}"
    );
}

#[test]
fn trait_spec_expansion_reports_trait_specific_contract_errors() {
    let input: syn::ItemTrait = syn::parse2(quote! {
        trait Sortable {
            #[requires = "self.len() > 0"]
            fn sort(&self) -> Self;
        }
    })
    .expect("parse trait");

    let expanded = normalize(expand_trait_spec(input));
    assert!(expanded.contains("trait_spec"));
    assert!(!expanded.contains("extern_spec"));
}
