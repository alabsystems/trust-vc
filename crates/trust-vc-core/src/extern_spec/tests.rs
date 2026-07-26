// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use proc_macro2::Span;
use quote::quote;
use syn::{parse_quote, TypePath};

#[test]
fn test_parse_extern_spec_input() {
    let input: ExternSpecInput = parse_quote! {
        impl<T> Option::<T> {
            #[requires(self.is_some())]
            fn unwrap(self) -> T;

            fn is_some(&self) -> bool;
        }
    };

    assert_eq!(input.items.len(), 1);
    assert_eq!(input.items[0].methods.len(), 2);
}

#[test]
fn test_expand_extern_spec_basic() {
    let input: ExternSpecInput = parse_quote! {
        impl core::option::Option::<T> {
            #[requires(self.is_some())]
            #[ensures(Some(result) == old(self))]
            fn unwrap(self) -> T;
        }
    };

    let output = expand_extern_spec(input)
        .expect("expand_extern_spec should succeed for basic input")
        .to_string();
    assert!(output.contains("const _"));
    assert!(output.contains("__trust_vc_extern_spec"));
    assert!(output.contains("trust_vc:extern_spec:target"));
    assert!(output.contains("trust_vc:extern_spec:requires"));
    assert!(output.contains("trust_vc:extern_spec:ensures"));
}

#[test]
fn test_project_extern_spec_entries_preserve_generic_target_path() {
    let input: ExternSpecInput = parse_quote! {
        impl core::option::Option::<T> {
            #[requires(self.is_some())]
            fn unwrap(self) -> T;
        }
    };

    let entries = try_project_extern_spec_entries(input).expect("projection should succeed");
    assert_eq!(entries.len(), 1);
    assert_eq!(entries[0].target_path, "core::option::Option::<T>::unwrap");
    assert!(entries[0].param_names.is_empty());
    // token-stream to_string() inserts spaces around punctuation;
    // downstream verify reparses, so whitespace is semantically irrelevant (#1802)
    assert_eq!(entries[0].requires, vec!["self . is_some ()"]);
}

#[test]
fn test_try_project_extern_spec_entries_uses_parse_error_for_bare_requires() {
    let input = ExternSpecInput {
        items: vec![ExternImplBlock {
            generics: Default::default(),
            self_ty: parse_quote!(MyType),
            methods: vec![ExternMethod {
                attrs: vec![parse_quote!(#[requires])],
                sig: parse_quote!(fn foo(x: i32) -> i32),
            }],
        }],
    };

    match try_project_extern_spec_entries(input) {
        Err(TrustVcError::Parse { context, source }) => {
            assert_eq!(context, "parse extern_spec contract attribute");
            assert!(source.to_string().contains("parenthesized"));
        }
        other => panic!("expected TrustVcError::Parse, got {other:?}"),
    }
}

#[test]
fn test_try_project_extern_spec_entries_uses_parse_error_for_qualified_paths() {
    let input = ExternSpecInput {
        items: vec![ExternImplBlock {
            generics: Default::default(),
            self_ty: Type::Path(TypePath {
                qself: Some(syn::QSelf {
                    lt_token: Default::default(),
                    ty: Box::new(parse_quote!(T)),
                    position: 0,
                    as_token: Some(Default::default()),
                    gt_token: Default::default(),
                }),
                path: parse_quote!(Trait::Assoc),
            }),
            methods: vec![ExternMethod {
                attrs: vec![parse_quote!(#[requires(true)])],
                sig: parse_quote!(fn foo(x: i32) -> i32),
            }],
        }],
    };

    match try_project_extern_spec_entries(input) {
        Err(TrustVcError::Parse { context, source }) => {
            assert_eq!(context, "parse extern_spec target type");
            assert!(source.to_string().contains("Qualified paths"));
        }
        other => panic!("expected TrustVcError::Parse, got {other:?}"),
    }
}

#[test]
fn test_expand_extern_spec_multiple_methods() {
    let input: ExternSpecInput = parse_quote! {
        impl<T> Vec::<T> {
            #[requires(self.len() < self.capacity())]
            fn push(&mut self, value: T);

            #[ensures(result.is_some() == (old(self.len()) > 0))]
            fn pop(&mut self) -> Option::<T>;
        }
    };

    let output = expand_extern_spec(input)
        .expect("expand_extern_spec should succeed for multiple methods")
        .to_string();
    assert!(output.contains("__trust_vc_extern_spec"));
    assert!(output.contains("push"));
    assert!(output.contains("pop"));
}

#[test]
fn test_expand_extern_spec_error_on_qualified_path() {
    let input = ExternSpecInput {
        items: vec![ExternImplBlock {
            generics: Default::default(),
            self_ty: Type::Path(TypePath {
                qself: Some(syn::QSelf {
                    lt_token: Default::default(),
                    ty: Box::new(parse_quote!(T)),
                    position: 0,
                    as_token: Some(Default::default()),
                    gt_token: Default::default(),
                }),
                path: parse_quote!(Trait::Assoc),
            }),
            methods: vec![],
        }],
    };

    let err = expand_extern_spec(input).expect_err("qualified path should be rejected");
    assert!(err.to_string().contains("Qualified paths"));
}

#[test]
fn test_expand_rejects_bare_requires() {
    let input = ExternSpecInput {
        items: vec![ExternImplBlock {
            generics: Default::default(),
            self_ty: parse_quote!(MyType),
            methods: vec![ExternMethod {
                attrs: vec![parse_quote!(#[requires])],
                sig: parse_quote!(fn foo(x: i32) -> i32),
            }],
        }],
    };
    let err = expand_extern_spec(input).expect_err("bare #[requires] should be rejected");
    assert!(
        err.to_string().contains("parenthesized"),
        "bare #[requires] should be rejected"
    );
}

#[test]
fn test_expand_rejects_name_value_ensures() {
    let input = ExternSpecInput {
        items: vec![ExternImplBlock {
            generics: Default::default(),
            self_ty: parse_quote!(MyType),
            methods: vec![ExternMethod {
                attrs: vec![parse_quote!(#[ensures = "result > 0"])],
                sig: parse_quote!(fn foo(x: i32) -> i32),
            }],
        }],
    };
    let err = expand_extern_spec(input).expect_err("name-value #[ensures] should be rejected");
    assert!(
        err.to_string().contains("parenthesized"),
        "name-value #[ensures] should be rejected"
    );
}

#[test]
fn test_parse_extern_spec_without_turbofish_via_syn() {
    // #945: syn's parser accepts non-turbofish form internally. However, the
    // Rust compiler's macro-input parser rejects `Option<T>` (interprets `<` as
    // a comparison), so turbofish remains required at the proc-macro call site.
    // This test documents that the parser itself is not the limitation.
    let input: ExternSpecInput = parse_quote! {
        impl<T> core::option::Option<T> {
            #[requires(self.is_some())]
            fn unwrap(self) -> T;
        }
    };

    assert_eq!(input.items.len(), 1);
    assert_eq!(input.items[0].methods.len(), 1);
}

#[test]
fn test_turbofish_and_non_turbofish_produce_same_target_path() {
    // Both forms produce identical target paths when parsed by syn.
    // In practice, only turbofish works at the proc-macro level (Rust parser
    // limitation), but the internal parser treats them equivalently.
    let input_no_turbofish: ExternSpecInput = parse_quote! {
        impl<T> core::option::Option<T> {
            #[requires(self.is_some())]
            fn unwrap(self) -> T;
        }
    };
    let entries_a =
        try_project_extern_spec_entries(input_no_turbofish).expect("projection should succeed");

    let input_turbofish: ExternSpecInput = parse_quote! {
        impl<T> core::option::Option::<T> {
            #[requires(self.is_some())]
            fn unwrap(self) -> T;
        }
    };
    let entries_b =
        try_project_extern_spec_entries(input_turbofish).expect("projection should succeed");

    assert_eq!(
        entries_a[0].target_path, entries_b[0].target_path,
        "turbofish and non-turbofish must produce identical target paths"
    );
}

#[test]
fn test_stub_idents_injective_for_colons_vs_underscores() {
    let a = generate_stub_ident("foo::bar", "method", Span::call_site());
    let b = generate_stub_ident("foo_bar", "method", Span::call_site());
    assert_ne!(
        a.to_string(),
        b.to_string(),
        "foo::bar and foo_bar must produce distinct stub idents"
    );
}

#[test]
fn test_expand_replaces_self_in_params() {
    let sig: Signature = parse_quote!(fn merge(&self, other: Option<Self>) -> Self);
    let self_ty: Type = parse_quote!(MyType);

    let stub_sig = transform_sig_for_stub(&sig, &self_ty);
    let output = quote!(#stub_sig).to_string();

    assert!(
        !output.contains("Self"),
        "bare Self should be replaced everywhere: {output}"
    );
    assert!(
        output.contains("MyType"),
        "should contain concrete type: {output}"
    );
}
