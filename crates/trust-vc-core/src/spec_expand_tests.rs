// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::expand_spec;
use quote::quote;

fn normalize_tokens(tokens: proc_macro2::TokenStream) -> String {
    tokens
        .to_string()
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

#[test]
fn expand_spec_uses_type_param_for_generic_signature_types() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        fn identity<T>(x: T) -> T {
            x
        }
    })
    .expect("parse generic spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains(
            "declare_var_typed(\"x\",::trust_vc_core::ir::TrustVcType::TypeParam(\"T\".to_string()))"
        ),
        "generic params should be declared with TypeParam: {expanded}"
    );
    assert!(
        expanded.contains(
            "vec![(\"x\".to_string(),::trust_vc_core::ir::TrustVcType::TypeParam(\"T\".to_string()))],"
        ),
        "function context should keep generic params typed: {expanded}"
    );
    assert!(
        expanded.contains(
            "::trust_vc_core::ir::TrustVcType::TypeParam(\"T\".to_string()),::trust_vc_core::mode::FunctionMode::Spec,"
        ),
        "generic return type should stay typed: {expanded}"
    );
    assert!(
        !expanded.contains("TrustVcType::Opaque(\"T\".to_string())"),
        "generic signature types should not fall back to Opaque: {expanded}"
    );
}

#[test]
fn expand_spec_leaves_non_generic_unknown_types_opaque() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        fn echo_widget(x: Widget) -> Widget {
            x
        }
    })
    .expect("parse opaque spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains("declare_var_typed(\"x\",")
            && expanded.contains("TrustVcType::Opaque(\"Widget\".to_string())"),
        "non-generic unknown types should use typed registration with Opaque: {expanded}"
    );
    assert!(
        expanded.contains(
            "::trust_vc_core::ir::TrustVcType::Opaque(\"Widget\".to_string()),::trust_vc_core::mode::FunctionMode::Spec,"
        ),
        "non-generic unknown return types should remain opaque: {expanded}"
    );
}

#[test]
fn expand_spec_preserves_trait_bounds_in_function_context() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        fn sort_wrapper<T: Sortable>(x: T) -> T
        where
            T: Audited,
        {
            x
        }
    })
    .expect("parse trait-bound spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains(".with_trait_bounds(vec!["),
        "function context should populate trait_bounds: {expanded}"
    );
    assert!(
        expanded.contains("declare_helper_function_typed_with_bounds"),
        "helper registration should preserve trait bounds too: {expanded}"
    );
    let helper_call_start = expanded
        .find("declare_helper_function_typed_with_bounds")
        .expect("helper registration should be present in expansion");
    let function_context_start = expanded
        .find("__trust_vc_ctx.set_function_context")
        .expect("function context should be present in expansion");
    let helper_section = &expanded[helper_call_start..function_context_start];
    let function_context_section = &expanded[function_context_start..];

    for (bound, helper_message, context_message) in [
        (
            "::trust_vc_core::ir::TraitBound::new(\"T\",\"Sortable\")",
            "helper registration should preserve the generic-bound trait",
            "function context should preserve the generic-bound trait",
        ),
        (
            "::trust_vc_core::ir::TraitBound::new(\"T\",\"Audited\")",
            "helper registration should preserve the where-clause trait",
            "function context should preserve the where-clause trait",
        ),
    ] {
        assert!(
            helper_section.contains(bound),
            "{}: {expanded}",
            helper_message
        );
        assert!(
            function_context_section.contains(bound),
            "{}: {expanded}",
            context_message
        );
    }
    assert_eq!(
        expanded
            .matches("::trust_vc_core::ir::TraitBound::new(\"T\",\"Sortable\")")
            .count(),
        2,
        "generic-bound trait should appear in helper registration and function context: {expanded}"
    );
    assert_eq!(
        expanded
            .matches("::trust_vc_core::ir::TraitBound::new(\"T\",\"Audited\")")
            .count(),
        2,
        "where-clause trait should appear in helper registration and function context: {expanded}"
    );
}

#[test]
fn expand_spec_rlimit_emits_set_rlimit_call() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        #[rlimit(5000)]
        fn fast_spec(x: u64) -> u64 {
            x
        }
    })
    .expect("parse rlimit spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains("set_rlimit(5000u64)"),
        "rlimit attribute should emit set_rlimit call: {expanded}"
    );
    assert!(
        !expanded.contains("#[rlimit"),
        "rlimit attribute should be stripped from output: {expanded}"
    );
}

#[test]
fn expand_spec_without_rlimit_omits_set_rlimit() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        fn normal_spec(x: u64) -> u64 {
            x
        }
    })
    .expect("parse normal spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        !expanded.contains("set_rlimit"),
        "no rlimit attribute should not emit set_rlimit: {expanded}"
    );
}

#[test]
fn expand_spec_rejects_returns_attr() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        #[returns(result)]
        fn spec_with_returns(x: u8) -> bool {
            x == 3
        }
    })
    .expect("parse spec fn with returns attr");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains("compile_error!"),
        "spec function returns attr should produce compile_error: {expanded}"
    );
    assert!(
        expanded.contains("specfunctionscannothave`returns`clause"),
        "error message should match Verus diagnostic: {expanded}"
    );
}

// --- Inline spec function attribute tests (#2488) ---

#[test]
fn expand_spec_inline_emits_with_inline_true() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        #[inline]
        fn double(x: i32) -> i32 {
            x + x
        }
    })
    .expect("parse inline spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains(".with_inline(true)"),
        "inline attribute should emit with_inline(true): {expanded}"
    );
    assert!(
        !expanded.contains("#[inline"),
        "inline attribute should be stripped from output: {expanded}"
    );
}

#[test]
fn expand_spec_non_inline_emits_with_inline_false() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        fn normal(x: i32) -> i32 {
            x
        }
    })
    .expect("parse normal spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains(".with_inline(false)"),
        "non-inline should emit with_inline(false): {expanded}"
    );
}

#[test]
fn expand_spec_inline_opaque_conflict_produces_compile_error() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        #[inline]
        #[opaque]
        fn bad_spec(x: i32) -> i32 {
            x
        }
    })
    .expect("parse inline+opaque spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains("compile_error!"),
        "inline+opaque should produce compile_error: {expanded}"
    );
    assert!(
        expanded.contains("mutuallyexclusive"),
        "error message should mention mutual exclusion: {expanded}"
    );
}

#[test]
fn expand_spec_inline_recursive_produces_compile_error() {
    crate::mode::clear_compile_time_mode_registry();
    let input: syn::ItemFn = syn::parse2(quote! {
        #[inline]
        fn fact(n: u64) -> u64 {
            if n == 0 { 1 } else { n * fact(n - 1) }
        }
    })
    .expect("parse inline recursive spec fn");

    let expanded = normalize_tokens(expand_spec(input));

    assert!(
        expanded.contains("compile_error!"),
        "inline recursive spec should produce compile_error: {expanded}"
    );
    assert!(
        expanded.contains("cannotbeusedonrecursivespecfunctions"),
        "error message should mention recursive inline rejection: {expanded}"
    );
}
