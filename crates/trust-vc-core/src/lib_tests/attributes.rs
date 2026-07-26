// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_expand_broadcast_and_trigger_emit_doc_attrs_2569() {
    clear_expand_proof_registries();
    let input = quote! {
        fn lemma_sum_nonneg(n: u64) {
            trust_vc::ensures!(sum(n) >= 0);
        }
    };

    let broadcast_input: syn::ItemFn = syn::parse2(input).expect("parse broadcast fn");
    let broadcasted = expand_broadcast_with_group(broadcast_input, Some("arith".to_string()));
    let broadcast_fn: syn::ItemFn =
        syn::parse2(broadcasted).expect("broadcast expansion should produce a valid function");
    let triggered = expand_trigger_with_group(broadcast_fn, quote!(sum(n), group = 2));
    let triggered_fn: syn::ItemFn =
        syn::parse2(triggered).expect("trigger expansion should produce a valid function");
    let auto = expand_auto_trigger(triggered_fn);
    let generated: syn::ItemFn =
        syn::parse2(auto).expect("auto_trigger expansion should produce a valid function");

    let broadcast_metadata =
        crate::attr_doc_metadata::extract_broadcast_doc_metadata(&generated.attrs)
            .expect("broadcast metadata extraction should succeed")
            .expect("broadcast metadata should be present");
    assert!(broadcast_metadata.is_broadcast);
    assert_eq!(broadcast_metadata.group_name.as_deref(), Some("arith"));

    let trigger_metadata = crate::attr_doc_metadata::extract_trigger_doc_metadata(&generated.attrs)
        .expect("trigger metadata extraction should succeed")
        .expect("trigger metadata should be present");
    let expected_pattern = quote!(sum(n)).to_string();
    assert_eq!(
        trigger_metadata.triggers,
        vec![crate::attr_doc_metadata::TriggerDocEntry {
            index: 0,
            group: 2,
            pattern: expected_pattern,
        }]
    );
    assert_eq!(
        trigger_metadata.mode,
        Some(crate::attr_doc_metadata::TriggerModeDoc::Conservative)
    );
}

#[test]
fn test_expand_spec() {
    let input = quote! {
        fn spec_function(x: i32) -> bool {
            x > 0
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_spec(ast);

    // Parse the result to verify structure
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name is preserved
    assert_eq!(generated.sig.ident, "spec_function");

    // Verify the function returns bool
    match &generated.sig.output {
        syn::ReturnType::Type(_, ty) => {
            // Check if return type is bool
            let ty_str = quote!(#ty).to_string();
            assert_eq!(ty_str, "bool");
        }
        _ => panic!("Expected a return type"),
    }
}

#[test]
fn test_expand_spec_allows_unregistered_constructor_calls() {
    crate::mode::clear_compile_time_mode_registry();
    let input = quote! {
        fn spec_unknown_constructor_2081<T: Default>(x: i32) -> Option<T> {
            if x > 0 {
                Some(T::default())
            } else {
                None
            }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_spec(ast);
    let result_str = result.to_string();

    assert!(
        !result_str.contains("compile_error"),
        "spec expansion should allow constructor/default calls: {}",
        result_str
    );
    let generated: syn::ItemFn =
        syn::parse2(result).expect("spec expansion should emit a function item");
    assert_eq!(generated.sig.ident, "spec_unknown_constructor_2081");
}

#[test]
fn test_expand_spec_after_decreases_allows_injected_runtime_calls() {
    crate::mode::clear_compile_time_mode_registry();
    let input = quote! {
        fn spec_with_decreases_2081(n: u64) -> Option<u64> {
            if n == 0 {
                Some(0)
            } else {
                spec_with_decreases_2081(n - 1)
            }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let decreased = expand_decreases_with_clauses(ast, quote! { n });
    let decreased_fn: syn::ItemFn =
        syn::parse2(decreased).expect("decreases expansion should produce a function item");
    let spec_expanded = expand_spec(decreased_fn);
    let spec_str = spec_expanded.to_string();

    assert!(
        !spec_str.contains("compile_error"),
        "spec mode validation should ignore unregistered injected calls: {}",
        spec_str
    );
    let generated: syn::ItemFn =
        syn::parse2(spec_expanded).expect("combined decreases+spec should remain a function item");
    assert_eq!(generated.sig.ident, "spec_with_decreases_2081");
}

#[test]
fn test_expand_broadcast() {
    let input = quote! {
        fn broadcast_lemma(x: i32) {
            trust_vc::assert!(x * 0 == 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_broadcast(ast);

    // Parse the result to verify structure
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name is preserved
    assert_eq!(generated.sig.ident, "broadcast_lemma");

    // Verify it has a doc comment about being a broadcast lemma
    assert!(generated.attrs.iter().any(|attr| {
        if let syn::Meta::NameValue(meta) = &attr.meta {
            meta.path.is_ident("doc")
        } else {
            false
        }
    }));
}

#[test]
fn test_expand_broadcast_registers_proof_mode() {
    let input = quote! {
        fn broadcast_lemma(x: i32) {
            trust_vc::ensures!(x >= 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_broadcast(ast).to_string();

    assert!(
        result.contains("register_function_mode"),
        "broadcast expansion should register a runtime function mode: {result}"
    );
    assert!(
        result.contains("FunctionMode :: Proof") || result.contains("FunctionMode::Proof"),
        "broadcast expansion should register as proof mode: {result}"
    );
}

#[test]
fn test_expand_broadcast_self_param_fails_closed_1753() {
    let input = quote! {
        fn broadcast_method_1753(&self, x: i32) {
            trust_vc::assert!(x > 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_broadcast(ast);
    let result_str = result.to_string();

    assert!(
        result_str.contains("compile_error"),
        "broadcast self parameter should fail closed with compile_error, got: {result_str}"
    );
    assert!(
        result_str.contains("does not support self parameters"),
        "broadcast self parameter error should explain the unsupported pattern, got: {result_str}"
    );
    assert_eq!(
        result_str.matches("collect_variable").count(),
        1,
        "named broadcast parameters should still register while self fails closed"
    );
}

#[test]
fn test_expand_broadcast_tuple_param_fails_closed_1753() {
    let input = quote! {
        fn broadcast_tuple_1753((a, b): (i32, i32)) {
            trust_vc::assert!(a + b > 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_broadcast(ast);
    let result_str = result.to_string();

    assert!(
        result_str.contains("compile_error"),
        "broadcast tuple parameter should fail closed with compile_error, got: {result_str}"
    );
    assert!(
        result_str.contains("does not support complex parameter patterns"),
        "broadcast tuple parameter error should explain the unsupported pattern, got: {result_str}"
    );
    assert_eq!(
        result_str.matches("collect_variable").count(),
        0,
        "tuple destructuring should not register partial broadcast variables before failing closed"
    );
}

#[test]
fn test_expand_memoize() {
    let input = quote! {
        fn fib(n: u64) -> u64 {
            if n <= 1 { n } else { fib(n-1) + fib(n-2) }
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_memoize(ast);

    // Parse the result to verify structure
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name is preserved
    assert_eq!(generated.sig.ident, "fib");

    // Verify return type
    match &generated.sig.output {
        syn::ReturnType::Type(_, ty) => {
            let ty_str = quote!(#ty).to_string();
            assert_eq!(ty_str, "u64");
        }
        _ => panic!("Expected a return type"),
    }
}

#[test]
fn test_expand_trigger_with_group() {
    let attr_tokens = quote! { 1, sum(n) };
    let input = quote! {
        fn grouped_trigger(n: i32) {
            assert!(sum(n) >= 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_trigger_with_group(ast, attr_tokens);

    let result_str = result.to_string();
    // Should include trigger group marker
    assert!(result_str.contains("__trust_vc_trigger_group"));
    assert!(result_str.contains("grouped_trigger"));
}

#[test]
fn test_expand_auto_trigger() {
    let input = quote! {
        fn auto_triggered(x: i32) {
            assert!(x * x >= 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_auto_trigger(ast);

    let result_str = result.to_string();
    // Should include trigger mode marker (normalize spaces)
    let normalized = result_str.replace(" ", "");
    assert!(normalized.contains("trust_vc_runtime::__trigger::auto_conservative"));
    assert!(result_str.contains("auto_triggered"));
}

#[test]
fn test_expand_all_triggers() {
    let input = quote! {
        fn all_triggers_fn(x: i32, y: i32) {
            assert!(x + y >= 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_all_triggers(ast);

    let result_str = result.to_string();
    // Should include all triggers marker (normalize spaces)
    let normalized = result_str.replace(" ", "");
    assert!(normalized.contains("trust_vc_runtime::__trigger::auto_aggressive"));
    assert!(result_str.contains("all_triggers_fn"));
}

#[test]
fn test_expand_via_fn() {
    let input = quote! {
        fn via_function(n: u64) -> u64 {
            n * 2
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_via_fn(ast);

    let result_str = result.to_string();
    // Should include via marker
    assert!(result_str.contains("__trust_vc_via_fn"));
    assert!(result_str.contains("via_function"));
    assert!(result_str.contains("Via function"));
}

#[test]
fn test_expand_returns() {
    let return_names = quote! { (result, success) };
    let input = quote! {
        fn returns_tuple() -> (i32, bool) {
            (42, true)
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_returns(ast, return_names);

    let result_str = result.to_string();
    // Should include return names marker
    assert!(result_str.contains("__trust_vc_return_names"));
    assert!(result_str.contains("returns_tuple"));
}

#[test]
fn test_expand_external_body() {
    let input = quote! {
        fn external_impl() -> i32 {
            // External implementation
            42
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_external_body(ast);

    let result_str = result.to_string();
    // Should include external body marker
    assert!(result_str.contains("__trust_vc_external_body"));
    assert!(result_str.contains("external_impl"));
}

#[test]
fn test_expand_opens_invariants() {
    let attr_tokens = quote! { set1.inv, set2.inv };
    let input = quote! {
        fn opens_multiple() {
            // Function that opens invariants
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_opens_invariants(ast, attr_tokens);

    let result_str = result.to_string();
    // Should include opens invariants marker
    assert!(result_str.contains("__trust_vc_opens_invariants"));
    assert!(result_str.contains("opens_multiple"));
    assert!(
        result_str.contains("set1 . inv"),
        "field-path invariants should survive expansion: {result_str}"
    );
    assert!(
        result_str.contains(". namespace ()"),
        "specific invariants should be lowered through namespace() calls: {result_str}"
    );
}
