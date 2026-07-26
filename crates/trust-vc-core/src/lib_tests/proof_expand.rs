// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_expand_proof_basic() {
    clear_expand_proof_registries();
    let input = quote! {
        fn test_proof(x: i32) -> i32 {
            x + 1
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof(ast);

    // Parse the result back to verify structure
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name is preserved
    assert_eq!(generated.sig.ident, "test_proof");

    // Verify the function has the durable trust_vc:proof doc marker (#2482)
    let result_str = quote!(#generated).to_string();
    assert!(
        result_str.contains("trust_vc:proof"),
        "proof expansion must emit #[doc = \"trust_vc:proof\"] marker (#2482): {result_str}"
    );
}

#[test]
fn test_expand_proof_with_parameters() {
    clear_expand_proof_registries();
    let input = quote! {
        fn verify_sum(a: i32, b: i32) -> i32 {
            a + b
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof(ast);

    // Parse the result and verify parameter tracking
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name and signature
    assert_eq!(generated.sig.ident, "verify_sum");

    // Verify we have two parameters (excluding self)
    let params: Vec<_> = generated
        .sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => Some(pat_type),
            _ => None,
        })
        .collect();

    assert_eq!(params.len(), 2);
}

#[test]
fn test_expand_proof_emits_static_contract_doc_attrs_2593() {
    clear_expand_proof_registries();
    let input = quote! {
        fn lemma_positive(x: u64) {
            trust_vc::requires!(x > 0);
            trust_vc::ensures!(x >= 1);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).expect("parse proof fn");
    let result = expand_proof(ast);
    let generated: syn::ItemFn =
        syn::parse2(result).expect("proof expansion should produce a valid function");

    let static_context = crate::static_extraction::extract_static_proof_context(
        &generated.attrs,
        &generated.sig.ident.to_string(),
    )
    .expect("static proof metadata extraction should succeed")
    .expect("static proof metadata should exist");

    assert_eq!(
        static_context.params,
        vec![("x".to_string(), "u64".to_string())]
    );
    assert_eq!(static_context.requires, vec!["x > 0"]);
    assert_eq!(static_context.ensures, vec!["x >= 1"]);
}

#[test]
fn test_expand_proof_self_param_does_not_emit_static_metadata_2593() {
    clear_expand_proof_registries();
    let input = quote! {
        fn method_proof_static_2593(&self, x: i32) {
            trust_vc::requires!(x > 0);
            trust_vc::ensures!(x >= 1);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).expect("parse proof fn");
    let result = expand_proof(ast);
    let result_str = result.to_string();
    let generated: syn::ItemFn =
        syn::parse2(result).expect("proof expansion should still produce a function item");

    assert!(
        result_str.contains("compile_error"),
        "self parameters must still fail closed, got: {result_str}"
    );
    assert!(
        crate::proof_doc_metadata::extract_proof_doc_metadata(&generated.attrs)
            .expect("proof metadata extraction should succeed")
            .is_none(),
        "compile-error proof expansions must not emit durable trust_vc:proof metadata"
    );
    assert!(
        crate::static_extraction::extract_static_proof_context(
            &generated.attrs,
            &generated.sig.ident.to_string(),
        )
        .expect("static proof metadata extraction should succeed")
        .is_none(),
        "compile-error proof expansions must not be discoverable via static extraction"
    );
}

#[test]
fn test_expand_proof_accepts_tracked_parameter_syntax_2427() {
    clear_expand_proof_registries();
    let ast = parse_item_fn_allow_tracked(quote! {
        fn tracked_proof_2427(tracked token: Token) {
            consume(token);
        }
    })
    .expect("tracked proof parameter syntax should normalize before expansion");
    let result = expand_proof(ast);
    let result_str = result.to_string();
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    assert_eq!(generated.sig.ident, "tracked_proof_2427");
    assert!(
        result_str.contains("collect_variable"),
        "tracked proof parameters should still register as verification variables"
    );

    let params: Vec<_> = generated
        .sig
        .inputs
        .iter()
        .filter_map(|arg| match arg {
            syn::FnArg::Typed(pat_type) => Some(pat_type),
            _ => None,
        })
        .collect();
    assert_eq!(params.len(), 1);

    let syn::Pat::Ident(binding) = &*params[0].pat else {
        panic!("tracked parameter should normalize to an identifier binding");
    };
    assert_eq!(binding.ident.to_string(), "token");
}

#[test]
fn test_expand_proof_rejects_unsafe_proof_fn() {
    clear_expand_proof_registries();
    let input = quote! {
        unsafe fn unsafe_proof_fn_fail() {}
    };

    let ast: syn::ItemFn = syn::parse2(input).expect("parse unsafe proof fn");
    let result = expand_proof(ast).to_string();

    assert!(
        result.contains("compile_error")
            && result.contains("unsafe")
            && result.contains("exec-mode functions"),
        "unsafe proof functions must fail closed with the Verus-compatible mode diagnostic: {result}"
    );
}

/// #2482: expand_proof_with_tracked must emit durable tracked-parameter doc attrs.
#[test]
fn test_expand_proof_with_tracked_emits_doc_attrs_2482() {
    clear_expand_proof_registries();
    let input = quote! {
        fn tracked_lemma(token: Token, perm: Perm) {
            consume(token, perm);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof_with_tracked(ast, &["token".into(), "perm".into()]);
    let result_str = result.to_string();

    assert!(
        result_str.contains("trust_vc:proof"),
        "tracked proof must emit #[doc = \"trust_vc:proof\"] marker: {result_str}"
    );
    assert!(
        result_str.contains("trust_vc:proof:tracked=token"),
        "tracked proof must emit tracked=token doc attr: {result_str}"
    );
    assert!(
        result_str.contains("trust_vc:proof:tracked=perm"),
        "tracked proof must emit tracked=perm doc attr: {result_str}"
    );

    // Round-trip: parse back and extract via proof_doc_metadata
    let generated: syn::ItemFn =
        syn::parse2(result).expect("tracked proof expansion should produce a valid function");
    let meta = crate::proof_doc_metadata::extract_proof_doc_metadata(&generated.attrs)
        .expect("extraction should succeed")
        .expect("proof metadata should be present");
    assert!(meta.is_proof);
    assert_eq!(meta.tracked_params, vec!["token", "perm"]);
}

#[test]
fn test_expand_proof_handles_self() {
    clear_expand_proof_registries();
    let input = quote! {
        fn method_proof(&self, x: i32) -> i32 {
            x * 2
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof(ast);

    // Parse the result to verify structure
    let generated: syn::ItemFn = syn::parse2(result).expect("Should generate valid Rust function");

    // Verify function name is preserved
    assert_eq!(generated.sig.ident, "method_proof");

    // Verify the function has a self parameter
    assert!(generated
        .sig
        .inputs
        .iter()
        .any(|arg| { matches!(arg, syn::FnArg::Receiver(_)) }));
}

// ========================================================================
// SOUNDNESS: #1753 — proof fns with self/complex patterns skip var registration
// ========================================================================

/// #1753: expand_proof with `&self` must fail closed instead of silently
/// skipping self registration in the verification context.
#[test]
fn test_expand_proof_self_param_missing_collect_variable_1753() {
    clear_expand_proof_registries();
    let input = quote! {
        fn method_proof_1753(&self, x: i32) {
            trust_vc::assert!(x > 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof(ast);
    let result_str = result.to_string();

    assert!(
        result_str.contains("compile_error"),
        "proof self parameter should fail closed with compile_error, got: {result_str}"
    );
    assert!(
        result_str.contains("does not support self parameters"),
        "self parameter error should explain the unsupported pattern, got: {result_str}"
    );
    let collect_count = result_str.matches("collect_variable").count();
    assert_eq!(
        collect_count, 1,
        "named parameters should still register while self fails closed (got {} calls)",
        collect_count
    );
}

/// #1753: expand_proof with tuple destructuring must fail closed instead of
/// silently skipping parameter registration.
#[test]
fn test_expand_proof_tuple_param_missing_collect_variable_1753() {
    clear_expand_proof_registries();
    let input = quote! {
        fn tuple_proof_1753((a, b): (i32, i32)) {
            trust_vc::assert!(a + b > 0);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof(ast);
    let result_str = result.to_string();

    assert!(
        result_str.contains("compile_error"),
        "tuple parameter should fail closed with compile_error, got: {result_str}"
    );
    assert!(
        result_str.contains("does not support complex parameter patterns"),
        "tuple parameter error should explain the unsupported pattern, got: {result_str}"
    );
    assert_eq!(
        result_str.matches("collect_variable").count(),
        0,
        "tuple destructuring should not register partial variables before failing closed"
    );

    // The generated function still parses structurally as an ItemFn even though
    // compilation must fail due to the inserted compile_error!.
    let generated: syn::ItemFn = syn::parse2(result)
        .expect("proof fn with tuple params should still generate a structured ItemFn");
    assert_eq!(generated.sig.ident, "tuple_proof_1753");
}

#[test]
fn test_expand_proof_tuple_param_does_not_register_contracts_2593() {
    clear_expand_proof_registries();
    let callee: syn::ItemFn = syn::parse2(quote! {
        fn tuple_contract_2593((x, y): (i32, i32)) {
            trust_vc::requires!(x > 0);
            trust_vc::ensures!(y >= 0);
        }
    })
    .expect("parse tuple proof fn");
    let callee_result = expand_proof(callee).to_string();
    assert!(
        callee_result.contains("compile_error"),
        "tuple destructuring must still fail closed, got: {callee_result}"
    );
    assert!(
        crate::contract_registry::lookup_compile_time_function_contract("tuple_contract_2593")
            .is_none(),
        "compile-error proof expansions must not leak call-site contracts into the registry"
    );

    let caller: syn::ItemFn = syn::parse2(quote! {
        fn caller_contract_2593(x: i32) {
            tuple_contract_2593((x, x));
        }
    })
    .expect("parse caller proof fn");
    let caller_result = expand_proof(caller).to_string();

    assert!(
        !caller_result.contains("tuple_contract_2593_requires_0"),
        "caller expansion should not inject requires from an invalid callee: {caller_result}"
    );
    assert!(
        !caller_result.contains("arity mismatch"),
        "caller expansion should not see stale contract-registry state from an invalid callee: {caller_result}"
    );
}

#[test]
fn test_expand_proof_tolerates_unregistered_helper_calls() {
    clear_expand_proof_registries();
    let input = quote! {
        fn proof_unknown_helper_2081() {
            helper_not_registered_2081(3);
        }
    };

    let ast: syn::ItemFn = syn::parse2(input).unwrap();
    let result = expand_proof(ast);
    let result_str = result.to_string();

    // Per #2081/#2440: unknown callees are skipped (assumed compatible),
    // not rejected as exec. This allows trait-bound methods, stdlib
    // constructors, and other functions not in the mode registry.
    assert!(
        !result_str.contains("compile_error"),
        "unregistered helper calls should be tolerated per #2081 semantics: {}",
        result_str
    );
    let generated: syn::ItemFn =
        syn::parse2(result).expect("proof expansion should emit a valid function item");
    assert_eq!(generated.sig.ident, "proof_unknown_helper_2081");
}

#[test]
fn test_expand_proof_injects_call_site_contract_checks_2513() {
    clear_expand_proof_registries();

    let callee: syn::ItemFn = syn::parse2(quote! {
        fn lemma_contract_2513(n: i32) {
            trust_vc::requires!(n > 0);
            trust_vc::ensures!(mystery_2513(n) == 7);
        }
    })
    .unwrap();
    let _ = expand_proof(callee);

    let caller: syn::ItemFn = syn::parse2(quote! {
        fn caller_contract_2513(x: i32) {
            lemma_contract_2513(x + 1);
        }
    })
    .unwrap();
    let result = expand_proof(caller);
    let result_str = result.to_string();

    assert!(result_str.contains("lemma_contract_2513_requires_0"));
    assert!(result_str.contains("lemma_contract_2513_ensures_0"));
    assert!(result_str.contains("ObligationKind :: Assert"));
    assert!(result_str.contains("ObligationKind :: Assume"));
    assert!(result_str.contains("x + 1"));
}

#[test]
fn test_expand_proof_surfaces_contract_rewrite_errors_2513() {
    clear_expand_proof_registries();
    crate::contract_registry::register_compile_time_function_contract(
        "lemma_broken_2513",
        crate::contract_registry::FunctionContract {
            param_names: vec!["x".to_string()],
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
        },
    );

    let caller: syn::ItemFn = syn::parse2(quote! {
        fn caller_contract_error_2513() {
            lemma_broken_2513();
        }
    })
    .unwrap();
    let result = expand_proof(caller).to_string();

    assert!(result.contains("compile_error"));
    assert!(result.contains("failed to rewrite proof-call requires clause 0"));
    assert!(result.contains("arity mismatch"));
}
