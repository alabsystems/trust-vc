// Additional proof-coverage tests for broadcast expansion helpers.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn normalize_tokens(tokens: &TokenStream) -> String {
    tokens
        .to_string()
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

#[test]
fn test_trigger_with_multiple_patterns_falls_back_to_original_tokens() {
    let tokens: TokenStream = quote::quote! { f(a), g(b) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);

    assert_eq!(group, 0, "multiple patterns should fall back to group 0");
    assert_eq!(
        pattern,
        tokens.to_string(),
        "multiple-pattern trigger input should remain unchanged"
    );
}

#[test]
fn test_trigger_with_negative_group_falls_back_to_original_tokens() {
    let tokens: TokenStream = quote::quote! { -1, sum(n) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);

    assert_eq!(group, 0, "negative groups should not parse as valid groups");
    assert_eq!(
        pattern,
        tokens.to_string(),
        "malformed group input should preserve the original pattern"
    );
}

#[test]
fn test_expand_broadcast_params_collects_named_parameters() {
    let sig: syn::Signature = syn::parse_quote!(fn lemma_sum_nonneg(n: u64, elems: Seq<u8>));
    let (errors, declarations) = expand_broadcast_params(&sig);

    assert!(errors.is_empty(), "named parameters should not emit errors");
    assert_eq!(declarations.len(), 2, "both parameters should be collected");

    let declarations = declarations
        .iter()
        .map(normalize_tokens)
        .collect::<Vec<_>>()
        .join("");
    assert!(
        declarations.contains("collect_variable(\"n\".to_string(),\"u64\".to_string())"),
        "first parameter should register its name and type: {declarations}"
    );
    assert!(
        declarations.contains("collect_variable(\"elems\".to_string(),\"Seq<u8>\".to_string())"),
        "second parameter should register its name and type: {declarations}"
    );
}

#[test]
fn test_expand_broadcast_params_rejects_complex_patterns() {
    let sig: syn::Signature =
        syn::parse_quote!(fn lemma_sum_nonneg((lhs, rhs): (u64, u64), n: u64));
    let (errors, declarations) = expand_broadcast_params(&sig);

    assert_eq!(
        declarations.len(),
        1,
        "only the simple named parameter should be collected"
    );

    let errors = errors
        .iter()
        .map(normalize_tokens)
        .collect::<Vec<_>>()
        .join("");
    assert!(
        errors.contains("compile_error!"),
        "complex parameter patterns should fail closed: {errors}"
    );
    assert!(
        errors.contains("trust_vc::broadcastdoesnotsupportcomplexparameterpatterns"),
        "complex pattern error text should explain the restriction: {errors}"
    );
}

#[test]
fn test_expand_broadcast_params_rejects_self_receiver() {
    let sig: syn::Signature = syn::parse_quote!(fn lemma_sum_nonneg(&self));
    let (errors, declarations) = expand_broadcast_params(&sig);

    assert!(
        declarations.is_empty(),
        "receiver methods should not register vars"
    );

    let errors = errors
        .iter()
        .map(normalize_tokens)
        .collect::<Vec<_>>()
        .join("");
    assert!(
        errors.contains("compile_error!"),
        "self receivers should fail closed: {errors}"
    );
    assert!(
        errors.contains("trust_vc::broadcastdoesnotsupportselfparameters"),
        "receiver error text should explain the free-function requirement: {errors}"
    );
}

#[test]
fn test_expand_broadcast_with_group_registers_group_and_parameters() {
    let func: ItemFn = syn::parse_quote! {
        fn lemma_sum_nonneg(n: u64, elems: Seq<u8>) {}
    };
    let output = expand_broadcast_with_group(func, Some("arith".to_string()));
    let output = normalize_tokens(&output);

    assert!(
        output.contains("__trust_vc_broadcast_lemma"),
        "broadcast expansion should emit the trust_mc marker: {output}"
    );
    assert!(
        output.contains("BroadcastGuard::enter()"),
        "test-mode broadcast expansion should install the broadcast guard: {output}"
    );
    assert!(
        output.contains("collect_variable(\"n\".to_string(),\"u64\".to_string())"),
        "broadcast expansion should collect the first parameter: {output}"
    );
    assert!(
        output.contains("collect_variable(\"elems\".to_string(),\"Seq<u8>\".to_string())"),
        "broadcast expansion should collect the second parameter: {output}"
    );
    assert!(
        output.contains("register_broadcast_lemma_with_group"),
        "broadcast expansion should call the group registration helper: {output}"
    );
    assert!(
        output.contains("stringify!(lemma_sum_nonneg).to_string()"),
        "broadcast expansion should register the current lemma name: {output}"
    );
    assert!(
        output.contains("Some(\"arith\".to_string()),"),
        "broadcast expansion should register the selected group: {output}"
    );
}

#[test]
fn test_expand_broadcast_without_group_registers_none() {
    let func: ItemFn = syn::parse_quote! {
        fn lemma_sum_nonneg(n: u64) {}
    };
    let output = expand_broadcast(func);
    let output = normalize_tokens(&output);

    assert!(
        output.contains("register_broadcast_lemma_with_group"),
        "group-less broadcast expansion should call the registration helper: {output}"
    );
    assert!(
        output.contains("stringify!(lemma_sum_nonneg).to_string()"),
        "group-less broadcast expansion should register the current lemma name: {output}"
    );
    assert!(
        output.contains("None,"),
        "group-less broadcast expansion should register None: {output}"
    );
}

#[test]
fn test_expand_auto_trigger_sets_conservative_mode() {
    let func: ItemFn = syn::parse_quote! {
        fn lemma_sum_nonneg() {}
    };
    let output = expand_auto_trigger(func);
    let output = normalize_tokens(&output);

    assert!(
        output.contains("__trust_vc_auto_trigger_marker"),
        "auto_trigger should emit the trust_mc marker: {output}"
    );
    assert!(
        output.contains("set_trigger_inference_mode"),
        "auto_trigger should update inference mode under tests: {output}"
    );
    assert!(
        output.contains("TriggerInferenceMode::Conservative"),
        "auto_trigger should set conservative inference mode: {output}"
    );
}

#[test]
fn test_expand_all_triggers_sets_aggressive_mode() {
    let func: ItemFn = syn::parse_quote! {
        fn lemma_sum_nonneg() {}
    };
    let output = expand_all_triggers(func);
    let output = normalize_tokens(&output);

    assert!(
        output.contains("__trust_vc_all_triggers_marker"),
        "all_triggers should emit the trust_mc marker: {output}"
    );
    assert!(
        output.contains("set_trigger_inference_mode"),
        "all_triggers should update inference mode under tests: {output}"
    );
    assert!(
        output.contains("TriggerInferenceMode::Aggressive"),
        "all_triggers should set aggressive inference mode: {output}"
    );
}
