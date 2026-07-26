// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for protocol_expand.rs: `expand_protocol`, `expand_action`,
//! `expand_safety`, `expand_liveness`.
//!
//! Coverage targets: struct/function preservation, registration code emission,
//! attribute passthrough, and edge cases (empty fields, multiple actions).

use super::*;

// ──── expand_protocol ────────────────────────────────────────────────────

#[test]
fn test_expand_protocol_preserves_struct_and_emits_registration() {
    let input: syn::ItemStruct = syn::parse2(quote! {
        struct Counter {
            count: u64,
            enabled: bool,
        }
    })
    .expect("parse protocol struct");

    let expanded = expand_protocol(input);
    let expanded_str = expanded.to_string();

    // Original struct must survive.
    assert!(
        expanded_str.contains("Counter"),
        "struct name must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("count"),
        "struct field 'count' must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("enabled"),
        "struct field 'enabled' must be preserved: {expanded_str}"
    );

    // Registration method must be emitted.
    assert!(
        expanded_str.contains("__trust_vc_register_protocol"),
        "protocol expansion must emit __trust_vc_register_protocol method: {expanded_str}"
    );
    assert!(
        expanded_str.contains("register_protocol_state_var"),
        "protocol expansion must register state vars: {expanded_str}"
    );
}

#[test]
fn test_expand_protocol_empty_struct_emits_registration_without_fields() {
    let input: syn::ItemStruct = syn::parse2(quote! {
        struct EmptyProtocol {}
    })
    .expect("parse empty struct");

    let expanded = expand_protocol(input);
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("__trust_vc_register_protocol"),
        "empty struct must still emit registration method: {expanded_str}"
    );
    // No field registrations should appear.
    assert!(
        !expanded_str.contains("register_protocol_state_var"),
        "empty struct should have no state var registrations: {expanded_str}"
    );
}

// ──── expand_action ──────────────────────────────────────────────────────

#[test]
fn test_expand_action_preserves_function_and_emits_registration() {
    let input: syn::ItemFn = syn::parse2(quote! {
        fn increment(state: &mut Counter) {
            state.count += 1;
        }
    })
    .expect("parse action fn");

    let expanded = expand_action(input, "Counter");
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("increment"),
        "action function name must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("register_protocol_action"),
        "action expansion must emit register_protocol_action call: {expanded_str}"
    );
    assert!(
        expanded_str.contains("\"Counter\""),
        "action must reference its protocol name: {expanded_str}"
    );
}

// ──── expand_safety ──────────────────────────────────────────────────────

#[test]
fn test_expand_safety_preserves_function_and_emits_invariant_registration() {
    let input: syn::ItemFn = syn::parse2(quote! {
        fn count_nonneg(state: &Counter) -> bool {
            state.count >= 0
        }
    })
    .expect("parse safety fn");

    let expanded = expand_safety(input, "Counter");
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("count_nonneg"),
        "safety function name must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("register_protocol_invariant"),
        "safety expansion must emit register_protocol_invariant call: {expanded_str}"
    );
    assert!(
        expanded_str.contains("\"Counter\""),
        "safety must reference its protocol name: {expanded_str}"
    );
}

// ──── expand_liveness ────────────────────────────────────────────────────

#[test]
fn test_expand_liveness_preserves_function_and_emits_liveness_registration() {
    let input: syn::ItemFn = syn::parse2(quote! {
        fn eventually_enabled(state: &Counter) -> bool {
            state.enabled
        }
    })
    .expect("parse liveness fn");

    let expanded = expand_liveness(input, "Counter", "weak");
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("eventually_enabled"),
        "liveness function name must be preserved: {expanded_str}"
    );
    assert!(
        expanded_str.contains("register_protocol_liveness"),
        "liveness expansion must emit register_protocol_liveness call: {expanded_str}"
    );
    assert!(
        expanded_str.contains("\"Counter\""),
        "liveness must reference its protocol name: {expanded_str}"
    );
    assert!(
        expanded_str.contains("\"weak\""),
        "liveness must include fairness specifier: {expanded_str}"
    );
}
