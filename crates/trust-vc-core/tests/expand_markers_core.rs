//! Core proc-macro expansion marker tests
//!
//! Tests that returns, external_body, proof, spec, memoize, and opens_invariants
//! attributes properly add expansion markers to generated code.
//!
//! Split from expand_markers.rs per #2380.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;
use syn::ItemFn;
use trust_vc_core::{
    expand_external_body, expand_memoize, expand_opens_invariants, expand_proof, expand_returns,
    expand_spec,
};

fn parse_fn() -> ItemFn {
    syn::parse2(quote! {
        fn add_one(x: i32) -> i32 {
            x + 1
        }
    })
    .expect("parse test function")
}

#[test]
fn expand_returns_includes_marker() {
    let input = parse_fn();
    let expanded = expand_returns(input, quote!(ret));
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_return_names"),
        "expected return marker in expansion: {expanded_str}"
    );
}

#[test]
fn expand_external_body_includes_marker() {
    let input = parse_fn();
    let expanded = expand_external_body(input);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_external_body"),
        "expected external_body marker in expansion: {expanded_str}"
    );
}

// ============================================================================
// Proof Markers (spec/proof functions)
// ============================================================================

#[test]
fn expand_proof_produces_trust_mc_guarded_block() {
    let input: ItemFn = syn::parse2(quote! {
        fn lemma_positive(n: u64) {
            trust_vc::requires!(n > 0);
            trust_vc::ensures!(n >= 1);
        }
    })
    .expect("parse proof fn");
    let expanded = expand_proof(input);
    let expanded_str = expanded.to_string();
    // Proof functions should have cfg(trust_mc) guard
    assert!(
        expanded_str.contains("cfg (trust_mc)") || expanded_str.contains("cfg(trust_mc)"),
        "expected cfg(trust_mc) guard: {expanded_str}"
    );
    // Proof functions should have durable trust_vc:proof doc marker (#2482)
    assert!(
        expanded_str.contains("trust_vc:proof"),
        "expected #[doc = \"trust_vc:proof\"] marker (#2482): {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:requires:n > 0"),
        "expected durable requires doc marker (#2593): {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:ensures:n >= 1"),
        "expected durable ensures doc marker (#2593): {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:param:n:u64"),
        "expected durable param doc marker (#2593): {expanded_str}"
    );
}

#[test]
fn expand_spec_produces_ghost_function() {
    let input: ItemFn = syn::parse2(quote! {
        fn ghost_len(s: Seq<i32>) -> i32 {
            s.len() as i32
        }
    })
    .expect("parse spec fn");
    let expanded = expand_spec(input);
    let expanded_str = expanded.to_string();
    // Spec functions should have cfg(trust_mc) guard
    assert!(
        expanded_str.contains("cfg (trust_mc)") || expanded_str.contains("cfg(trust_mc)"),
        "expected cfg(trust_mc) guard: {expanded_str}"
    );
    // And should have unreachable at runtime (note: quote! produces "unreachable !")
    assert!(
        expanded_str.contains("unreachable !") || expanded_str.contains("unreachable!"),
        "expected unreachable at runtime: {expanded_str}"
    );
}

// ============================================================================
// Memoize Markers
// ============================================================================

#[test]
fn expand_memoize_includes_memoize_marker() {
    let input = parse_fn();
    let expanded = expand_memoize(input);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_memoize"),
        "expected memoize marker: {expanded_str}"
    );
}

// ============================================================================
// Opens Invariants Markers
// ============================================================================

#[test]
fn expand_opens_invariants_includes_marker() {
    let input = parse_fn();
    let attr = quote!(inv1, inv2);
    let expanded = expand_opens_invariants(input, attr);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_opens_invariants"),
        "expected opens_invariants marker: {expanded_str}"
    );
}
