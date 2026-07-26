// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for MutRefRewriter control flow depth and old!() resolution.
//!
//! These test invariants in mut_ref_proof_rewriter.rs that are NOT covered
//! by the existing integration tests in mut_ref_proof_unit_tests.rs:
//!
//! 1. Top-level store restriction: stores inside control flow (if/while/loop)
//!    must NOT be expanded into shadow assignments (only top-level stores).
//! 2. old!() macro resolution: old!(*x) must resolve to entry shadow (v0),
//!    old!(x) must produce an error, old!(*x) in nested blocks is supported.
//! 3. Version tracking: independent places maintain independent version counts.
//! 4. Error collection: multiple errors should be accumulated, not short-circuit.

use super::transform_proof_body;
use quote::quote;

// ========================================================================
// Control flow depth: stores inside if/while/loop are NOT expanded
// ========================================================================

/// DISCRIMINATING: store inside `if` block must NOT create a shadow.
/// The rewriter only expands top-level stores (nested_block_depth == 0,
/// control_flow_depth == 0). Inside if/while/loop, the store remains
/// as-is but should produce an error.
#[test]
fn store_inside_if_produces_error() {
    let input = quote! {
        fn cond_store(x: &mut i32) {
            if true {
                *x = 42;
            }
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("top-level"),
        "store inside if must produce a 'top-level' restriction error: {errors}"
    );
}

/// DISCRIMINATING: store inside `while` loop must NOT create a shadow.
#[test]
fn store_inside_while_produces_error() {
    let input = quote! {
        fn loop_store(x: &mut i32) {
            while *x < 10 {
                *x = *x + 1;
            }
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("top-level"),
        "store inside while must produce a 'top-level' restriction error: {errors}"
    );
}

/// DISCRIMINATING: store inside `loop` must NOT create a shadow.
#[test]
fn store_inside_loop_produces_error() {
    let input = quote! {
        fn loop_store(x: &mut i32) {
            loop {
                *x = *x + 1;
                break;
            }
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("top-level"),
        "store inside loop must produce a 'top-level' restriction error: {errors}"
    );
}

// ========================================================================
// old!() macro resolution
// ========================================================================

/// old!(*x) before any store should resolve to the entry shadow (v0).
/// After a store, old!(*x) should still resolve to v0 (not current version).
#[test]
fn old_resolves_to_entry_shadow_after_store() {
    let input = quote! {
        fn check(x: &mut i32) {
            *x = *x + 1;
            trust_vc::ensures!(*x == old!(*x) + 1);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");

    // old!(*x) must resolve to version 0, while *x in ensures resolves to latest (v1)
    assert!(
        block.contains("__trust_vc_mutref_x_0"),
        "old!(*x) should resolve to entry shadow v0: {block}"
    );
}

/// old!(x) without deref on a &mut param must produce an error.
#[test]
fn old_without_deref_errors() {
    let input = quote! {
        fn bad(x: &mut i32) {
            trust_vc::ensures!(old!(x) == 0);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("old!(*x)"),
        "old!(x) without deref should suggest old!(*x): {errors}"
    );
}

/// old!() on a field place should resolve to entry shadow of that field.
#[test]
fn old_field_resolves_to_entry() {
    let input = quote! {
        fn check(s: &mut State) {
            s.count = s.count + 1;
            trust_vc::ensures!(s.count == old!(s.count) + 1);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(
        transformed.errors.is_empty(),
        "unexpected errors in field old!(): {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_s_count_0"),
        "old!(s.count) should resolve to field entry shadow v0: {block}"
    );
}

// ========================================================================
// Independent place versioning
// ========================================================================

/// Two independent field places should maintain separate version counters.
#[test]
fn independent_fields_have_independent_versions() {
    let input = quote! {
        fn update(s: &mut State) {
            s.a = s.a + 1;
            s.a = s.a + 1;
            s.b = 42;
            trust_vc::ensures!(s.a == old!(s.a) + 2);
            trust_vc::ensures!(s.b == 42);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    // s.a should be at version 2 (two stores)
    assert!(
        block.contains("__trust_vc_mutref_s_a_2"),
        "s.a should be at version 2 after two stores: {block}"
    );
    // s.b should be at version 1 (one store)
    assert!(
        block.contains("__trust_vc_mutref_s_b_1"),
        "s.b should be at version 1 after one store: {block}"
    );
    // s.a v0 should exist in old!() reference
    assert!(
        block.contains("__trust_vc_mutref_s_a_0"),
        "old!(s.a) should reference v0: {block}"
    );
}

// ========================================================================
// Multiple error accumulation
// ========================================================================

/// Multiple errors in one function should all be collected, not short-circuited.
#[test]
fn multiple_errors_accumulated() {
    let input = quote! {
        fn bad(x: &mut i32) {
            x;
            *x += 1;
            trust_vc::ensures!(old!(x) == 0);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);

    // Should have at least 3 errors:
    // 1. bare `x` use without deref
    // 2. compound assignment `*x += 1`
    // 3. old!(x) without deref
    assert!(
        transformed.errors.len() >= 3,
        "should accumulate multiple errors (bare x, compound assign, old!(x)), got {}: {:?}",
        transformed.errors.len(),
        transformed
            .errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );
}

// ========================================================================
// assert_by rewriting
// ========================================================================

/// assert_by! with a proof block should rewrite references inside the block.
#[test]
fn assert_by_rewrites_proof_block() {
    let input = quote! {
        fn check(x: &mut i32) {
            *x = *x + 1;
            trust_vc::assert_by!(*x > 0, {
                trust_vc::assert!(*x == old!(*x) + 1);
            });
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(
        transformed.errors.is_empty(),
        "unexpected errors in assert_by: {block}"
    );
    // The assert_by condition and its proof block should both be rewritten
    assert!(
        block.contains("__trust_vc_mutref_x_1"),
        "assert_by condition should use current version: {block}"
    );
}
