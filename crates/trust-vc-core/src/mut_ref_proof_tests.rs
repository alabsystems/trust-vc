// Soundness-critical tests for mut_ref_proof.rs
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Companion test file for mut_ref_proof.rs.
// Wire into mut_ref_proof.rs with:
//   #[cfg(test)]
//   #[path = "mut_ref_proof_tests.rs"]
//   mod soundness_tests;
//
// Part of #2421 strategic audit.

use super::transform_proof_body;
use quote::quote;

// --- Store inside control flow must be rejected (soundness) ---
//
// If stores inside control flow were silently accepted, SSA versioning would
// break: the version bump happens unconditionally but the store is conditional.
// This creates a mismatch between the runtime store and the shadow variable,
// making proofs unsound.

#[test]
fn rejects_store_inside_if() {
    let input = quote! {
        fn bad(x: &mut i32) {
            if *x > 0 {
                *x = *x - 1;
            }
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|tokens| tokens.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("top-level"),
        "store inside if should be rejected as non-top-level: {errors}"
    );
}

#[test]
fn rejects_store_inside_while() {
    let input = quote! {
        fn bad(x: &mut i32) {
            while *x > 0 {
                *x = *x - 1;
            }
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|tokens| tokens.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("top-level"),
        "store inside while should be rejected as non-top-level: {errors}"
    );
}

#[test]
fn rejects_store_inside_nested_block() {
    let input = quote! {
        fn bad(x: &mut i32) {
            {
                *x = *x + 1;
            }
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|tokens| tokens.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("top-level"),
        "store inside nested block should be rejected as non-top-level: {errors}"
    );
}

// --- old!(param) bare param error ---

#[test]
fn rejects_old_bare_param() {
    let input = quote! {
        fn bad(x: &mut i32) {
            *x = *x + 1;
            trust_vc::ensures!(*x == old!(x) + 1);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let errors = transformed
        .errors
        .iter()
        .map(|tokens| tokens.to_string())
        .collect::<Vec<_>>()
        .join("\n");

    assert!(
        errors.contains("old!(*x)"),
        "old!(x) on &mut param should suggest old!(*x): {errors}"
    );
}

// --- assert_by rewriting ---

#[test]
fn rewrites_assert_by_with_mut_ref() {
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
        "assert_by with valid mut-ref usage should not error: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_x_1 > 0"),
        "assert_by condition should rewrite *x to current shadow: {block}"
    );
}
