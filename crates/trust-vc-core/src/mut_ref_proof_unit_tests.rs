// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::transform_proof_body;
use quote::quote;

#[test]
fn rewrites_top_level_store_and_ensures() {
    let input = quote! {
        fn bump(x: &mut i32) {
            *x = *x + 1;
            trust_vc::ensures!(*x == old!(*x) + 1);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("__trust_vc_mutref_x_0"),
        "entry shadow should be declared: {block}"
    );
    assert!(
        block.contains("collect_let_binding_runtime_value_from_ref"),
        "entry shadow should capture its runtime value: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_x_1"),
        "post-store shadow should be declared: {block}"
    );
    assert!(
        block
            .contains("trust_vc :: ensures ! (__trust_vc_mutref_x_1 == __trust_vc_mutref_x_0 + 1)"),
        "ensures condition should rewrite to shadow variables (old!() stripped): {block}"
    );
}

#[test]
fn rejects_raw_mut_ref_param_use() {
    let input = quote! {
        fn bad(x: &mut i32) {
            trust_vc::assert!(x > 0);
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
        errors.contains("must be used via `*x`"),
        "expected raw-parameter compile error, got: {errors}"
    );
}

#[test]
fn rejects_compound_assignment() {
    let input = quote! {
        fn bad(x: &mut i32) {
            *x += 1;
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
        errors.contains("compound assignment"),
        "expected compound-assignment compile error, got: {errors}"
    );
}

#[test]
fn rewrites_two_independent_mut_params() {
    let input = quote! {
        fn swap_like(a: &mut i32, b: &mut i32) {
            let tmp: i32 = *a;
            *a = *b;
            *b = tmp;
            trust_vc::ensures!(*a == old!(*b));
            trust_vc::ensures!(*b == old!(*a));
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("__trust_vc_mutref_a_0"),
        "entry shadow for a: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_b_0"),
        "entry shadow for b: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_a_1"),
        "post-store shadow for a: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_b_1"),
        "post-store shadow for b: {block}"
    );
    assert!(
        transformed.skipped_params.contains("a"),
        "a should be skipped from normal param registration"
    );
    assert!(
        transformed.skipped_params.contains("b"),
        "b should be skipped from normal param registration"
    );
}

#[test]
fn rewrites_requires_with_deref() {
    let input = quote! {
        fn bounded(x: &mut u32) {
            trust_vc::requires!(*x < 100);
            *x = *x + 1;
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("trust_vc :: requires ! (__trust_vc_mutref_x_0 < 100"),
        "requires should rewrite *x to entry shadow: {block}"
    );
}

#[test]
fn rewrites_old_inside_requires() {
    let input = quote! {
        fn bounded(x: &mut i32) {
            trust_vc::requires!(old!(*x) < 100);
            *x = *x + 1;
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("trust_vc :: requires ! (__trust_vc_mutref_x_0 < 100"),
        "old!(*x) in requires should resolve to entry shadow: {block}"
    );
}

#[test]
fn rejects_unsupported_referent_type() {
    let input = quote! {
        fn bad(x: &mut String) {
            *x = "hello".to_string();
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
        errors.contains("referent type is bool/integer"),
        "unsupported referent type should error: {errors}"
    );
}

#[test]
fn rewrites_field_place_with_frame_condition() {
    let input = quote! {
        fn bump(counter: &mut Counter) {
            counter.count = counter.count + 1;
            trust_vc::ensures!(counter.count == old!(counter.count) + 1);
            trust_vc::ensures!(counter.max == old!(counter.max));
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("__trust_vc_mutref_counter_count_0"),
        "entry shadow for count should exist: {block}"
    );
    assert!(
        block.contains("register_counterexample_display"),
        "entry shadow should register a counterexample alias: {block}"
    );
    assert!(
        block.contains("\"counter.count@0\""),
        "entry shadow alias should preserve the dotted source path: {block}"
    );
    assert!(
        block.contains("collect_let_binding_runtime_value_from_ref"),
        "field-place entry shadows should capture runtime values: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_counter_max_0"),
        "entry shadow for unchanged field should exist: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_counter_count_1"),
        "post-store shadow for changed field should exist: {block}"
    );
    assert!(
        block.contains("\"counter.count@1\""),
        "post-store alias should preserve the dotted source path: {block}"
    );
    assert!(
        block.contains(
            "trust_vc :: ensures ! (__trust_vc_mutref_counter_max_0 == __trust_vc_mutref_counter_max_0)"
        ),
        "untouched field should stay on entry shadow (old!() stripped): {block}"
    );
}

#[test]
fn rewrites_nested_field_place() {
    let input = quote! {
        fn bump(counter: &mut OuterCounter) {
            counter.inner.count = counter.inner.count + 1;
            trust_vc::ensures!(counter.inner.count == old!(counter.inner.count) + 1);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("__trust_vc_mutref_counter_inner_count_0"),
        "entry shadow for nested place should exist: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_counter_inner_count_1"),
        "post-store shadow for nested place should exist: {block}"
    );
}

#[test]
fn multiple_stores_advance_version() {
    let input = quote! {
        fn double_bump(x: &mut i32) {
            *x = *x + 1;
            *x = *x + 1;
            trust_vc::ensures!(*x == old!(*x) + 2);
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains("__trust_vc_mutref_x_1"),
        "first store creates version 1: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_x_2"),
        "second store creates version 2: {block}"
    );
    assert!(
        block.contains("__trust_vc_mutref_x_2 == __trust_vc_mutref_x_0 + 2"),
        "ensures uses latest version (old!() stripped): {block}"
    );
}

#[test]
fn rewrites_old_inside_assert() {
    let input = quote! {
        fn check(x: &mut i32) {
            *x = *x + 1;
            trust_vc::assert!(*x > old!(*x));
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);
    let transformed_block = &transformed.transformed_block;
    let block = quote!(#transformed_block).to_string();

    assert!(transformed.errors.is_empty(), "unexpected errors: {block}");
    assert!(
        block.contains(
            "trust_vc :: assert ! (__trust_vc_mutref_x_1 > __trust_vc_mutref_x_0)"
        ),
        "assert should rewrite *x to current shadow and old!(*x) to entry shadow (stripped): {block}"
    );
}

#[test]
fn skips_non_mut_ref_params() {
    let input = quote! {
        fn mixed(x: &mut i32, y: i32) {
            *x = *x + y;
        }
    };
    let func: syn::ItemFn = syn::parse2(input).unwrap();
    let transformed = transform_proof_body(&func.sig, &func.block);

    assert!(transformed.errors.is_empty());
    assert!(
        transformed.skipped_params.contains("x"),
        "x should be skipped"
    );
    assert!(
        !transformed.skipped_params.contains("y"),
        "y is not &mut, should NOT be skipped"
    );
}
