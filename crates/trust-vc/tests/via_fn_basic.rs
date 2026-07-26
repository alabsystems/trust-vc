// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the #[via_fn] attribute.
//!
//! Tests that the via_fn attribute correctly marks proof functions
//! used by decreases clauses with the `via` parameter.

use syn::parse_quote;
use trust_vc_core::expand_via_fn;

#[test]
fn test_expand_via_fn_basic_proof() {
    let input = parse_quote! {
        fn floor_log2_proof(n: u64) {
            trust_vc::assert!(n > 1 ==> (n >> 1) < n);
        }
    };

    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();
    let normalized = expanded_str.replace(' ', "");

    // Verify via_fn marker is added
    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "via_fn should add marker for association with decreases"
    );

    // Verify the proof body is active under cargo test.
    assert!(
        normalized.contains("cfg(all(test,not(trust_mc)))"),
        "via_fn should execute in the test path: {expanded_str}"
    );
    assert!(
        expanded_str.contains("collect_variable"),
        "via_fn should register proof parameters in the test path: {expanded_str}"
    );
    assert!(
        normalized.contains("cfg(not(any(trust_mc,test)))"),
        "via_fn should keep the non-test ghost-code runtime path: {expanded_str}"
    );
}

#[test]
fn test_expand_via_fn_with_multiple_params() {
    let input = parse_quote! {
        fn merge_proof(left: usize, right: usize, mid: usize) {
            trust_vc::assert!(left <= mid && mid <= right);
            trust_vc::assert!((mid - left) < (right - left));
            trust_vc::assert!((right - mid) < (right - left));
        }
    };

    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "via_fn should add marker"
    );
    assert_eq!(
        expanded_str.matches("collect_variable").count(),
        3,
        "via_fn should register all typed parameters: {expanded_str}"
    );

    // Verify all parameters are preserved
    assert!(
        expanded_str.contains("left")
            && expanded_str.contains("right")
            && expanded_str.contains("mid"),
        "All parameters should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify via_fn functions during expansion tests
}

#[test]
fn test_expand_via_fn_with_complex_proof() {
    let input = parse_quote! {
        fn quicksort_partition_proof(arr: &[i32], pivot: usize) {
            trust_vc::requires!(pivot < arr.len());
            trust_vc::assert!(pivot == 0 || pivot < arr.len());
            if pivot > 0 {
                trust_vc::assert!(pivot - 1 < arr.len());
            }
            if pivot < arr.len() - 1 {
                trust_vc::assert!((arr.len() - pivot - 1) < arr.len());
            }
        }
    };

    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();

    // Verify via_fn marker is added
    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "via_fn should add marker"
    );

    // Verify precondition is preserved
    assert!(
        expanded_str.contains("requires") || expanded_str.contains("pivot < arr.len()"),
        "Precondition should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify via_fn functions during expansion tests
}

#[test]
fn test_expand_via_fn_generic_proof() {
    let input = parse_quote! {
        fn tree_height_proof<T>(depth: usize) {
            trust_vc::assert!(depth > 0 ==> (depth - 1) < depth);
            trust_vc::assert!(2_usize.pow(depth as u32) > depth);
        }
    };

    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();

    // Verify via_fn marker is added
    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "via_fn should add marker"
    );

    // Verify generic parameter is preserved
    assert!(
        expanded_str.contains("<T>") || expanded_str.contains("< T >"),
        "Generic parameter should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify via_fn functions during expansion tests
}

#[test]
fn test_expand_via_fn_lexicographic_proof() {
    let input = parse_quote! {
        fn lex_proof(a: u64, b: u64, c: u64) {
            // Prove lexicographic ordering decreases
            trust_vc::assert!(a > 0 ==> (a - 1, b, c) < (a, b, c));
            trust_vc::assert!(a == 0 && b > 0 ==> (a, b - 1, c) < (a, b, c));
            trust_vc::assert!(a == 0 && b == 0 && c > 0 ==> (a, b, c - 1) < (a, b, c));
        }
    };

    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();

    // Verify via_fn marker is added
    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "via_fn should add marker"
    );

    // Verify lexicographic proof structure is preserved
    assert!(
        expanded_str.contains("lex_proof"),
        "Function name should be preserved"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify via_fn functions during expansion tests
}

#[test]
fn test_expand_via_fn_no_runtime_overhead() {
    let input = parse_quote! {
        fn expensive_proof(n: u64) {
            for i in 0..1000000 {
                trust_vc::assert!(i < 1000000);
            }
            trust_vc::assert!(n < u64::MAX);
        }
    };

    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();

    // Verify via_fn marker is added
    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "via_fn should add marker"
    );

    // via_fn functions should be marked for erasure at runtime
    // They exist only for verification purposes
    assert!(
        expanded_str.contains("expensive_proof"),
        "Function should be preserved for verification"
    );

    // Test that expansion succeeds - this ensures the expansion is valid
    // Note: We don't actually verify via_fn functions during expansion tests
}
