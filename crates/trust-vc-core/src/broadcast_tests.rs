// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for trigger pattern parsing and expansion.
//!
//! Extracted from `broadcast.rs` to keep production code under 500 lines.

use super::*;

#[test]
fn test_trigger_simple_pattern() {
    // #[trigger(sum(n))] — group 0, pattern "sum(n)"
    let tokens: TokenStream = quote::quote! { sum(n) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 0, "simple trigger should be group 0");
    assert!(
        pattern.contains("sum") && pattern.contains("n"),
        "pattern should contain sum(n), got: {}",
        pattern
    );
}

#[test]
fn test_trigger_with_group_simple() {
    // #[trigger(1, sum(n))] — group 1, pattern "sum(n)"
    let tokens: TokenStream = quote::quote! { 1, sum(n) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 1, "trigger(1, sum(n)) should be group 1");
    assert!(
        pattern.contains("sum") && pattern.contains("n"),
        "pattern should contain sum(n), got: {}",
        pattern
    );
}

#[test]
fn test_trigger_with_group_multi_arg_pattern() {
    // #[trigger(1, f(a, b))] — group 1, pattern must include full "f(a, b)"
    // This was the bug: find(',') truncated pattern to "f(a" (#1838)
    let tokens: TokenStream = quote::quote! { 1, f(a, b) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 1, "trigger(1, f(a, b)) should be group 1");
    assert!(
        pattern.contains("a") && pattern.contains("b"),
        "pattern must include full f(a, b), not truncated — got: {} (#1838)",
        pattern
    );
}

#[test]
fn test_trigger_multi_arg_no_group() {
    // #[trigger(f(a, b))] — group 0, pattern "f(a, b)"
    let tokens: TokenStream = quote::quote! { f(a, b) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 0, "trigger(f(a, b)) should be group 0");
    assert!(
        pattern.contains("a") && pattern.contains("b"),
        "pattern should be full f(a, b), got: {}",
        pattern
    );
}

#[test]
fn test_trigger_numeric_prefix_without_comma_is_pattern() {
    // #[trigger(1)] should be treated as a plain pattern, not a group.
    let tokens: TokenStream = quote::quote! { 1 };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 0, "trigger(1) should not infer a group");
    assert_eq!(pattern, "1", "trigger(1) pattern should remain unchanged");
}

#[test]
fn test_trigger_group_with_missing_pattern_falls_back() {
    // #[trigger(1,)] is malformed; keep legacy fallback behavior.
    let tokens: TokenStream = quote::quote! { 1, };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 0, "malformed trigger should fall back to group 0");
    assert_eq!(
        pattern,
        tokens.to_string(),
        "malformed trigger should preserve original pattern"
    );
}

#[test]
fn test_trigger_with_suffixed_group_literal() {
    // #[trigger(1u32, sum(n))] should parse group from literal value.
    let tokens: TokenStream = quote::quote! { 1u32, sum(n) };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 1, "suffixed group literal should parse as group 1");
    assert!(
        pattern.contains("sum") && pattern.contains("n"),
        "pattern should contain sum(n), got: {}",
        pattern
    );
}

#[test]
fn test_trigger_with_named_group_clause() {
    // #[trigger(sum(n), group = 2)] should parse the trailing named group.
    let tokens: TokenStream = quote::quote! { sum(n), group = 2 };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 2, "named trigger group should parse as group 2");
    assert!(
        pattern.contains("sum") && pattern.contains("n"),
        "pattern should contain sum(n), got: {}",
        pattern
    );
}

#[test]
fn test_trigger_named_group_preserves_multi_arg_pattern() {
    // #[trigger(f(a, b), group = 3)] must preserve the full multi-arg pattern.
    let tokens: TokenStream = quote::quote! { f(a, b), group = 3 };
    let (group, pattern) = parse_trigger_group_and_pattern(&tokens);
    assert_eq!(group, 3, "named trigger group should parse as group 3");
    assert!(
        pattern.contains("a") && pattern.contains("b"),
        "pattern must include full f(a, b), got: {}",
        pattern
    );
}

#[test]
fn test_expand_trigger_registers_parsed_group_and_pattern() {
    // Integration-level sanity check: parser output is what expansion uses.
    let func: ItemFn = syn::parse_quote! { fn f() {} };
    let tokens: TokenStream = quote::quote! { 7, f(a, b) };
    let output = expand_trigger_with_group(func, tokens);
    let output_str = output.to_string();
    assert!(
        output_str.contains("register_trigger")
            && (output_str.contains("7u32")
                || output_str.contains("(7")
                || output_str.contains("( 7")),
        "expanded tokens should register parsed group 7, got: {}",
        output_str
    );
    assert!(
        output_str.contains("\"f (a , b)\""),
        "expanded tokens should register full multi-arg pattern, got: {}",
        output_str
    );
}

#[test]
fn test_expand_trigger_registers_named_group_clause() {
    let func: ItemFn = syn::parse_quote! { fn f() {} };
    let tokens: TokenStream = quote::quote! { f(a, b), group = 9 };
    let output = expand_trigger_with_group(func, tokens);
    let output_str = output.to_string();
    assert!(
        output_str.contains("register_trigger")
            && (output_str.contains("9u32")
                || output_str.contains("(9")
                || output_str.contains("( 9")),
        "expanded tokens should register parsed named group 9, got: {}",
        output_str
    );
    assert!(
        output_str.contains("\"f (a , b)\""),
        "expanded tokens should register full multi-arg pattern, got: {}",
        output_str
    );
}
