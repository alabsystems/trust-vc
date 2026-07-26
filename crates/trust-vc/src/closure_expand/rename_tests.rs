// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use quote::quote;

fn do_rename(tokens: TokenStream, renames: &[(&str, &str)]) -> String {
    let renames: Vec<(String, String)> = renames
        .iter()
        .map(|(f, t)| (f.to_string(), t.to_string()))
        .collect();
    rename_idents(tokens, &renames).to_string()
}

#[test]
fn test_rename_simple_variable() {
    let result = do_rename(quote! { x + 1 }, &[("x", "__arg0")]);
    assert!(
        result.contains("__arg0"),
        "should rename x to __arg0, got: {result}"
    );
    assert!(
        !result.contains(" x "),
        "original x should be gone, got: {result}"
    );
}

#[test]
fn test_rename_skips_method_call() {
    let result = do_rename(quote! { vec.len() }, &[("len", "__arg0")]);
    // Token stream renders as `vec . len ()` with spaces between tokens.
    assert!(
        result.contains(". len"),
        "method call .len() should NOT be renamed, got: {result}"
    );
    assert!(
        !result.contains("__arg0"),
        "should not contain renamed ident in method position, got: {result}"
    );
}

#[test]
fn test_rename_skips_field_access() {
    let result = do_rename(quote! { point.x + point.y }, &[("x", "__arg0")]);
    // Token stream renders as `point . x` with spaces.
    assert!(
        result.contains(". x"),
        "field access .x should NOT be renamed, got: {result}"
    );
    assert!(
        !result.contains("__arg0"),
        "should not contain renamed ident in field position, got: {result}"
    );
}

#[test]
fn test_rename_variable_but_not_method_same_name() {
    // Parameter `len` used as variable AND as method name on another object
    let result = do_rename(
        quote! { len + vec.len() },
        &[("len", "__trust_vc_closure_arg0")],
    );
    assert!(
        result.contains("__trust_vc_closure_arg0 +"),
        "standalone `len` variable should be renamed, got: {result}"
    );
    assert!(
        result.contains(". len"),
        "method call .len() should NOT be renamed, got: {result}"
    );
}

#[test]
fn test_rename_preserves_local_shadowing() {
    let result = do_rename(quote! { { let x = x + 1; x } }, &[("x", "__arg0")]);
    assert!(
        result.contains("let x = __arg0 + 1"),
        "initializer should rename outer x but preserve local binding, got: {result}"
    );
    assert!(
        !result.contains("let __arg0"),
        "local binding name should be preserved, got: {result}"
    );
}

#[test]
fn test_rename_inside_group() {
    let result = do_rename(quote! { (x + 1) }, &[("x", "__arg0")]);
    assert!(
        result.contains("__arg0"),
        "should rename inside parenthesized group, got: {result}"
    );
}

#[test]
fn test_rename_skips_method_inside_group() {
    let result = do_rename(quote! { (v.count() + 1) }, &[("count", "__arg0")]);
    assert!(
        result.contains(". count"),
        "method .count() inside group should NOT be renamed, got: {result}"
    );
    assert!(
        !result.contains("__arg0"),
        "should not rename method in group, got: {result}"
    );
}

#[test]
fn test_rename_chained_method() {
    let result = do_rename(quote! { items.iter().count() }, &[("count", "__arg0")]);
    assert!(
        result.contains(". count"),
        "chained method .count() should NOT be renamed, got: {result}"
    );
}

#[test]
fn test_rename_struct_field_shorthand_becomes_explicit() {
    let result = do_rename(quote! { Point { x, y: x } }, &[("x", "__arg0")]);
    assert!(
        result.contains("x : __arg0"),
        "field shorthand should expand to explicit field assignment, got: {result}"
    );
    assert!(
        !result.contains("{ __arg0"),
        "field name should not be renamed, got: {result}"
    );
}

#[test]
fn test_rename_multiple_params() {
    let result = do_rename(quote! { x + y }, &[("x", "__arg0"), ("y", "__arg1")]);
    assert!(result.contains("__arg0"), "x should be renamed: {result}");
    assert!(result.contains("__arg1"), "y should be renamed: {result}");
}

#[test]
fn test_rename_skips_path_qualified_call() {
    // HashMap::new() — `new` after `::` should NOT be renamed
    let result = do_rename(quote! { HashMap::new() }, &[("new", "__arg0")]);
    assert!(
        !result.contains("__arg0"),
        "path-qualified ::new() should NOT be renamed, got: {result}"
    );
}

#[test]
fn test_rename_skips_leading_path_segment() {
    let result = do_rename(quote! { Vec::<i32>::new() }, &[("Vec", "__arg0")]);
    assert!(
        result.contains("Vec"),
        "leading path segment should be preserved, got: {result}"
    );
    assert!(
        !result.contains("__arg0"),
        "should not rename type path segment, got: {result}"
    );
}

#[test]
fn test_rename_variable_but_not_path_qualified_same_name() {
    // `new` as variable AND as `::new()` associated function
    let result = do_rename(
        quote! { new + HashMap::new() },
        &[("new", "__trust_vc_closure_arg0")],
    );
    assert!(
        result.contains("__trust_vc_closure_arg0 +"),
        "standalone `new` variable should be renamed, got: {result}"
    );
    assert!(
        result.contains(":: new"),
        "path-qualified ::new() should NOT be renamed, got: {result}"
    );
}

#[test]
fn test_rename_single_colon_still_renames() {
    // `let x: i32` — single `:` is NOT `::`, so `i32` after `:` is fine
    // (in practice type names don't match param names, but verify the logic)
    let result = do_rename(quote! { let x : val }, &[("val", "__arg0")]);
    assert!(
        result.contains("__arg0"),
        "single colon should not suppress rename, got: {result}"
    );
}
