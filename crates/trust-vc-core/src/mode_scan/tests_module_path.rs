// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::module_path::find_inline_module_path;
use super::scan::normalize_fn_tokens;
use super::tests::parse_item_fn;

#[test]
fn test_find_inline_module_path_top_level() {
    let parsed = syn::parse_file("fn target() {}").expect("parse");
    let function = parse_item_fn("fn target() {}");
    let result = find_inline_module_path(
        &parsed.items,
        "target",
        &normalize_fn_tokens(&function),
        &[],
    );
    assert_eq!(
        result,
        Some(vec![]),
        "top-level function should have empty module path"
    );
}

#[test]
fn test_find_inline_module_path_nested_module() {
    let parsed = syn::parse_file(
        r#"
        mod outer {
            mod inner {
                fn target() {}
            }
        }
        "#,
    )
    .expect("parse");

    let inner_fn = {
        let outer = parsed
            .items
            .iter()
            .find_map(|item| {
                if let syn::Item::Mod(module) = item {
                    if module.ident == "outer" {
                        Some(module)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .expect("outer module should exist");
        let inner = outer
            .content
            .as_ref()
            .expect("outer should be inline")
            .1
            .iter()
            .find_map(|item| {
                if let syn::Item::Mod(module) = item {
                    if module.ident == "inner" {
                        Some(module)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .expect("inner module should exist");
        inner
            .content
            .as_ref()
            .expect("inner should be inline")
            .1
            .iter()
            .find_map(|item| {
                if let syn::Item::Fn(function) = item {
                    Some(function)
                } else {
                    None
                }
            })
            .expect("target function should exist")
    };

    let result =
        find_inline_module_path(&parsed.items, "target", &normalize_fn_tokens(inner_fn), &[]);
    assert_eq!(
        result,
        Some(vec!["outer".to_string(), "inner".to_string()]),
        "should find nested module path"
    );
}

#[test]
fn test_find_inline_module_path_not_found() {
    let parsed = syn::parse_file("fn other() {}").expect("parse");
    let function = parse_item_fn("fn missing() {}");
    let result = find_inline_module_path(
        &parsed.items,
        "missing",
        &normalize_fn_tokens(&function),
        &[],
    );
    assert_eq!(result, None, "non-existent function should return None");
}
