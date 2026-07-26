// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::scan::{
    collect_matching_modules, locate_unique_module_items, normalize_fn_tokens,
    sibling_modes_from_items,
};
use super::tests::{inline_module_fn, parse_item_fn};
use crate::mode::FunctionMode;

#[test]
fn test_locate_unique_module_items_rejects_ambiguous_duplicate_matches() {
    let parsed = syn::parse_file(
        r#"
        mod alpha {
            fn target() {}
        }

        mod beta {
            fn target() {}
        }
        "#,
    )
    .expect("source should parse");

    let current_fn = inline_module_fn(&parsed, "alpha", "target");
    let maybe_items =
        locate_unique_module_items(&parsed.items, "target", &normalize_fn_tokens(current_fn));

    assert!(
        maybe_items.is_none(),
        "same-name identical functions in different modules must not resolve to an arbitrary sibling set"
    );
}

#[test]
fn test_locate_unique_module_items_finds_unique_match() {
    let parsed = syn::parse_file(
        r#"
        mod alpha {
            fn unique_fn() { let _ = 42; }
            fn other() {}
        }

        mod beta {
            fn different() {}
        }
        "#,
    )
    .expect("source should parse");

    let current_fn = inline_module_fn(&parsed, "alpha", "unique_fn");
    let items =
        locate_unique_module_items(&parsed.items, "unique_fn", &normalize_fn_tokens(current_fn));

    assert!(
        items.is_some(),
        "should find the unique module containing unique_fn"
    );
    let items = items.expect("unique match should exist");
    let fn_names: Vec<_> = items
        .iter()
        .filter_map(|item| {
            if let syn::Item::Fn(function) = item {
                Some(function.sig.ident.to_string())
            } else {
                None
            }
        })
        .collect();
    assert!(fn_names.contains(&"unique_fn".to_string()));
    assert!(fn_names.contains(&"other".to_string()));
}

#[test]
fn test_normalize_fn_tokens_ignores_attributes() {
    let with_attr = parse_item_fn("#[inline] fn target() { helper(); }");
    let without_attr = parse_item_fn("fn target() { helper(); }");

    assert_eq!(
        normalize_fn_tokens(&with_attr),
        normalize_fn_tokens(&without_attr),
        "mode scanning should match functions by signature and body, not attributes"
    );
}

#[test]
fn test_normalize_fn_tokens_differs_on_body() {
    let left = parse_item_fn("fn target() { let _ = 1; }");
    let right = parse_item_fn("fn target() { let _ = 2; }");

    assert_ne!(
        normalize_fn_tokens(&left),
        normalize_fn_tokens(&right),
        "different function bodies should produce different normalized tokens"
    );
}

#[test]
fn test_collect_matching_modules_finds_nested_module() {
    let parsed = syn::parse_file(
        r#"
        mod outer {
            mod inner {
                fn target() {}
            }
        }
        "#,
    )
    .expect("source should parse");
    let function = parse_item_fn("fn target() {}");
    let mut matches = Vec::new();

    collect_matching_modules(
        &parsed.items,
        "target",
        &normalize_fn_tokens(&function),
        &mut matches,
    );

    assert_eq!(matches.len(), 1, "should find target in nested module");
}

#[test]
fn test_collect_matching_modules_reports_multiple_ambiguous_matches() {
    let parsed = syn::parse_file(
        r#"
        mod alpha { fn dup() {} }
        mod beta { fn dup() {} }
        "#,
    )
    .expect("source should parse");
    let function = parse_item_fn("fn dup() {}");
    let mut matches = Vec::new();

    collect_matching_modules(
        &parsed.items,
        "dup",
        &normalize_fn_tokens(&function),
        &mut matches,
    );

    assert_eq!(
        matches.len(),
        2,
        "identical functions in different modules should produce multiple matches"
    );
}

#[test]
fn test_sibling_modes_mixed_functions() {
    let parsed = syn::parse_file(
        r#"
        #[trust_vc::proof]
        fn lemma() {}

        #[trust_vc::spec]
        fn ghost() {}

        fn exec_fn() {}
        "#,
    )
    .expect("source should parse");

    let modes = sibling_modes_from_items(&parsed.items);
    assert_eq!(modes.len(), 3);
    assert_eq!(modes["lemma"], FunctionMode::Proof);
    assert_eq!(modes["ghost"], FunctionMode::Spec);
    assert_eq!(modes["exec_fn"], FunctionMode::Exec);
}

#[test]
fn test_sibling_modes_skips_non_function_items() {
    let parsed = syn::parse_file(
        r#"
        struct Foo;
        const X: i32 = 1;
        fn only_fn() {}
        "#,
    )
    .expect("source should parse");

    let modes = sibling_modes_from_items(&parsed.items);
    assert_eq!(modes.len(), 1, "only functions should appear in mode map");
    assert_eq!(modes["only_fn"], FunctionMode::Exec);
}
