// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use proc_macro2::Span;
use syn::visit::Visit;

use super::exec_callers::{find_exec_callers_in_items, has_test_attr, CallCollector};
use super::scan::{normalize_fn_tokens, ModeScan};
use super::tests::{inline_module_fn, parse_item_fn};
use crate::mode::FunctionMode;

#[test]
fn test_find_exec_callers_ignores_same_name_in_other_module() {
    let parsed = syn::parse_file(
        r#"
        mod alpha {
            fn target() {}

            fn exec_caller() {
                target();
            }
        }

        mod beta {
            #[trust_vc::proof]
            fn target() {
                let _ = 1;
            }
        }
        "#,
    )
    .expect("source should parse");

    let current_fn = inline_module_fn(&parsed, "beta", "target");
    let scan = ModeScan {
        sibling_modes: HashMap::from([(String::from("target"), FunctionMode::Proof)]),
    };

    let errors = find_exec_callers_in_items(
        &scan,
        "target",
        &normalize_fn_tokens(current_fn),
        FunctionMode::Proof,
        &parsed.items,
        Span::call_site(),
        None,
        &[],
    );

    assert!(
        errors.is_empty(),
        "inbound exec-caller scan should stay inside the current module when another module defines the same function name"
    );
}

#[test]
fn test_has_test_attr_standard() {
    let function = parse_item_fn("#[test] fn test_it() {}");
    assert!(has_test_attr(&function), "should detect #[test]");
}

#[test]
fn test_has_test_attr_tokio() {
    let function = parse_item_fn("#[tokio::test] fn test_async() {}");
    assert!(has_test_attr(&function), "should detect #[tokio::test]");
}

#[test]
fn test_has_test_attr_absent() {
    let function = parse_item_fn("fn not_a_test() {}");
    assert!(
        !has_test_attr(&function),
        "plain function should not be detected as test"
    );
}

#[test]
fn test_has_test_attr_other_attrs_not_confused() {
    let function = parse_item_fn("#[cfg(test)] fn cfg_test() {}");
    assert!(
        !has_test_attr(&function),
        "#[cfg(test)] is a conditional compilation flag, not a test attribute"
    );
}

#[test]
fn test_call_collector_finds_unqualified_calls() {
    let function = parse_item_fn("fn caller() { helper(); other(1, 2); }");
    let mut collector = CallCollector { calls: Vec::new() };
    collector.visit_item_fn(&function);
    assert!(
        collector.calls.contains(&"helper".to_string()),
        "should collect 'helper' call"
    );
    assert!(
        collector.calls.contains(&"other".to_string()),
        "should collect 'other' call"
    );
    assert_eq!(collector.calls.len(), 2);
}

#[test]
fn test_call_collector_ignores_qualified_calls() {
    let function =
        parse_item_fn("fn caller() { self::helper(); crate::other(); std::mem::drop(x); }");
    let mut collector = CallCollector { calls: Vec::new() };
    collector.visit_item_fn(&function);
    assert!(
        collector.calls.is_empty(),
        "qualified calls should not appear as unqualified: {:?}",
        collector.calls
    );
}

#[test]
fn test_call_collector_finds_nested_calls() {
    let function = parse_item_fn("fn caller() { if true { inner(); } }");
    let mut collector = CallCollector { calls: Vec::new() };
    collector.visit_item_fn(&function);
    assert!(
        collector.calls.contains(&"inner".to_string()),
        "should collect calls inside blocks"
    );
}

#[test]
fn test_find_exec_callers_detects_exec_to_proof_violation() {
    let parsed = syn::parse_file(
        r#"
        mod m {
            #[trust_vc::proof]
            fn lemma() {}

            fn caller() {
                lemma();
            }
        }
        "#,
    )
    .expect("source should parse");

    let current_fn = inline_module_fn(&parsed, "m", "lemma");
    let scan = ModeScan {
        sibling_modes: HashMap::from([
            (String::from("lemma"), FunctionMode::Proof),
            (String::from("caller"), FunctionMode::Exec),
        ]),
    };

    let errors = find_exec_callers_in_items(
        &scan,
        "lemma",
        &normalize_fn_tokens(current_fn),
        FunctionMode::Proof,
        &parsed.items,
        Span::call_site(),
        None,
        &[],
    );

    assert_eq!(
        errors.len(),
        1,
        "exec function calling proof function should produce exactly one error"
    );
}

#[test]
fn test_find_exec_callers_skips_test_functions() {
    let parsed = syn::parse_file(
        r#"
        mod m {
            #[trust_vc::proof]
            fn lemma() {}

            #[test]
            fn test_it() {
                lemma();
            }
        }
        "#,
    )
    .expect("source should parse");

    let current_fn = inline_module_fn(&parsed, "m", "lemma");
    let scan = ModeScan {
        sibling_modes: HashMap::from([
            (String::from("lemma"), FunctionMode::Proof),
            (String::from("test_it"), FunctionMode::Exec),
        ]),
    };

    let errors = find_exec_callers_in_items(
        &scan,
        "lemma",
        &normalize_fn_tokens(current_fn),
        FunctionMode::Proof,
        &parsed.items,
        Span::call_site(),
        None,
        &[],
    );

    assert!(
        errors.is_empty(),
        "#[test] functions should be exempt from exec-caller violation: {:?}",
        errors.len()
    );
}

#[test]
fn test_find_exec_callers_allows_proof_calling_proof() {
    let parsed = syn::parse_file(
        r#"
        mod m {
            #[trust_vc::proof]
            fn target() {}

            #[trust_vc::proof]
            fn other_proof() {
                target();
            }
        }
        "#,
    )
    .expect("source should parse");

    let current_fn = inline_module_fn(&parsed, "m", "target");
    let scan = ModeScan {
        sibling_modes: HashMap::from([
            (String::from("target"), FunctionMode::Proof),
            (String::from("other_proof"), FunctionMode::Proof),
        ]),
    };

    let errors = find_exec_callers_in_items(
        &scan,
        "target",
        &normalize_fn_tokens(current_fn),
        FunctionMode::Proof,
        &parsed.items,
        Span::call_site(),
        None,
        &[],
    );

    assert!(errors.is_empty(), "proof calling proof should be allowed");
}
