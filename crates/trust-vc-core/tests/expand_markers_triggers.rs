//! Broadcast and trigger expansion marker tests
//!
//! Tests that broadcast, trigger_with_group, auto_trigger, and all_triggers
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
    expand_all_triggers, expand_auto_trigger, expand_broadcast, expand_trigger_with_group,
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
fn expand_broadcast_includes_broadcast_lemma_marker() {
    let input: ItemFn = syn::parse2(quote! {
        fn lemma_sum_nonneg(n: u64) {
            // ensures sum(n) >= 0
        }
    })
    .expect("parse broadcast fn");
    let expanded = expand_broadcast(input);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_broadcast_lemma"),
        "expected broadcast_lemma marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:broadcast"),
        "expected durable broadcast doc attr: {expanded_str}"
    );
}

#[test]
fn expand_trigger_with_group_includes_both_markers() {
    let input = parse_fn();
    let attr = quote!(1, sum(n));
    let expanded = expand_trigger_with_group(input, attr);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_trigger_group"),
        "expected trigger_group marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_trigger_pattern"),
        "expected trigger_pattern marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:trigger:0:group=1"),
        "expected indexed trigger group doc attr: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:trigger:0:pattern=sum (n)")
            || expanded_str.contains("trust_vc:trigger:0:pattern=sum(n)"),
        "expected indexed trigger pattern doc attr: {expanded_str}"
    );
}

#[test]
fn expand_trigger_with_named_group_clause_includes_both_markers() {
    let input = parse_fn();
    let attr = quote!(sum(n), group = 4);
    let expanded = expand_trigger_with_group(input, attr);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_trigger_group"),
        "expected trigger_group marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_trigger_pattern"),
        "expected trigger_pattern marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("4u32")
            || expanded_str.contains("(4")
            || expanded_str.contains("( 4"),
        "expected parsed named group 4 in expanded output: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:trigger:0:group=4"),
        "expected durable named-group trigger doc attr: {expanded_str}"
    );
}

#[test]
fn expand_trigger_with_group_appends_next_doc_index() {
    let input = parse_fn();
    let first = expand_trigger_with_group(input, quote!(sum(n)));
    let first_fn: ItemFn = syn::parse2(first).expect("parse first trigger expansion");
    let second = expand_trigger_with_group(first_fn, quote!(1, prod(n)));
    let expanded_str = second.to_string();

    assert!(
        expanded_str.contains("trust_vc:trigger:0:group=0"),
        "expected first trigger doc attr to keep index 0: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:trigger:1:group=1"),
        "expected second trigger doc attr to advance to index 1: {expanded_str}"
    );
}

#[test]
fn expand_auto_trigger_includes_trigger_mode_auto() {
    let input = parse_fn();
    let expanded = expand_auto_trigger(input);
    let expanded_str = expanded.to_string();
    // Normalize spaces in token stream
    let normalized = expanded_str.replace(" ", "");
    assert!(
        normalized.contains("trust_vc_runtime::__trigger::auto_conservative"),
        "expected auto_conservative trigger call: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:trigger:mode=conservative"),
        "expected conservative trigger mode doc attr: {expanded_str}"
    );
}

#[test]
fn expand_all_triggers_includes_trigger_mode_all() {
    let input = parse_fn();
    let expanded = expand_all_triggers(input);
    let expanded_str = expanded.to_string();
    // Normalize spaces in token stream
    let normalized = expanded_str.replace(" ", "");
    assert!(
        normalized.contains("trust_vc_runtime::__trigger::auto_aggressive"),
        "expected auto_aggressive trigger call: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:trigger:mode=aggressive"),
        "expected aggressive trigger mode doc attr: {expanded_str}"
    );
}
