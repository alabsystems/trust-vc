// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::collections::BTreeSet;
use syn::parse_quote;

fn names(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|name| (*name).to_string()).collect()
}

#[test]
fn fn_value_edges_restore_outer_binding_after_inner_shadow() {
    let block: syn::Block = parse_quote!({
        let f = outer_target;
        {
            let f = inner_target;
            f();
        }
        f();
    });

    let actual = fn_value_call_edges(&block);
    assert!(actual.complete);
    assert_eq!(actual.edges, names(&["inner_target", "outer_target"]));
}

#[test]
fn fn_value_edges_resolve_aliases_in_pre_binding_environment() {
    let block: syn::Block = parse_quote!({
        let f = recursive_target;
        let f = f;
        let alias = f;
        alias();
    });

    let actual = fn_value_call_edges(&block);
    assert!(actual.complete);
    assert_eq!(actual.edges, names(&["recursive_target"]));
}

#[test]
fn fn_value_edges_fail_closed_after_reassignment() {
    let block: syn::Block = parse_quote!({
        let mut f = harmless_leaf;
        f = recursive_target;
        f();
    });

    let actual = fn_value_call_edges(&block);
    assert!(!actual.complete);
    assert!(actual.edges.is_empty());
}

#[test]
fn fn_value_edges_keep_conditional_reassignment_incomplete_after_block_restore() {
    let block: syn::Block = parse_quote!({
        let mut f = harmless_leaf;
        if condition {
            f = recursive_target;
        }
        f();
    });

    let actual = fn_value_call_edges(&block);
    assert!(!actual.complete);
    // The lexical snapshot may conservatively retain the pre-branch leaf as an
    // edge, but `complete = false` forces a self-edge at the owning function.
    assert_eq!(actual.edges, names(&["harmless_leaf"]));
}

#[test]
fn fn_value_edges_keep_nonrecursive_alias_control_precise() {
    let block: syn::Block = parse_quote!({
        let f = nonrecursive_leaf;
        let alias = f;
        alias();
    });

    let actual = fn_value_call_edges(&block);
    assert!(actual.complete);
    assert_eq!(actual.edges, names(&["nonrecursive_leaf"]));
}

#[test]
fn ordinary_mutable_local_does_not_make_call_graph_incomplete() {
    let block: syn::Block = parse_quote!({
        let mut value = 0u32;
        value = value + 1u32;
        nonrecursive_leaf();
    });

    let actual = fn_value_call_edges(&block);
    assert!(actual.complete);
    assert!(actual.edges.is_empty());
}

#[test]
fn unmodelable_decreases_cycle_is_suppressed() {
    let file: syn::File = parse_quote! {
        #[trust_vc::decreases(n)]
        fn generic_cycle<T>(n: u32) {
            generic_cycle::<T>(n);
        }
    };

    let ill_founded = ill_founded_recursive_function_names(&file, &VerificationContext::new());
    assert_eq!(ill_founded, names(&["generic_cycle"]));
}

#[test]
fn ambiguous_decreases_cycle_is_suppressed() {
    let file: syn::File = parse_quote! {
        mod left {
            #[trust_vc::decreases(n)]
            fn duplicate(n: u32) {
                duplicate(n);
            }
        }
        mod right {
            #[trust_vc::decreases(n)]
            fn duplicate(n: u32) {
                duplicate(n);
            }
        }
    };

    let ill_founded = ill_founded_recursive_function_names(&file, &VerificationContext::new());
    assert_eq!(ill_founded, names(&["duplicate"]));
}
