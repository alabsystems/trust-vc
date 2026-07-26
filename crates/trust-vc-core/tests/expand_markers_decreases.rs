//! Termination/decreases expansion marker tests
//!
//! Tests that decreases and via_fn attributes properly add expansion markers,
//! plus macro-to-encoder regression tests (#1817).
//!
//! Split from expand_markers.rs per #2380.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use quote::quote;
use syn::ItemFn;
use trust_vc_core::{expand_decreases, expand_decreases_with_clauses, expand_via_fn};

fn parse_fn() -> ItemFn {
    syn::parse2(quote! {
        fn add_one(x: i32) -> i32 {
            x + 1
        }
    })
    .expect("parse test function")
}

// ============================================================================
// Termination Markers (Contract: Termination category)
// ============================================================================

#[test]
fn expand_decreases_includes_measures_entry_marker() {
    let input = parse_fn();
    let measures = quote!(n);
    let expanded = expand_decreases(input, measures);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_measures_entry"),
        "expected measures_entry marker in expansion: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:decreases:entry=n"),
        "expected durable decreases entry doc attr in expansion: {expanded_str}"
    );
}

#[test]
fn expand_decreases_multiple_measures_produces_tuple() {
    let input: ItemFn = syn::parse2(quote! {
        fn ack(m: u64, n: u64) -> u64 {
            if m == 0 { n + 1 }
            else if n == 0 { self.ack(m - 1, 1) }
            else { self.ack(m - 1, self.ack(m, n - 1)) }
        }
    })
    .expect("parse test function");
    let measures = quote!(m, n);
    let expanded = expand_decreases(input, measures);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_measures_entry"),
        "expected measures_entry marker in expansion: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:decreases:entry"),
        "expected durable decreases entry doc attr in expansion: {expanded_str}"
    );
    // Tuple syntax for lexicographic measures
    assert!(
        expanded_str.contains("(m , n)") || expanded_str.contains("(m, n)"),
        "expected lexicographic tuple in expansion: {expanded_str}"
    );
}

#[test]
fn expand_decreases_with_when_clause_includes_when_marker() {
    let input = parse_fn();
    let attr = quote!(n, when = x > 0);
    let expanded = expand_decreases_with_clauses(input, attr);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_measures_entry"),
        "expected measures_entry marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_decreases_when"),
        "expected decreases_when marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:decreases:when=x > 0")
            || expanded_str.contains("trust_vc:decreases:when=x>0"),
        "expected durable decreases when doc attr: {expanded_str}"
    );
}

#[test]
fn expand_decreases_with_via_clause_includes_via_marker() {
    let input = parse_fn();
    let attr = quote!(n, via = prove_termination);
    let expanded = expand_decreases_with_clauses(input, attr);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_measures_entry"),
        "expected measures_entry marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("__trust_vc_decreases_via"),
        "expected decreases_via marker: {expanded_str}"
    );
    assert!(
        expanded_str.contains("trust_vc:decreases:via=prove_termination"),
        "expected durable decreases via doc attr: {expanded_str}"
    );
}

// ============================================================================
// Via/Proof Markers (Contract: Via/Proof category)
// ============================================================================

#[test]
fn expand_via_fn_includes_via_fn_marker() {
    let input: ItemFn = syn::parse2(quote! {
        fn prove_termination(n: u64) {
            // termination proof
        }
    })
    .expect("parse via fn");
    let expanded = expand_via_fn(input);
    let expanded_str = expanded.to_string();
    assert!(
        expanded_str.contains("__trust_vc_via_fn"),
        "expected via_fn marker: {expanded_str}"
    );
}

// ============================================================================
// Macro-to-Encoder Regression Tests (#1817)
//
// The `when` and `via` paths must both stay connected to the active test-mode
// verification pipeline.
// ============================================================================

/// Verifies that decreases(when = ...) reaches the test-mode
/// MeasureDecreases obligation rather than staying confined to the cfg(trust_mc)
/// marker block.
#[test]
fn decreases_when_condition_reaches_test_path_measure_obligation() {
    let input: ItemFn = syn::parse2(quote! {
        fn countdown(n: u64) -> u64 {
            if n == 0 { 0 } else { countdown(n - 1) }
        }
    })
    .expect("parse countdown fn");

    let attr = quote!(n, when = n > 0);
    let expanded = expand_decreases_with_clauses(input, attr);
    let expanded_str = expanded.to_string();

    // MACRO SIDE: when marker IS generated (in cfg(trust_mc) block)
    assert!(
        expanded_str.contains("__trust_vc_decreases_when"),
        "macro should generate when marker: {expanded_str}"
    );

    assert!(
        expanded_str.contains("MeasureDecreases"),
        "test-mode path should generate MeasureDecreases obligations: {expanded_str}"
    );

    let snippets: Vec<String> = expanded_str
        .split("MeasureDecreases")
        .skip(1)
        .map(|part| part.chars().take(400).collect())
        .collect();
    assert!(
        snippets.iter().any(|snippet| snippet.contains("n > 0")),
        "MeasureDecreases obligation should include when condition: {snippets:?}"
    );
    assert!(
        snippets.iter().any(|snippet| snippet.contains("n - 1 < n")),
        "MeasureDecreases obligation should keep decrease relation: {snippets:?}"
    );
    assert!(
        snippets
            .iter()
            .any(|snippet| snippet.contains("||") && snippet.contains("!")),
        "MeasureDecreases obligation should gate with !when || decrease: {snippets:?}"
    );
}

#[test]
fn decreases_checks_stay_at_recursive_call_sites() {
    let input: ItemFn = syn::parse2(quote! {
        fn countdown(n: u64) -> u64 {
            if n == 0 { 0 } else { countdown(n - 1) }
        }
    })
    .expect("parse countdown fn");

    let expanded = expand_decreases_with_clauses(input, quote!(n));
    let normalized = expanded.to_string().replace(' ', "");
    let branch_index = normalized
        .find("ifn==0{0}else{")
        .expect("expected recursive branch in expansion");
    let obligation_index = normalized
        .find("recursive_call_")
        .expect("expected recursive call obligation label");
    let call_offset = normalized[obligation_index..]
        .find("countdown(n-1)")
        .expect("expected recursive call after obligation");
    let call_index = obligation_index + call_offset;

    assert!(
        branch_index < obligation_index,
        "recursive-call obligation should be injected inside the taken branch, not at function entry: {normalized}"
    );
    assert!(
        obligation_index < call_index,
        "recursive-call obligation should be collected before the recursive call: {normalized}"
    );
}

/// Verifies that decreases(via = ...) calls the proof function in the cfg(test)
/// path. When via is present, the via function provides the complete termination
/// proof, so MeasureDecreases is NOT injected — only MeasureNonNegative remains.
/// See #2658 Category G1.
#[test]
fn decreases_via_calls_proof_in_test_path() {
    let input: ItemFn = syn::parse2(quote! {
        fn countdown(n: u64) -> u64 {
            if n == 0 { 0 } else { countdown(n - 1) }
        }
    })
    .expect("parse countdown fn");

    let attr = quote!(n, via = prove_countdown_terminates);
    let expanded = expand_decreases_with_clauses(input, attr);
    let expanded_str = expanded.to_string();

    // MACRO SIDE: via marker IS generated (in cfg(trust_mc) block)
    assert!(
        expanded_str.contains("__trust_vc_decreases_via"),
        "macro should generate via marker: {expanded_str}"
    );

    let normalized = expanded_str.replace(' ', "");
    assert!(
        normalized.contains("prove_countdown_terminates(n);"),
        "test-mode path should call via function: {expanded_str}"
    );
    // Via function provides the termination proof, so MeasureDecreases is
    // deliberately omitted (#2658 G1). Non-negativity is still required.
    assert!(
        !expanded_str.contains("MeasureDecreases"),
        "via path should NOT inject MeasureDecreases (via fn is the proof): {expanded_str}"
    );
    assert!(
        expanded_str.contains("MeasureNonNegative"),
        "via path should still collect MeasureNonNegative obligations: {expanded_str}"
    );
}

/// Verifies that decreases(when = ..., via = ...) guards the proof call with
/// the when-condition in the cfg(test) path. MeasureDecreases is NOT injected
/// when via is present — the via function is the termination proof. See #2658 G1.
#[test]
fn decreases_when_via_guards_proof_call_in_test_path() {
    let input: ItemFn = syn::parse2(quote! {
        fn countdown(n: u64) -> u64 {
            if n == 0 { 0 } else { countdown(n - 1) }
        }
    })
    .expect("parse countdown fn");

    let attr = quote!(n, when = n > 0, via = prove_countdown_terminates);
    let expanded = expand_decreases_with_clauses(input, attr);
    let expanded_str = expanded.to_string();
    let normalized = expanded_str.replace(' ', "");

    assert!(
        normalized.contains("ifn>0{prove_countdown_terminates(n);}"),
        "when+via should guard the proof call in test-mode: {expanded_str}"
    );
    // Via function provides the termination proof, so MeasureDecreases is
    // deliberately omitted (#2658 G1). Non-negativity is still required.
    assert!(
        !expanded_str.contains("MeasureDecreases"),
        "when+via should NOT inject MeasureDecreases (via fn is the proof): {expanded_str}"
    );
    assert!(
        expanded_str.contains("MeasureNonNegative"),
        "when+via should still collect MeasureNonNegative obligations: {expanded_str}"
    );
}

/// Verifies that mutual recursive calls with recursive-aware measures
/// conservatively reject when the caller's parameter mapping cannot be reused
/// for a peer call.
#[test]
fn decreases_mutual_recursive_aware_peer_call_rejects_in_test_path() {
    let input: ItemFn = syn::parse2(quote! {
        fn walk(tree: Tree<i32>, fuel: u64) -> u64 {
            if fuel == 0 { 0 } else { peer(fuel - 1, tree) }
        }
    })
    .expect("parse mutual recursion fn");

    let attr = quote!(tree, fuel, when = fuel > 0, mutual_with(peer));
    let expanded = expand_decreases_with_clauses(input, attr);
    let expanded_str = expanded.to_string();

    assert!(
        expanded_str.contains("MeasureDecreases"),
        "mutual peer call should still emit a MeasureDecreases obligation: {expanded_str}"
    );

    let snippets: Vec<String> = expanded_str
        .split("MeasureDecreases")
        .skip(1)
        .map(|part| part.chars().take(400).collect())
        .collect();

    assert!(
        snippets.iter().any(|snippet| snippet.contains("fuel > 0")),
        "rejecting mutual-call obligation should retain the when guard: {snippets:?}"
    );
    assert!(
        snippets.iter().any(|snippet| snippet.contains("false")),
        "rejecting mutual-call obligation should use a conservative false condition: {snippets:?}"
    );
}
