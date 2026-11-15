// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// LOCAL refutation witnesses for `evals/verus/ported/maps.rs`, held OUTSIDE it.
//
// These are the liar twins of maps.rs's VERIFIED rows: each keeps its twin's
// shape with one false claim and is refuted (Counterexample), pinned by
// `COUNTEREXAMPLE_CASES` in
// `crates/trust-vc/tests/maps_rs_trust_vc_regressions.rs`.
//
// They cannot live in `maps.rs`. That file is a declared `trust_vc_path` of the
// `source/rust_verify_test/tests/maps.rs` manifest entry, and the corpus gate
// scans every contract-carrying function in a declared path as a case of that
// entry: an undeclared one fails with `unexpected observed case`, and DECLARING
// one is worse — their upstream cases (`map_contains`,
// `map_insert_implies_contains`, `map index syntax`) are `=> Ok(())`, so a
// mapped `counterexample` row would be a Layer-1 verdict mismatch. This file is
// declared by no manifest entry, so the twins keep their contracts, their
// bodies and their pins, and the corpus gate never reads them as upstream
// cases.
//
// NOT every verified row of maps.rs has one: `set_choose_regression_408`'s
// negation came back `unknown ((incomplete quantifier-unhandled))` rather than a
// Counterexample, so that pin stays without a twin (the hole is disclosed at the
// foot of `maps.rs`).

use trust_vc_types::Map;

#[trust_vc::ensures(true)]
fn map_contains_absent_key_fails() {
    trust_vc::assert!(trust_vc_types::map![10i32 => 100i32, 20i32 => 200i32].contains_key(30i32));
}

#[trust_vc::ensures(true)]
fn map_contains_absent_value_fails() {
    trust_vc::assert!(trust_vc_types::map![10i32 => 100i32, 20i32 => 200i32].contains_value(300i32));
}

#[trust_vc::ensures(true)]
fn map_insert_does_not_imply_contains_fails(m: Map<i32, i32>) {
    trust_vc::assert!(!m.insert(1i32, 2i32).insert(3i32, 4i32).contains_key(1i32));
}

#[trust_vc::ensures(true)]
fn map_index_syntax_wrong_value_fails(m: Map<i32, i32>) {
    trust_vc::assert!(m.insert(1i32, 2i32)[1i32] == 3i32);
}
