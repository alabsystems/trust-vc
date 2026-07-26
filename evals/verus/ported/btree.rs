// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `rust_verify_test/tests/btree.rs`.
//
// This file intentionally keeps the corpus manifest entry as `unsupported-gap`.
// The upstream file exercises std BTreeMap/BTreeSet mutation, `@` collection
// views, custom key ordering assumptions, deep views, key/value/entry iterator
// models, and recursive decreases through BTreeMap values. TrustVc does not yet
// model that full std ordered-collection surface.
//
// The Rust-valid scout below pins only stable behavior TrustVc can execute today:
// - concrete std BTreeMap/BTreeSet runtime behavior matching the simplest
//   upstream shapes;
// - spec-level Map/Set insert, lookup, remove, and membership obligations that
//   mirror the upstream collection-view intent; and
// - direct std BTreeMap/BTreeSet view observations.

#![allow(dead_code, unused_imports, unused_variables)]

use std::collections::{BTreeMap, BTreeSet};
use trust_vc_types::{Map, Set, View};

pub const BTREE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "btree_map_view_model_insert_lookup_verified",
        "test_btree_map",
        "verified",
        4,
    ),
    (
        "btree_set_view_model_insert_membership_verified",
        "test_btree_set",
        "verified",
        4,
    ),
    (
        "btree_map_view_model_wrong_lookup_counterexample",
        "test_btree_map",
        "counterexample",
        1,
    ),
    (
        "btree_set_view_model_wrong_membership_counterexample",
        "test_btree_set",
        "counterexample",
        1,
    ),
    (
        "std_btree_map_direct_view_verified",
        "test_btree_map",
        "verified",
        1,
    ),
    (
        "std_btree_set_direct_view_verified",
        "test_btree_set",
        "verified",
        1,
    ),
];

pub fn btree_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    BTREE_RS_EXPECTED_CASES
}

pub fn test_btree_map_runtime_std_behavior() {
    let mut m = BTreeMap::<u32, i8>::new();
    assert!(m.is_empty());

    m.insert(3, 4);
    assert!(!m.is_empty());

    m.insert(6, -8);
    assert_eq!(m.get(&3), Some(&4));
    assert!(m.contains_key(&3));
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(&6), Some(&-8));

    m.remove(&6);
    assert!(!m.contains_key(&6));
    assert!(m.contains_key(&3));

    m.clear();
    assert!(!m.contains_key(&3));
    assert!(m.is_empty());
}

pub fn test_btree_map_runtime_wrong_removed_key_counterexample() {
    let mut m = BTreeMap::<u32, i8>::new();
    m.insert(3, 4);
    m.insert(6, -8);
    m.remove(&6);

    assert!(m.contains_key(&6));
}

pub fn test_btree_set_runtime_std_behavior() {
    let mut m = BTreeSet::<u32>::new();
    assert!(m.is_empty());

    let inserted = m.insert(3);
    assert!(inserted);
    m.insert(6);
    assert!(!m.is_empty());

    let inserted_again = m.insert(3);
    assert!(!inserted_again);
    assert!(m.contains(&3));
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(&6), Some(&6));

    let removed = m.remove(&6);
    assert!(removed);
    let removed_again = m.remove(&6);
    assert!(!removed_again);
    assert!(!m.contains(&6));
    assert!(m.contains(&3));

    m.clear();
    assert!(!m.contains(&3));
    assert!(m.is_empty());
}

pub fn test_btree_set_runtime_wrong_duplicate_insert_counterexample() {
    let mut m = BTreeSet::<u32>::new();
    let inserted = m.insert(3);
    let inserted_again = m.insert(3);

    assert!(inserted);
    assert!(inserted_again);
}

fn btree_map_view_model_insert_lookup_verified() {
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .contains_key(3u32));
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .contains_key(6u32));
    trust_vc::assert!(
        Map::<u32, i8>::empty()
            .insert(3u32, 4i8)
            .insert(6u32, -8i8)
            .get(3u32)
            == 4i8
    );
    trust_vc::assert!(
        Map::<u32, i8>::empty()
            .insert(3u32, 4i8)
            .insert(6u32, -8i8)
            .get(6u32)
            == -8i8
    );
}

fn btree_set_view_model_insert_membership_verified() {
    trust_vc::assert!(Set::<u32>::empty().insert(3u32).insert(6u32).contains(3u32));
    trust_vc::assert!(Set::<u32>::empty().insert(3u32).insert(6u32).contains(6u32));
    trust_vc::assert!(!Set::<u32>::empty()
        .insert(3u32)
        .insert(6u32)
        .remove(6u32)
        .contains(6u32));
    trust_vc::assert!(Set::<u32>::empty()
        .insert(3u32)
        .insert(6u32)
        .remove(6u32)
        .contains(3u32));
}

fn btree_map_view_model_wrong_lookup_counterexample() {
    trust_vc::assert!(
        Map::<u32, i8>::empty()
            .insert(3u32, 4i8)
            .insert(6u32, -8i8)
            .get(6u32)
            == 4i8
    );
}

fn btree_set_view_model_wrong_membership_counterexample() {
    trust_vc::assert!(Set::<u32>::empty().insert(3u32).contains(6u32));
}

fn std_btree_map_direct_view_verified(m: BTreeMap<u32, i8>) {
    trust_vc::assert!(m.view().contains_key(3u32) == m.view().contains_key(3u32));
}

fn std_btree_set_direct_view_verified(s: BTreeSet<u32>) {
    trust_vc::assert!(s.view().contains(3u32) == s.view().contains(3u32));
}
