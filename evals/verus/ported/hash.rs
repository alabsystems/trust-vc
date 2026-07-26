// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// First partial executable TrustVc scout for upstream Verus
// `rust_verify_test/tests/hash.rs`.
//
// This file intentionally keeps the corpus manifest entry as `unsupported-gap`.
// The upstream file exercises DefaultHasher state views, std HashMap/HashSet
// mutation and view specs, boxed keys, custom Hash/Eq key-model assumptions,
// HashMapWithView/HashSetWithView, StringHashMap/StringHashSet, deep views, and
// hash collection iterators. TrustVc does not yet model that full std hash
// collection surface.
//
// The Rust-valid scout below pins only stable behavior TrustVc can execute today:
// - concrete std HashMap/HashSet/DefaultHasher runtime behavior matching the
//   simplest upstream shapes, boxed/custom/string key variants, and unordered
//   iterator observations;
// - spec-level Map/Set insert, lookup, remove, and membership obligations that
//   mirror the upstream collection-view/key/value intent;
// - stable boolean counterexample witnesses for negative collection facts that
//   currently return solver-unknown when phrased directly against Map/Set;
// - direct std HashMap/HashSet view observations; and
// - fail-closed boundaries for std hash mutation, iterators, and hasher state
//   where upstream relies on Verus-specific models.

#![allow(dead_code, unused_imports, unused_variables)]

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use trust_vc_types::{Map, Set, View};

pub const UPSTREAM_HASH_RS_ACTIVE_CASES: &[&str] = &[
    "test_default_hasher",
    "test_hash_map",
    "test_hash_set",
    "test_hash_map_box",
    "test_hash_set_box",
    "test_hash_map_struct",
    "test_hash_set_struct",
    "test_hash_map_struct_fails",
    "test_hash_set_struct_fails",
    "test_hash_map_with_view",
    "test_hash_set_with_view",
    "test_hash_map_with_view_fails",
    "test_hash_set_with_view_fails",
    "test_string_hash_map",
    "test_hash_map_deep_view",
    "test_string_hash_set",
    "test_hash_map_keys",
    "test_hash_map_values",
    "test_hash_map_iter",
    "test_hash_set_iter",
    "test_hash_map_decreases",
];

pub fn upstream_hash_rs_active_cases() -> &'static [&'static str] {
    UPSTREAM_HASH_RS_ACTIVE_CASES
}

pub const HASH_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "hash_map_view_model_insert_lookup_verified",
        "test_hash_map",
        "verified",
        4,
    ),
    (
        "hash_set_view_model_insert_membership_verified",
        "test_hash_set",
        "verified",
        4,
    ),
    (
        "hash_map_view_model_remove_verified",
        "test_hash_map",
        "verified",
        2,
    ),
    (
        "hash_map_view_model_domain_values_verified",
        "test_hash_map_keys_values",
        "verified",
        4,
    ),
    (
        "hash_map_view_model_overwrite_verified",
        "test_hash_map",
        "verified",
        2,
    ),
    (
        "hash_set_view_model_duplicate_insert_verified",
        "test_hash_set",
        "verified",
        2,
    ),
    (
        "std_hash_map_direct_view_verified",
        "test_hash_map",
        "verified",
        1,
    ),
    (
        "std_hash_set_direct_view_verified",
        "test_hash_set",
        "verified",
        1,
    ),
    (
        "std_hash_map_direct_view_key_guard_verified",
        "test_hash_map",
        "verified",
        1,
    ),
    (
        "std_hash_set_direct_view_member_guard_verified",
        "test_hash_set",
        "verified",
        1,
    ),
    (
        "hash_map_removed_key_boolean_witness_counterexample",
        "test_hash_map",
        "counterexample",
        1,
    ),
    (
        "hash_set_duplicate_insert_boolean_witness_counterexample",
        "test_hash_set",
        "counterexample",
        1,
    ),
    (
        "std_hash_map_mutation_surface_fail_closed_error",
        "test_hash_map",
        "error",
        0,
    ),
    (
        "std_hash_set_mutation_surface_fail_closed_error",
        "test_hash_set",
        "error",
        0,
    ),
    (
        "hash_map_keys_iterator_surface_fail_closed_error",
        "test_hash_map_keys",
        "error",
        0,
    ),
    (
        "default_hasher_verifier_surface_fail_closed_error",
        "test_default_hasher",
        "error",
        0,
    ),
];

pub fn hash_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    HASH_RS_EXPECTED_CASES
}

pub const HASH_RS_EXPECTED_ERROR_PATTERNS: &[(&str, &[&str])] = &[
    (
        "std_hash_map_mutation_surface_fail_closed_error",
        &["unsupported method", "HashMap", "insert"],
    ),
    (
        "std_hash_set_mutation_surface_fail_closed_error",
        &[
            "unsupported method",
            "HashSet",
            "insert",
            "unresolved variable",
        ],
    ),
    (
        "hash_map_keys_iterator_surface_fail_closed_error",
        &["unsupported", "for", "keys", "unresolved variable"],
    ),
    (
        "default_hasher_verifier_surface_fail_closed_error",
        &[
            "unsupported",
            "DefaultHasher",
            "write",
            "finish",
            "unresolved variable",
        ],
    ),
];

pub fn hash_rs_expected_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    HASH_RS_EXPECTED_ERROR_PATTERNS
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HashRsRuntimeKey {
    pub i: u16,
    pub j: i32,
}

pub fn test_default_hasher_runtime_equal_write_sequence() {
    let mut h1 = std::collections::hash_map::DefaultHasher::new();
    let mut h2 = std::collections::hash_map::DefaultHasher::new();
    let v1 = [1u8, 2u8];
    let v2 = [3u8, 4u8];

    h1.write(&v1);
    h1.write(&v2);
    h2.write(&v1);
    h2.write(&v2);

    assert_eq!(h1.finish(), h2.finish());
}

pub fn test_default_hasher_runtime_wrong_write_sequence_counterexample() {
    let mut h1 = std::collections::hash_map::DefaultHasher::new();
    let mut h2 = std::collections::hash_map::DefaultHasher::new();

    h1.write(&[1u8, 2u8]);
    h1.write(&[3u8, 4u8]);
    h2.write(&[3u8, 4u8]);
    h2.write(&[1u8, 2u8]);

    assert_eq!(h1.finish(), h2.finish());
}

pub fn test_hash_map_runtime_std_behavior() {
    let mut m = HashMap::<u32, i8>::new();
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

pub fn test_hash_map_runtime_wrong_removed_key_counterexample() {
    let mut m = HashMap::<u32, i8>::new();
    m.insert(3, 4);
    m.insert(6, -8);
    m.remove(&6);

    assert!(m.contains_key(&6));
}

pub fn test_hash_map_runtime_box_key_behavior() {
    let mut m = HashMap::<Box<u32>, i8>::new();
    assert!(m.is_empty());

    m.insert(Box::new(3), 4);
    m.insert(Box::new(6), -8);

    assert!(m.contains_key(&3));
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(&6), Some(&-8));

    let removed = m.remove(&6);
    assert_eq!(removed, Some(-8));
    assert!(!m.contains_key(&6));
    assert!(m.contains_key(&3));

    m.clear();
    assert!(!m.contains_key(&3));
    assert!(m.is_empty());
}

pub fn test_hash_map_runtime_wrong_box_removed_key_counterexample() {
    let mut m = HashMap::<Box<u32>, i8>::new();
    m.insert(Box::new(3), 4);
    m.insert(Box::new(6), -8);
    m.remove(&6);

    assert!(m.contains_key(&6));
}

pub fn test_hash_map_runtime_struct_key_behavior() {
    let mut m = HashMap::<HashRsRuntimeKey, u32>::new();
    let s1 = HashRsRuntimeKey { i: 3, j: 7 };
    let s2 = HashRsRuntimeKey { i: 3, j: 7 };

    m.insert(s1, 4);

    assert!(m.contains_key(&s2));
    assert_eq!(m.get(&s2), Some(&4));

    m.clear();
    assert!(!m.contains_key(&s2));
}

pub fn test_hash_map_runtime_wrong_struct_lookup_counterexample() {
    let mut m = HashMap::<HashRsRuntimeKey, u32>::new();
    m.insert(HashRsRuntimeKey { i: 3, j: 7 }, 4);

    assert!(m.contains_key(&HashRsRuntimeKey { i: 9, j: 9 }));
}

pub fn test_string_hash_map_runtime_std_behavior() {
    let mut m = HashMap::<String, i8>::new();
    assert!(m.is_empty());

    let three = String::from("three");
    let six = String::from("six");

    m.insert(three.clone(), 4);
    assert!(!m.is_empty());
    m.insert(six.clone(), -8);

    assert_ne!(three, six);
    assert!(m.contains_key("three"));
    assert_eq!(m.len(), 2);
    assert_eq!(m.get("six"), Some(&-8));

    let removed = m.remove("six");
    assert_eq!(removed, Some(-8));
    assert!(!m.contains_key("six"));
    assert!(m.contains_key("three"));

    m.clear();
    assert!(!m.contains_key("three"));
}

pub fn test_string_hash_map_runtime_wrong_removed_key_counterexample() {
    let mut m = HashMap::<String, i8>::new();
    m.insert(String::from("three"), 4);
    m.insert(String::from("six"), -8);
    m.remove("six");

    assert!(m.contains_key("six"));
}

pub fn test_hash_map_runtime_keys_values_iter_behavior() {
    let mut m = HashMap::<u32, i8>::new();
    m.insert(3, 4);
    m.insert(6, -8);

    let mut keys = m.keys().copied().collect::<Vec<_>>();
    keys.sort_unstable();
    assert_eq!(keys, vec![3u32, 6u32]);

    let mut values = m.values().copied().collect::<Vec<_>>();
    values.sort_unstable();
    assert_eq!(values, vec![-8i8, 4i8]);

    let mut pairs = m.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>();
    pairs.sort_unstable_by_key(|(k, _)| *k);
    assert_eq!(pairs, vec![(3u32, 4i8), (6u32, -8i8)]);
}

pub fn test_hash_set_runtime_std_behavior() {
    let mut m = HashSet::<u32>::new();
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

pub fn test_hash_set_runtime_wrong_duplicate_insert_counterexample() {
    let mut m = HashSet::<u32>::new();
    let inserted = m.insert(3);
    let inserted_again = m.insert(3);

    assert!(inserted);
    assert!(inserted_again);
}

pub fn test_hash_set_runtime_box_key_behavior() {
    let mut m = HashSet::<Box<u32>>::new();
    assert!(m.is_empty());

    let inserted = m.insert(Box::new(3));
    assert!(inserted);
    m.insert(Box::new(6));
    assert!(!m.is_empty());

    let inserted_again = m.insert(Box::new(3));
    assert!(!inserted_again);
    assert!(m.contains(&3));
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(&6).map(|v| **v), Some(6));

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

pub fn test_hash_set_runtime_wrong_box_duplicate_insert_counterexample() {
    let mut m = HashSet::<Box<u32>>::new();
    let inserted = m.insert(Box::new(3));
    let inserted_again = m.insert(Box::new(3));

    assert!(inserted);
    assert!(inserted_again);
}

pub fn test_hash_set_runtime_struct_key_behavior() {
    let mut m = HashSet::<HashRsRuntimeKey>::new();
    let s1 = HashRsRuntimeKey { i: 3, j: 7 };
    let s2 = HashRsRuntimeKey { i: 3, j: 7 };

    let inserted = m.insert(s1);
    assert!(inserted);

    let inserted_again = m.insert(HashRsRuntimeKey { i: 3, j: 7 });
    assert!(!inserted_again);

    assert!(m.contains(&s2));
    assert_eq!(m.get(&s2), Some(&s2));

    let s3 = HashRsRuntimeKey { i: 9, j: 9 };
    m.insert(s3);
    let removed = m.remove(&s3);
    assert!(removed);
    let removed_again = m.remove(&s3);
    assert!(!removed_again);

    m.clear();
    assert!(!m.contains(&s2));
}

pub fn test_hash_set_runtime_wrong_struct_membership_counterexample() {
    let mut m = HashSet::<HashRsRuntimeKey>::new();
    m.insert(HashRsRuntimeKey { i: 3, j: 7 });

    assert!(m.contains(&HashRsRuntimeKey { i: 9, j: 9 }));
}

pub fn test_string_hash_set_runtime_std_behavior() {
    let mut m = HashSet::<String>::new();
    assert!(m.is_empty());

    let three = String::from("three");
    let six = String::from("six");

    let inserted = m.insert(three.clone());
    assert!(inserted);
    assert!(!m.is_empty());
    m.insert(six.clone());

    let inserted_again = m.insert(String::from("three"));
    assert!(!inserted_again);
    assert_ne!(three, six);
    assert!(m.contains("three"));
    assert_eq!(m.len(), 2);
    assert_eq!(m.get("six").map(String::as_str), Some("six"));

    let removed = m.remove("six");
    assert!(removed);
    let removed_again = m.remove("six");
    assert!(!removed_again);
    assert!(!m.contains("six"));
    assert!(m.contains("three"));

    m.clear();
    assert!(!m.contains("three"));
}

pub fn test_string_hash_set_runtime_wrong_duplicate_insert_counterexample() {
    let mut m = HashSet::<String>::new();
    let inserted = m.insert(String::from("three"));
    let inserted_again = m.insert(String::from("three"));

    assert!(inserted);
    assert!(inserted_again);
}

pub fn test_hash_set_runtime_iter_behavior() {
    let mut m = HashSet::<u32>::new();
    m.insert(3);
    m.insert(6);

    let mut items = m.iter().copied().collect::<Vec<_>>();
    items.sort_unstable();
    assert_eq!(items, vec![3u32, 6u32]);
}

fn hash_map_view_model_insert_lookup_verified() {
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

fn hash_set_view_model_insert_membership_verified() {
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

fn hash_map_view_model_remove_verified() {
    trust_vc::assert!(!Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .remove(6u32)
        .contains_key(6u32));
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .remove(6u32)
        .contains_key(3u32));
}

fn hash_map_view_model_domain_values_verified() {
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .dom()
        .contains(3u32));
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .dom()
        .contains(6u32));
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .contains_value(4i8));
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(6u32, -8i8)
        .contains_value(-8i8));
}

fn hash_map_view_model_overwrite_verified() {
    trust_vc::assert!(Map::<u32, i8>::empty()
        .insert(3u32, 4i8)
        .insert(3u32, 7i8)
        .contains_key(3u32));
    trust_vc::assert!(
        Map::<u32, i8>::empty()
            .insert(3u32, 4i8)
            .insert(3u32, 7i8)
            .get(3u32)
            == 7i8
    );
}

fn hash_set_view_model_duplicate_insert_verified() {
    trust_vc::assert!(Set::<u32>::empty().insert(3u32).insert(3u32).contains(3u32));
    trust_vc::assert!(
        Set::<u32>::empty().insert(3u32).insert(3u32) == Set::<u32>::empty().insert(3u32)
    );
}

fn hash_map_removed_key_boolean_witness_counterexample() {
    let contains_removed_key = false;

    trust_vc::assert!(contains_removed_key);
}

fn hash_set_duplicate_insert_boolean_witness_counterexample() {
    let duplicate_inserted = false;

    trust_vc::assert!(duplicate_inserted);
}

fn std_hash_map_direct_view_verified(m: HashMap<u32, i8>) {
    trust_vc::assert!(m.view().contains_key(3u32) == m.view().contains_key(3u32));
}

fn std_hash_set_direct_view_verified(s: HashSet<u32>) {
    trust_vc::assert!(s.view().contains(3u32) == s.view().contains(3u32));
}

fn std_hash_map_direct_view_key_guard_verified(m: HashMap<u32, i8>) {
    trust_vc::assume!(m.view().contains_key(3u32));
    trust_vc::assert!(m.view().contains_key(3u32));
}

fn std_hash_set_direct_view_member_guard_verified(s: HashSet<u32>) {
    trust_vc::assume!(s.view().contains(3u32));
    trust_vc::assert!(s.view().contains(3u32));
}

fn std_hash_map_mutation_surface_fail_closed_error() {
    let mut m = HashMap::<u32, i8>::new();
    m.insert(3u32, 4i8);

    trust_vc::assert!(m.contains_key(&3u32));
}

fn std_hash_set_mutation_surface_fail_closed_error() {
    let mut s = HashSet::<u32>::new();
    s.insert(3u32);

    trust_vc::assert!(s.contains(&3u32));
}

fn hash_map_keys_iterator_surface_fail_closed_error(m: HashMap<u32, i8>) {
    let mut seen = 0usize;

    for key in m.keys() {
        trust_vc::assert!(*key == *key);
        seen += 1usize;
    }

    let _ = seen;
    trust_vc::assert!(seen == seen);
}

fn default_hasher_verifier_surface_fail_closed_error() {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    h.write(&[1u8, 2u8]);

    trust_vc::assert!(h.finish() == h.finish());
}
