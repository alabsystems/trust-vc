//! Map lemma specifications for `trust_vc_types::Map`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::Map;

// ---------------------------------------------------------------------------
// 6 required lemmas from issue #2741
// ---------------------------------------------------------------------------

/// Lemma: inserting a key-value pair makes the key present in the domain.
///
/// Property:
/// `m.insert(k, v).contains_key(k)`.
#[trust_vc::proof]
pub fn map_insert_domain<K: Copy, V: Copy>(m: Map<K, V>, k: K, v: V) {
    trust_vc::ensures!(m.insert(k, v).contains_key(k));
}

/// Lemma: removing a key ensures that looking it up fails (key is absent).
///
/// Property:
/// `!m.remove(k).contains_key(k)`.
#[trust_vc::proof]
pub fn map_remove_lookup<K: Copy, V: Copy>(m: Map<K, V>, k: K) {
    trust_vc::ensures!(!m.remove(k).contains_key(k));
}

/// Lemma: the domain of a map has the same length as the map (domain is finite
/// whenever the map is finite).
///
/// Property:
/// `m.dom().len() == m.len()`.
#[trust_vc::proof]
pub fn map_domain_finite<K: Copy, V: Copy>(m: Map<K, V>) {
    trust_vc::ensures!(m.dom().len() == m.len());
}

/// Lemma: two maps are equal when they have the same domain and agree on every
/// key (extensional equality).
///
/// Property:
/// if `forall k: a.contains_key(k) == b.contains_key(k)` and
/// `forall k: a.contains_key(k) implies a.get(k) == b.get(k)`,
/// then `a == b`.
#[trust_vc::proof]
pub fn map_ext_equal<K: Copy + PartialEq, V: Copy + PartialEq>(a: Map<K, V>, b: Map<K, V>) {
    trust_vc::requires!(trust_vc::forall!(
        |k: K| a.contains_key(k) == b.contains_key(k)
    ));
    trust_vc::requires!(trust_vc::forall!(
        |k: K| !a.contains_key(k) || a.get(k) == b.get(k)
    ));
    trust_vc::ensures!(a == b);
}

/// Lemma: looking up the key just inserted returns the inserted value.
///
/// Property:
/// `m.insert(k, v).get(k) == v`.
#[trust_vc::proof]
pub fn map_insert_lookup_same<K: Copy, V: Copy + PartialEq>(m: Map<K, V>, k: K, v: V) {
    trust_vc::ensures!(m.insert(k, v).get(k) == v);
}

/// Lemma: inserting at one key preserves the value at every other key.
///
/// Property:
/// if `k2 != k` and `m.contains_key(k2)`, then
/// `m.insert(k, v).get(k2) == m.get(k2)`.
#[trust_vc::proof]
pub fn map_insert_lookup_diff<K: Copy + PartialEq, V: Copy + PartialEq>(
    m: Map<K, V>,
    k: K,
    v: V,
    k2: K,
) {
    trust_vc::requires!(k2 != k);
    trust_vc::requires!(m.contains_key(k2));
    let old_val: V = m.get(k2);
    trust_vc::ensures!(m.insert(k, v).get(k2) == old_val);
}
