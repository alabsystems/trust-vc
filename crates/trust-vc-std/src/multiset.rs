//! Multiset lemma specifications for `trust_vc_types::Multiset`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::Multiset;

/// Lemma: inserting an element increases that element's multiplicity by 1.
///
/// Property:
/// `ms.insert(v).count(v) == ms.count(v) + 1`.
#[trust_vc::proof]
pub fn multiset_insert_count<T: Copy>(ms: Multiset<T>, v: T) {
    let old_count: usize = ms.count(v);
    trust_vc::ensures!(ms.insert(v).count(v) == old_count + 1);
}

/// Lemma: inserting an element increases the total multiset size by 1.
///
/// Property:
/// `ms.insert(v).len() == ms.len() + 1`.
#[trust_vc::proof]
pub fn multiset_insert_len<T: Copy>(ms: Multiset<T>, v: T) {
    let old_len: usize = ms.len();
    trust_vc::ensures!(ms.insert(v).len() == old_len + 1);
}

/// Lemma: removing an element with positive multiplicity decreases its count by 1.
///
/// Property:
/// if `ms.count(v) > 0`, then `ms.remove(v).count(v) == ms.count(v) - 1`.
#[trust_vc::proof]
pub fn multiset_remove_count<T: Copy>(ms: Multiset<T>, v: T) {
    trust_vc::requires!(ms.count(v) > 0);
    let old_count: usize = ms.count(v);
    trust_vc::ensures!(ms.remove(v).count(v) == old_count - 1);
}

/// Lemma: the empty multiset has length 0.
///
/// Property:
/// `Multiset::empty().len() == 0`.
#[trust_vc::proof]
pub fn multiset_empty_len<T>() {
    trust_vc::ensures!(Multiset::<T>::empty().is_empty());
}

/// Lemma: containment is equivalent to having positive multiplicity.
///
/// Property:
/// `ms.contains(v) iff ms.count(v) > 0`.
#[trust_vc::proof]
pub fn multiset_contains_count<T: Copy>(ms: Multiset<T>, v: T) {
    trust_vc::ensures!(ms.contains(v) == (ms.count(v) > 0));
}

/// Lemma: inserting an element makes that element contained.
///
/// Property:
/// `ms.insert(v).contains(v)`.
#[trust_vc::proof]
pub fn multiset_contains_after_insert<T: Copy>(ms: Multiset<T>, v: T) {
    trust_vc::ensures!(ms.insert(v).contains(v));
}

/// Lemma: the union length is the sum of the input lengths.
///
/// Property:
/// `a.union(b).len() == a.len() + b.len()`.
#[trust_vc::proof]
pub fn multiset_union_len<T: Copy>(a: Multiset<T>, b: Multiset<T>) {
    let al: usize = a.len();
    let bl: usize = b.len();
    trust_vc::ensures!(a.union(b).len() == al + bl);
}

/// Lemma: union is commutative.
///
/// Property:
/// `a.union(b) == b.union(a)`.
#[trust_vc::proof]
pub fn multiset_union_commutative<T: Copy + PartialEq>(a: Multiset<T>, b: Multiset<T>) {
    trust_vc::ensures!(a.union(b) == b.union(a));
}

/// Lemma: intersection is commutative.
///
/// Property:
/// `a.intersect(b) == b.intersect(a)`.
#[trust_vc::proof]
pub fn multiset_intersect_commutative<T: Copy + PartialEq>(a: Multiset<T>, b: Multiset<T>) {
    trust_vc::ensures!(a.intersect(b) == b.intersect(a));
}

/// Lemma: the empty multiset is the identity for union.
///
/// Property:
/// `Multiset::empty().union(s) == s`.
#[trust_vc::proof]
pub fn multiset_empty_union_identity<T: Copy + PartialEq>(s: Multiset<T>) {
    trust_vc::ensures!(Multiset::<T>::empty().union(s) == s);
}

/// Lemma: multiplicities are bounded below by zero (type-level guarantee
/// since `count` returns `usize`, but verified for specification completeness).
///
/// Property:
/// `ms.count(v) == 0 || ms.count(v) > 0`.
#[trust_vc::proof]
pub fn multiset_count_nonneg<T: Copy>(ms: Multiset<T>, v: T) {
    trust_vc::ensures!(ms.count(v) == 0 || ms.count(v) > 0);
}
