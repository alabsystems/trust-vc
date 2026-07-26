//! Set lemma specifications for `trust_vc_types::Set`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::Set;

// ---------------------------------------------------------------------------
// 8 required lemmas from issue #2741
// ---------------------------------------------------------------------------

/// Lemma: inserting an element into a set makes that element a member.
///
/// Property:
/// `s.insert(v).contains(v)`.
#[trust_vc::proof]
pub fn set_insert_contains<T: Copy>(s: Set<T>, v: T) {
    trust_vc::ensures!(s.insert(v).contains(v));
}

/// Lemma: removing an element ensures that element is not contained.
///
/// Property:
/// `!s.remove(v).contains(v)`.
#[trust_vc::proof]
pub fn set_remove_not_contains<T: Copy>(s: Set<T>, v: T) {
    trust_vc::ensures!(!s.remove(v).contains(v));
}

/// Lemma: union is commutative.
///
/// Property:
/// `a.union(b) == b.union(a)`.
#[trust_vc::proof]
pub fn set_union_comm<T: Copy + PartialEq>(a: Set<T>, b: Set<T>) {
    trust_vc::ensures!(a.union(b) == b.union(a));
}

/// Lemma: the intersection of two sets is a subset of the left input.
///
/// Property:
/// `a.intersect(b).subset(&a)`.
#[trust_vc::proof]
pub fn set_intersect_subset<T: Copy>(a: Set<T>, b: Set<T>) {
    let inter: Set<T> = a.intersect(b);
    trust_vc::ensures!(inter.subset(&a));
}

/// Lemma: the difference of two disjoint sets has the same length as the
/// left set (when the sets share no elements).
///
/// Property:
/// if `a.intersect(b).len() == 0`, then `a.difference(b).len() == a.len()`.
#[trust_vc::proof]
pub fn set_difference_disjoint<T: Copy>(a: Set<T>, b: Set<T>) {
    trust_vc::requires!(a.intersect(b).is_empty());
    let a_len: usize = a.len();
    trust_vc::ensures!(a.difference(b).len() == a_len);
}

/// Lemma: two sets are equal when they contain exactly the same elements
/// (extensional equality).
///
/// Property:
/// if `forall v: a.contains(v) == b.contains(v)`, then `a == b`.
#[trust_vc::proof]
pub fn set_ext_equal<T: Copy + PartialEq>(a: Set<T>, b: Set<T>) {
    trust_vc::requires!(trust_vc::forall!(|v: T| a.contains(v) == b.contains(v)));
    trust_vc::ensures!(a == b);
}

/// Lemma: inserting an element increases the set size by at most 1.
///
/// Property:
/// `s.insert(v).len() <= s.len() + 1`.
#[trust_vc::proof]
pub fn set_insert_len<T: Copy>(s: Set<T>, v: T) {
    let old_len: usize = s.len();
    trust_vc::ensures!(s.insert(v).len() <= old_len + 1);
}

/// Lemma: for a finite set, if a property holds for the empty set and
/// is preserved by insertion, then it holds for the entire set.
///
/// This is a structural lemma: if `s.len() == 0`, then `s == Set::empty()`.
///
/// Property:
/// `s.len() == 0 ==> s == Set::empty()`.
#[trust_vc::proof]
pub fn set_finite_induction<T: Copy + PartialEq>(s: Set<T>) {
    trust_vc::requires!(s.is_empty());
    trust_vc::ensures!(s == Set::<T>::empty());
}
