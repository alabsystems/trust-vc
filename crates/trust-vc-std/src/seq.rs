//! Sequence lemma specifications for `trust_vc_types::Seq`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::Seq;

// ---------------------------------------------------------------------------
// 12 required lemmas from issue #2741
// ---------------------------------------------------------------------------

/// Lemma: pushing an element onto a sequence increases its length by exactly 1.
///
/// Property:
/// `seq.push(value).len() == seq.len() + 1`.
#[trust_vc::proof]
pub fn seq_push_len<T: Copy>(seq: Seq<T>, value: T) {
    let old_len: usize = seq.len();
    trust_vc::ensures!(seq.push(value).len() == old_len + 1);
}

/// Lemma: after pushing an element, the new element appears at the old length.
///
/// Property:
/// `seq.push(value).index(seq.len()) == value`.
#[trust_vc::proof]
pub fn seq_index_push<T: Copy + PartialEq>(seq: Seq<T>, value: T) {
    let idx: usize = seq.len();
    trust_vc::ensures!(seq.push(value).index(idx) == value);
}

/// Lemma: two sequences are equal when they have the same length and equal
/// elements at every valid index (extensional equality).
///
/// Property:
/// if `lhs.len() == rhs.len()` and
/// `forall i < lhs.len(): lhs.index(i) == rhs.index(i)`,
/// then `lhs == rhs`.
#[trust_vc::proof]
pub fn seq_ext_equal<T: Copy + PartialEq>(lhs: Seq<T>, rhs: Seq<T>) {
    trust_vc::requires!(lhs.len() == rhs.len());
    trust_vc::requires!(trust_vc::forall!(
        |i: usize| (i >= lhs.len()) || lhs.index(i) == rhs.index(i)
    ));
    trust_vc::ensures!(lhs == rhs);
}

/// Lemma: splitting a sequence at position `mid` and concatenating the halves
/// reconstructs a sequence whose length is the original length.
///
/// Property:
/// if `mid <= seq.len()`, then
/// `seq.subrange(0, mid).add(seq.subrange(mid, seq.len())).len() == seq.len()`.
#[trust_vc::proof]
pub fn seq_subrange_concat<T: Copy>(seq: Seq<T>, mid: usize) {
    trust_vc::requires!(mid <= seq.len());
    let total: usize = seq.len();
    let left: Seq<T> = seq.subrange(0, mid);
    let right: Seq<T> = seq.subrange(mid, total);
    trust_vc::ensures!(left.add(right).len() == total);
}

/// Lemma: concatenating two sequences yields a sequence whose length is the
/// sum of the input lengths.
///
/// Property:
/// `lhs.add(rhs).len() == lhs.len() + rhs.len()`.
#[trust_vc::proof]
pub fn seq_add_len<T: Copy>(lhs: Seq<T>, rhs: Seq<T>) {
    let l: usize = lhs.len();
    let r: usize = rhs.len();
    trust_vc::ensures!(lhs.add(rhs).len() == l + r);
}

/// Lemma: taking the first `n` elements of a sequence produces a sequence of
/// length `n` when `n <= seq.len()`.
///
/// Property:
/// if `n <= seq.len()`, then `seq.take(n).len() == n`.
#[trust_vc::proof]
pub fn seq_take_len<T: Copy>(seq: Seq<T>, n: usize) {
    trust_vc::requires!(n <= seq.len());
    trust_vc::ensures!(seq.take(n).len() == n);
}

/// Lemma: skipping the first `n` elements of a sequence produces a sequence of
/// length `seq.len() - n` when `n <= seq.len()`.
///
/// Property:
/// if `n <= seq.len()`, then `seq.skip(n).len() == seq.len() - n`.
#[trust_vc::proof]
pub fn seq_skip_len<T: Copy>(seq: Seq<T>, n: usize) {
    trust_vc::requires!(n <= seq.len());
    let total: usize = seq.len();
    trust_vc::ensures!(seq.skip(n).len() == total - n);
}

/// Lemma: filtering a sequence yields a subsequence whose length is at most the
/// original length (filter produces a subset).
///
/// Property:
/// `s.filter(pred).len() <= s.len()`.
#[trust_vc::proof]
pub fn seq_filter_subset<T: Copy>(s: Seq<T>, pred: trust_vc_types::SpecFn<T, bool>) {
    let total: usize = s.len();
    trust_vc::ensures!(s.filter(pred).len() <= total);
}

/// Lemma: mapping a sequence preserves its length.
///
/// Property:
/// `s.map_values(f).len() == s.len()`.
#[trust_vc::proof]
pub fn seq_map_len<T: Copy, U>(s: Seq<T>, f: trust_vc_types::SpecFn<T, U>) {
    let total: usize = s.len();
    trust_vc::ensures!(s.map_values(f).len() == total);
}

/// Lemma: if a sequence contains a value, then there exists an index where
/// that value appears.
///
/// Property:
/// if `s.contains(v)`, then `exists i: i < s.len() && s.index(i) == v`.
#[trust_vc::proof]
pub fn seq_contains_index<T: Copy + PartialEq>(s: Seq<T>, v: T) {
    trust_vc::requires!(s.contains(v));
    trust_vc::ensures!(trust_vc::exists!(|i: usize| i < s.len() && s.index(i) == v));
}

/// Lemma: updating a sequence at index `i` replaces the element at `i` with
/// the new value.
///
/// Property:
/// if `i < seq.len()`, then `seq.update(i, value).index(i) == value`.
#[trust_vc::proof]
pub fn seq_update_index<T: Copy + PartialEq>(seq: Seq<T>, i: usize, value: T) {
    trust_vc::requires!(i < seq.len());
    trust_vc::ensures!(seq.update(i, value).index(i) == value);
}

/// Lemma: reversing a sequence preserves its length.
///
/// Property:
/// `s.reverse().len() == s.len()`.
#[trust_vc::proof]
pub fn seq_reverse_len<T: Copy>(s: Seq<T>) {
    let total: usize = s.len();
    trust_vc::ensures!(s.reverse().len() == total);
}
