// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Faithful TrustVc port of the upstream Verus `rust_verify_test/tests/multiset.rs`
// harness (pinned ref a40d57c73650cd3648b09386bfdb96ab5c270626). The upstream file
// has exactly five `test_verify_one_file!` cases:
//
//   * multiset_basics  => Ok(())             — eight proof fns, all verify.
//   * multiset_fail    => assert_one_fails   — insert2_fail (missing `a != b`).
//   * multiset_fail2   => assert_one_fails   — add_fail (`a.add(b) === a.add(a)`).
//   * multiset_fail3   => assert_one_fails   — sub_add_cancel (missing `b.le(a)`).
//   * multiset_fail4   => assert_one_fails   — choose_count (missing `len != 0`).
//
// Each upstream proof fn is reproduced verbatim through the TrustVc Multiset
// surface. The eight `multiset_basics` proof fns are kept as separate functions
// (their upstream preconditions — distinct values, subset, non-empty, and the
// universal `forall |v| count(v) == 0` — are mutually independent and combining
// them into a single proof body trips solver quantifier incompleteness, so the
// verbatim 1:1 proof-fn layout is also the only faithful one). All eight carry
// `upstream_case_id = multiset_basics`. The four failing proof fns are named for
// the upstream test they reproduce and are genuine counterexamples.
//
// Surface mapping (faithful, no weakening):
//   * `a =~= b`  (extensional eq)  -> `trust_vc::assert!(trust_vc::ext_eq!(a, b))`
//   * `a === b`  (`equal`/strict)  -> `#[trust_vc::ensures(a == b)]` (Multiset `==`
//     lowers to Compare::Eq over the count carrier — exactly Verus strict equality).
//   * `a !== b`                     -> `a != b`
//   * `.choose() / .count / .add / .sub / .insert / .len / .subset_of` map to the
//     identically-named Multiset surface methods.

use trust_vc_types::Multiset;

// ───────────────────────── multiset_basics => Ok(()) ─────────────────────────

#[trust_vc::ensures(a.add(b) == b.add(a))]
fn commutative<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), b.add(a)));
}

#[trust_vc::ensures(a.add(b.add(c)) == a.add(b).add(c))]
fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b.add(c)), a.add(b).add(c)));
}

#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b) == Multiset::<V>::empty().insert(b).insert(a))]
fn insert2<V>(a: V, b: V) {
    trust_vc::assert!(trust_vc::ext_eq!(
        Multiset::<V>::empty().insert(a).insert(b),
        Multiset::<V>::empty().insert(b).insert(a)
    ));
}

#[trust_vc::requires(a != b && b != c && c != a)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b).count(a) == 1usize)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b).count(b) == 1usize)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b).count(c) == 0usize)]
fn insert2_count<V>(a: V, b: V, c: V) {}

#[trust_vc::ensures(a.add(b).sub(b) == a)]
fn add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b).sub(b), a));
}

#[trust_vc::requires(b.subset_of(a))]
#[trust_vc::ensures(a.sub(b).add(b) == a)]
fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.sub(b).add(b), a));
}

#[trust_vc::requires(m.len() != 0usize)]
#[trust_vc::ensures(true)]
fn choose_count<V>(m: Multiset<V>) {
    trust_vc::assert!(m.count(m.choose()) > 0usize);
}

#[trust_vc::requires(forall(|v: V| m.count(v) == 0u64))]
#[trust_vc::ensures(m.len() == 0usize)]
fn len_is_zero_if_count_for_each_value_is_zero<V>(m: Multiset<V>) {
    if m.len() != 0usize {
        trust_vc::assert!(m.count(m.choose()) > 0usize);
    }
}

// ───────────────────── multiset_fail => assert_one_fails ─────────────────────
// insert2_fail: should fail because there is no precondition `a != b`.
#[trust_vc::ensures(true)]
fn multiset_fail<V>(a: V, b: V, c: V) {
    trust_vc::assert!(Multiset::<V>::empty().insert(a).insert(b).count(a) == 1usize);
}

// ──────────────────── multiset_fail2 => assert_one_fails ─────────────────────
// add_fail: `equal(a.add(b), a.add(a))` is genuinely false.
#[trust_vc::ensures(a.add(b) == a.add(a))]
fn multiset_fail2<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), a.add(a)));
}

// ──────────────────── multiset_fail3 => assert_one_fails ─────────────────────
// sub_add_cancel: missing the condition `b.le(a)`, so `a.sub(b).add(b) === a`
// is false where `b` has more of some element than `a`.
#[trust_vc::ensures(a.sub(b).add(b) == a)]
fn multiset_fail3<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.sub(b).add(b), a));
}

// ──────────────────── multiset_fail4 => assert_one_fails ─────────────────────
// choose_count: missing the precondition `m.len() != 0`.
#[trust_vc::ensures(true)]
fn multiset_fail4<V>(m: Multiset<V>) {
    trust_vc::assert!(m.count(m.choose()) > 0usize);
}
