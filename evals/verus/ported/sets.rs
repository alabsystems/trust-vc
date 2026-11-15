// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused executable TrustVc port for a smallest exact upstream
// `rust_verify_test/tests/sets.rs` subset. The rest of sets.rs remains blocked
// on Set::new comprehensions, reverse Set::map exactness, map_by, and set_build!.

use trust_vc_types::{int, nat, Seq, Set, SpecFn};

pub const SETS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test_len", "test_len", "verified", 1),
    ("test_len_fails", "test_len_fails", "counterexample", 1),
    (
        "test_set_fold_singleton",
        "test_set_fold",
        "verified",
        1,
    ),
    ("test_set_fold_empty", "test_set_fold", "verified", 1),
    (
        "test_set_fold_two_insert_sum",
        "test_set_fold",
        "verified",
        1,
    ),
    (
        "test_set_fold_collection_accumulator_fail_closed",
        "test_set_fold",
        "error",
        0,
    ),
    (
        "test1_filter_preserves_positive_member",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_set_new_empty_alias_boundary",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_filter_excludes_nonpositive_member",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_map_forward_image_contains_successor",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_finite_insert_order_extensionality",
        "test1",
        "verified",
        1,
    ),
    (
        "test_choose_assert_witness",
        "test_choose_assert_witness",
        "verified",
        1,
    ),
    (
        "test_choose_fails_witness",
        "test_choose_fails_witness",
        "counterexample",
        1,
    ),
];

pub fn sets_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    SETS_RS_EXPECTED_CASES
}

pub const SETS_RS_FAIL_CLOSED_ERROR_PATTERNS: &[(&str, &[&str])] = &[(
    "test_set_fold_collection_accumulator_fail_closed",
    &["Set::fold currently supports non-collection accumulator/result types only"],
)];

pub fn sets_rs_fail_closed_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    SETS_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::ensures(true)]
fn test_len<A>(s: Set<A>) {
    trust_vc::assert!((s.len() as int) >= 0);
}

#[trust_vc::ensures(true)]
fn test_len_fails<A>(s1: Set<A>, s2: Set<A>) {
    trust_vc::assert!(s1.len() == s2.len());
}

#[trust_vc::ensures(true)]
fn test_set_fold_singleton() {
    trust_vc::assert!(Set::<usize>::empty().insert(9usize).finite());
    trust_vc::assert!(Set::<usize>::empty().insert(9usize).len() > 0usize);
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(9usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 9usize
    );
}

#[trust_vc::ensures(true)]
fn test_set_fold_empty() {
    trust_vc::assert!(
        Set::<usize>::empty().fold(0usize, SpecFn::new(|p: usize, a: usize| p + a)) == 0usize
    );
}

#[trust_vc::ensures(true)]
fn test_set_fold_two_insert_sum() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(4usize)
            .insert(7usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 11usize
    );
}

// Liar twins of the verified `test_set_fold_singleton` / `test_set_fold_two_insert_sum` /
// `test_set_fold_empty` rows: the SAME shapes with a false sum. They are refuted
// (Counterexample) and pinned by the suite's `FOLD_LIAR_TWINS`, deliberately NOT as rows
// of the table above:
// upstream `test_set_fold` is `=> Ok(())`, and a mapped `counterexample` row would be
// a per-case verdict mismatch for the gate.
#[trust_vc::ensures(true)]
fn test_set_fold_singleton_wrong_sum_counterexample() {
    trust_vc::assert!(Set::<usize>::empty().insert(9usize).finite());
    trust_vc::assert!(Set::<usize>::empty().insert(9usize).len() > 0usize);
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(9usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 10usize
    );
}

#[trust_vc::ensures(true)]
fn test_set_fold_two_insert_wrong_sum_counterexample() {
    trust_vc::assert!(
        Set::<usize>::empty()
            .insert(4usize)
            .insert(7usize)
            .fold(0usize, SpecFn::new(|p: usize, a: usize| p + a))
            == 12usize
    );
}

#[trust_vc::ensures(true)]
fn test_set_fold_empty_wrong_sum_counterexample() {
    trust_vc::assert!(
        Set::<usize>::empty().fold(0usize, SpecFn::new(|p: usize, a: usize| p + a)) == 1usize
    );
}

#[trust_vc::ensures(true)]
fn test_set_fold_collection_accumulator_fail_closed() {
    trust_vc::assert!(
        Set::<i32>::empty()
            .insert(4i32)
            .fold(
                Seq::<i32>::empty(),
                SpecFn::new(|acc: Seq<i32>, x: i32| acc.push(x))
            )
            .len()
            == 1usize
    );
}

#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::ensures(true)]
fn test1_filter_preserves_positive_member(s: Set<i32>) {
    trust_vc::assert!(s.filter(SpecFn::new(|i: i32| i > 0i32)).contains(5i32));
}

#[trust_vc::ensures(true)]
fn test1_set_new_empty_alias_boundary() {
    trust_vc::assert!(Set::<int>::new() == Set::<int>::empty());
    trust_vc::assert!(!Set::<int>::new().contains(0 as int));
}

#[trust_vc::requires(s.contains(0 as int))]
#[trust_vc::ensures(true)]
fn test1_filter_excludes_nonpositive_member(s: Set<int>) {
    trust_vc::assert!(!s
        .filter(SpecFn::new(|i: int| i > (0 as int)))
        .contains(0 as int));
}

#[trust_vc::requires(s.contains(2 as int))]
#[trust_vc::ensures(true)]
fn test1_map_forward_image_contains_successor(s: Set<int>) {
    trust_vc::assert!(s
        .map(SpecFn::new(|i: int| i + (1 as int)))
        .contains(3 as int));
}

#[trust_vc::ensures(true)]
fn test1_finite_insert_order_extensionality() {
    trust_vc::assert!(
        Set::<i32>::empty().insert(1i32).insert(2i32)
            == Set::<i32>::empty().insert(2i32).insert(1i32)
    );
}

// Liar twins of verified `test1` rows above: each is the SAME shape with a false claim,
// refuted (Counterexample) and pinned by the suite's `TEST1_LIAR_TWINS`, not as table rows
// (upstream `test1` is `=> Ok(())`). The three SYMBOLIC-set rows (`filter` twice, `map`)
// have no twin here: re-measured 2026-09-14 at ay 0.26.0, five false claims on those
// shapes all came back `unknown ((incomplete quantifier-unhandled))`, never a
// Counterexample, and an unrefuted liar is not evidence.
#[trust_vc::ensures(true)]
fn test1_set_new_empty_contains_counterexample() {
    trust_vc::assert!(Set::<int>::new().contains(0 as int));
}

#[trust_vc::ensures(true)]
fn test1_finite_insert_wrong_extensionality_counterexample() {
    trust_vc::assert!(
        Set::<i32>::empty().insert(1i32).insert(2i32)
            == Set::<i32>::empty().insert(2i32).insert(3i32)
    );
}

#[trust_vc::requires(s.contains(w))]
#[trust_vc::ensures(true)]
fn test_choose_assert_witness(s: Set<nat>, w: nat) {
    trust_vc::assert!(s.contains(w));
    trust_vc::assert!(s.contains(s.choose()));
}

#[trust_vc::requires(s.contains(w))]
#[trust_vc::ensures(true)]
fn test_choose_fails_witness(s: Set<nat>, w: nat) {
    trust_vc::assert!(s.contains(s.choose()));
    trust_vc::assert!(s.contains(w) && false);
}
