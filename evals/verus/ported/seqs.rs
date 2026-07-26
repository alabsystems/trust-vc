// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial TrustVc port for upstream Verus `rust_verify_test/tests/seqs.rs`.
//
// This intentionally covers only Seq cases that produce stable TrustVc evidence
// on the current direct-source corpus path: verified, counterexample, or error.
// The manifest keeps the upstream file fail-closed because broader vstd::Seq
// extensionality, to_set, filter, fold, and macro behavior still need support.

use trust_vc_types::{Seq, SpecFn};

pub type SeqsExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const SEQS_RS_EXPECTED_CASES: &[SeqsExpectedCase] = &[
    (
        "test1_empty_and_single_push_len_exact_subset",
        "test1",
        "verified",
        1,
    ),
    ("test1_finite_push_len_and_index", "test1", "verified", 1),
    ("test1_push_index_last_element", "test1", "verified", 1),
    (
        "test1_push_extensional_adjacent_exact_subset",
        "test1",
        "verified",
        1,
    ),
    ("test1_seq_map_index", "test1", "verified", 1),
    ("test1_bool_and_repeat_literals", "test1", "verified", 1),
    ("test1_seq_to_set_contains", "test1", "verified", 1),
    (
        "test1_seq_to_set_contains_matches_source_contains",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_contains_matches_source_contains_variable",
        "test1",
        "verified",
        1,
    ),
    ("test1_subrange_add_len", "test1", "verified", 1),
    (
        "test1_seq_new_generator_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_update_len_and_indices_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_update_extensional_adjacent_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_subrange_empty_and_zero_offset_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_subrange_extensional_adjacent_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_subrange_indices_and_add_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_three_element_membership_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_five_element_membership_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "test1_seq_to_set_finite_exact_subset",
        "test1",
        "verified",
        1,
    ),
    (
        "filter_lemmas_length_bound_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_retained_membership_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_len_and_index_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_drop_then_pack_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_all_retained_indices_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_all_excluded_len_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_small_filter_to_set_retained_membership_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "filter_lemmas_add_then_push_last_index_exact_subset",
        "filter_lemmas",
        "verified",
        1,
    ),
    (
        "auto_extensionality_syntax1",
        "auto_extensionality_syntax1",
        "verified",
        1,
    ),
    (
        "auto_extensionality_syntax2",
        "auto_extensionality_syntax2",
        "verified",
        1,
    ),
    (
        "test1_subrange_wrong_index_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_seq_new_wrong_index_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_update_wrong_value_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_update_wrong_len_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_push_wrong_len_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_extensional_wrong_length_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_extensional_wrong_value_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_seq_to_set_five_element_absent_member_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_seq_to_set_absent_member_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    (
        "test1_subrange_to_set_absent_member_counterexample",
        "test1",
        "counterexample",
        1,
    ),
    ("test1_fails1", "test1_fails1", "counterexample", 1),
    (
        "test1_push_index_wrong_value_fails",
        "test1_fails1",
        "counterexample",
        1,
    ),
    ("test1_fails2", "test1_fails2", "counterexample", 1),
    (
        "seq_flat_map_binder_dependent_take_currently_blocked",
        "broader vstd::Seq::flat_map",
        "error",
        0,
    ),
    (
        "seq_fold_left_collection_accumulator_currently_blocked",
        "broader vstd::Seq::fold_left",
        "error",
        0,
    ),
    (
        "seq_empty_macro_type_inference_currently_blocked",
        "broader vstd::seq! empty literal",
        "error",
        0,
    ),
];

pub fn seqs_rs_expected_cases() -> &'static [SeqsExpectedCase] {
    SEQS_RS_EXPECTED_CASES
}

#[trust_vc::ensures(true)]
fn test1_empty_and_single_push_len_exact_subset() {
    trust_vc::assert!(Seq::<i32>::empty().len() == 0usize);
    trust_vc::assert!(Seq::<i32>::empty().push(42i32).len() == 1usize);
}

#[trust_vc::ensures(true)]
fn test1_finite_push_len_and_index() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            .len()
            == 5usize
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            .index(3usize)
            == 30i32
    );
}

#[trust_vc::ensures(true)]
fn test1_push_index_last_element() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(11i32)
            .push(22i32)
            .push(33i32)
            .index(2usize)
            == 33i32
    );
}

#[trust_vc::ensures(true)]
fn test1_push_extensional_adjacent_exact_subset() {
    trust_vc::assert_seqs_equal!(
        trust_vc_types::seq![10i32, 20i32].push(30i32) == trust_vc_types::seq![10i32, 20i32, 30i32]
    );
}

#[trust_vc::ensures(true)]
fn test1_seq_map_index() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a))
            .len()
            == Seq::<i32>::empty()
                .push(10i32)
                .push(20i32)
                .push(30i32)
                .len()
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .map(SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a))
            .index(2usize)
            == 34i32
    );
}

#[trust_vc::ensures(true)]
fn test1_bool_and_repeat_literals() {
    trust_vc::assert!(!Seq::<bool>::empty().push(false).push(true).index(0usize));
    trust_vc::assert!(Seq::<bool>::empty().push(false).push(true).index(1usize));
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .index(0usize)
            == 5i32
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .push(5i32)
            .len()
            == 10usize
    );
}

#[trust_vc::ensures(true)]
fn test1_seq_to_set_contains() {
    trust_vc::assert!(Seq::<i32>::empty()
        .push(5i32)
        .push(8i32)
        .to_set()
        .contains(5i32));
}

#[trust_vc::requires(s.contains(5i32))]
#[trust_vc::ensures(true)]
fn test1_seq_to_set_contains_matches_source_contains(s: Seq<i32>) {
    trust_vc::assert!(s.to_set().contains(5i32));
}

#[trust_vc::requires(s.contains(needle))]
#[trust_vc::ensures(true)]
fn test1_seq_to_set_contains_matches_source_contains_variable(s: Seq<i32>, needle: i32) {
    trust_vc::assert!(s.to_set().contains(needle));
}

#[trust_vc::requires(!s.contains(9i32))]
#[trust_vc::ensures(true)]
fn test1_seq_to_set_absent_element_fails(s: Seq<i32>) {
    trust_vc::assert!(s.to_set().contains(9i32));
}

#[trust_vc::requires(!s.contains(needle))]
#[trust_vc::ensures(true)]
fn test1_seq_to_set_absent_variable_counterexample(s: Seq<i32>, needle: i32) {
    trust_vc::assert!(s.to_set().contains(needle));
}

#[trust_vc::requires(s.len() == 5usize)]
#[trust_vc::requires(t.len() == 5usize)]
#[trust_vc::ensures(true)]
fn test1_subrange_add_len(s: Seq<i32>, t: Seq<i32>) {
    trust_vc::assert!(s.subrange(1usize, 4usize).len() == 3usize);
    trust_vc::assert!(s.subrange(1usize, 4usize).add(t).len() == 8usize);
}

#[trust_vc::ensures(true)]
fn test1_seq_new_generator_exact_subset() {
    trust_vc::assert!(
        Seq::<i32>::new(5usize, SpecFn::new(|i: usize| 10i32 * (i as i32))).len() == 5usize
    );
    trust_vc::assert!(
        Seq::<i32>::new(5usize, SpecFn::new(|i: usize| 10i32 * (i as i32))).index(3usize) == 30i32
    );
}

#[trust_vc::ensures(true)]
fn test1_seq_new_wrong_index_counterexample() {
    trust_vc::assert!(
        Seq::<i32>::new(5usize, SpecFn::new(|i: usize| 10i32 * (i as i32))).index(3usize) == 40i32
    );
}

#[trust_vc::ensures(true)]
fn test1_update_len_and_indices_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .update(1usize, 25i32)
            .len()
            == 3usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .update(1usize, 25i32)
            .index(0usize)
            == 10i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .update(1usize, 25i32)
            .index(1usize)
            == 25i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .update(1usize, 25i32)
            .index(2usize)
            == 30i32
    );
}

#[trust_vc::ensures(true)]
fn test1_update_extensional_adjacent_exact_subset() {
    trust_vc::assert_seqs_equal!(
        trust_vc_types::seq![10i32, 20i32, 30i32].update(1usize, 25i32)
            == trust_vc_types::seq![10i32, 25i32, 30i32]
    );
}

#[trust_vc::ensures(true)]
fn test1_subrange_empty_and_zero_offset_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .subrange(1usize, 1usize)
            .len()
            == 0usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .subrange(0usize, 2usize)
            .len()
            == 2usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .subrange(0usize, 2usize)
            .index(1usize)
            == 20i32
    );
}

#[trust_vc::ensures(true)]
fn test1_subrange_extensional_adjacent_exact_subset() {
    trust_vc::assert_seqs_equal!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32].subrange(1usize, 4usize)
            == trust_vc_types::seq![10i32, 20i32, 30i32]
    );
}

#[trust_vc::ensures(true)]
fn test1_subrange_indices_and_add_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .len()
            == 3usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .index(0usize)
            == 10i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .index(1usize)
            == 20i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .index(2usize)
            == 30i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .add(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32])
            .len()
            == 8usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .add(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32])
            .index(1usize)
            == 20i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .add(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32])
            .index(6usize)
            == 30i32
    );
}

#[trust_vc::ensures(true)]
fn test1_subrange_wrong_index_counterexample() {
    trust_vc::assert!(
        trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
            .subrange(1usize, 4usize)
            .index(1usize)
            == 30i32
    );
}

#[trust_vc::ensures(true)]
fn test1_update_wrong_value_counterexample() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .update(1usize, 25i32)
            .index(1usize)
            == 20i32
    );
}

#[trust_vc::ensures(true)]
fn test1_update_wrong_len_counterexample() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32]
            .update(1usize, 25i32)
            .len()
            == 4usize
    );
}

#[trust_vc::ensures(true)]
fn test1_push_wrong_len_counterexample() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32].push(30i32).len() == 2usize);
}

#[trust_vc::ensures(true)]
fn test1_extensional_wrong_length_counterexample() {
    trust_vc::assert_seqs_equal!(
        trust_vc_types::seq![10i32, 20i32] == trust_vc_types::seq![10i32, 20i32, 30i32]
    );
}

#[trust_vc::ensures(true)]
fn test1_extensional_wrong_value_counterexample() {
    trust_vc::assert_seqs_equal!(
        trust_vc_types::seq![10i32, 20i32, 30i32] == trust_vc_types::seq![10i32, 25i32, 30i32]
    );
}

#[trust_vc::ensures(true)]
fn test1_seq_to_set_three_element_membership_exact_subset() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32]
        .to_set()
        .contains(10i32));
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32]
        .to_set()
        .contains(30i32));
}

#[trust_vc::ensures(true)]
fn test1_seq_to_set_five_element_membership_exact_subset() {
    trust_vc::assert!(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
        .to_set()
        .contains(0i32));
    trust_vc::assert!(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
        .to_set()
        .contains(40i32));
}

#[trust_vc::ensures(true)]
fn test1_seq_to_set_finite_exact_subset() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32].to_set().finite());
}

#[trust_vc::ensures(true)]
fn test1_seq_to_set_five_element_absent_member_counterexample() {
    trust_vc::assert!(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
        .to_set()
        .contains(50i32));
}

#[trust_vc::ensures(true)]
fn test1_seq_to_set_absent_member_counterexample() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32]
        .to_set()
        .contains(99i32));
}

#[trust_vc::ensures(true)]
fn test1_subrange_to_set_membership_exact_subset() {
    trust_vc::assert!(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
        .subrange(1usize, 4usize)
        .to_set()
        .contains(10i32));
    trust_vc::assert!(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
        .subrange(1usize, 4usize)
        .to_set()
        .contains(30i32));
}

#[trust_vc::ensures(true)]
fn test1_subrange_to_set_absent_member_counterexample() {
    trust_vc::assert!(trust_vc_types::seq![0i32, 10i32, 20i32, 30i32, 40i32]
        .subrange(1usize, 4usize)
        .to_set()
        .contains(40i32));
}

#[trust_vc::ensures(true)]
fn filter_lemmas_length_bound_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            <= trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32].len()
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_wrong_length_bound_currently_blocked() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            > trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32].len()
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_retained_membership_exact_subset() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 45i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .contains(10i32));
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_len_and_index_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 45i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            == 1usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 45i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .index(0usize)
            == 10i32
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_drop_then_pack_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![45i32, 10i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            == 1usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![45i32, 10i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .index(0usize)
            == 10i32
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_all_retained_indices_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            == 2usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .index(0usize)
            == 10i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .index(1usize)
            == 20i32
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_all_excluded_len_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![45i32, 55i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            == 0usize
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_filter_to_set_retained_membership_exact_subset() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 45i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .to_set()
        .contains(10i32));
}

#[trust_vc::ensures(true)]
fn filter_lemmas_add_then_push_last_index_exact_subset() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32]
            .add(trust_vc_types::seq![90i32, 100i32])
            .push(120i32)
            .len()
            == 5usize
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32]
            .add(trust_vc_types::seq![90i32, 100i32])
            .push(120i32)
            .index(2usize)
            == 90i32
    );
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 20i32]
            .add(trust_vc_types::seq![90i32, 100i32])
            .push(120i32)
            .index(4usize)
            == 120i32
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_filter_to_set_excluded_member_counterexample() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 45i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .to_set()
        .contains(45i32));
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_wrong_len_currently_blocked() {
    trust_vc::assert!(
        trust_vc_types::seq![10i32, 45i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .len()
            == 2usize
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_small_wrong_index_currently_blocked() {
    trust_vc::assert!(
        trust_vc_types::seq![45i32, 10i32]
            .filter(SpecFn::new(|x: i32| x < 40i32))
            .index(0usize)
            == 45i32
    );
}

#[trust_vc::ensures(true)]
fn filter_lemmas_retained_membership_currently_blocked() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .contains(10i32));
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .contains(20i32));
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .contains(30i32));
}

#[trust_vc::ensures(true)]
fn filter_lemmas_excluded_element_currently_blocked() {
    trust_vc::assert!(trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
        .filter(SpecFn::new(|x: i32| x < 40i32))
        .contains(45i32));
}

#[trust_vc::ensures(true)]
fn filter_lemmas_distribution_currently_blocked() {
    trust_vc::assert!(
        (trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
            + trust_vc_types::seq![90i32, 100i32])
        .filter(SpecFn::new(|x: i32| x < 40i32))
            == (trust_vc_types::seq![10i32, 20i32, 30i32, 45i32, 55i32, 70i32]
                .filter(SpecFn::new(|x: i32| x < 40i32))
                + trust_vc_types::seq![90i32, 100i32].filter(SpecFn::new(|x: i32| x < 40i32)))
    );
}

#[trust_vc::requires(s.len() == 1usize)]
#[trust_vc::ensures(true)]
fn seq_flat_map_binder_dependent_take_currently_blocked(s: Seq<i32>) {
    trust_vc::assert!(
        s.flat_map(SpecFn::new(|x: i32| {
            Seq::<i32>::empty().push(x).take(x as usize)
        }))
        .len()
            == 1usize
    );
}

#[trust_vc::requires(s.len() == 2usize)]
#[trust_vc::ensures(true)]
fn seq_fold_left_collection_accumulator_currently_blocked(s: Seq<i32>) {
    trust_vc::assert!(
        s.fold_left(
            Seq::<i32>::empty(),
            SpecFn::new(|(acc, x): (Seq<i32>, i32)| acc.push(x)),
        )
        .len()
            == 2usize
    );
}

#[trust_vc::ensures(true)]
fn seq_empty_macro_type_inference_currently_blocked() {
    trust_vc::assert!(trust_vc_types::seq![].len() == 0usize);
}

#[trust_vc::ensures(true)]
fn test1_fails1() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            .index(5usize)
            == 50i32
    );
}

#[trust_vc::ensures(true)]
fn test1_push_index_wrong_value_fails() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(11i32)
            .push(22i32)
            .push(33i32)
            .index(2usize)
            == 22i32
    );
}

#[trust_vc::ensures(true)]
fn test1_fails2() {
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            .len()
            == 5usize
    );
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            .index(3usize)
            == 30i32
    );
    trust_vc::assert!(false);
}

#[trust_vc::ensures(true)]
fn auto_extensionality_syntax1() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32),
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
    ));
    trust_vc::assert!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            == Seq::<i32>::empty()
                .push(0i32)
                .push(10i32)
                .push(20i32)
                .push(30i32)
                .push(40i32)
    );
}

#[trust_vc::ensures(true)]
fn auto_extensionality_syntax2() {
    trust_vc::assert_seqs_equal!(
        Seq::<i32>::empty()
            .push(0i32)
            .push(10i32)
            .push(20i32)
            .push(30i32)
            .push(40i32)
            == Seq::<i32>::empty()
                .push(0i32)
                .push(10i32)
                .push(20i32)
                .push(30i32)
                .push(40i32)
    );
}
