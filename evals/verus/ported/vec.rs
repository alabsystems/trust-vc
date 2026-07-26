// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Faithful scout port for upstream Verus `rust_verify_test/tests/vec.rs`.
//
// This is intentionally not manifest-promoted. The active upstream file has two
// harness cases:
// - `test_vec_into_iter`: Vec mutation, `v@` view assertions, and into-iterator
//   invariants.
// - `test_vec_dec`: recursive decreases through `Vec<Tree>` children.
//
// The executable functions below preserve the concrete Rust Vec behavior. The
// TrustVc verifier probes use the actual `Vec<T>::view()` and Vec-backed child
// surfaces instead of standalone Seq-model witnesses. The local empty, push, and
// insert/append/remove/swap_remove view prefixes are verified; broader Vec mutation/iterator and
// recursive Vec-child decreases support remains fail-closed.

#![allow(
    clippy::explicit_counter_loop,
    clippy::len_zero,
    clippy::vec_init_then_push,
    dead_code,
    unused_assignments,
    unused_imports,
    unused_variables
)]

use trust_vc_types::View;

pub const UPSTREAM_VEC_RS_ACTIVE_CASES: &[&str] = &["test_vec_into_iter", "test_vec_dec"];

pub const VEC_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "test_vec_new_empty_view_len_verified",
        "test_vec_into_iter",
        "verified",
        1,
    ),
    (
        "test_vec_push_view_exact_verified",
        "test_vec_into_iter",
        "verified",
        4,
    ),
    (
        "test_vec_insert_middle_view_verified",
        "test_vec_into_iter",
        "verified",
        4,
    ),
    (
        "test_vec_insert_front_view_verified",
        "test_vec_into_iter",
        "verified",
        4,
    ),
    (
        "test_vec_insert_end_view_verified",
        "test_vec_into_iter",
        "verified",
        4,
    ),
    (
        "test_vec_append_view_len_prefix_verified",
        "test_vec_into_iter",
        "verified",
        2,
    ),
    (
        "test_vec_remove_middle_view_prefix_verified",
        "test_vec_into_iter",
        "verified",
        2,
    ),
    (
        "test_vec_swap_remove_tail_view_prefix_verified",
        "test_vec_into_iter",
        "verified",
        2,
    ),
];

pub fn upstream_vec_rs_active_cases() -> &'static [&'static str] {
    UPSTREAM_VEC_RS_ACTIVE_CASES
}

pub fn vec_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    VEC_RS_EXPECTED_CASES
}

pub fn test_vec_into_iter_runtime_mutation_prefix() {
    let mut v1: Vec<u32> = Vec::new();
    let mut v2: Vec<u32> = Vec::new();
    v1.push(3);
    v1.push(4);
    assert_eq!(v1, vec![3u32, 4u32]);

    v2.push(5);
    assert_eq!(v2.len(), 1);
    v2.push(7);
    assert_eq!(v2.len(), 2);
    v2.insert(1, 6);
    assert_eq!(v2, vec![5u32, 6u32, 7u32]);

    v1.append(&mut v2);
    assert_eq!(v2.len(), 0);
    assert_eq!(v1.len(), 5);
    assert_eq!(v1, vec![3u32, 4u32, 5u32, 6u32, 7u32]);
    v1.remove(2);
    assert_eq!(v1, vec![3u32, 4u32, 6u32, 7u32]);

    v1.push(8u32);
    v1.push(9u32);
    assert_eq!(v1, vec![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

    v1.swap_remove(5);
    assert_eq!(v1, vec![3u32, 4u32, 6u32, 7u32, 8u32]);

    let mut i: usize = 0;
    for x in v1 {
        assert!(x > 2);
        assert!(x < 10);
        i += 1;
    }
    assert_eq!(i, 5);
}

pub fn test_vec_push_runtime_view_prefix() {
    let mut v: Vec<u32> = Vec::new();
    v.push(3u32);
    v.push(4u32);
    assert_eq!(v, vec![3u32, 4u32]);
}

pub fn test_vec_new_runtime_empty() {
    let v: Vec<u32> = Vec::new();
    assert!(v.is_empty());
    assert_eq!(v.len(), 0);
}

pub fn test_vec_into_iter_runtime_wrong_value_counterexample() {
    let mut v1: Vec<u32> = Vec::new();
    v1.push(3);
    v1.push(4);
    assert_eq!(v1, vec![3u32, 5u32]);
}

pub fn test_vec_insert_remove_runtime_slice() {
    let mut v = vec![5u32, 7u32];
    v.insert(1usize, 6u32);
    assert_eq!(v, vec![5u32, 6u32, 7u32]);

    let removed = v.remove(1usize);
    assert_eq!(removed, 6u32);
    assert_eq!(v, vec![5u32, 7u32]);
}

pub fn test_vec_insert_remove_runtime_wrong_value_counterexample() {
    let mut v = vec![5u32, 7u32];
    v.insert(1usize, 6u32);
    v.remove(1usize);
    assert_eq!(v, vec![5u32, 6u32]);
}

pub fn test_vec_swap_remove_tail_runtime_slice() {
    let mut v = vec![3u32, 4u32, 6u32, 7u32, 8u32, 9u32];
    let removed = v.swap_remove(5usize);
    assert_eq!(removed, 9u32);
    assert_eq!(v, vec![3u32, 4u32, 6u32, 7u32, 8u32]);
}

pub fn test_vec_swap_remove_tail_runtime_wrong_value_counterexample() {
    let mut v = vec![3u32, 4u32, 6u32, 7u32, 8u32, 9u32];
    let removed = v.swap_remove(5usize);
    assert_eq!(removed, 8u32);
}

fn test_vec_push_view_exact_verified() {
    let mut v: Vec<u32> = Vec::new();
    v.push(3u32);
    v.push(4u32);
    trust_vc::assert!(v.view().len() == 2usize);
    trust_vc::assert!(v.view().index(0usize) == 3u32);
    trust_vc::assert!(v.view().index(1usize) == 4u32);
    trust_vc::assert!(v.view() == trust_vc_types::seq![3u32, 4u32]);
}

fn test_vec_new_empty_view_len_verified() {
    let v: Vec<u32> = Vec::new();
    trust_vc::assert!(v.view().len() == 0usize);
}

fn test_vec_insert_middle_view_verified() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5u32);
    v.push(7u32);
    v.insert(1usize, 6u32);
    trust_vc::assert!(v.view().len() == 3usize);
    trust_vc::assert!(v.view().index(0usize) == 5u32);
    trust_vc::assert!(v.view().index(1usize) == 6u32);
    trust_vc::assert!(v.view().index(2usize) == 7u32);
    trust_vc::assert!(v.view() == trust_vc_types::seq![5u32, 6u32, 7u32]);
}

fn test_vec_insert_front_view_verified() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5u32);
    v.push(7u32);
    v.insert(0usize, 4u32);
    trust_vc::assert!(v.view().len() == 3usize);
    trust_vc::assert!(v.view().index(0usize) == 4u32);
    trust_vc::assert!(v.view().index(1usize) == 5u32);
    trust_vc::assert!(v.view().index(2usize) == 7u32);
}

fn test_vec_insert_end_view_verified() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5u32);
    v.push(7u32);
    v.insert(2usize, 9u32);
    trust_vc::assert!(v.view().len() == 3usize);
    trust_vc::assert!(v.view().index(0usize) == 5u32);
    trust_vc::assert!(v.view().index(1usize) == 7u32);
    trust_vc::assert!(v.view().index(2usize) == 9u32);
}

fn test_vec_append_view_len_prefix_verified() {
    let mut v1: Vec<u32> = Vec::new();
    let mut v2: Vec<u32> = Vec::new();
    v1.push(3u32);
    v1.push(4u32);
    v2.push(5u32);
    v2.push(7u32);
    v2.insert(1usize, 6u32);

    v1.append(&mut v2);
    trust_vc::assert!(v2.view().len() == 0usize);
    trust_vc::assert!(v1.view().len() == 5usize);
}

fn test_vec_remove_middle_view_prefix_verified() {
    let mut v1: Vec<u32> = Vec::new();
    v1.push(3u32);
    v1.push(4u32);
    v1.push(5u32);
    v1.push(6u32);
    v1.push(7u32);
    v1.remove(2usize);
    trust_vc::assert!(v1.view().len() == 4usize);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32, 6u32, 7u32]);
}

fn test_vec_swap_remove_tail_view_prefix_verified() {
    let mut v1: Vec<u32> = Vec::new();
    v1.push(3u32);
    v1.push(4u32);
    v1.push(6u32);
    v1.push(7u32);
    v1.push(8u32);
    v1.push(9u32);
    v1.swap_remove(5usize);
    trust_vc::assert!(v1.view().len() == 5usize);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32, 6u32, 7u32, 8u32]);
}

fn test_vec_insert_out_of_bounds_currently_rejected() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5u32);
    v.push(7u32);
    v.insert(3usize, 9u32);
    trust_vc::assert!(v.view().len() == 3usize);
}

fn test_vec_insert_wrong_shift_counterexample() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5u32);
    v.push(7u32);
    v.insert(1usize, 6u32);
    trust_vc::assert!(v.view().index(2usize) == 6u32);
}

fn test_vec_insert_mut_ref_alias_currently_rejected() {
    let mut v: Vec<u32> = Vec::new();
    v.push(5u32);
    v.push(7u32);
    let r = &mut v;
    r.insert(1usize, 6u32);
    trust_vc::assert!(v.view().len() == 3usize);
}

fn test_vec_into_iter_trust_vc_view_surface_currently_blocked() {
    let mut v1: Vec<u32> = Vec::new();
    let mut v2: Vec<u32> = Vec::new();
    v1.push(3);
    v1.push(4);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32]);

    v2.push(5);
    trust_vc::assert!(v2.len() == 1usize);
    v2.push(7);
    trust_vc::assert!(v2.view().len() == 2usize);
    v2.insert(1, 6);
    trust_vc::assert!(v2.view() == trust_vc_types::seq![5u32, 6u32, 7u32]);

    v1.append(&mut v2);
    trust_vc::assert!(v2.view().len() == 0usize);
    trust_vc::assert!(v1.view().len() == 5usize);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32, 5u32, 6u32, 7u32]);
    v1.remove(2);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32, 6u32, 7u32]);

    v1.push(8u32);
    v1.push(9u32);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

    v1.swap_remove(5);
    trust_vc::assert!(v1.view() == trust_vc_types::seq![3u32, 4u32, 6u32, 7u32, 8u32]);

    let mut i: usize = 0;
    for x in v1 {
        trust_vc::assert!(x > 2u32);
        trust_vc::assert!(x < 10u32);
        i += 1;
    }
    trust_vc::assert!(i == 5usize);
}

struct Tree {
    children: Vec<Tree>,
}

fn test_vec_dec_vec_children_decreases_currently_blocked(tree: &Tree) {
    if tree.children.len() > 0 {
        let child = &tree.children[0];
        trust_vc::assert!(child.children.len() <= tree.children.len());
        test_vec_dec_vec_children_decreases_currently_blocked(child);
    }
}
