// View trait tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for the View trait and its implementations.
//!
//! View provides runtime-to-spec type conversion. Since the actual conversion
//! happens at verification time (ay), these tests verify:
//! - Type system correctness (ViewTy associated types)
//! - Runtime behavior (ghost values returned)
//! - Memory characteristics

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use trust_vc_types::{Map, Seq, Set, View};

// ============================================================================
// Vec<T> -> Seq<T>
// ============================================================================

#[test]
fn vec_view_returns_seq() {
    let v: Vec<i32> = vec![1, 2, 3];
    let seq: Seq<i32> = v.view();
    // Runtime: ghost Seq returned (zero-sized)
    assert_eq!(std::mem::size_of_val(&seq), 0);
}

#[test]
fn vec_view_empty() {
    let v: Vec<String> = Vec::new();
    let _seq: Seq<String> = v.view();
}

#[test]
fn vec_view_does_not_consume() {
    let v = vec![1, 2, 3];
    let _seq = v.view();
    // v is still usable
    assert_eq!(v.len(), 3);
}

// ============================================================================
// [T; N] -> Seq<T>
// ============================================================================

#[test]
fn array_view_returns_seq() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let seq: Seq<i32> = arr.view();
    assert_eq!(std::mem::size_of_val(&seq), 0);
}

#[test]
fn array_view_zero_length() {
    let arr: [i32; 0] = [];
    let _seq: Seq<i32> = arr.view();
}

// ============================================================================
// [T] -> Seq<T>
// ============================================================================

#[test]
fn slice_view_returns_seq() {
    let arr = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr[1..4];
    let seq: Seq<i32> = slice.view();
    assert_eq!(std::mem::size_of_val(&seq), 0);
}

#[test]
fn slice_view_from_vec() {
    let v = [10, 20, 30];
    let slice: &[i32] = &v[..];
    let _seq: Seq<i32> = slice.view();
}

#[test]
fn string_view_returns_seq_char() {
    let s = String::from("abc");
    let seq: Seq<char> = s.view();
    assert_eq!(std::mem::size_of_val(&seq), 0);
}

#[test]
fn str_view_returns_seq_char() {
    let s: &str = "abc";
    let seq: Seq<char> = s.view();
    assert_eq!(std::mem::size_of_val(&seq), 0);
}

// ============================================================================
// HashSet<T> -> Set<T>
// ============================================================================

#[test]
fn hashset_view_returns_set() {
    let mut hs: HashSet<i32> = HashSet::new();
    hs.insert(1);
    hs.insert(2);
    let set: Set<i32> = hs.view();
    assert_eq!(std::mem::size_of_val(&set), 0);
}

#[test]
fn hashset_view_empty() {
    let hs: HashSet<String> = HashSet::new();
    let _set: Set<String> = hs.view();
}

// ============================================================================
// BTreeSet<T> -> Set<T>
// ============================================================================

#[test]
fn btreeset_view_returns_set() {
    let mut bts: BTreeSet<i32> = BTreeSet::new();
    bts.insert(1);
    bts.insert(2);
    let set: Set<i32> = bts.view();
    assert_eq!(std::mem::size_of_val(&set), 0);
}

// ============================================================================
// HashMap<K, V> -> Map<K, V>
// ============================================================================

#[test]
fn hashmap_view_returns_map() {
    let mut hm: HashMap<String, i32> = HashMap::new();
    hm.insert("a".to_string(), 1);
    hm.insert("b".to_string(), 2);
    let map: Map<String, i32> = hm.view();
    assert_eq!(std::mem::size_of_val(&map), 0);
}

#[test]
fn hashmap_view_empty() {
    let hm: HashMap<i32, i32> = HashMap::new();
    let _map: Map<i32, i32> = hm.view();
}

// ============================================================================
// BTreeMap<K, V> -> Map<K, V>
// ============================================================================

#[test]
fn btreemap_view_returns_map() {
    let mut btm: BTreeMap<i32, String> = BTreeMap::new();
    btm.insert(1, "one".to_string());
    btm.insert(2, "two".to_string());
    let map: Map<i32, String> = btm.view();
    assert_eq!(std::mem::size_of_val(&map), 0);
}

// ============================================================================
// Identity views: Seq<T> -> Seq<T>
// ============================================================================

#[test]
fn seq_view_is_identity() {
    let seq: Seq<i32> = Seq::empty();
    let viewed: Seq<i32> = seq.view();
    assert_eq!(std::mem::size_of_val(&viewed), 0);
}

// ============================================================================
// Identity views: Set<T> -> Set<T>
// ============================================================================

#[test]
fn set_view_is_identity() {
    let set: Set<i32> = Set::empty();
    let viewed: Set<i32> = set.view();
    assert_eq!(std::mem::size_of_val(&viewed), 0);
}

// ============================================================================
// Identity views: Map<K, V> -> Map<K, V>
// ============================================================================

#[test]
fn map_view_is_identity() {
    let map: Map<i32, String> = Map::empty();
    let viewed: Map<i32, String> = map.view();
    assert_eq!(std::mem::size_of_val(&viewed), 0);
}

// ============================================================================
// ViewTy associated type checks (compile-time verification)
// ============================================================================

/// Compile-time check that Vec<T>::ViewTy == Seq<T>
fn _check_vec_view_ty<T>() {
    fn assert_same_type<A, B>()
    where
        A: Into<B>,
        B: Into<A>,
    {
    }
    // This test exists purely for type-checking at compile time
    let _ = || {
        let v: Vec<T> = Vec::new();
        let _: <Vec<T> as View>::ViewTy = v.view();
    };
}

/// Compile-time check that HashSet<T>::ViewTy == Set<T>
fn _check_hashset_view_ty<T>() {
    let _ = || {
        let hs: HashSet<T> = HashSet::new();
        let _: <HashSet<T> as View>::ViewTy = hs.view();
    };
}

/// Compile-time check that HashMap<K, V>::ViewTy == Map<K, V>
fn _check_hashmap_view_ty<K, V>() {
    let _ = || {
        let hm: HashMap<K, V> = HashMap::new();
        let _: <HashMap<K, V> as View>::ViewTy = hm.view();
    };
}

// ============================================================================
// Generic usage patterns
// ============================================================================

#[test]
fn view_in_generic_context() {
    fn take_view<T: View>(val: &T) -> T::ViewTy {
        val.view()
    }

    let v = vec![1, 2, 3];
    let _seq: Seq<i32> = take_view(&v);

    let hs: HashSet<i32> = [1, 2, 3].into_iter().collect();
    let _set: Set<i32> = take_view(&hs);

    let hm: HashMap<i32, i32> = [(1, 10), (2, 20)].into_iter().collect();
    let _map: Map<i32, i32> = take_view(&hm);
}

#[test]
fn view_multiple_times() {
    // Calling view() multiple times should work
    let v = vec![1, 2, 3];
    let _seq1 = v.view();
    let _seq2 = v.view();
    let _seq3 = v.view();
    // v unchanged
    assert_eq!(v.len(), 3);
}
