// TrustWp compatibility facade tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::compat::trust_wp::{FMap, FSet, Ghost, Seq, Snapshot, View};

#[test]
fn trust_wp_compat_imports_compile() {
    let ghost: Ghost<i32> = Ghost::new(1);
    let value = 7;
    let snapshot: Snapshot<i32> = Snapshot::capture(&value);
    let seq: Seq<i32> = vec![1, 2, 3].view();
    let _ = (ghost, snapshot, seq);
}

#[test]
fn trust_wp_seq_alias_methods_compile() {
    let seq: Seq<i32> = Seq::new().push_back(1).push_back(2);
    let _: Seq<i32> = seq.pop_back();
    let _: Seq<i32> = seq.subsequence(0, 2);
    let _: Seq<i32> = seq.set(1, 9);
}

#[test]
fn trust_wp_set_alias_methods_compile() {
    let left: FSet<i32> = FSet::new().insert(1);
    let right: FSet<i32> = FSet::new().insert(2);
    let _: FSet<i32> = left.intersection(right);
    let _: bool = left.is_subset(right);
    let _: bool = left.is_superset(right);
}

#[test]
fn trust_wp_map_alias_methods_compile() {
    let map: FMap<i32, i32> = FMap::new().insert(1, 2);
    let _: bool = map.contains(1);
    let _ = std::panic::catch_unwind(|| {
        let _: i32 = map.lookup(1);
    });
}

#[test]
fn trust_wp_aliases_match_trust_vc_types() {
    let _: trust_vc_types::Seq<i32> = Seq::new();
    let _: trust_vc_types::Set<i32> = FSet::new();
    let _: trust_vc_types::Map<i32, i32> = FMap::new();
}
