// Seq methods tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for Seq collection methods.
//!
//! These are ghost types, so tests verify compilation and type-checking.
//! Actual verification happens via ay.

use trust_vc_types::Seq;

#[test]
fn seq_last_compiles() {
    // Use non-empty sequence to satisfy precondition (fixes #83)
    // last() panics at runtime (spec-only ghost method) — verify type compiles
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(3);
    let _ = std::panic::catch_unwind(|| {
        let _: i32 = s.last();
    });
}

#[test]
fn seq_drop_last_compiles() {
    // Use non-empty sequence to satisfy precondition (fixes #83)
    let s: Seq<i32> = Seq::empty().push(1).push(2);
    let _: Seq<i32> = s.drop_last();
}

#[test]
fn seq_subrange_compiles() {
    // Use sequence with 5+ elements to satisfy precondition (fixes #83)
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(3).push(4).push(5);
    let _: Seq<i32> = s.subrange(0, 5);
}

#[test]
fn seq_add_compiles() {
    // add() kept for Verus compatibility
    let s1: Seq<i32> = Seq::empty();
    let s2: Seq<i32> = Seq::empty();
    let _: Seq<i32> = s1.add(s2);
}

#[test]
fn seq_add_operator_compiles() {
    let s1: Seq<i32> = Seq::empty();
    let s2: Seq<i32> = Seq::empty();
    let _: Seq<i32> = s1 + s2;
}

#[test]
#[allow(deprecated)]
fn seq_concat_compiles() {
    // concat() is deprecated — use add() or + operator instead
    let s1: Seq<i32> = Seq::empty();
    let s2: Seq<i32> = Seq::empty();
    let _: Seq<i32> = s1.concat(s2);
}

#[test]
fn seq_first_compiles() {
    // Use non-empty sequence to satisfy precondition (fixes #83)
    // first() panics at runtime (spec-only ghost method) — verify type compiles
    let s: Seq<i32> = Seq::empty().push(1).push(2);
    let _ = std::panic::catch_unwind(|| {
        let _: i32 = s.first();
    });
}

#[test]
fn seq_get_compiles() {
    // get() panics at runtime (spec-only ghost method) — verify type compiles
    let s: Seq<i32> = Seq::empty().push(1);
    let _ = std::panic::catch_unwind(|| {
        let _: i32 = s.get(0);
    });
}

#[test]
fn seq_drop_first_compiles() {
    // Use non-empty sequence to satisfy precondition (fixes #83)
    let s: Seq<i32> = Seq::empty().push(1).push(2);
    let _: Seq<i32> = s.drop_first();
}

#[test]
fn seq_take_compiles() {
    // Use sequence with 3+ elements to satisfy precondition (fixes #83)
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(3);
    let _: Seq<i32> = s.take(3);
}

#[test]
fn seq_skip_compiles() {
    // Use sequence with 3+ elements to satisfy precondition (fixes #83)
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(3);
    let _: Seq<i32> = s.skip(3);
}

#[test]
fn seq_chained_methods_compile() {
    // Verify methods chain correctly (VISION pattern)
    // Use sequences with sufficient elements to satisfy preconditions (fixes #83)
    // last() panics at runtime (spec-only ghost method) — wrap in catch_unwind
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(3).push(4).push(5);
    let _ = std::panic::catch_unwind(|| {
        let _: i32 = s.drop_last().last(); // needs len >= 2
    });
    let _: Seq<i32> = s.take(5).drop_first(); // needs len >= 5, then len >= 1
    let _: Seq<i32> = s.add(s).subrange(0, 10); // add gives 10 elements
}

#[test]
fn seq_generic_types_compile() {
    // Works with various types
    let _s1: Seq<String> = Seq::empty();
    let _s2: Seq<(i32, i32)> = Seq::empty();
    let _s3: Seq<Vec<u8>> = Seq::empty();
}

// ============================================================================
// Map tests
// ============================================================================

use trust_vc_types::{Map, Set};

#[test]
fn map_dom_compiles() {
    let m: Map<i32, String> = Map::empty();
    let _: Set<i32> = m.dom();
}

#[test]
fn map_dom_chained_compiles() {
    let m: Map<i32, String> = Map::empty();
    // Can check if a key is in the domain
    let _: bool = m.dom().contains(42);
}

#[test]
fn map_contains_key_compiles() {
    let m: Map<i32, String> = Map::empty();
    let _: bool = m.contains_key(42);
}

#[test]
fn map_contains_value_compiles() {
    let m: Map<i32, String> = Map::empty();
    let _: bool = m.contains_value("value".to_string());
}

#[test]
fn map_literal_macro_compiles() {
    let _: Map<i32, bool> = trust_vc_types::map![1 => true, 2 => false];
}

#[test]
fn map_remove_compiles() {
    let m: Map<i32, String> = Map::empty();
    let _: Map<i32, String> = m.remove(42);
}

// ============================================================================
// Regression: non-Default types work with element accessors (#2125)
// ============================================================================

use std::num::NonZeroU32;

#[test]
fn seq_index_non_default_type() {
    let s: Seq<NonZeroU32> = Seq::empty().push(NonZeroU32::new(1).unwrap());
    // NonZeroU32 does NOT implement Default — this must compile (#2125)
    let _ = std::panic::catch_unwind(|| s.index(0));
}

#[test]
fn seq_first_non_default_type() {
    let s: Seq<NonZeroU32> = Seq::empty().push(NonZeroU32::new(1).unwrap());
    let _ = std::panic::catch_unwind(|| s.first());
}

#[test]
fn seq_last_non_default_type() {
    let s: Seq<NonZeroU32> = Seq::empty().push(NonZeroU32::new(1).unwrap());
    let _ = std::panic::catch_unwind(|| s.last());
}

#[test]
fn map_get_non_default_value() {
    let m: Map<i32, NonZeroU32> = Map::empty().insert(1, NonZeroU32::new(42).unwrap());
    // V=NonZeroU32 does NOT implement Default — this must compile (#2125)
    let _ = std::panic::catch_unwind(|| m.get(1));
}

// ============================================================================
// Additional Seq tests
// ============================================================================

#[test]
fn seq_contains_compiles() {
    let s: Seq<i32> = Seq::empty();
    let _: bool = s.contains(42);
}

#[test]
fn seq_reverse_compiles() {
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(3);
    let _: Seq<i32> = s.reverse();
}

#[test]
fn seq_no_duplicates_compiles() {
    let s: Seq<i32> = Seq::empty().push(1).push(2);
    let _: bool = s.no_duplicates();
}

#[test]
fn seq_to_set_compiles() {
    let s: Seq<i32> = Seq::empty().push(1).push(2);
    let _: Set<i32> = s.to_set();
}

#[test]
fn seq_to_multiset_compiles() {
    let s: Seq<i32> = Seq::empty().push(1).push(2).push(1);
    let _: trust_vc_types::Multiset<i32> = s.to_multiset();
}

// ============================================================================
// Set tests
// ============================================================================

#[test]
fn set_difference_compiles() {
    let s1: Set<i32> = Set::empty();
    let s2: Set<i32> = Set::empty();
    let _: Set<i32> = s1.difference(s2);
}

#[test]
fn set_contains_compiles() {
    let s: Set<i32> = Set::empty();
    let _: bool = s.contains(42);
}

#[test]
fn set_remove_compiles() {
    let s: Set<i32> = Set::empty();
    let _: Set<i32> = s.remove(42);
}

#[test]
fn set_subset_compiles() {
    let s1: Set<i32> = Set::empty();
    let s2: Set<i32> = Set::empty();
    let _: bool = s1.subset(&s2);
}

#[test]
fn set_superset_compiles() {
    let s1: Set<i32> = Set::empty();
    let s2: Set<i32> = Set::empty();
    let _: bool = s1.superset(&s2);
}
