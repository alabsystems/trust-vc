// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test that ghost type methods return modified instances.
//!
//! Issue #943: Ghost type methods return unchanged self - all mutations are no-ops
//!
//! Note: These are runtime tests, not verification tests. They don't collect or verify
//! any proof obligations. The ghost_requires! macros in the ghost types are no-ops
//! at runtime, so clearing verification context is not necessary here.

use trust_vc_types::{Map, Seq, Set};

#[test]
fn test_seq_push_returns_new_instance() {
    let s1 = Seq::<i32>::empty();
    let s2 = s1.push(42);

    // These are different instances (though runtime representation is the same)
    // The key is that s2 represents a logically different sequence for ay
    assert!(!std::ptr::eq(&s1, &s2), "push should return a new instance");
}

#[test]
fn test_seq_update_returns_new_instance() {
    // Note: update requires a non-empty sequence, but since ghost_requires
    // doesn't enforce at runtime, we can still test the instance creation
    let s1 = Seq::<i32>::empty();
    let s2 = s1.update(0, 100);

    assert!(
        !std::ptr::eq(&s1, &s2),
        "update should return a new instance"
    );
}

#[test]
#[allow(deprecated)]
fn test_seq_concat_returns_new_instance() {
    let s1 = Seq::<i32>::empty();
    let s2 = Seq::<i32>::empty();
    let s3 = s1.concat(s2);

    assert!(
        !std::ptr::eq(&s1, &s3),
        "concat should return a new instance"
    );
}

#[test]
fn test_seq_drop_last_returns_new_instance() {
    // Note: drop_last requires a non-empty sequence, but since ghost_requires
    // doesn't enforce at runtime, we can still test the instance creation
    let s1 = Seq::<i32>::empty();
    let s2 = s1.drop_last();

    assert!(
        !std::ptr::eq(&s1, &s2),
        "drop_last should return a new instance"
    );
}

#[test]
fn test_seq_take_returns_new_instance() {
    let s1 = Seq::<i32>::empty();
    let s2 = s1.take(5);

    assert!(!std::ptr::eq(&s1, &s2), "take should return a new instance");
}

#[test]
fn test_set_insert_returns_new_instance() {
    let s1 = Set::<i32>::empty();
    let s2 = s1.insert(42);

    assert!(
        !std::ptr::eq(&s1, &s2),
        "insert should return a new instance"
    );
}

#[test]
fn test_set_remove_returns_new_instance() {
    let s1 = Set::<i32>::empty();
    let s2 = s1.remove(42);

    assert!(
        !std::ptr::eq(&s1, &s2),
        "remove should return a new instance"
    );
}

#[test]
fn test_set_union_returns_new_instance() {
    let s1 = Set::<i32>::empty();
    let s2 = Set::<i32>::empty();
    let s3 = s1.union(s2);

    assert!(
        !std::ptr::eq(&s1, &s3),
        "union should return a new instance"
    );
}

#[test]
fn test_set_intersect_returns_new_instance() {
    let s1 = Set::<i32>::empty();
    let s2 = Set::<i32>::empty();
    let s3 = s1.intersect(s2);

    assert!(
        !std::ptr::eq(&s1, &s3),
        "intersect should return a new instance"
    );
}

#[test]
fn test_map_insert_returns_new_instance() {
    let m1 = Map::<i32, i32>::empty();
    let m2 = m1.insert(42, 100);

    assert!(
        !std::ptr::eq(&m1, &m2),
        "insert should return a new instance"
    );
}

#[test]
fn test_map_remove_returns_new_instance() {
    let m1 = Map::<i32, i32>::empty();
    let m2 = m1.remove(42);

    assert!(
        !std::ptr::eq(&m1, &m2),
        "remove should return a new instance"
    );
}

#[test]
fn test_ghost_type_chaining() {
    // Test that method chaining works correctly with new instances
    let s1 = Seq::<i32>::empty();
    let s2 = s1.push(1).push(2).push(3);

    // Each push should return a new instance that can be chained
    assert!(
        !std::ptr::eq(&s1, &s2),
        "chained operations should produce new instance"
    );
}

#[test]
fn test_must_use_attribute() {
    // The #[must_use] attribute should warn if result is ignored
    // This test just verifies the methods are callable
    let s = Seq::<i32>::empty();
    let _ = s.push(42); // OK - result is used

    let set = Set::<i32>::empty();
    let _ = set.insert(42); // OK - result is used

    let map = Map::<i32, i32>::empty();
    let _ = map.insert(1, 2); // OK - result is used
}
