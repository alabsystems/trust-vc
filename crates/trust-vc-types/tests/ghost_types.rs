// Ghost and Snapshot types tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for Ghost<T> and Snapshot<T> wrapper types.
//!
//! These are ghost types, so tests verify compilation, type-checking,
//! and runtime behavior (panics). Actual verification happens via ay.

use trust_vc_types::{Ghost, Snapshot};

// ============================================================================
// Ghost<T> tests
// ============================================================================

#[test]
fn ghost_is_zero_sized() {
    assert_eq!(std::mem::size_of::<Ghost<i32>>(), 0);
    assert_eq!(std::mem::size_of::<Ghost<Vec<i32>>>(), 0);
    assert_eq!(std::mem::size_of::<Ghost<String>>(), 0);
}

#[test]
fn ghost_creation() {
    let x = 42;
    let _ghost = Ghost::new(x);
    // x is consumed, ghost is zero-sized
}

#[test]
fn ghost_copy() {
    let ghost1: Ghost<i32> = Ghost::new(42);
    let ghost2 = ghost1; // Copy
    let ghost3 = ghost1; // Still valid because Copy
    let _ = (ghost2, ghost3);
}

#[test]
fn ghost_copy_even_when_t_is_not_copy() {
    // Ghost<T> is always Copy because it contains PhantomData, not T
    // This is important: Vec<i32> is NOT Copy, but Ghost<Vec<i32>> IS Copy
    let ghost1: Ghost<Vec<i32>> = Ghost::new(vec![1, 2, 3]);
    let ghost2 = ghost1; // Copy works
    let ghost3 = ghost1; // Still valid - Ghost is Copy regardless of T
    let _ = (ghost2, ghost3);
}

#[test]
fn ghost_default() {
    let ghost: Ghost<i32> = Ghost::default();
    let _ = ghost;
}

#[test]
fn ghost_debug() {
    let ghost: Ghost<i32> = Ghost::new(42);
    let s = format!("{:?}", ghost);
    assert!(s.contains("Ghost"));
}

#[test]
#[should_panic(expected = "Ghost::inner called at runtime")]
fn ghost_inner_panics() {
    let ghost: Ghost<i32> = Ghost::new(42);
    let _ = ghost.inner();
}

#[test]
#[should_panic(expected = "Ghost::inner_mut called at runtime")]
fn ghost_inner_mut_panics() {
    let mut ghost: Ghost<i32> = Ghost::new(42);
    let _ = ghost.inner_mut();
}

// ============================================================================
// Snapshot<T> tests
// ============================================================================

#[test]
fn snapshot_is_zero_sized() {
    assert_eq!(std::mem::size_of::<Snapshot<i32>>(), 0);
    assert_eq!(std::mem::size_of::<Snapshot<Vec<i32>>>(), 0);
    assert_eq!(std::mem::size_of::<Snapshot<String>>(), 0);
}

#[test]
fn snapshot_capture_does_not_consume() {
    let x = 42;
    let _snap = Snapshot::capture(&x);
    // x is NOT consumed - only a reference is taken
    assert_eq!(x, 42);
}

#[test]
fn snapshot_always_copy() {
    // Snapshot<T> is always Copy, even when T is not
    let v = vec![1, 2, 3];
    let snap1 = Snapshot::capture(&v);
    let snap2 = snap1; // Copy
    let snap3 = snap1; // Still valid - Snapshot is Copy
    let _ = (snap2, snap3);
    // v is still valid
    assert_eq!(v.len(), 3);
}

#[test]
#[allow(clippy::clone_on_copy)] // Intentionally testing Clone impl
fn snapshot_clone() {
    let x = 42;
    let snap1 = Snapshot::capture(&x);
    let snap2 = snap1.clone();
    let _ = (snap1, snap2);
}

#[test]
fn snapshot_debug() {
    let x = 42;
    let snap = Snapshot::capture(&x);
    let s = format!("{:?}", snap);
    assert!(s.contains("Snapshot"));
}

#[test]
#[should_panic(expected = "Snapshot::inner called at runtime")]
fn snapshot_inner_panics() {
    let x = 42;
    let snap = Snapshot::capture(&x);
    let _ = snap.inner();
}

// ============================================================================
// Usage patterns
// ============================================================================

#[test]
fn ghost_with_various_types() {
    // Works with various types
    let _g1: Ghost<i32> = Ghost::new(42);
    let _g2: Ghost<String> = Ghost::new(String::from("hello"));
    let _g3: Ghost<(i32, i32)> = Ghost::new((1, 2));
    let _g4: Ghost<Vec<u8>> = Ghost::new(vec![1, 2, 3]);
}

#[test]
fn snapshot_with_various_types() {
    let i = 42i32;
    let s = String::from("hello");
    let t = (1, 2);
    let v = vec![1u8, 2, 3];

    let _s1 = Snapshot::capture(&i);
    let _s2 = Snapshot::capture(&s);
    let _s3 = Snapshot::capture(&t);
    let _s4 = Snapshot::capture(&v);
}

#[test]
fn ghost_in_struct() {
    // Ghost can be used in structs
    #[allow(dead_code)]
    struct ProofState {
        counter: Ghost<usize>,
    }

    let _state = ProofState {
        counter: Ghost::new(0),
    };
}

#[test]
fn snapshot_in_function() {
    // Snapshot pattern: capture value before mutation
    fn modify_vec(v: &mut Vec<i32>) -> usize {
        let _original_len = Snapshot::capture(&v.len());
        v.push(42);
        v.len()
    }

    let mut v = vec![1, 2, 3];
    let new_len = modify_vec(&mut v);
    assert_eq!(new_len, 4);
}
