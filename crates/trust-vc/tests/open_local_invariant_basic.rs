// open_local_invariant integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration coverage for `open_local_invariant!` symbolic lowering.
//!
//! Part of #2427.

mod common;

use trust_vc_types::{InvariantPredicate, LocalInvariant};

struct TestPred;

impl InvariantPredicate<(), i32> for TestPred {
    fn inv(_k: (), _v: i32) -> bool {
        true
    }
}

type TestInvariant = LocalInvariant<(), i32, TestPred>;

fn test_invariant_handle() -> TestInvariant {
    // SAFETY: `LocalInvariant` is a zero-sized marker type (`PhantomData` only),
    // so creating a zeroed value does not materialize invalid runtime state.
    unsafe { std::mem::MaybeUninit::<TestInvariant>::zeroed().assume_init() }
}

#[trust_vc::opens_invariants(any)]
fn open_local_invariant_noop(inv: &TestInvariant) {
    trust_vc::open_local_invariant!(&inv => inner => {
        trust_vc::assert!(*inner == *inner);
    });
}

#[trust_vc::opens_invariants(any)]
fn open_local_invariant_identity_assign(inv: &TestInvariant) {
    trust_vc::open_local_invariant!(&inv => inner => {
        *inner = *inner;
        trust_vc::assert!(*inner == *inner);
    });
}

#[trust_vc::opens_invariants(any)]
fn open_local_invariant_fresh_value(inv: &TestInvariant) {
    trust_vc::open_local_invariant!(&inv => inner => {
        *inner = 0i32;
    });
}

#[trust_vc::opens_invariants(none)]
fn open_local_invariant_blocked(inv: &TestInvariant) {
    trust_vc::open_local_invariant!(&inv => inner => {
        trust_vc::assert!(*inner == *inner);
    });
}

#[test]
fn open_local_invariant_noop_verifies() {
    let inv = test_invariant_handle();
    let _ = common::verify_should_pass(|| open_local_invariant_noop(&inv));
}

#[test]
fn open_local_invariant_identity_assign_verifies() {
    let inv = test_invariant_handle();
    let _ = common::verify_should_pass(|| open_local_invariant_identity_assign(&inv));
}

#[test]
fn open_local_invariant_fresh_value_fails() {
    let inv = test_invariant_handle();
    let _ = common::verify_should_fail(|| open_local_invariant_fresh_value(&inv));
}

#[test]
fn open_local_invariant_respects_mask() {
    let inv = test_invariant_handle();
    let _ = common::verify_should_fail(|| open_local_invariant_blocked(&inv));
}
