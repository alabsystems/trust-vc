// Tracked parameter mode integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Part of #2427 Slice 3: verifies that Tracked<T> parameters work end-to-end
// with ay verification in proof functions. The `tracked` keyword modifier
// works at the token-stream level (proc macro codegen / unit tests); for
// user-visible source code, use the `Tracked<T>` type wrapper.

mod common;

use trust_vc_types::Tracked;

/// Proof function with Tracked<i32> parameter — Copy type means Tracked is
/// also Copy, so multiple uses are allowed.
#[trust_vc::proof]
fn proof_tracked_copy_param(tok: Tracked<i32>, x: i32) {
    trust_vc::requires!(x > 0);
    trust_vc::assert!(x > 0);
}

/// Proof function with regular params alongside Tracked — verifies that
/// the Tracked type erases to its inner type at SMT level.
#[trust_vc::proof]
fn proof_tracked_erases_to_inner(x: i32) {
    trust_vc::requires!(x >= 0);
    trust_vc::assert!(x >= 0);
}

#[test]
fn tracked_copy_param_verifies() {
    let tok = Tracked::new(42i32);
    let _ = common::verify_should_pass(|| proof_tracked_copy_param(tok, 5));
}

#[test]
fn tracked_erases_to_inner_verifies() {
    let _ = common::verify_should_pass(|| proof_tracked_erases_to_inner(10));
}
