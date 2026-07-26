// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration test for `old!()` inside `#[trust_vc::contract]` ensures clauses.
//!
//! Regression test for #2455: the test-path expansion of
//! `#[trust_vc::contract(ensures(ret == old!(x) + 1), returns(ret))]`
//! panicked at `obligation_collection.rs` with "old!() variable must be
//! declared before use" because contract functions don't declare parameters
//! in the verification context (unlike `#[proof]` functions).
//!
//! The fix emits `collect_variable_runtime` before `collect_old_value` in
//! the test-path old registrations so the parameter type is available.
//!
//! VERIFICATION LEVEL: RUNTIME
//! Tests exercise the contract macro expansion in test mode.

/// Simple increment function with old!() in ensures.
///
/// Before #2455 fix, calling this function in test mode panicked during
/// obligation collection because `x` was not declared in the verification
/// context when `collect_old_value("x")` tried to look it up.
#[trust_vc::contract(
    requires(x < u32::MAX),
    ensures(ret == old!(x) + 1),
    returns(ret),
)]
fn increment(x: u32) -> u32 {
    x + 1
}

/// Contract with old!() on multiple Copy parameters.
#[trust_vc::contract(
    ensures(ret == old!(a) + old!(b)),
    returns(ret),
)]
fn add(a: u32, b: u32) -> u32 {
    a + b
}

#[test]
fn test_contract_old_in_ensures_does_not_panic() {
    // Before the fix, this call panicked with:
    // "invariant: old!() variable must be declared before use (#1669)"
    let result = increment(5);
    assert_eq!(result, 6);
}

#[test]
fn test_contract_old_multiple_captures() {
    let result = add(3, 4);
    assert_eq!(result, 7);
}
