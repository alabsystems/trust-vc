// Opens invariants basic tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for #[trust_vc::opens_invariants(...)] attribute.
//!
//! This attribute specifies which tracked invariants a function may open,
//! enforcing reentrancy restrictions for concurrent verification.
//!
//! Syntax:
//! - `#[trust_vc::opens_invariants(any)]` - Allow any invariant
//! - `#[trust_vc::opens_invariants(none)]` - Allow no invariants
//! - `#[trust_vc::opens_invariants(inv1, inv2)]` - Allow specific invariants
//!
//! Default behavior:
//! - exec functions default to `any` (open any invariant)
//! - proof functions default to `none` (safe by default)

use trust_vc_types::{InvariantPredicate, LocalInvariant};

struct TestPred;
impl InvariantPredicate<(), i32> for TestPred {
    fn inv(_k: (), _v: i32) -> bool {
        true
    }
}

struct Inv1Pred;
impl InvariantPredicate<(), i32> for Inv1Pred {
    fn inv(_k: (), _v: i32) -> bool {
        true
    }
}

struct Inv2Pred;
impl InvariantPredicate<(), i32> for Inv2Pred {
    fn inv(_k: (), _v: i32) -> bool {
        true
    }
}

struct Inv3Pred;
impl InvariantPredicate<(), i32> for Inv3Pred {
    fn inv(_k: (), _v: i32) -> bool {
        true
    }
}

type TestInvariant = LocalInvariant<(), i32, TestPred>;
type Inv1 = LocalInvariant<(), i32, Inv1Pred>;
type Inv2 = LocalInvariant<(), i32, Inv2Pred>;
type Inv3 = LocalInvariant<(), i32, Inv3Pred>;

/// Simple opens_invariants with 'any' mode
#[trust_vc::opens_invariants(any)]
fn opens_any() -> i32 {
    // Can open any tracked invariant
    42
}

/// Simple opens_invariants with 'none' mode
#[trust_vc::opens_invariants(none)]
fn opens_none() -> i32 {
    // Cannot open any tracked invariant - safe for callbacks
    42
}

/// Opens specific named invariant
#[trust_vc::opens_invariants(counter_inv)]
fn opens_single_invariant(counter_inv: &TestInvariant) {
    let _ = counter_inv;
    // Can only open the 'counter_inv' invariant
}

/// Opens multiple named invariants
#[trust_vc::opens_invariants(inv1, inv2)]
fn opens_multiple_invariants(inv1: &Inv1, inv2: &Inv2) {
    let _ = (inv1, inv2);
    // Can open 'inv1' or 'inv2'
}

/// Opens invariants with computation
#[trust_vc::opens_invariants(none)]
fn pure_computation(x: i32) -> i32 {
    // Safe for callbacks - cannot open any invariants
    x + 1
}

/// Opens invariants with requires
#[trust_vc::opens_invariants(data_inv)]
fn guarded_open(data_inv: &TestInvariant, x: i32) -> i32 {
    let _ = data_inv;
    trust_vc::requires!(x >= 0);
    // Can only open 'data_inv'
    x * 2
}

/// Opens invariants combined with returns
#[trust_vc::opens_invariants(state_inv)]
#[trust_vc::returns(result)]
fn opens_with_returns(state_inv: &TestInvariant, x: i32) -> i32 {
    let _ = state_inv;
    trust_vc::requires!(x > 0);
    // Can open 'state_inv', result named for postconditions
    x + x
}

/// Opens invariants with external_body
/// Trust boundary with invariant restrictions
#[trust_vc::opens_invariants(none)]
#[trust_vc::external_body]
fn trusted_pure_fn(x: i32) -> i32 {
    trust_vc::requires!(x >= 0);
    // Body trusted, cannot open invariants
    x
}

/// Generic function with opens_invariants
#[trust_vc::opens_invariants(any)]
fn generic_opens<T: Default>() -> T {
    T::default()
}

/// Opens invariants with complex invariant name
#[trust_vc::opens_invariants(module_state_invariant)]
fn opens_complex_name(module_state_invariant: &TestInvariant) {
    let _ = module_state_invariant;
    // Long invariant names work
}

/// Opens three invariants
#[trust_vc::opens_invariants(inv_a, inv_b, inv_c)]
fn opens_three(inv_a: &Inv1, inv_b: &Inv2, inv_c: &Inv3) {
    let _ = (inv_a, inv_b, inv_c);
    // Can open any of the three
}

/// Opens invariants with mutable reference
#[trust_vc::opens_invariants(data_inv)]
fn opens_with_mut_ref(data_inv: &TestInvariant, x: &mut i32) {
    let _ = data_inv;
    let _current: i32 = *x;
    trust_vc::requires!(_current >= 0);
    *x += 1;
}

/// Opens invariants with slice parameter
#[trust_vc::opens_invariants(buffer_inv)]
fn opens_with_slice(buffer_inv: &TestInvariant, buf: &[u8]) -> usize {
    let _ = buffer_inv;
    trust_vc::requires!(!buf.is_empty());
    buf.len()
}

#[test]
fn opens_any_compiles() {
    assert_eq!(opens_any(), 42);
}

#[test]
fn opens_none_compiles() {
    assert_eq!(opens_none(), 42);
}

#[test]
fn opens_single_invariant_compiles() {
    let _f: fn(&TestInvariant) = opens_single_invariant;
}

#[test]
fn opens_multiple_invariants_compiles() {
    let _f: fn(&Inv1, &Inv2) = opens_multiple_invariants;
}

#[test]
fn pure_computation_compiles() {
    assert_eq!(pure_computation(10), 11);
}

#[test]
fn guarded_open_compiles() {
    let _f: fn(&TestInvariant, i32) -> i32 = guarded_open;
}

#[test]
fn opens_with_returns_compiles() {
    let _f: fn(&TestInvariant, i32) -> i32 = opens_with_returns;
}

#[test]
fn trusted_pure_fn_compiles() {
    assert_eq!(trusted_pure_fn(10), 10);
}

#[test]
fn generic_opens_compiles() {
    let x: i32 = generic_opens();
    assert_eq!(x, 0);
}

#[test]
fn opens_complex_name_compiles() {
    let _f: fn(&TestInvariant) = opens_complex_name;
}

#[test]
fn opens_three_compiles() {
    let _f: fn(&Inv1, &Inv2, &Inv3) = opens_three;
}

#[test]
fn opens_with_mut_ref_compiles() {
    let _f: fn(&TestInvariant, &mut i32) = opens_with_mut_ref;
}

#[test]
fn opens_with_slice_compiles() {
    let _f: fn(&TestInvariant, &[u8]) -> usize = opens_with_slice;
}

#[test]
fn multiple_opens_calls() {
    // Multiple functions with different opens clauses work together
    let a = opens_any();
    let b = opens_none();
    let c = pure_computation(a);
    assert_eq!(a, 42);
    assert_eq!(b, 42);
    assert_eq!(c, 43);
}

#[test]
fn opens_invariants_executes_at_runtime() {
    // Unlike spec/proof/broadcast, opens_invariants preserves the function body.
    // At runtime, the invariant clause has no effect.
    use std::panic::catch_unwind;

    let result = catch_unwind(opens_any);
    assert!(
        result.is_ok(),
        "opens_invariants functions should not panic"
    );
    assert_eq!(result.unwrap(), 42);

    let result = catch_unwind(|| pure_computation(5));
    assert!(
        result.is_ok(),
        "opens_invariants functions should not panic"
    );
    assert_eq!(result.unwrap(), 6);
}

#[test]
fn opens_invariants_not_ghost_code() {
    // opens_invariants is a verification-time constraint, not ghost code.
    // Functions execute normally at runtime.

    let _ = opens_any();
    let _ = opens_none();
    let _ = pure_computation(100);
}
