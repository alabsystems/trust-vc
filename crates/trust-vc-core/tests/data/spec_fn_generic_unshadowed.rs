// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! UNSHADOWED CONTROL for `spec_fn_generic_shadowed_by_struct.rs`: identical
//! apart from the absence of `struct T`. A generic spec fn parameter behaves the
//! same whether or not a same-named struct happens to be in scope, so this file
//! fixes the expected verdict for its shadowed twin.

#[trust_vc::spec]
fn always<T>(x: T) -> bool {
    true
}

#[trust_vc::requires(always(n))]
#[trust_vc::ensures(result == n)]
fn generic_shadowed_by_struct(n: u64) -> u64 {
    n
}
