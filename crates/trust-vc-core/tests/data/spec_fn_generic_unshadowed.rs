// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! UNSHADOWED CONTROL for `spec_fn_generic_shadowed_by_struct.rs`: identical
//! apart from the absence of `struct T`. It fixes the verdict its shadowed twin
//! reaches before the type-name rule refuses it.

#[trust_vc::spec]
fn always<T>(x: T) -> bool {
    true
}

#[trust_vc::requires(always(n))]
#[trust_vc::ensures(result == n)]
fn generic_shadowed_by_struct(n: u64) -> u64 {
    n
}
