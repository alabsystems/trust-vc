// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// H10 (macro lane): a `#[trust_vc::spec]` function registers a helper keyed by
// NAME and ARGUMENTS, so a generic parameter no value parameter carries
// collapses every instantiation into one uninterpreted application. That is
// admissible only while the body axiom is published for EVERY use — the body is
// then lowered in the erased environment, where an instantiation-dependent body
// fails to lower and fails the query, so a body that does lower is T-uniform.
//
// MEASURED liar (Verified before this refusal): `rsz::<u8>(0) == rsz::<u64>(0)`
// for the recursive `rsz` below, which every execution refutes 1 != 8.

// Recursive with no `decreases`: the body axiom is SUPPRESSED, so the
// `size_of::<T>()` body is never lowered and never fails.
#[trust_vc::spec]
fn rsz<T>(n: u64) -> u64 {
    if n == 0 {
        core::mem::size_of::<T>() as u64
    } else {
        rsz::<T>(n - 1)
    }
}

// Opaque: the body axiom is gated out of the query.
#[trust_vc::spec]
#[trust_vc::opaque]
fn csz<T>() -> u64 {
    core::mem::size_of::<T>() as u64
}

// CONTROL — NOT refused: the parameter is carried by a value parameter, so the
// argument's own `Box_T` keeps the instantiations apart.
#[trust_vc::spec]
fn carried<T>(x: T) -> u64 {
    0u64
}

// CONTROL — NOT refused: uncarried, but the body axiom is published for every
// use, so the body is lowered (and a `size_of::<T>()` body would fail the query
// there) and the value is T-uniform.
#[trust_vc::spec]
fn uniform<T>() -> u64 {
    7u64
}

fn main() {}
