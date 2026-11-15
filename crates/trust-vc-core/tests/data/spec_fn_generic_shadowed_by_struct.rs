// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! NARROWNESS PIN for the short-name struct param fix.
//!
//! A struct named `T` coexists with a spec fn that declares its OWN generic
//! parameter `T`. Per Rust name resolution the signature's generic shadows the
//! struct inside that signature, so `x: T` denotes the erased poly var and must
//! NOT be pinned to the struct's datatype carrier. Resolving it would
//! monomorphize a polymorphic axiom to one carrier and break every other
//! instantiation — here the `u64` call site.
//!
//! Compare against `spec_fn_generic_unshadowed.rs`, which is byte-identical
//! except that it does not declare `struct T`. Both reach `Verified`; here the
//! type-name rule then refuses it, because a generic is spelled like a type of
//! the file.

pub struct T {
    pub a: u64,
}

#[trust_vc::spec]
fn always<T>(x: T) -> bool {
    true
}

#[trust_vc::requires(always(n))]
#[trust_vc::ensures(result == n)]
fn generic_shadowed_by_struct(n: u64) -> u64 {
    n
}
