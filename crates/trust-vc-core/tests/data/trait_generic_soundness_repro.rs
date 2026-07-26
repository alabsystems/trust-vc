// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the trait-side A2-generic adversarial soundness suite: a
// PARAMETERIZED trait (`trait Give<A>`) implemented at a concrete instantiation
// (`impl Give<u64> for S1`) exposes the trait contract to concrete-receiver
// callers through Box-bridged Poly slots. Every TRUE instantiated fact must
// VERIFY; every FALSE fact must NOT verify; every non-instantiable shape
// (blanket impl, method-own generic, nested TypeParam position) must stay
// fail-closed WITHOUT sinking the rest of the file. Verified via
// `verify_function_from_file` in `trait_generic_soundness.rs`.

#![allow(dead_code)]

struct S1 {
    x: u64,
}
struct S2 {
    y: bool,
}
struct S3 {
    z: u64,
}
struct S4 {
    w: u64,
}

#[trust_vc::trait_spec]
trait Give<A> {
    #[trust_vc::ensures(result == a)]
    fn give(&self, a: A) -> A;
}

#[trust_vc::trait_impl]
impl Give<u64> for S1 {
    fn give(&self, a: u64) -> u64 {
        a
    }
}

#[trust_vc::trait_impl]
impl Give<bool> for S2 {
    fn give(&self, a: bool) -> bool {
        a
    }
}

#[trust_vc::trait_spec]
trait Pick<A> {
    #[trust_vc::ensures(true)]
    fn pick(&self) -> A;
}

#[trust_vc::trait_impl]
impl Pick<u64> for S1 {
    fn pick(&self) -> u64 {
        7u64
    }
}

#[trust_vc::trait_impl]
impl Pick<u64> for S2 {
    fn pick(&self) -> u64 {
        9u64
    }
}

#[trust_vc::trait_spec]
trait Give2<A> {
    #[trust_vc::ensures(true)]
    fn g2(&self, a: A) -> bool;
}

// Blanket impl with a TypeParam-bearing trait argument: NOT instantiable; every
// consumer must skip it fail-closed without sinking the file.
#[trust_vc::trait_impl]
impl<C> Give2<(C, u16)> for S3 {
    fn g2(&self, a: (C, u16)) -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait Own<A> {
    #[trust_vc::ensures(true)]
    fn m<B>(&self, x: B) -> bool;
}

#[trust_vc::trait_impl]
impl Own<u64> for S3 {
    fn m<B>(&self, x: B) -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait Nest<A> {
    #[trust_vc::ensures(true)]
    fn f(&self, xs: Seq<A>) -> bool;
}

#[trust_vc::trait_impl]
impl Nest<u64> for S4 {
    fn f(&self, xs: Seq<u64>) -> bool {
        true
    }
}

#[trust_vc::trait_spec]
trait Pair<A, B> {
    #[trust_vc::ensures(result == b)]
    fn second(&self, a: A, b: B) -> B;
}

#[trust_vc::trait_impl]
impl Pair<u64, bool> for S4 {
    fn second(&self, a: u64, b: bool) -> bool {
        b
    }
}

// ---------------------------------------------------------------------------
// POSITIVE: the instantiated trait contract is applied — verifies.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn give_pos(s1: S1) {
    trust_vc::assert!(s1.give(7u64) == 7u64);
}

#[trust_vc::ensures(true)]
fn give_bool_pos(s2: S2) {
    trust_vc::assert!(s2.give(true) == true);
}

#[trust_vc::ensures(true)]
fn second_pos(s4: S4, a: u64, b: bool) {
    trust_vc::assert!(s4.second(a, b) == b);
}

// ---------------------------------------------------------------------------
// NEGATIVE: a FALSE instantiated fact must NOT verify.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn give_neg(s1: S1) {
    trust_vc::assert!(s1.give(7u64) == 8u64);
}

#[trust_vc::ensures(true)]
fn give_bool_neg(s2: S2) {
    trust_vc::assert!(s2.give(true) == false);
}

// Binding-order guard: `second` returns B (bool), never A (u64).
#[trust_vc::ensures(true)]
fn second_neg(s4: S4, a: u64, b: bool) {
    trust_vc::assert!(s4.second(a, b) == !b);
}

// Cross-impl discrimination: S2's `pick` body returns 9 but publishes no value
// through its (trivial) contract; S1's linking axiom (`Box_S1` trigger) must
// not leak into an S2 receiver.
#[trust_vc::ensures(true)]
fn cross_neg(s2: S2) {
    trust_vc::assert!(s2.pick() == 7u64);
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED: non-instantiable shapes never verify — and never sink the file.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn blanket_stays_closed(s3: S3) {
    trust_vc::assert!(s3.g2((1u64, 2u16)) == true);
}

#[trust_vc::ensures(true)]
fn own_generic_stays_closed(s3: S3) {
    trust_vc::assert!(s3.m(1u64) == true);
}

#[trust_vc::ensures(true)]
fn nested_param_stays_closed(s4: S4, xs: Seq<u64>) {
    trust_vc::assert!(s4.f(xs) == true);
}

// File-sink regression pin: with every non-instantiable impl above present in
// THIS file, an unrelated true assertion still verifies (generic-signature
// impls no longer sink the whole file through `register_trait_impl`).
#[trust_vc::ensures(true)]
fn unrelated_true() {
    trust_vc::assert!(1u64 + 1u64 == 2u64);
}
