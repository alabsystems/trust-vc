// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the Phase A2-generic adversarial soundness suite: a GENERIC
// inherent method (`impl<A> Base<A> { fn m(self) -> A }`) called on a CONCRETE
// receiver instantiation (`Base::<u64>`) is monomorphized (`A -> u64`) and its
// conformance-checked contract applied at the call site. Every TRUE fact must
// VERIFY; every FALSE fact must NOT verify (a false Verified is a cardinal
// false-verify). Verified via `verify_function_from_file` in
// `a2_generic_soundness.rs`.

#![allow(dead_code)]

struct AWrapper<A> {
    value: A,
}

impl<A> AWrapper<A> {
    #[trust_vc::ensures(result == self.value)]
    fn take(self: AWrapper<A>) -> A {
        self.value
    }

    // Contract is FALSE (result != self.value contradicts the identity body):
    // must Counterexample at its OWN verification, so it is never trusted.
    #[trust_vc::ensures(result != self.value)]
    fn take_bad(self: AWrapper<A>) -> A {
        self.value
    }
}

struct ATwo<A, B> {
    a: A,
    b: B,
}

impl<A, B> ATwo<A, B> {
    #[trust_vc::ensures(result == self.a)]
    fn first(self: ATwo<A, B>) -> A {
        self.a
    }

    #[trust_vc::ensures(result == self.b)]
    fn second(self: ATwo<A, B>) -> B {
        self.b
    }
}

// A method with its OWN generic param stays a separate (fail-closed) axis.
struct AOwnGen<A> {
    value: A,
}

impl<A> AOwnGen<A> {
    #[trust_vc::ensures(true)]
    fn take_extra<B>(self: AOwnGen<A>, other: B) -> A {
        self.value
    }
}

// ---------------------------------------------------------------------------
// POSITIVE: monomorphized contract applied — verifies.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn take_pos(value: u64) {
    let w = AWrapper::<u64> { value };
    trust_vc::assert!(w.take() == value);
}

#[trust_vc::ensures(true)]
fn first_pos(a: u64, b: bool) {
    let t = ATwo::<u64, bool> { a, b };
    trust_vc::assert!(t.first() == a);
}

// Binding ORDER: `second` returns B = bool (not A = u64). A wrong binding order
// would either mis-sort or falsely verify `second_neg`.
#[trust_vc::ensures(true)]
fn second_pos(a: u64, b: bool) {
    let t = ATwo::<u64, bool> { a, b };
    trust_vc::assert!(t.second() == b);
}

// ---------------------------------------------------------------------------
// NEGATIVE: a FALSE post-monomorphization fact must NOT verify.
// ---------------------------------------------------------------------------

#[trust_vc::ensures(true)]
fn take_neg(value: u64) {
    let w = AWrapper::<u64> { value };
    trust_vc::assert!(w.take() == value + 1u64);
}

#[trust_vc::ensures(true)]
fn first_neg(a: u64, b: bool) {
    let t = ATwo::<u64, bool> { a, b };
    trust_vc::assert!(t.first() == a + 1u64);
}

#[trust_vc::ensures(true)]
fn second_neg(a: u64, b: bool) {
    let t = ATwo::<u64, bool> { a, b };
    trust_vc::assert!(t.second() == !b);
}

// Calling the broken-contract method and asserting its (false) ensures must not
// verify — the unsound contract cannot be laundered through monomorphization.
#[trust_vc::ensures(true)]
fn bad_caller_neg(value: u64) {
    let w = AWrapper::<u64> { value };
    trust_vc::assert!(w.take_bad() != value);
}

// A method-level generic (`take_extra<B>`) is out of scope: the call must stay
// fail-closed (never Verified) even though the assertion is trivially true.
#[trust_vc::ensures(true)]
fn own_generic_method_stays_closed(value: u64) {
    let w = AOwnGen::<u64> { value };
    trust_vc::assert!(w.take_extra(7u64) == value);
}

// Registries keyed only by the receiver/method leaf names can select the first
// `value` contract for the second, unrelated wrapper.
mod collision_a {
    pub struct Wrapper<A> {
        pub first: A,
        pub second: A,
    }

    impl<A> Wrapper<A> {
        #[trust_vc::ensures(result == self.first)]
        pub fn pick(self: Wrapper<A>) -> A {
            self.first
        }
    }
}

mod collision_b {
    pub struct Wrapper<A> {
        pub first: A,
        pub second: A,
    }

    impl<A> Wrapper<A> {
        #[trust_vc::ensures(result == self.second)]
        pub fn pick(self: Wrapper<A>) -> A {
            self.second
        }
    }
}

#[trust_vc::ensures(true)]
fn same_leaf_method_names_cannot_cross_contaminate(first: u64) {
    let w = collision_b::Wrapper::<u64> {
        first,
        second: first + 1u64,
    };
    trust_vc::assert!(w.pick() == first);
}

// ---------------------------------------------------------------------------
// POSITIVE CONTROL: two DISTINCT-leaf structs sharing the method name `pick`
// must STILL each monomorphize independently. The collision guard keys on
// (base-leaf, method), so it fails closed ONLY on a true leaf collision
// (`Wrapper::pick` above), never on every shared method name. If the guard
// over-fired, these calls would fail closed and this would NOT verify. (Distinct
// leaves need no module, so their struct literals resolve — unlike the
// same-leaf pair above, which requires modules and is expected to fail closed.)
// ---------------------------------------------------------------------------

struct PickX<A> {
    v: A,
}

impl<A> PickX<A> {
    #[trust_vc::ensures(result == self.v)]
    fn pick(self: PickX<A>) -> A {
        self.v
    }
}

struct PickY<A> {
    v: A,
}

impl<A> PickY<A> {
    #[trust_vc::ensures(result == self.v)]
    fn pick(self: PickY<A>) -> A {
        self.v
    }
}

#[trust_vc::ensures(true)]
fn distinct_leaf_pick_still_monomorphizes(x: u64, y: u64) {
    let a = PickX::<u64> { v: x };
    let b = PickY::<u64> { v: y };
    trust_vc::assert!(a.pick() == x);
    trust_vc::assert!(b.pick() == y);
}

// ---------------------------------------------------------------------------
// RECEIVER-RESOLVABLE same-leaf collision — the probe that actually EXERCISES
// the guard end-to-end. Unlike `collision_a/collision_b` above (whose caller
// builds a module-QUALIFIED `collision_b::Wrapper::<u64>` that the struct-literal
// lowering rejects, masking any registration outcome), here a `shadow::LeafClash`
// impl is declared FIRST (so a naive first-wins registration would make ITS
// `self.b` body own `LeafClash_u64__grab`) and the caller builds the UNQUALIFIED
// top-level `LeafClash`, which DOES lower. Top-level `grab` really returns
// `self.a`; under `a != b`, `w.grab() == b` is FALSE for the top-level type — it
// can only "verify" by laundering the shadow impl's `self.b` body onto the
// top-level receiver's symbol. The collision guard drops BOTH `(LeafClash, grab)`
// registrations, so this MUST fail closed. (Toggling the guard off flips this to
// a Verified false-verify — the proof the guard is load-bearing. No arithmetic,
// so no overflow-check incompleteness can mask the result.)
// ---------------------------------------------------------------------------

mod shadow {
    pub struct LeafClash<A> {
        pub a: A,
        pub b: A,
    }

    impl<A> LeafClash<A> {
        #[trust_vc::ensures(result == self.b)]
        pub fn grab(self: LeafClash<A>) -> A {
            self.b
        }
    }
}

struct LeafClash<A> {
    a: A,
    b: A,
}

impl<A> LeafClash<A> {
    #[trust_vc::ensures(result == self.a)]
    fn grab(self: LeafClash<A>) -> A {
        self.a
    }
}

#[trust_vc::requires(a != b)]
#[trust_vc::ensures(true)]
fn resolvable_same_leaf_cannot_cross_contaminate(a: u64, b: u64) {
    let w = LeafClash::<u64> { a, b };
    trust_vc::assert!(w.grab() == b);
}

// ---------------------------------------------------------------------------
// NESTED generics: a generic struct instantiated at ANOTHER generic type
// (`Outer::<Inner<u64>>`). The monomorphized `get` returns `A = Inner<u64>`, and
// a field read on that result (`got.x`) must resolve — the carrier
// `Outer<Inner<u64>>` and the `A -> Inner<u64>` binding are nested. A wrong
// binding would mis-type the result or falsely verify the negative.
// ---------------------------------------------------------------------------

struct NInner<A> {
    x: A,
}

struct NOuter<A> {
    inner: A,
}

impl<A> NOuter<A> {
    #[trust_vc::ensures(result == self.inner)]
    fn get(self: NOuter<A>) -> A {
        self.inner
    }
}

#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
fn nested_generic_true_fact(n: u64) {
    let i = NInner::<u64> { x: n };
    let o = NOuter::<NInner<u64>> { inner: i };
    let got = o.get();
    trust_vc::assert!(got.x == n);
}

// A FALSE fact through the nested projection must NOT verify (a genuine CE — the
// `n < 100` bound keeps it clear of the `n + 1` overflow-check incompleteness).
#[trust_vc::requires(n < 100u64)]
#[trust_vc::ensures(true)]
fn nested_generic_false_fact(n: u64) {
    let i = NInner::<u64> { x: n };
    let o = NOuter::<NInner<u64>> { inner: i };
    let got = o.get();
    trust_vc::assert!(got.x == 999u64);
}
