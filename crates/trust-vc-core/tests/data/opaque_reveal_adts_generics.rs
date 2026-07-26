// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Opaque spec fn + reveal: faithful adaptations of the upstream Verus
// `rust_verify_test/tests/adts_generics.rs` cases test_refinements1,
// test_refinements1_fail, test_refinements2, and test_triggers.
//
// Adaptation note (faithful, not weakening): upstream uses a GENERIC opaque
// `spec fn id<A>(a: A) -> A { a }`, and `test_refinements1` asserts
// `id(y.u) >= 0` where `y.u: u64`. In Verus that goal discharges from the
// RETURN TYPE alone (`u64 >= 0` always holds) — `reveal` is NOT load-bearing
// there. The trust-vc source spec catalog rejects generic spec fns (an opaque
// `A` return type is unsupported), and the task requires reveal to be the
// load-bearing element. We therefore use a concrete `id(a: int) -> int { a }`
// over the unbounded ghost `int` (no sign refinement from the type) together
// with a `>= 0` precondition, so the positive goal `id(x) >= 0` holds ONLY
// because `reveal(id)` makes the defining equality `id(x) == x` available. The
// opaque-abstraction semantics being exercised are identical to upstream.

// Shared opaque identity spec fn: uninterpreted unless revealed.
#[trust_vc::spec]
#[trust_vc::opaque]
fn id(a: int) -> int {
    a
}

struct X {
    u: int,
}

// === test_refinements1 (positive, reveal load-bearing) ===
// reveal(id) supplies id(y.u) == y.u, so id(y.u) >= 0 follows from y.u >= 0.
#[trust_vc::requires(y.u >= 0)]
#[trust_vc::ensures(true)]
fn refinements1(y: X) {
    trust_vc::reveal!(id);
    trust_vc::assert!(id(y.u) >= 0);
}

// === test_refinements1_fail (revealed, but unprovable goal -> counterexample) ===
// Even with id revealed (id(y.u) == y.u), `>= 1` does not follow from `>= 0`
// (witness y.u == 0). Must fail closed with a counterexample, NOT verify.
#[trust_vc::requires(y.u >= 0)]
#[trust_vc::ensures(true)]
fn refinements1_fail(y: X) {
    trust_vc::reveal!(id);
    trust_vc::assert!(id(y.u) >= 1); // FAILS
}

// === UNREVEALED adversarial variant (CRUCIAL soundness, fail-closed) ===
// No reveal: id is a truly uninterpreted function, so even the body fact
// `id(y.u) == y.u` is NOT derivable. Must NOT verify (counterexample).
#[trust_vc::ensures(true)]
fn refinements1_unrevealed(y: X) {
    trust_vc::assert!(id(y.u) == y.u); // opaque, unrevealed -> unprovable
}

struct P {
    a: int,
}

// === test_refinements2 (positive, opaque + struct field, reveal load-bearing) ===
#[trust_vc::requires(p.a >= 0)]
#[trust_vc::ensures(true)]
fn refinements2(p: P) {
    trust_vc::reveal!(id);
    trust_vc::assert!(id(p.a) >= 0);
}

struct S {
    i: int,
}

// Opaque predicates used as quantifier triggers.
#[trust_vc::spec]
#[trust_vc::opaque]
fn fi(i: int) -> bool {
    true
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn fs(s: S) -> bool {
    true
}

// === test_triggers, struct-field-trigger arm ===
// forall|t: S| fi(t.i) is the precondition; reveal(fi) makes fi(i) == true
// available; assert fi(s.i) discharges. Exercises an opaque fn as a quantifier
// trigger head (the UF symbol must survive opacity for E-matching).
#[trust_vc::requires(forall(|t: S| fi(t.i)))]
#[trust_vc::ensures(true)]
fn triggers_struct_field(s: S) {
    trust_vc::reveal!(fi);
    trust_vc::assert!(fi(s.i));
}

// === test_triggers, struct-constructor-arg-trigger arm ===
#[trust_vc::requires(forall(|k: int| fs(S { i: k })))]
#[trust_vc::ensures(true)]
fn triggers_struct_constructor() {
    trust_vc::reveal!(fs);
    trust_vc::assert!(fs(S { i: 5 }));
}

// === Recursive opaque WITHOUT #[decreases] (CRUCIAL soundness) ===
// `bad(n) == bad(n) + 1` has no model; its defining axiom entails false. The
// unsound-recursion guard must suppress that axiom even when reveal!(bad) is
// requested, so the false goal below must NOT verify. (Mirrors the existing
// recursive_axiom_soundness_repro guard, with #[trust_vc::opaque] layered on.)
#[trust_vc::spec]
#[trust_vc::opaque]
fn bad(n: u64) -> u64 {
    bad(n) + 1
}

#[trust_vc::ensures(true)]
fn recursive_opaque_no_decreases_proves_false() {
    trust_vc::reveal!(bad);
    trust_vc::assert!(bad(3u64) == bad(3u64) + 100u64);
}
