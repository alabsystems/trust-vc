// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Faithful 1:1 TrustVc port of upstream
// `source/rust_verify_test/tests/z3_restart.rs` (Verus pin
// a40d57c73650cd3648b09386bfdb96ab5c270626). The upstream file is explicitly a
// mashup of `nonlinear.rs`, `adts_generics.rs`, `multiset.rs`, and
// `examples/bitvector_basic.rs` (its own comments link the sources), exercised
// under Verus's z3 spinoff/restart scheduling. Every upstream case is
// reproduced here with the verdict upstream expects:
//
//   upstream case              upstream outcome            TrustVc verdict
//   -------------------------  --------------------------  ---------------
//   test_with_bitvec_nlarith   Ok(())                      verified
//   test_box_unbox_struct      Ok(())                      verified   (2 fns)
//   test_with_nlarith          Ok(())                      verified
//   test_with_bv               Ok(())                      verified
//   test1_fails                Err / assert_one_fails      counterexample
//   test2_fails                Err / assert_one_fails      counterexample
//   multiset_basics            Err / assert_one_fails      counterexample (6 fns;
//                                                          the trailing
//                                                          `assert(false)` in
//                                                          sub_add_cancel is the
//                                                          single upstream failure)
//
// Multi-fn upstream cases keep one TrustVc fn per upstream proof/exec fn, all
// carrying the same `upstream_case_id` (the same convention the accepted
// `multiset.rs` port uses).
//
// Surface notes (TrustVc spellings of the Verus constructs):
//   * `proof fn f(..) requires .. ensures ..` is written as attribute contracts
//     (`#[trust_vc::requires(..)]`, `#[trust_vc::ensures(..)]`). Upstream fns
//     with no postcondition carry `#[trust_vc::ensures(true)]` so the body's
//     obligations are still scheduled.
//   * `#[verifier(nonlinear)]` / `#[verifier(bit_vector)]` /
//     `#[verifier(spinoff_prover)]` are the identically-named
//     `#[trust_vc::verifier(..)]` attributes. `spinoff_prover` is a solver
//     SCHEDULING knob with no verdict semantics: TrustVc already discharges each
//     obligation as its own query, so honouring it is verdict-equivalent.
//   * `assert(G) by(nonlinear_arith) requires R { .. }` is
//     `trust_vc::assert_by_nonlinear!(G; requires R; { .. })`;
//     `assert(G) by(bit_vector)` is `trust_vc::assert_by_bit_vector!(G)`.
//   * `P ==> Q` is written `!(P) || (Q)`.
//   * `a =~= b` (extensional eq) is `trust_vc::assert!(trust_vc::ext_eq!(a, b))`;
//     `a === b` is `a == b` (Multiset `==` lowers to Compare::Eq over the count
//     carrier — exactly Verus strict equality); `a !== b` is `a != b`.
//   * Verus builtins `add`/`mul` are the same-named TrustVc truncating builtins.

#![allow(dead_code, unused_variables, unused_mut)]

use trust_vc_types::{int, Multiset};

pub type Z3RestartRsExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const Z3_RESTART_RS_EXPECTED_CASES: &[Z3RestartRsExpectedCase] = &[
    (
        "test_with_bitvec_nlarith",
        "test_with_bitvec_nlarith",
        "verified",
        1,
    ),
    (
        "test_box_unbox_struct_one",
        "test_box_unbox_struct",
        "verified",
        1,
    ),
    (
        "test_box_unbox_struct_two",
        "test_box_unbox_struct",
        "verified",
        1,
    ),
    ("test_with_nlarith", "test_with_nlarith", "verified", 1),
    ("test_with_bv", "test_with_bv", "verified", 1),
    ("test1_fails", "test1_fails", "counterexample", 1),
    ("test2_fails", "test2_fails", "counterexample", 1),
    (
        "multiset_basics_commutative",
        "multiset_basics",
        "verified",
        1,
    ),
    (
        "multiset_basics_associative",
        "multiset_basics",
        "verified",
        1,
    ),
    ("multiset_basics_insert2", "multiset_basics", "verified", 1),
    (
        "multiset_basics_insert2_count",
        "multiset_basics",
        "verified",
        1,
    ),
    (
        "multiset_basics_add_sub_cancel",
        "multiset_basics",
        "verified",
        1,
    ),
    (
        "multiset_basics_sub_add_cancel",
        "multiset_basics",
        "counterexample",
        1,
    ),
];

pub fn z3_restart_rs_expected_cases() -> &'static [Z3RestartRsExpectedCase] {
    Z3_RESTART_RS_EXPECTED_CASES
}

// ─────────────────── test_with_bitvec_nlarith => Ok(()) ──────────────────────
// upstream `proof fn test6(x: u32, y: u32, z: u32) requires x < 0xfff`: a
// nonlinear by-assert with a scoped requires and an empty proof block, the same
// fact re-asserted unscoped, a bit-vector by-assert of the implication, the
// bit-vector fact re-asserted unscoped, and an unscoped nonlinear
// commutativity/associativity by-assert. One fn, exactly as upstream.
//
// ONE DOCUMENTED DEVIATION — statement ORDER. Upstream's last statement is the
// `x * y * z == y * x * z` nonlinear by-assert; here it is hoisted ABOVE the
// bit-vector by-assert. TrustVc cannot currently encode a bit-vector-derived
// general `&` fact as an assumption of a subsequent NONLINEAR-solver query
// ("BitAnd (&) in quantifier body only supports power-of-2 masks"), so upstream's
// literal order hard-errors. The body is straight-line and side-effect-free, so
// the hoist preserves every obligation and only ever REMOVES hypotheses from the
// hoisted one: `x * y * z == y * x * z` is now discharged WITHOUT the bit-vector
// fact in scope (strictly harder — measured VERIFIED standalone), and the
// bit-vector obligations are unchanged (measured: with the hoisted fact in scope,
// asserting the negation `x & y >= 0xfff` is still a COUNTEREXAMPLE, so nothing
// is proved vacuously). No obligation is dropped or weakened.
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn test_with_bitvec_nlarith(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_nonlinear!(
        x * x + x == x * (x + 1u32);
        requires x < 0xfffu32;
        {}
    );
    trust_vc::assert!(x * x + x == x * (x + 1u32));

    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);

    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xfffu32));
    trust_vc::assert!(x & y < 0xfffu32);
}

// ──────────────────── test_box_unbox_struct => Ok(()) ────────────────────────
// upstream `struct Thing<A> { a: A }` plus `proof fn one(v: int)` and
// `fn two(v: Thing<u8>)`: generic-struct box/unbox at `int` and at `u8`.
#[derive(Eq, PartialEq)]
struct Thing<A> {
    a: A,
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(true)]
fn test_box_unbox_struct_one(v: int) {
    let t1 = Thing { a: v };
    let t2 = Thing { a: v };
    let a: int = t2.a;
}

#[trust_vc::ensures(true)]
fn test_box_unbox_struct_two(v: Thing<u8>) {
    trust_vc::assert!(v.a >= 0u8);
}

// ─────────────────────── test_with_nlarith => Ok(()) ─────────────────────────
// upstream `#[verifier(nonlinear)] proof fn lemma_div_pos_is_pos(x: int, d: int)`
// — the same lemma the accepted `nonlinear.rs` port carries as `test4`.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(0 <= x)]
#[trust_vc::requires(0 < d)]
#[trust_vc::ensures(0 <= x / d)]
fn test_with_nlarith(x: int, d: int) {}

// ────────────────────────── test_with_bv => Ok(()) ───────────────────────────
// upstream `#[verifier(bit_vector)] #[verifier(spinoff_prover)] proof fn
// bit_or32_auto()` — five quantified u32 bit-or laws as function-level
// postconditions (upstream's `#[trigger]` annotations are trigger hints with no
// verdict semantics and are not part of the TrustVc surface).
#[trust_vc::verifier(bit_vector)]
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(forall(|a: u32, b: u32| (a | b) == (b | a)))]
#[trust_vc::ensures(forall(|a: u32, b: u32, c: u32| ((a | b) | c) == (a | (b | c))))]
#[trust_vc::ensures(forall(|a: u32| (a | a) == a))]
#[trust_vc::ensures(forall(|a: u32| (a | 0u32) == a))]
#[trust_vc::ensures(forall(|a: u32| (a | 0xffff_ffffu32) == 0xffff_ffffu32))]
fn test_with_bv() {}

// ───────────────── test1_fails => Err / assert_one_fails ─────────────────────
// upstream `#[verifier(spinoff_prover)] proof fn test6(b: u32, b2: u32)`: the
// nonlinear commutativity by-assert and the bit-vector shift/mul by-assert both
// hold; the third assert — the shift-to-int-arithmetic bridge — is upstream's
// single `// FAILS` obligation (`b << 2` truncates, `(b as int) * 4` does not).
//
// Measured: the first two obligations VERIFY on their own (prefix-only control),
// and the third is genuinely FALSE — asserted on its own it returns a
// model-bearing COUNTEREXAMPLE. In the full upstream shape the nonlinear
// by-assert's product fact in the hypothesis set pushes the third obligation's
// query into the known BV<->Int bridge incompleteness, so it comes back as a
// model-less INCOMPLETENESS non-proof rather than a model. That is a
// verification FAILURE with no fabricated model, and it maps to the corpus
// `counterexample` (= upstream `assert_one_fails`) label exactly as
// docs/design-unknown-as-failure.md prescribes — the same mechanism Verus uses
// when Z3 answers `unknown` (Invalid(None, None, None)).
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(true)]
fn test1_fails(b: u32, b2: u32) {
    trust_vc::assert_by_nonlinear!(b * b2 == b2 * b);
    trust_vc::assert_by_bit_vector!(b << 2u32 == mul(b, 4u32));
    trust_vc::assert!(((b << 2u32) as int) == (b as int) * 4); // FAILS
}

// ───────────────── test2_fails => Err / assert_one_fails ─────────────────────
// upstream `#[verifier(nonlinear)] proof fn wrong_lemma_2` — the same lemma the
// accepted `nonlinear.rs` port carries as `test2_fails`.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(x > y)]
#[trust_vc::requires(3 <= z)]
#[trust_vc::ensures(y * z > x)] // FAILS
fn test2_fails(x: int, y: int, z: int) {}

// ─────────────── multiset_basics => Err / assert_one_fails ───────────────────
// upstream's six `#[verifier(spinoff_prover)]` multiset proof fns. The first
// five are the same proofs the accepted `multiset.rs` port carries and they
// verify; `sub_add_cancel` carries upstream's trailing `assert(false) // FAILS`,
// which is the case's single failing obligation.
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(a.add(b) == b.add(a))]
fn multiset_basics_commutative<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b), b.add(a)));
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(a.add(b.add(c)) == a.add(b).add(c))]
fn multiset_basics_associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b.add(c)), a.add(b).add(c)));
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(Multiset::<V>::empty().insert(a).insert(b) == Multiset::<V>::empty().insert(b).insert(a))]
fn multiset_basics_insert2<V>(a: V, b: V) {
    trust_vc::assert!(trust_vc::ext_eq!(
        Multiset::<V>::empty().insert(a).insert(b),
        Multiset::<V>::empty().insert(b).insert(a)
    ));
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(a != b && b != c && c != a)]
#[trust_vc::ensures(true)]
fn multiset_basics_insert2_count<V>(a: V, b: V, c: V) {
    trust_vc::assert!(Multiset::<V>::empty().insert(a).insert(b).count(a) == 1usize);
    trust_vc::assert!(Multiset::<V>::empty().insert(a).insert(b).count(b) == 1usize);
    trust_vc::assert!(Multiset::<V>::empty().insert(a).insert(b).count(c) == 0usize);
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(a.add(b).sub(b) == a)]
fn multiset_basics_add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.add(b).sub(b), a));
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(b.subset_of(a))]
#[trust_vc::ensures(a.sub(b).add(b) == a)]
fn multiset_basics_sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
    trust_vc::assert!(trust_vc::ext_eq!(a.sub(b).add(b), a));
    trust_vc::assert!(false); // FAILS
}
