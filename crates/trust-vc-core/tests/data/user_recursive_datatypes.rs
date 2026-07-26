// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Source fixtures for user-defined self-recursive datatype support + the
// soundness battery that guards it. See `user_recursive_datatypes.rs` (the
// integration test) for the per-function expectations and their rationale.

#![allow(dead_code, unused_variables)]

// ── Peano naturals (self-recursive enum through Box) ────────────────────────
enum Nat {
    Zero,
    Succ(Box<Nat>),
}

// ── cons-list (self-recursive enum carrying a payload) ──────────────────────
enum IntList {
    Nil,
    Cons(i32, Box<IntList>),
}

// ── binary tree (TWO self-recursive children) ───────────────────────────────
enum IntTree {
    Leaf(i32),
    Branch(Box<IntTree>, Box<IntTree>),
}

// ── no-base-case enum: every variant recurses → must stay FAIL-CLOSED ───────
enum Stream {
    More(Box<Stream>),
}

// ── mutual recursion: must stay FAIL-CLOSED (no cross RecursiveRef inlined) ──
enum EvenNat {
    EZero,
    ESucc(Box<OddNat>),
}
enum OddNat {
    OSucc(Box<EvenNat>),
}

// ── negative position (fn(Self) field): must stay FAIL-CLOSED ───────────────
enum NegPos {
    Base,
    Fn(fn(NegPos) -> i32),
}

// ══════════════════════════ spec functions ═════════════════════════════════

// Non-recursive spec fn over the user datatype (no decreases needed; trusted).
#[trust_vc::spec]
fn is_zero(n: Nat) -> bool {
    match n {
        Nat::Zero => true,
        Nat::Succ(_) => false,
    }
}

// Non-recursive spec fn over a payload-carrying user datatype (selector).
#[trust_vc::spec]
fn head_or(xs: IntList, d: i32) -> i32 {
    match xs {
        IntList::Nil => d,
        IntList::Cons(h, _) => h,
    }
}

// Recursive spec fn over the user datatype, WITH a #[decreases] measure.
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn depth(n: Nat) -> nat {
    match n {
        Nat::Zero => 0,
        Nat::Succ(p) => (1 + depth(*p)) as nat,
    }
}

// Recursive spec fn over the user datatype WITHOUT #[decreases]: its defining
// axiom must stay SUPPRESSED (uninterpreted helper, no unsound equation).
#[trust_vc::spec]
fn bad_depth(n: Nat) -> nat {
    match n {
        Nat::Zero => 0,
        Nat::Succ(p) => (1 + bad_depth(*p)) as nat,
    }
}

// Spec fns over the fail-closed datatypes (used only to probe extraction errors).
#[trust_vc::spec]
fn stream_probe(s: Stream) -> bool {
    true
}
#[trust_vc::spec]
fn even_probe(e: EvenNat) -> bool {
    true
}
#[trust_vc::spec]
fn negpos_probe(n: NegPos) -> bool {
    true
}

// Recursive spec fn over the user datatype, used in a true goal. This is a
// KNOWN pre-existing completeness gap (Unknown today) shared with the builtin
// List/Tree recursive-spec-fn-with-#[decreases] path; kept as a witness, not a
// pass/fail assertion.
#[trust_vc::ensures(true)]
fn depth_zero_is_zero() {
    trust_vc::assert!(depth(Nat::Zero) == 0);
}

// Goals that EXERCISE the fail-closed datatypes (each must produce an
// extraction/encoding Error — the param/return type is unsupported).
#[trust_vc::ensures(true)]
fn use_stream(s: Stream) {
    trust_vc::assert!(stream_probe(s));
}
#[trust_vc::ensures(true)]
fn use_even(e: EvenNat) {
    trust_vc::assert!(even_probe(e));
}
#[trust_vc::ensures(true)]
fn use_negpos(n: NegPos) {
    trust_vc::assert!(negpos_probe(n));
}

// ═══════════════════════ TRUE goals (must Verify) ══════════════════════════

#[trust_vc::ensures(true)]
fn t_is_zero_zero() {
    trust_vc::assert!(is_zero(Nat::Zero) == true);
}

#[trust_vc::ensures(true)]
fn t_is_zero_succ() {
    trust_vc::assert!(is_zero(Nat::Succ(Box::new(Nat::Zero))) == false);
}

#[trust_vc::ensures(true)]
fn t_head_or_cons() {
    trust_vc::assert!(head_or(IntList::Cons(5, Box::new(IntList::Nil)), 0) == 5);
}

#[trust_vc::ensures(true)]
fn t_head_or_nil() {
    trust_vc::assert!(head_or(IntList::Nil, 7) == 7);
}

// Disjoint variants: a Succ value is never Zero (native datatype theory).
#[trust_vc::ensures(true)]
fn t_variants_disjoint() {
    trust_vc::assert!(Nat::Succ(Box::new(Nat::Zero)) != Nat::Zero);
}

// Tree constructor/selector smoke: a Branch is never a Leaf.
#[trust_vc::ensures(true)]
fn t_tree_disjoint() {
    trust_vc::assert!(
        IntTree::Branch(Box::new(IntTree::Leaf(1)), Box::new(IntTree::Leaf(2)))
            != IntTree::Leaf(1)
    );
}

// ═══════════════════ FALSE goals (must be Counterexample) ══════════════════

#[trust_vc::ensures(true)]
fn f_is_zero_wrong() {
    trust_vc::assert!(is_zero(Nat::Zero) == false);
}

#[trust_vc::ensures(true)]
fn f_head_or_wrong() {
    trust_vc::assert!(head_or(IntList::Cons(5, Box::new(IntList::Nil)), 0) == 6);
}

#[trust_vc::ensures(true)]
fn f_variants_equal() {
    trust_vc::assert!(Nat::Succ(Box::new(Nat::Zero)) == Nat::Zero);
}

// Acyclicity (positive dt_size witness): no Nat equals its own successor.
// This is VALID (UNSAT of `n == Succ(n)` via dt_size), so it must Verify.
#[trust_vc::ensures(true)]
fn t_acyclic(n: Nat) {
    trust_vc::assert!(n != Nat::Succ(Box::new(n)));
}

// ══════════════ CYCLIC claim (must NOT be Verified — acyclicity) ════════════
// `n == Succ(n)` holds for NO Nat (dt_size: size(n) == 1 + size(n) ⇒ 0 == 1).
// Asserting the cyclic structure must be REFUTED (Counterexample), never proved.
#[trust_vc::ensures(true)]
fn c_assert_cycle(n: Nat) {
    trust_vc::assert!(n == Nat::Succ(Box::new(n)));
}

// The dangerous direction: assume a cyclic structure, then try to prove a
// concrete arithmetic falsehood about an unrelated value. The engine must NOT
// build a cyclic model and use it to prove `0 == 1` for real values.
#[trust_vc::ensures(true)]
fn c_cycle_assume_then_false(n: Nat) {
    trust_vc::assume!(n == Nat::Succ(Box::new(n)));
    trust_vc::assert!(0u64 == 1u64);
}

// ════════ ill-founded recursion: NO unsound axiom (must NOT prove false) ════
// bad_depth has no #[decreases]; its defining axiom is suppressed. Reflexivity
// of an uninterpreted application holds, but a genuinely false arithmetic goal
// must still fail (no vacuous proof of `false`).
#[trust_vc::ensures(true)]
fn g_bad_depth_no_false() {
    trust_vc::assert!(bad_depth(Nat::Zero) == bad_depth(Nat::Zero));
    trust_vc::assert!(0u64 == 1u64);
}
