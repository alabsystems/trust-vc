// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Soundness + completeness fixtures for STRUCTURAL-DESCENT `#[decreases]` over
// recursive datatypes. A recursive spec fn whose measure is a recursive-datatype
// parameter earns its defining (unfolding) axiom ONLY when the termination gate
// proves the structural child strictly shrinks `dt_size` — derived purely from
// the match-arm constructor equation (`n == Succ(p)`) and the trusted `dt_size`
// acyclicity recurrence. Self-recursion, non-child recursion, and ill-founded
// (no terminating base) recursion must all stay uninterpreted (#50 class).
//
// NOTE (scope): a BRANCHING recursive spec fn (e.g. `tree_size(Node(l, r))` with
// two self-calls) is intentionally NOT exercised here. The structural-descent
// gate correctly ADMITS its axiom, but the downstream ay solver's e-matching
// diverges on a doubly-self-triggering quantified axiom (an orthogonal,
// pre-existing solver-completeness limitation, not a soundness gap). Single
// structural recursion (`Nat`/`List`) is the supported, verified case.

#![allow(dead_code, unused_variables)]

enum Nat {
    Zero,
    Succ(Box<Nat>),
}

enum IntList {
    Nil,
    Cons(i32, Box<IntList>),
}

// ── genuine structural decrease on a match-bound child (must earn its axiom) ──

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn depth(n: Nat) -> nat {
    match n {
        Nat::Zero => 0,
        Nat::Succ(p) => (1 + depth(*p)) as nat,
    }
}

#[trust_vc::spec]
#[trust_vc::decreases(xs)]
fn len(xs: IntList) -> nat {
    match xs {
        IntList::Nil => 0,
        IntList::Cons(_, t) => (1 + len(*t)) as nat,
    }
}

// ── self-recursion on the SAME param (NOT a child): #50 — must stay suppressed ─
// In the `Succ(p)` arm this recurses on `n`, so `size(n) < size(n)` is false and
// the axiom must be suppressed. If emitted, `self_rec(Succ(p)) == 1 + self_rec(Succ(p))`
// is contradictory and ANY goal would verify vacuously.
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn self_rec(n: Nat) -> nat {
    match n {
        Nat::Zero => 0,
        Nat::Succ(p) => (1 + self_rec(n)) as nat,
    }
}

// ── non-child recursion: recurse on an UNRELATED datatype param `m`, not the
// matched child `p`. No arm equation links `size(m)` to `size(n)`, so the
// decrease is unprovable and the axiom must stay suppressed. Recursing on `m`
// (which can be larger) is genuinely non-terminating / contradictory.
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn non_child(n: Nat, m: Nat) -> nat {
    match n {
        Nat::Zero => 0,
        Nat::Succ(p) => (1 + non_child(m, m)) as nat,
    }
}

// ── ill-founded: the base arm itself recurses (no terminating base). The `Zero`
// edge `1 + no_base(n)` does not decrease (`size(n) < size(n)` is false), so the
// axiom must stay suppressed; if emitted, `no_base(Zero) == 1 + no_base(Zero)`
// is contradictory.
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn no_base(n: Nat) -> nat {
    match n {
        Nat::Zero => (1 + no_base(n)) as nat,
        Nat::Succ(p) => (1 + no_base(*p)) as nat,
    }
}

// ══════════════════════ TRUE goals (must Verify) ════════════════════════════

#[trust_vc::ensures(true)]
fn t_depth_zero() {
    trust_vc::assert!(depth(Nat::Zero) == 0);
}

#[trust_vc::ensures(true)]
fn t_depth_one() {
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Zero))) == 1);
}

#[trust_vc::ensures(true)]
fn t_depth_two() {
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Succ(Box::new(Nat::Zero))))) == 2);
}

#[trust_vc::ensures(true)]
fn t_len_zero() {
    trust_vc::assert!(len(IntList::Nil) == 0);
}

#[trust_vc::ensures(true)]
fn t_len_one() {
    trust_vc::assert!(len(IntList::Cons(7, Box::new(IntList::Nil))) == 1);
}

#[trust_vc::ensures(true)]
fn t_len_two() {
    trust_vc::assert!(len(IntList::Cons(7, Box::new(IntList::Cons(8, Box::new(IntList::Nil))))) == 2);
}

// ═══════════════ FALSE goals (must be Counterexample/Unknown, never Verified) ═

#[trust_vc::ensures(true)]
fn f_depth_one_wrong() {
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Zero))) == 2);
}

#[trust_vc::ensures(true)]
fn f_len_one_wrong() {
    trust_vc::assert!(len(IntList::Cons(7, Box::new(IntList::Nil))) == 0);
}

// ═══════════ SELF-RECURSION: must stay uninterpreted (#50 — DECISIVE) ════════

// Reflexivity of an uninterpreted application holds, but a genuine arithmetic
// falsehood must NOT verify through the suppressed axiom.
#[trust_vc::ensures(true)]
fn self_rec_no_false() {
    trust_vc::assert!(self_rec(Nat::Zero) == self_rec(Nat::Zero));
    trust_vc::assert!(0u64 == 1u64);
}

// The base-case fact would follow only from the (suppressed) defining axiom; with
// the axiom suppressed this stays unproven (uninterpreted helper).
#[trust_vc::ensures(true)]
fn self_rec_base_unproven() {
    trust_vc::assert!(self_rec(Nat::Zero) == 0);
}

// ═══════════ NON-CHILD recursion: must stay uninterpreted (suppressed) ═══════

#[trust_vc::ensures(true)]
fn non_child_no_false() {
    trust_vc::assert!(non_child(Nat::Zero, Nat::Zero) == non_child(Nat::Zero, Nat::Zero));
    trust_vc::assert!(0u64 == 1u64);
}

// ═══════════ NO-BASE-CASE recursion: must stay uninterpreted (suppressed) ════

#[trust_vc::ensures(true)]
fn no_base_no_false() {
    trust_vc::assert!(no_base(Nat::Zero) == no_base(Nat::Zero));
    trust_vc::assert!(0u64 == 1u64);
}
