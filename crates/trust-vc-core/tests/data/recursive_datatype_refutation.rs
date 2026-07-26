// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the CONCRETE recursive-datatype REFUTATION recovery (the
// completeness dual of the compute-mode `Some(true)` upgrade): a WRONG closed
// ground claim over a recursive datatype (or a non-recursive selector) is
// synthesized into a `Counterexample` instead of `Unknown(Incompleteness)`,
// GATED to a bare closed/ground goal with no constraining hypotheses.
//
// This is FIRST a soundness battery (the critical risk is a FALSE counterexample
// on a TRUE claim):
//   * WRONG concrete recursive / selector claims  -> Counterexample;
//   * TRUE concrete claims                         -> still Verified (no false cex);
//   * claims under a constraining / vacuous hypothesis -> NOT falsely cex'd (gated);
//   * SUPPRESSED / ill-founded recursive fns       -> Unknown (no fabricated cex);
//   * SYMBOLIC-parameter claims                    -> Unknown (no fabricated cex).

#![allow(dead_code, unused_variables)]

enum Nat {
    Zero,
    Succ(Box<Nat>),
}

enum IntList {
    Nil,
    Cons(i32, Box<IntList>),
}

// Non-recursive selector (trusted body axiom, no decreases needed).
#[trust_vc::spec]
fn is_zero(n: Nat) -> bool {
    match n {
        Nat::Zero => true,
        Nat::Succ(_) => false,
    }
}

// Recursive spec fns WITH a valid structural #[decreases] (axiom emitted).
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

// Recursive spec fn WITHOUT #[decreases]: axiom SUPPRESSED (uninterpreted helper,
// absent from the compute body catalog).
#[trust_vc::spec]
fn bad_depth(n: Nat) -> nat {
    match n {
        Nat::Zero => 0,
        Nat::Succ(p) => (1 + bad_depth(*p)) as nat,
    }
}

// ═══════════ WRONG concrete recursive claim -> Counterexample ════════════════

// depth(Succ(Zero)) is 1, claim 2.
#[trust_vc::ensures(true)]
fn wrong_depth_one() {
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Zero))) == 2);
}

// depth(Succ(Succ(Zero))) is 2, claim 5 (needs the unfolding axiom twice).
#[trust_vc::ensures(true)]
fn wrong_depth_two() {
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Succ(Box::new(Nat::Zero))))) == 5);
}

// len(Cons(7, Nil)) is 1, claim 0.
#[trust_vc::ensures(true)]
fn wrong_len_one() {
    trust_vc::assert!(len(IntList::Cons(7, Box::new(IntList::Nil))) == 0);
}

// ═══════ WRONG concrete NON-recursive selector claim -> Counterexample ═══════

// is_zero(Zero) is true, claim false.
#[trust_vc::ensures(true)]
fn wrong_is_zero() {
    trust_vc::assert!(is_zero(Nat::Zero) == false);
}

// ═════════════════ TRUE concrete claim -> still Verified ═════════════════════

#[trust_vc::ensures(true)]
fn true_depth_one() {
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Zero))) == 1);
}

#[trust_vc::ensures(true)]
fn true_len_one() {
    trust_vc::assert!(len(IntList::Cons(7, Box::new(IntList::Nil))) == 1);
}

#[trust_vc::ensures(true)]
fn true_is_zero() {
    trust_vc::assert!(is_zero(Nat::Zero) == true);
}

// ════ UNDER-HYPOTHESES: must NOT be falsely Counterexampled (gated out) ══════

// Vacuous risk: the cyclic assumption `n == Succ(n)` is contradictory (dt_size
// acyclicity), so the goal is VACUOUSLY true. A naive ground compute of the goal
// would say `false`; the gate (any hypothesis present) MUST block the cex so we
// never manufacture a counterexample for a vacuously-true goal.
#[trust_vc::ensures(true)]
fn cex_blocked_under_cyclic_hyp(n: Nat) {
    trust_vc::assume!(n == Nat::Succ(Box::new(n)));
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Zero))) == 2);
}

// Constraining (non-equality) hypothesis present: even though the ground goal is
// genuinely false, the gate conservatively withholds the cex shortcut whenever
// any hypothesis is in scope (the bare-assert gate). Must stay non-Counterexample.
#[trust_vc::ensures(true)]
fn cex_blocked_under_benign_hyp() {
    trust_vc::assume!(is_zero(Nat::Zero) == true);
    trust_vc::assert!(depth(Nat::Succ(Box::new(Nat::Zero))) == 2);
}

// TRUE claim under an equality hypothesis: routes through the `Some(true)` upgrade
// (binding n -> Zero, depth(Zero) == 0), stays Verified — never a counterexample.
#[trust_vc::ensures(true)]
fn true_under_binding_hyp(n: Nat) {
    trust_vc::assume!(n == Nat::Zero);
    trust_vc::assert!(depth(n) == 0);
}

// ═══ SUPPRESSED / ill-founded recursive fn: Unknown (no fabricated cex) ══════

// bad_depth has no #[decreases]; its body is absent from the compute catalog, so
// the evaluator returns None and the gate never fires. The claim happens to be
// TRUE (bad_depth(Succ(Zero)) == 1) but must stay Unknown (uninterpreted helper),
// never a false Verified.
#[trust_vc::ensures(true)]
fn suppressed_bad_depth_true() {
    trust_vc::assert!(bad_depth(Nat::Succ(Box::new(Nat::Zero))) == 1);
}

// A FALSE claim through the suppressed fn must ALSO stay Unknown — never a
// fabricated counterexample (the body is absent from the compute catalog).
#[trust_vc::ensures(true)]
fn suppressed_bad_depth_wrong() {
    trust_vc::assert!(bad_depth(Nat::Succ(Box::new(Nat::Zero))) == 9);
}

// ═══════════ SYMBOLIC parameter: Unknown (no fabricated cex) ═════════════════

// `n` is symbolic; depth(n) cannot be matched (eval_match -> None), compute -> None,
// the gate never fires. A genuinely-false-for-most-n bare assert stays Unknown.
#[trust_vc::ensures(true)]
fn symbolic_param_assert(n: Nat) {
    trust_vc::assert!(depth(n) == 99);
}

// Symbolic-parameter FALSE postcondition: stays Unknown, never a fabricated cex.
#[trust_vc::ensures(depth(n) == 99)]
fn symbolic_param_postcond(n: Nat) -> Nat {
    n
}
