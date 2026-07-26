// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the CROSS-OPERATOR datatype-disequality (`!=`) soundness fix.
//
// ay's native datatype theory case-splits constructors only at solver
// scope-depth 0, but every obligation is discharged inside a `push` scope. For a
// datatype DISEQUALITY goal `a != b` (lowered as `not(eq(a, b))`), the verifier
// asserts the negation `eq(a, b)` and checks UNSAT; with the constructor
// case-split unavailable at depth 1, ay declares `eq(a, b)` UNSOUNDLY UNSAT for a
// datatype-VALUED spec-fn-result operand, returning a DIRECT (wrong) `Verified` —
// even for the tautologically-false `a != a`. The `==` direction was unaffected
// (its negated goal `not(eq)` stays Unknown(Incompleteness) and routes to the
// compute refutation recovery). The fix re-validates a CLOSED/GROUND datatype
// (dis)equality goal that the SMT reported `Verified` against the concrete
// evaluator; a `false` evaluation demotes the unsound `Verified` to a
// Counterexample (gated to a bare goal with no constraining hypotheses).
//
// Soundness battery (the critical risk is over-rejecting a TRUE `!=`):
//   * FALSE `!=` (closed/ground)          -> Counterexample (was a false Verified);
//   * TRUE  `!=` (closed/ground)          -> still Verified (no over-rejection);
//   * TRUE/FALSE `==` (closed/ground)     -> verdicts unchanged;
//   * TRUE `!=` under a constraining hyp  -> still Verified (gate withholds the override);
//   * SYMBOLIC `!=`                        -> not falsely refuted.

#![allow(dead_code, unused_variables)]

enum Nat {
    Zero,
    Succ(Box<Nat>),
}

// Datatype-VALUED recursive spec fn (Peano doubling): dbl(Succ(Zero)) == Succ(Succ(Zero)).
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn dbl(n: Nat) -> Nat {
    match n {
        Nat::Zero => Nat::Zero,
        Nat::Succ(p) => Nat::Succ(Box::new(Nat::Succ(Box::new(dbl(*p))))),
    }
}

// Datatype-VALUED identity spec fn.
#[trust_vc::spec]
fn idn(n: Nat) -> Nat {
    n
}

// ════════════ FALSE `!=` goals -> Counterexample ════════════

// dbl(Succ(Zero)) == Succ(Succ(Zero)); the `!=` is FALSE.
#[trust_vc::ensures(true)]
fn f_dbl_one_neq() {
    trust_vc::assert!(
        dbl(Nat::Succ(Box::new(Nat::Zero)))
            != Nat::Succ(Box::new(Nat::Succ(Box::new(Nat::Zero))))
    );
}

// `x != x` over a datatype-valued spec-fn result: TAUTOLOGICALLY FALSE.
#[trust_vc::ensures(true)]
fn f_self_neq() {
    trust_vc::assert!(
        dbl(Nat::Succ(Box::new(Nat::Zero))) != dbl(Nat::Succ(Box::new(Nat::Zero)))
    );
}

// idn is identity, so idn(Succ(Zero)) == Succ(Zero); the `!=` is FALSE.
#[trust_vc::ensures(true)]
fn f_idn_neq() {
    trust_vc::assert!(idn(Nat::Succ(Box::new(Nat::Zero))) != Nat::Succ(Box::new(Nat::Zero)));
}

// ════════════ TRUE `!=` goals -> still Verified (no over-rejection) ════════════

// dbl(Succ(Zero)) == Succ(Succ(Zero)) != Zero: the `!=` is TRUE.
#[trust_vc::ensures(true)]
fn t_dbl_one_neq_zero() {
    trust_vc::assert!(dbl(Nat::Succ(Box::new(Nat::Zero))) != Nat::Zero);
}

// idn(Succ(Zero)) == Succ(Zero) != Zero: the `!=` is TRUE.
#[trust_vc::ensures(true)]
fn t_idn_neq_zero() {
    trust_vc::assert!(idn(Nat::Succ(Box::new(Nat::Zero))) != Nat::Zero);
}

// ════════════ `==` direction -> verdicts unchanged ════════════

// TRUE `==`: dbl(Succ(Zero)) == Succ(Succ(Zero)).
#[trust_vc::ensures(true)]
fn t_dbl_one_eq() {
    trust_vc::assert!(
        dbl(Nat::Succ(Box::new(Nat::Zero)))
            == Nat::Succ(Box::new(Nat::Succ(Box::new(Nat::Zero))))
    );
}

// FALSE `==` (off-by-one-Succ): dbl(Succ(Zero)) == Succ(Zero) is false.
#[trust_vc::ensures(true)]
fn f_dbl_one_eq_wrong() {
    trust_vc::assert!(dbl(Nat::Succ(Box::new(Nat::Zero))) == Nat::Succ(Box::new(Nat::Zero)));
}

// ════════════ TRUE `!=` under a hypothesis -> still Verified (gate withholds override) ════════════

// Under the equality hypothesis `n == Succ(Zero)`, `n != Zero` is TRUE. The
// closed-ground gate is OFF (a hypothesis is present), so the override never
// fires and the SMT `Verified` (resting on the hypothesis) is preserved.
#[trust_vc::ensures(true)]
fn neq_under_eq_hyp(n: Nat) {
    trust_vc::assume!(n == Nat::Succ(Box::new(Nat::Zero)));
    trust_vc::assert!(n != Nat::Zero);
}

// Under the disequality hypothesis `n != Zero`, `n != Zero` is TRUE (direct).
#[trust_vc::ensures(true)]
fn neq_under_neq_hyp(n: Nat) {
    trust_vc::assume!(n != Nat::Zero);
    trust_vc::assert!(n != Nat::Zero);
}
