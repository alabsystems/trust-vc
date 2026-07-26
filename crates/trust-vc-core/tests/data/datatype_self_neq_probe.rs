// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Soundness regression: a reflexive datatype `!=` (`a != a`) must not verify
// even under a (satisfiable) hypothesis — the datatype-eq depth-1 UNSAT hole
// reached by defeating goal_is_closed_ground.
enum Nat { Zero, Succ(Box<Nat>) }
#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn dbl(n: Nat) -> Nat {
    match n { Nat::Zero => Nat::Zero, Nat::Succ(p) => Nat::Succ(Box::new(Nat::Succ(Box::new(dbl(*p))))) }
}
// TARGET (must NOT verify): `a != a` is false by reflexivity; the assume does not
// make it true. Was Verified (false-verify); now Counterexample.
#[trust_vc::ensures(true)]
fn reflexive_datatype_neq_under_hyp_must_not_verify(m: u64) {
    trust_vc::assume!(m == 0u64);
    trust_vc::assert!(dbl(Nat::Succ(Box::new(Nat::Zero))) != dbl(Nat::Succ(Box::new(Nat::Zero))));
}
// CONTROL (must verify): a genuinely-true datatype `!=` is preserved.
#[trust_vc::ensures(true)]
fn true_datatype_neq_under_hyp_verifies(m: u64) {
    trust_vc::assume!(m == 0u64);
    trust_vc::assert!(dbl(Nat::Succ(Box::new(Nat::Zero))) != Nat::Zero);
}
