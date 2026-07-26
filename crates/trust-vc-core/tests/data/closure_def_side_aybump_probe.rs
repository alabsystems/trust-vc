// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// AY-BUMP adversarial probe for the closure DEF-SIDE isolation lane (fix
// eea3c5e), aimed at the ded7b9c7 `forall_inst` / assume-mismatch
// quantifier-expansion delta in the ay bump a998c3e3 -> 4df6ab25. Verified via
// `verify_function_from_file`, cache-OFF.
//
// THE HOLE THIS GUARDS: a spec-carrying `trust_vc::closure!` whose precondition
// is CONTRADICTORY must never inject that contradiction into the PARENT's
// assumption vector. The fix discharges the closure's `R ∧ res == BODY ⊢ E` in
// an ISOLATED child `VerificationContext` that is DISCARDED; the parent receives
// ZERO closure conjuncts, so a poisoned (UNSAT) parent that vacuously discharges
// every obligation (the cardinal false-verify) cannot arise.
//
// WHY A QUANTIFIED CONTRADICTION (not the existing literal `requires(false)`):
// two vacuity backstops protect the parent, and BOTH have a quantifier-shaped
// gap that only ded7b9c7 can pry open:
//   1. `check_vacuous_truth` (encoder/verification/vacuous.rs) solver-checks the
//      assumption set up front and downgrades an UNSAT set to
//      Unknown(VacuousTruth). It is `catch_unwind`-wrapped and, by its own
//      contract, SKIPS (falls through to normal verification) when a QUANTIFIED
//      assumption trips an encoding/sort mismatch. A ground `requires(false)` is
//      always caught here; a `forall` may slip through.
//   2. The `Verified -> VacuousTruth` broadcast-vacuity downgrade in
//      `finish_regular_assertion_step` / `verify_typed_step` is GATED on
//      `context_has_broadcast_lemma`. This fixture carries NO `#[broadcast]`
//      lemma, so that backstop is inert.
// With both backstops bypassed, if the closure's `forall` leaked into the parent
// AND ded7b9c7's newly-eager `forall_inst` instantiates it in the ASSERTION path
// (k := 5 -> 5 < 5 -> false), the parent's `assert!(false)` discharges under an
// UNSAT hypothesis and surfaces as a HARD `Verified` — with no VacuousTruth
// demotion. `forall(|k: int| k < 5)` is genuinely UNSAT yet only refutable by
// INSTANTIATING the universal, so it exercises exactly the new instantiation
// machinery the ground probe never touches.

// ---------------------------------------------------------------------------
// TARGET (must NOT verify — correct verdict: Counterexample). A never-called
// closure whose `requires` is a QUANTIFIED contradiction (`forall k. k < 5` is
// false, since 5 exists) sits alongside a parent `assert!(false)`. The closure's
// own def-side check is vacuously valid in the isolated child and contributes
// nothing; the parent's `assert!(false)` must Counterexample because the
// closure's `forall` never enters the parent's assumption set. A `Verified`
// here is the cardinal false-verify: the quantified contradiction leaked into
// the parent and ded7b9c7's `forall_inst` discharged the false assert vacuously.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn quantified_requires_contradiction_cannot_poison_parent() {
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(forall(|k: int| k < 5))
        ensures(|z: u64| z == y)
        y
    );
    trust_vc::assert!(false);
}

// ---------------------------------------------------------------------------
// POSITIVE CONTROL (must VERIFY). A def-side-valid closure with a SATISFIABLE
// quantified `requires` (`forall k. k <= k`, trivially true) and an ensures the
// body establishes. This confirms `forall(...)` inside a closure `requires` is
// ACCEPTED and reaches the solver — so the target above is genuinely exercising
// the quantifier path and is NOT passing merely because a `forall` requires
// fails closed at parse/extraction time (which would make the target's
// non-verify uninformative).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn def_side_quantified_requires_valid_verifies() {
    let _ = trust_vc::closure!(
        |y: u64| -> u64
        requires(forall(|k: int| k <= k))
        ensures(|z: u64| z == y)
        y
    );
}