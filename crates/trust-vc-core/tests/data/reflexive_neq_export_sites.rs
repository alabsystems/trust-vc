// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// DISCRIMINATOR fixtures, one per verdict-producing lane that can export an
// unsound `Verified` for a syntactic self-disequality `a != a`.
//
// `a != a` is false in EVERY model, so a `Verified` for it is necessarily
// unsound — it is the datatype-eq depth-1 UNSAT hole (ay case-splits datatype
// constructors only at solver scope-depth 0, but every obligation is discharged
// inside a `push` scope). The hypothesis-robust demote that closes it used to
// live ONLY on the regular-assertion lane
// (`typed_assertions::finish_regular_assertion_step`). Every function below
// reaches the solver through a DIFFERENT lane, and each one exports its
// `Verified` as an assumption for later obligations — so a false `Verified`
// here injects a contradiction and the deliberately-wrong `ensures` verifies.
//
// Every EXPLOIT function returns 0 while claiming `result == 1`. It must NEVER
// verify. Every CONTROL function is genuinely true and must STILL verify (the
// no-over-rejection direction the guard most endangers).

enum Nat {
    Zero,
    Succ(Box<Nat>),
}

#[trust_vc::spec]
#[trust_vc::decreases(n)]
fn dbl(n: Nat) -> Nat {
    match n {
        Nat::Zero => Nat::Zero,
        Nat::Succ(p) => Nat::Succ(Box::new(Nat::Succ(Box::new(dbl(*p))))),
    }
}

// ── LANE 2a: `assert ... by` CONCLUSION ──────────────────────────────────────
// A verified assert_by conclusion is pushed into `verified_assert_by` whenever
// `calc_step_exports_after_verification` holds (true for every non-calc
// assert_by). That vector becomes `verified_post_loop_facts` and is fed to the
// postcondition slices and to every later obligation — the WIDEST blast radius
// of all these lanes. The vacuity probe cannot catch it: it fires only when
// `context_publishes_unverified_axiom` holds (a genuine `#[broadcast]` lemma or
// a trait-method `ensures` axiom), and a forwarded assert_by is neither.
#[trust_vc::ensures(result == 1u64)]
fn assert_by_conclusion_export_exploit() -> u64 {
    trust_vc::assert_by!(
        dbl(Nat::Succ(Box::new(Nat::Zero))) != dbl(Nat::Succ(Box::new(Nat::Zero))),
        {}
    );
    0u64
}

// CONTROL for lane 2a: a genuinely TRUE datatype `!=` conclusion must still
// verify. `is_syntactic_self_disequality` needs STRUCTURALLY IDENTICAL
// operands, so this never enters the short circuit.
#[trust_vc::ensures(true)]
fn assert_by_conclusion_true_neq_control() {
    trust_vc::assert_by!(dbl(Nat::Succ(Box::new(Nat::Zero))) != Nat::Zero, {});
}

// ── LANE 2b: an assert_by's SCOPED assertions ────────────────────────────────
// Each scoped assertion is verified through the same `verify_typed_step` and
// pushed into `verified_assert_by_for_scope`, which is in scope for the
// conclusion.
#[trust_vc::ensures(result == 1u64)]
fn assert_by_scoped_export_exploit() -> u64 {
    trust_vc::assert_by!(true, {
        trust_vc::assert!(
            dbl(Nat::Succ(Box::new(Nat::Zero))) != dbl(Nat::Succ(Box::new(Nat::Zero)))
        );
    });
    0u64
}

// ── LANE 2c: the postcondition-forwarding PRE-PASS ───────────────────────────
// The pre-pass verifies each forwardable body assert in isolation and forwards
// the VERIFIED ones as assumptions for the postcondition, which is proved
// FIRST. It reaches the solver through `verify_typed_step`.
#[trust_vc::ensures(result == 1u64)]
fn forwarding_prepass_export_exploit() -> u64 {
    trust_vc::assert!(
        dbl(Nat::Succ(Box::new(Nat::Zero))) != dbl(Nat::Succ(Box::new(Nat::Zero)))
    );
    0u64
}

// ── LANE 1: the regular-assertion lane (already closed before this change) ───
// Kept here as the CONTROL that the pre-existing site did not regress.
#[trust_vc::ensures(true)]
fn regular_assertion_lane_control(m: u64) {
    trust_vc::assume!(m == 0u64);
    trust_vc::assert!(
        dbl(Nat::Succ(Box::new(Nat::Zero))) != dbl(Nat::Succ(Box::new(Nat::Zero)))
    );
}
