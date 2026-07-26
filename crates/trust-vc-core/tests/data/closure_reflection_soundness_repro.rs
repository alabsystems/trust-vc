// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the Phase C closure-reflection adversarial soundness suite.
// Verified via verify_function_from_file in closure_reflection_soundness.rs.
//
// Reflection (`f.requires((a,))` / `f.ensures((a,), r)`) over a KNOWN LOCAL
// `trust_vc::closure!` literal lowers to the OPAQUE, DISJOINT UF predicates
// `call_requires%` / `call_ensures%`, whose meaning is fixed ONLY by a
// definitional-equality axiom co-emitted at the closure literal. The axiom
// cannot poison or rescue the parent (fresh symbol, conservative extension),
// and the independent def-side obligation forces the body to back the ensures.
// Direct application `f(..)` stays deferred (fail closed).

// ---------------------------------------------------------------------------
// PROBE 1 — CARDINAL lying-ensures false-verify (unchecked-closure). The body
// `y` does NOT establish the declared `ensures(z == 100)`, so the co-emitted
// def-side obligation COUNTEREXAMPLES; the reflection read `f.ensures((3,),100)`
// is definitionally `100 == 100 == true`, but that only fixes the UF value and
// NEVER rescues the failing def-side. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_lying_ensures_reflection_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 100u64)
        y
    );
    trust_vc::assert!(f.ensures((3u64,), 100u64));
}

// ---------------------------------------------------------------------------
// PROBE 2 — ACCEPTANCE / anti-vacuity. A def-side-VALID closure; the reflection
// asserts hold against the WRITTEN contract. This verifies ONLY if the axioms
// are wired AND the def-side passes. MUST verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_reflection_verified() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == y)
        y
    );
    trust_vc::assert!(f.requires((2u64,)));
    trust_vc::assert!(!f.ensures((2u64,), 3u64));
}

// ---------------------------------------------------------------------------
// PROBE 3 — reflection soundness (bad requires reflection). `f.requires((3,))`
// is definitionally `3 == 2 == false`, so the assert COUNTEREXAMPLES. MUST NOT
// verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_reflection_bad_requires_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == y)
        y
    );
    trust_vc::assert!(f.requires((3u64,)));
}

// ---------------------------------------------------------------------------
// PROBE 4 — capture fails closed. The ensures references a captured outer `c`.
// The capture guard fires BEFORE any reflection axiom is emitted, so `f` is
// never modeled and extraction fails closed. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_capture_reflection_fail_closed() {
    let mut c = 5u64;
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == c)
        c
    );
    c = 9u64;
    trust_vc::assert!(f.ensures((0u64,), 5u64));
}

// ---------------------------------------------------------------------------
// PROBE 5 — no-vacuity control. A BARE Rust closure carries no `closure!` spec,
// so there is no axiom to reflect and `f.requires(..)` fails to resolve. This
// confirms PROBE 2's pass comes from the closure! axioms, not a "reflection is
// always provable" bug. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_reflection_control_no_axiom() {
    let f = |y: u64| -> u64 { y };
    trust_vc::assert!(f.requires((2u64,)));
}

// ---------------------------------------------------------------------------
// PROBE 6 — loop-drop discipline. A closure defined in a loop body publishes its
// reflection axioms through add_assumption_noted, which DROPS loop-body
// assumptions. The in-loop reflection assert is a real obligation but cannot be
// discharged from the dropped axiom (fail closed) — no verified-by-leak. MUST
// NOT verify. (A `Verified` here would mean the axiom leaked out of the loop.)
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_reflection_loop_drop_fails_closed() {
    let mut i = 0u64;
    while i < 3u64 {
        let f = trust_vc::closure!(
            |y: u64| -> u64
            requires(y == 2u64)
            ensures(|z: u64| z == y)
            y
        );
        trust_vc::assert!(f.requires((2u64,)));
        i = i + 1u64;
    }
}

// ---------------------------------------------------------------------------
// PROBE 7 — direct application NOW VERIFIES (Phase C part 2). `f(2u64)` is the
// closure VALUE applied directly for a UNARY closure! literal: the call lowers to
// the shared `spec_fn_apply` UF and the call-site seam PROVES `f.requires(2)`
// (2 == 2) and ASSUMES `f.ensures(2, f(2))` (f(2) == 2), so the assert reading
// the identical term discharges. The def-side check independently backs the
// ensures. MUST VERIFY. (Formerly pinned as "still deferred"; that invariant is
// exactly what this increment removes for the unary-closure! case. The
// n-ary/bare-closure deferred pins live in the direct-application suite.)
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_direct_application_now_verifies() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == y)
        y
    );
    let t = f(2u64);
    trust_vc::assert!(t == 2u64);
}

// ---------------------------------------------------------------------------
// PROBE 8 — unmodelable-param closure stays fail-closed. A closure whose
// parameter type has no modelable SMT sort (`ProofPerm`, an unknown/opaque
// type — the SAME guard that keeps genuine proof_fn / linear-resource closures
// out of scope) registers NO reflection contract and its def-side rejects the
// unmodelable parameter, so `f.requires(..)` cannot resolve. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_unmodelable_param_closure_stays_deferred() {
    let f = trust_vc::closure!(
        |y: ProofPerm| -> u64
        requires(true)
        ensures(|z: u64| z == 0u64)
        0u64
    );
    trust_vc::assert!(f.requires((0u64,)));
}

// ---------------------------------------------------------------------------
// PROBE 9 — a caller cannot read a FALSE ensures as an established fact. The
// closure is def-side-VALID (`ensures(z == y)`, body `y`), so the function does
// not fail at the definition; but a reflection read of a WRONG postcondition
// value (`f.ensures((2,), 5)` = `5 == 2 == false`) must COUNTEREXAMPLE, proving
// call_ensures% carries only the definitional value, never "the closure returns
// 5 at 2". MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn probe_reflection_false_ensures_not_a_fact() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == y)
        y
    );
    trust_vc::assert!(f.ensures((2u64,), 5u64));
}
